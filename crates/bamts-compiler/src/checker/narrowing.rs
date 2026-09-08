//! Control-flow narrowing and contextual typing over the interned
//! [`TypeTable`].
//!
//! The module has four layers, each driven by an outside caller (the
//! statement-level flow pass or the checker-side demand scheduler); nothing
//! here walks statements on its own.
//!
//! - **Flow facts.** A [`NarrowingContext`] owns an arena of flow frames.
//!   [`NarrowingContext::branch`] forks a frame, [`NarrowingContext::join`]
//!   merges forked frames back into their common parent by unioning the
//!   per-branch refinements, and [`NarrowingContext::type_at`] resolves the
//!   effective type of a [`FlowKey`] at one program point. Facts are keyed by
//!   *reference* — a rooted property path (`shape.kind`), not just a symbol —
//!   so discriminated-union member accesses narrow independently of their
//!   root.
//! - **Discriminant narrowing.** [`NarrowingGuard`] is the closed set of
//!   conditions the syntax layer can prove from a guard expression:
//!   `typeof`, `instanceof`, `in`, equality against a literal, and bare
//!   truthiness. [`NarrowingContext::guards_from`] extracts them from an
//!   [`Expr`] through the caller-supplied [`GuardResolver`] seam (the checker
//!   owns symbol resolution and expression typing; this module owns the
//!   control-flow logic). Each guard maps to one total algebra operation:
//!   [`NarrowingContext::narrow_typeof`], [`NarrowingContext::narrow_in`],
//!   [`NarrowingContext::narrow_equality`],
//!   [`NarrowingContext::narrow_instanceof`],
//!   [`NarrowingContext::narrow_truthiness`], and the union-discriminant
//!   special case [`NarrowingContext::narrow_discriminant`].
//! - **Contextual typing.** Object, array, and function literals take the
//!   type the surrounding position expects: [`NarrowingContext::contextual_property_type`]
//!   and [`NarrowingContext::contextual_element_type`] project a contextual
//!   composite into one member position, and
//!   [`NarrowingContext::contextual_function`] types a function literal
//!   against a contextual signature, filling unannotated parameters and
//!   unwrapping the awaited body return of `async` literals.
//! - **Demand-side packets.** The binder-prepared `ProgramFlow` graph models
//!   the syntax/control flow of one execution boundary. `FlowFacts` carries
//!   complete root/path state between narrowing sessions through
//!   `root_packet` and `install_root_packet`, and `analyze_definite_assignment`
//!   solves definite assignment for the C038 use-before-assignment check.
//!   Solutions are pure values; the single memo owner is the checker-side
//!   demand state (`assignment_memo`), keyed by the entry [`ScopeId`] of the
//!   analyzed boundary — one analysis per boundary, never cached in this
//!   module.
//!
//! Every operation is total. Opaque inputs — `any`, `unknown`, `error`, and
//! the nominal [`Type::Named`] / generic [`Type::Object`] members whose
//! runtime shape this closed type space cannot see — are never refined away:
//! they pass through both polarities of every narrowing unchanged, so one
//! unresolvable input never collapses a fact to `never`. When no guard
//! applies, the result is the input type unchanged.

use std::collections::{HashMap, HashSet, VecDeque};

use super::binder::{
    DeclId, ExecutionBoundary, ExecutionPoint, FlowPointId, FunctionParameter, ScopeId, SymbolId,
    Type, TypeId, TypeTable,
};
use crate::literal::number_value;
use crate::source::TextRange;
use crate::syntax::{
    BinaryExpression, BinaryOperator, Expr, Expression, IdentifierNode, Literal, LogicalOperator,
    MemberProperty, NodeId, Token, UnaryOperator,
};

/// A program point in the flow graph: one frame in the narrowing arena.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FlowNodeId(u32);

impl FlowNodeId {
    /// The entry point every context starts with.
    pub const ROOT: Self = Self(0);

    #[must_use]
    pub const fn get(self) -> u32 {
        self.0
    }

    const fn index(self) -> usize {
        self.0 as usize
    }
}

impl Default for FlowNodeId {
    fn default() -> Self {
        Self::ROOT
    }
}

/// A trackable reference: a rooted property-access chain such as `shape` or
/// `shape.kind`. Roots resolve through the checker's symbol table; path
/// segments are the cooked names of non-optional named member accesses.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FlowKey {
    root: SymbolId,
    path: Box<[Box<str>]>,
}

impl FlowKey {
    /// The flow key for a bare symbol reference.
    #[must_use]
    pub fn root(symbol: SymbolId) -> Self {
        Self {
            root: symbol,
            path: Box::new([]),
        }
    }

    /// Extends the key by one member-access segment (`key.name`).
    #[must_use]
    pub fn child(mut self, segment: &str) -> Self {
        let mut path = self.path.into_vec();
        path.push(segment.into());
        self.path = path.into_boxed_slice();
        self
    }

    /// The symbol the chain is rooted at.
    #[must_use]
    pub const fn root_symbol(&self) -> SymbolId {
        self.root
    }

    /// The member-access segments below the root, outermost first.
    #[must_use]
    pub fn path(&self) -> &[Box<str>] {
        &self.path
    }
}

/// The closed set of strings a `typeof` guard can compare against.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TypeofName {
    String,
    Number,
    BigInt,
    Boolean,
    Symbol,
    Undefined,
    Object,
    Function,
}

impl TypeofName {
    /// Parses the cooked string literal of a `typeof` comparison.
    #[must_use]
    pub fn from_keyword(text: &str) -> Option<Self> {
        Some(match text {
            "string" => Self::String,
            "number" => Self::Number,
            "bigint" => Self::BigInt,
            "boolean" => Self::Boolean,
            "symbol" => Self::Symbol,
            "undefined" => Self::Undefined,
            "object" => Self::Object,
            "function" => Self::Function,
            _ => return None,
        })
    }

    /// The runtime string this name corresponds to.
    #[must_use]
    pub const fn keyword(self) -> &'static str {
        match self {
            Self::String => "string",
            Self::Number => "number",
            Self::BigInt => "bigint",
            Self::Boolean => "boolean",
            Self::Symbol => "symbol",
            Self::Undefined => "undefined",
            Self::Object => "object",
            Self::Function => "function",
        }
    }
}

/// One narrowing condition extracted from a guard expression, with polarity.
///
/// `negated` records the polarity at the program point the guard is applied
/// to: the truthy branch of `if (x !== null)` applies
/// `Equality { negated: true, .. }`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NarrowingGuard {
    /// `typeof reference === "name"`.
    Typeof {
        reference: FlowKey,
        name: TypeofName,
        negated: bool,
    },
    /// `reference instanceof Class`; `class_type` is the resolver-typed right
    /// operand.
    Instanceof {
        reference: FlowKey,
        class_type: TypeId,
        negated: bool,
    },
    /// `"property" in reference`.
    In {
        reference: FlowKey,
        property: Box<str>,
        negated: bool,
    },
    /// `reference === literal`. A loose `== null` comparison is represented
    /// with `literal` as the `null | undefined` union.
    Equality {
        reference: FlowKey,
        literal: TypeId,
        negated: bool,
    },
    /// A bare reference used as a condition: truthiness narrowing.
    Truthiness { reference: FlowKey, negated: bool },
}

impl NarrowingGuard {
    /// The reference whose type this guard refines.
    #[must_use]
    pub fn reference(&self) -> &FlowKey {
        match self {
            Self::Typeof { reference, .. }
            | Self::Instanceof { reference, .. }
            | Self::In { reference, .. }
            | Self::Equality { reference, .. }
            | Self::Truthiness { reference, .. } => reference,
        }
    }

    /// The polarity at the program point this guard applies to.
    #[must_use]
    pub const fn negated(&self) -> bool {
        match self {
            Self::Typeof { negated, .. }
            | Self::Instanceof { negated, .. }
            | Self::In { negated, .. }
            | Self::Equality { negated, .. }
            | Self::Truthiness { negated, .. } => *negated,
        }
    }
}

/// The checker-owned facts the syntax interpretation layer needs. The real
/// adapter answers from a [`super::SemanticModel`]; tests can stub it.
pub trait GuardResolver {
    /// Resolves a value identifier to its bound symbol.
    fn resolve_identifier(&self, identifier: &IdentifierNode) -> Option<SymbolId>;

    /// Types an arbitrary expression with the checker's best current
    /// knowledge (used for the right operand of `instanceof`).
    fn expression_type(&self, expression: &Expr) -> TypeId;

    /// The raw source lexeme of one token. String lexemes retain their
    /// quotes, matching how the binder keys literal types.
    fn token_text(&self, token: &Token) -> &str;
}

/// Resolves an expression in reference position to its trackable flow key:
/// a bare identifier, or a chain of non-optional named member accesses over
/// one. Anything else (calls, computed or optional accesses, literals) is
/// not flow-trackable and yields `None`.
#[must_use]
pub fn flow_key_of(expression: &Expr, resolver: &dyn GuardResolver) -> Option<FlowKey> {
    match expression.data() {
        Expression::Identifier(identifier) => {
            Some(FlowKey::root(resolver.resolve_identifier(identifier)?))
        }
        Expression::Member(member) => {
            if member.optional {
                return None;
            }
            let key = flow_key_of(&member.object, resolver)?;
            let MemberProperty::Named(property) = &member.property else {
                return None;
            };
            let name = resolver.token_text(property.data().token());
            Some(key.child(name))
        }

        _ => None,
    }
}

/// The syntax/control-flow graph built by the lexical preparation pass.
///
/// `FlowPointId` belongs to this graph and is deliberately distinct from the
/// public [`FlowNodeId`] arena used by the older typed narrowing algebra.
#[derive(Clone, Debug, Default)]
pub(crate) struct ProgramFlow {
    pub(crate) points: HashMap<ExecutionPoint, FlowPointId>,
    pub(crate) nodes: Vec<ProgramFlowNode>,
    pub(crate) edges: Vec<FlowEdge>,
    pub(crate) incoming: Vec<Vec<usize>>,
    pub(crate) outgoing: Vec<Vec<usize>>,
    pub(crate) roots: Vec<FlowPointId>,
}

impl ProgramFlow {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Adds one point and returns its graph identity.
    ///
    /// The binder owns source traversal and therefore decides which
    /// operation belongs at the point. This helper only maintains the graph's
    /// point index.
    pub(crate) fn add_node(
        &mut self,
        point: ExecutionPoint,
        boundary: ScopeId,
        operation: FlowOperation,
    ) -> FlowPointId {
        let id = FlowPointId::new(
            u32::try_from(self.nodes.len()).expect("program flow point count fits in u32"),
        );
        self.points.insert(point, id);
        self.nodes.push(ProgramFlowNode {
            point,
            boundary,
            operation,
        });
        self.incoming.push(Vec::new());
        self.outgoing.push(Vec::new());
        id
    }

    /// Adds an edge while keeping incoming/outgoing indexes in sync.
    pub(crate) fn add_edge(&mut self, edge: FlowEdge) {
        let edge_index = self.edges.len();
        self.edges.push(edge);
        let from = usize::try_from(edge.from.get()).expect("flow point index fits in usize");
        let to = usize::try_from(edge.to.get()).expect("flow point index fits in usize");
        if let Some(outgoing) = self.outgoing.get_mut(from) {
            outgoing.push(edge_index);
        }
        if let Some(incoming) = self.incoming.get_mut(to) {
            incoming.push(edge_index);
        }
    }

    pub(crate) fn add_root(&mut self, root: FlowPointId) {
        if !self.roots.contains(&root) {
            self.roots.push(root);
        }
    }
}

/// One syntax/control node in [`ProgramFlow`].
#[derive(Clone, Debug)]
pub(crate) struct ProgramFlowNode {
    pub(crate) point: ExecutionPoint,
    pub(crate) boundary: ScopeId,
    pub(crate) operation: FlowOperation,
}

/// One directed control-flow edge.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct FlowEdge {
    pub(crate) from: FlowPointId,
    pub(crate) to: FlowPointId,
    pub(crate) kind: FlowEdgeKind,
}

/// The semantic role of a control-flow edge.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[expect(
    dead_code,
    reason = "variants constructed only by the unwired demand pass"
)]
pub(crate) enum FlowEdgeKind {
    Sequential,
    Guarded,
    Join,
    Assignment,
    Captured,
    LoopBackedge,
    Abrupt,
    ConservativeCatch,
    Finally,
}

fn is_entry_operation(node: &ProgramFlowNode) -> bool {
    matches!(node.operation, FlowOperation::Entry)
        && matches!(node.point.boundary, ExecutionBoundary::Entry)
}

fn is_assignment_transfer_edge(kind: FlowEdgeKind, target_is_join: bool) -> bool {
    match kind {
        FlowEdgeKind::Sequential
        | FlowEdgeKind::Guarded
        | FlowEdgeKind::Join
        | FlowEdgeKind::Assignment
        | FlowEdgeKind::ConservativeCatch => true,
        // A backedge feeds the loop test but is not a normal post-loop join
        // predecessor.
        FlowEdgeKind::LoopBackedge => !target_is_join,
        // A normal try path may enter a finally block. It must not be
        // mistaken for a direct predecessor of the post-finally join.
        FlowEdgeKind::Finally => !target_is_join,
        FlowEdgeKind::Captured | FlowEdgeKind::Abrupt => false,
    }
}

/// The operation performed at one graph point.
#[derive(Clone, Debug)]
#[expect(
    dead_code,
    reason = "variants constructed only by the unwired demand pass"
)]
pub(crate) enum FlowOperation {
    Entry,
    Pass,
    Guard {
        condition: NodeId,
        polarity: GuardPolarity,
        value_point: FlowPointId,
    },
    Write {
        target: FlowKey,
        value: Option<NodeId>,
        value_point: FlowPointId,
    },
    DeclarationComplete {
        declaration: DeclId,
        assigned_roots: Box<[SymbolId]>,
    },
    Capture {
        source: FlowPointId,
        boundary: ScopeId,
    },
    Join,
    LoopSummary {
        entry: FlowPointId,
        body_exit: FlowPointId,
        skipped: Option<FlowPointId>,
    },
    Exit,
}

/// Branch polarity for a symbolic guard.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[expect(dead_code, reason = "used only by unwired symbolic-guard demand facet")]
pub(crate) enum GuardPolarity {
    Truthy,
    Falsy,
}

/// A guard retained symbolically until its expression/type dependencies are
/// available to the demand scheduler.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[expect(
    dead_code,
    reason = "guards retained for the not-yet-wired demand scheduler"
)]
pub(crate) struct SymbolicGuard {
    pub(crate) condition: NodeId,
    pub(crate) polarity: GuardPolarity,
    pub(crate) value_point: FlowPointId,
}

/// The complete root/path type state at one flow frame, as a value snapshot.
///
/// A packet is *closed*: it always contains the root key for `root`
/// ([`FlowKey::root`]) mapped to `effective_root`, plus every path
/// refinement visible at the frame it was taken from. `paths` is sorted in
/// *packet order* — root symbol id, then path segments — so packets for the
/// same visible state compare equal and the order is stable across
/// re-computation. [`FlowFacts::install_root_packet`] turns a packet back
/// into a self-contained frame: the round trip packet → frame → packet is a
/// fixpoint, no fact gained or lost.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RootFlowPacket {
    /// The root symbol the packet describes.
    pub(crate) root: SymbolId,
    /// The declared type, as registered with [`NarrowingContext::declare`];
    /// the fallback when no refinement touches the root.
    pub(crate) declared: TypeId,
    /// The innermost visible refinement of the root key, or `declared`.
    pub(crate) effective_root: TypeId,
    /// Every visible key for `root` (the root key included) with its
    /// effective type, sorted as described above.
    pub(crate) paths: Box<[(FlowKey, TypeId)]>,
}

/// Definite-assignment lattice values.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum AssignmentState {
    Assigned,
    Unassigned,
}

/// Reachability is kept separate from assignment so unreachable arms cannot
/// contaminate a meet.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum AssignmentReachability {
    Unreachable,
    Reachable(AssignmentState),
}

/// One finite assignment solution for a complete `ProgramFlow`, as a pure
/// memo value.
///
/// A solution covers exactly one execution boundary. The single memo owner
/// is the checker-side demand state (`assignment_memo`), keyed by the entry
/// [`ScopeId`] of the analyzed boundary — one analysis per boundary,
/// computed once. This module only produces fresh solutions; the analyzer
/// is pure (same graph and roots yield the same result), so a memo miss is
/// safe but never expected for an already-analyzed boundary.
///
/// Per root, only same-boundary points carry
/// [`AssignmentReachability::Reachable`] states; every other point of the
/// graph records [`AssignmentReachability::Unreachable`], keeping foreign
/// boundaries from contaminating a query.
#[derive(Clone, Debug, Default)]
pub(crate) struct AssignmentAnalysis {
    /// `(FlowPointId, SymbolId)` → state. Keys are graph-local indices into
    /// the analyzed `ProgramFlow` and must never be mixed across graphs.
    pub(crate) states: HashMap<(FlowPointId, SymbolId), AssignmentReachability>,
}

impl AssignmentAnalysis {
    /// The recorded state at one graph point, or `None` when the analysis
    /// never visited that point/root pair.
    #[must_use]
    pub(crate) fn state_at(
        &self,
        point: FlowPointId,
        root: SymbolId,
    ) -> Option<AssignmentReachability> {
        self.states.get(&(point, root)).copied()
    }
}

/// One root's entry seed for definite-assignment analysis.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct AssignmentRoot {
    pub(crate) symbol: SymbolId,
    pub(crate) boundary: ScopeId,
    pub(crate) entry: AssignmentState,
    pub(crate) declaration: DeclId,
}

/// A use-site record consumed by the check-owned C038 predicate.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct AssignmentUse {
    pub(crate) symbol: SymbolId,
    pub(crate) point: FlowPointId,
    pub(crate) scope: ScopeId,
    pub(crate) range: TextRange,
    pub(crate) live: bool,
    pub(crate) suppressed: bool,
    pub(crate) final_type: TypeId,
}

const fn assignment_meet(left: AssignmentState, right: AssignmentState) -> AssignmentState {
    match (left, right) {
        (AssignmentState::Assigned, AssignmentState::Assigned) => AssignmentState::Assigned,
        _ => AssignmentState::Unassigned,
    }
}

fn point_index(point: FlowPointId, len: usize) -> Option<usize> {
    let index = usize::try_from(point.get()).ok()?;
    (index < len).then_some(index)
}

fn point_id(index: usize) -> FlowPointId {
    FlowPointId::new(u32::try_from(index).expect("flow point count fits in u32"))
}

/// Computes definite assignment with a finite monotone worklist.
///
/// Reachability is solved first. Assignment then starts at the top element
/// (`Assigned`) for reachable non-entry points and descends only when a
/// reachable, same-boundary predecessor proves `Unassigned`. Captured and
/// abrupt edges never transfer assignment state; a normal `Finally` edge may
/// enter the finally body but cannot act as a direct post-finally join input.
/// The result is one [`AssignmentAnalysis`] for this graph: assignment
/// states are only ever propagated between same-boundary points (per root),
/// and the value's per-boundary scoping guarantees are documented on the
/// type.
pub(crate) fn analyze_definite_assignment(
    flow: &ProgramFlow,
    roots: &[AssignmentRoot],
    cancel: Option<&bamts_cancel::CancellationToken>,
) -> Result<AssignmentAnalysis, bamts_cancel::Cancelled> {
    let node_count = flow.nodes.len();
    let mut reachable = vec![false; node_count];
    let mut reach_queue = VecDeque::new();

    let initial_roots = if flow.roots.is_empty() {
        flow.nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| is_entry_operation(node).then_some(index))
            .collect::<Vec<_>>()
    } else {
        flow.roots
            .iter()
            .filter_map(|point| point_index(*point, node_count))
            .collect::<Vec<_>>()
    };
    for index in initial_roots {
        if !reachable[index] {
            reachable[index] = true;
            reach_queue.push_back(index);
        }
    }
    while let Some(index) = reach_queue.pop_front() {
        if let Some(token) = cancel {
            token.check()?;
        }
        let Some(outgoing) = flow.outgoing.get(index) else {
            continue;
        };
        for edge_index in outgoing {
            let Some(edge) = flow.edges.get(*edge_index) else {
                continue;
            };
            let Some(target) = point_index(edge.to, node_count) else {
                continue;
            };
            if !reachable[target] {
                reachable[target] = true;
                reach_queue.push_back(target);
            }
        }
    }

    let mut analysis = AssignmentAnalysis::default();
    for root in roots {
        if let Some(token) = cancel {
            token.check()?;
        }
        let mut queue = VecDeque::new();
        let mut queued = HashSet::new();

        for (index, node) in flow.nodes.iter().enumerate() {
            if !reachable[index] {
                analysis.states.insert(
                    (point_id(index), root.symbol),
                    AssignmentReachability::Unreachable,
                );
                continue;
            }
            let point = point_id(index);
            let initial = if node.boundary == root.boundary && is_entry_operation(node) {
                AssignmentReachability::Reachable(root.entry)
            } else if node.boundary == root.boundary {
                AssignmentReachability::Reachable(AssignmentState::Assigned)
            } else {
                AssignmentReachability::Unreachable
            };
            analysis.states.insert((point, root.symbol), initial);
            if node.boundary == root.boundary {
                queue.push_back(index);
                queued.insert(index);
            }
        }

        while let Some(index) = queue.pop_front() {
            queued.remove(&index);
            if let Some(token) = cancel {
                token.check()?;
            }
            let node = &flow.nodes[index];
            if !reachable[index] || node.boundary != root.boundary {
                continue;
            }

            let point = point_id(index);
            let desired = if is_entry_operation(node) {
                AssignmentReachability::Reachable(root.entry)
            } else {
                let mut meet = None;
                if let Some(incoming) = flow.incoming.get(index) {
                    for edge_index in incoming {
                        let Some(edge) = flow.edges.get(*edge_index) else {
                            continue;
                        };
                        let target_is_join = matches!(node.operation, FlowOperation::Join);
                        if !is_assignment_transfer_edge(edge.kind, target_is_join) {
                            continue;
                        }
                        let Some(predecessor) = point_index(edge.from, node_count) else {
                            continue;
                        };
                        if !reachable[predecessor]
                            || flow.nodes[predecessor].boundary != root.boundary
                        {
                            continue;
                        }
                        let predecessor_point = point_id(predecessor);
                        let Some(AssignmentReachability::Reachable(state)) =
                            analysis.state_at(predecessor_point, root.symbol)
                        else {
                            continue;
                        };
                        meet = Some(match meet {
                            Some(current) => assignment_meet(current, state),
                            None => state,
                        });
                    }
                }
                AssignmentReachability::Reachable(meet.unwrap_or(AssignmentState::Unassigned))
            };

            let desired = match (&node.operation, desired) {
                (
                    FlowOperation::DeclarationComplete { assigned_roots, .. },
                    AssignmentReachability::Reachable(_),
                ) if assigned_roots.contains(&root.symbol) => {
                    AssignmentReachability::Reachable(AssignmentState::Assigned)
                }
                (FlowOperation::Write { target, .. }, AssignmentReachability::Reachable(_))
                    if target.root_symbol() == root.symbol && target.path().is_empty() =>
                {
                    AssignmentReachability::Reachable(AssignmentState::Assigned)
                }
                (_, state) => state,
            };

            if analysis.states.get(&(point, root.symbol)).copied() != Some(desired) {
                analysis.states.insert((point, root.symbol), desired);
                if let Some(outgoing) = flow.outgoing.get(index) {
                    for edge_index in outgoing {
                        let Some(edge) = flow.edges.get(*edge_index) else {
                            continue;
                        };
                        let Some(successor) = point_index(edge.to, node_count) else {
                            continue;
                        };
                        if flow.nodes[successor].boundary == root.boundary
                            && queued.insert(successor)
                        {
                            queue.push_back(successor);
                        }
                    }
                }
            }
        }
    }
    Ok(analysis)
}

/// One frame of flow facts: the refinements that hold at one program point,
/// relative to the frame it forked from.
#[derive(Clone, Debug)]
struct FlowFrame {
    parent: Option<FlowNodeId>,
    facts: HashMap<FlowKey, TypeId>,
}

/// The per-member decision of a narrowing filter. `Replace` covers members
/// that refine rather than drop, such as `boolean` narrowing to `true`.
enum Narrow {
    Keep,
    Drop,
    Replace(TypeId),
}

/// Flow facts accumulated over one flow pass: the declared type of every
/// trackable symbol plus the frame forest of refinements.
///
/// Walk frames chain to the frame they forked from; packet frames installed
/// by `FlowFacts::install_root_packet` are parentless baselines, so the
/// frames form a forest of independent rooted snapshots.
///
/// State lives here rather than in [`NarrowingContext`] so the checker can own
/// it across a whole walk while the [`TypeTable`] stays borrowable between
/// narrowing steps.
#[derive(Clone, Debug)]
pub struct FlowFacts {
    declared: HashMap<SymbolId, TypeId>,
    frames: Vec<FlowFrame>,
}

impl Default for FlowFacts {
    fn default() -> Self {
        Self::new()
    }
}

impl FlowFacts {
    /// Opens an empty fact table whose only frame is [`FlowNodeId::ROOT`].
    #[must_use]
    pub fn new() -> Self {
        Self {
            declared: HashMap::new(),
            frames: vec![FlowFrame {
                parent: None,
                facts: HashMap::new(),
            }],
        }
    }

    /// Materializes all effective root/path facts visible at one frame.
    ///
    /// The walk starts at `flow` and ascends the parent chain, innermost
    /// frame first: the first frame that refines a key wins, and the walk
    /// stops at a frame with no parent. Packet frames are deliberately
    /// parentless, so a packet frame's answers come entirely from the packet.
    /// The root is undeclared → `Ok(None)`.
    ///
    /// The returned packet meets the [`RootFlowPacket`] contract: closed, in
    /// packet order, and a value snapshot safe for a demand frame to retain
    /// while another frame computes a different root.
    pub(crate) fn root_packet(
        &self,
        flow: FlowNodeId,
        root: SymbolId,
        cancel: Option<&bamts_cancel::CancellationToken>,
    ) -> Result<Option<RootFlowPacket>, bamts_cancel::Cancelled> {
        let Some(declared) = self.declared.get(&root).copied() else {
            return Ok(None);
        };
        let mut visible = HashMap::<FlowKey, TypeId>::new();
        let mut current = Some(flow);
        while let Some(id) = current {
            if let Some(token) = cancel {
                token.check()?;
            }
            let Some(frame) = self.frames.get(id.index()) else {
                break;
            };
            for (key, ty) in &frame.facts {
                if key.root_symbol() == root && !visible.contains_key(key) {
                    visible.insert(key.clone(), *ty);
                }
            }
            current = frame.parent;
        }

        let root_key = FlowKey::root(root);
        let effective_root = visible.get(&root_key).copied().unwrap_or(declared);
        visible.insert(root_key, effective_root);
        let mut paths = visible.into_iter().collect::<Vec<_>>();
        paths.sort_by(|(left, _), (right, _)| {
            left.root_symbol()
                .get()
                .cmp(&right.root_symbol().get())
                .then_with(|| {
                    left.path()
                        .iter()
                        .map(|segment| segment.as_ref())
                        .cmp(right.path().iter().map(|segment| segment.as_ref()))
                })
        });
        Ok(Some(RootFlowPacket {
            root,
            declared,
            effective_root,
            paths: paths.into_boxed_slice(),
        }))
    }

    /// Installs a packet as a fresh parentless baseline frame.
    ///
    /// The new frame has no parent, so it terminates the parent chain and every
    /// later lookup (`type_at`, `root_packet`, or refinements forked from the
    /// returned id) resolves entirely inside the packet. That self-containment
    /// is what lets a demand frame carry the packet across narrowing sessions
    /// without keeping the producer's frames alive. The root key is
    /// (re-)inserted from `effective_root`, so even a hand-built packet yields
    /// a closed frame, and the packet's `declared` type is registered for the
    /// root so `root_packet` can answer for it. Installing the same packet
    /// twice produces two equal-content frames with distinct ids.
    #[cfg_attr(not(test), expect(dead_code, reason = "awaits demand-frame producer"))]
    pub(crate) fn install_root_packet(&mut self, packet: &RootFlowPacket) -> FlowNodeId {
        let mut facts = HashMap::with_capacity(packet.paths.len() + 1);
        for (key, ty) in packet.paths.iter() {
            facts.insert(key.clone(), *ty);
        }
        facts.insert(FlowKey::root(packet.root), packet.effective_root);
        self.declared.insert(packet.root, packet.declared);
        self.frames.push(FlowFrame {
            parent: None,
            facts,
        });
        FlowNodeId(u32::try_from(self.frames.len() - 1).expect("flow frame count fits in u32"))
    }
}

/// Narrowing algebra over one interned [`TypeTable`] and one [`FlowFacts`].
///
/// Register the declared type of every trackable symbol with
/// [`NarrowingContext::declare`], then drive it over the syntax: fork frames
/// with [`NarrowingContext::branch`], apply guard conditions with
/// [`NarrowingContext::narrow_by_condition`], and merge frames with
/// [`NarrowingContext::join`].
pub struct NarrowingContext<'a> {
    table: &'a mut TypeTable,
    facts: &'a mut FlowFacts,
    /// Cooperative cancellation signal. `None` for the non-cancellable path.
    cancel: Option<bamts_cancel::CancellationToken>,
}

impl<'a> NarrowingContext<'a> {
    /// Borrows `table` and `facts` for one narrowing step.
    #[must_use]
    pub fn new(table: &'a mut TypeTable, facts: &'a mut FlowFacts) -> Self {
        Self::new_with_cancel(table, facts, None)
    }

    /// Borrows `table` and `facts` for one narrowing step, polling `cancel`
    /// during flow traversal loops. Pass `None` for the non-cancellable path.
    #[must_use]
    pub fn new_with_cancel(
        table: &'a mut TypeTable,
        facts: &'a mut FlowFacts,
        cancel: Option<bamts_cancel::CancellationToken>,
    ) -> Self {
        Self {
            table,
            facts,
            cancel,
        }
    }

    /// Registers the declared type of a trackable symbol: the fallback every
    /// flow lookup returns to when no refinement applies.
    pub fn declare(&mut self, symbol: SymbolId, declared: TypeId) {
        self.facts.declared.insert(symbol, declared);
    }

    /// The declared type of a symbol, if registered.
    #[must_use]
    pub fn declared_type(&self, symbol: SymbolId) -> Option<TypeId> {
        self.facts.declared.get(&symbol).copied()
    }

    /// Forks a frame that inherits every fact visible at `flow`.
    pub fn branch(&mut self, flow: FlowNodeId) -> FlowNodeId {
        self.push_frame(Some(flow), HashMap::new())
    }

    /// Merges forked frames back into `parent`: each key refined by any
    /// branch is unioned across all branches, with unrefined branches
    /// contributing the parent's effective type. Keys whose union equals the
    /// parent's effective type record no fact, keeping frames sparse.
    ///
    /// Branches are expected to descend from `parent` through
    /// [`NarrowingContext::branch`]; a frame that does not contributes
    /// nothing.
    pub fn join(&mut self, parent: FlowNodeId, branches: &[FlowNodeId]) -> FlowNodeId {
        match branches {
            [] => return parent,
            [single] => return *single,
            _ => {}
        }
        let mut candidates: Vec<FlowKey> = Vec::new();
        for branch in branches {
            for key in self.delta_facts(parent, *branch).into_keys() {
                if !candidates.contains(&key) {
                    candidates.push(key);
                }
            }
        }
        let mut facts = HashMap::new();
        for key in candidates {
            let base = self.type_at(parent, &key);
            let mut arms = Vec::with_capacity(branches.len());
            for branch in branches {
                match (self.type_at(*branch, &key), base) {
                    (Some(ty), _) => arms.push(ty),
                    (None, Some(base)) => arms.push(base),
                    (None, None) => {}
                }
            }
            if arms.is_empty() {
                continue;
            }
            let union = self.table.union(&arms);
            if Some(union) != base {
                facts.insert(key, union);
            }
        }
        self.push_frame(Some(parent), facts)
    }

    /// Records an unconditional fact — an assignment's new declared type, or
    /// a guard's refinement — at one program point.
    pub fn refine(&mut self, flow: FlowNodeId, key: FlowKey, ty: TypeId) {
        self.facts.frames[flow.index()].facts.insert(key, ty);
    }

    /// Invalidates refinements affected by a write to `key`. A write can
    /// invalidate both facts below that path and facts for its narrowed
    /// ancestors (for example, writing `shape.kind` invalidates a refinement
    /// of `shape` derived from that discriminant). Inherited facts are
    /// shadowed with their projections from the root's declared type.
    pub fn invalidate(&mut self, flow: FlowNodeId, key: &FlowKey) {
        let mut affected = Vec::new();
        let mut current = Some(flow);
        while let Some(id) = current {
            if let Some(token) = &self.cancel
                && token.is_cancelled()
            {
                return;
            }
            let frame = &self.facts.frames[id.index()];
            for candidate in frame.facts.keys() {
                if candidate.root == key.root
                    && (candidate.path.starts_with(&key.path)
                        || key.path.starts_with(&candidate.path))
                    && !affected.contains(candidate)
                {
                    affected.push(candidate.clone());
                }
            }
            current = frame.parent;
        }

        for candidate in affected {
            let Some(declared) = self.facts.declared.get(&candidate.root).copied() else {
                continue;
            };
            let Some(baseline) = self.project(declared, &candidate.path) else {
                continue;
            };
            self.facts.frames[flow.index()]
                .facts
                .insert(candidate, baseline);
        }
    }

    /// The refined type of a reference at one program point, looking only at
    /// the flow-frame facts and never falling back to a declared projection.
    #[must_use]
    pub fn refined_type_at(&mut self, flow: FlowNodeId, key: &FlowKey) -> Option<TypeId> {
        let mut current = Some(flow);
        while let Some(id) = current {
            if let Some(token) = &self.cancel
                && token.is_cancelled()
            {
                return None;
            }
            let frame = &self.facts.frames[id.index()];
            if let Some(ty) = frame.facts.get(key) {
                return Some(*ty);
            }
            current = frame.parent;
        }
        None
    }

    /// The effective type of a reference at one program point: the nearest
    /// refinement walking up the frame chain, else the declared root type
    /// projected through the key's property path, else `None` for
    /// undeclared roots.
    #[must_use]
    pub fn type_at(&mut self, flow: FlowNodeId, key: &FlowKey) -> Option<TypeId> {
        if let Some(ty) = self.refined_type_at(flow, key) {
            return Some(ty);
        }
        let mut current = Some(flow);
        while let Some(id) = current {
            let frame = &self.facts.frames[id.index()];
            let ancestor = frame
                .facts
                .iter()
                .filter(|(candidate, _)| {
                    candidate.root_symbol() == key.root_symbol()
                        && candidate.path().len() < key.path().len()
                        && key.path().starts_with(candidate.path())
                })
                .max_by_key(|(candidate, _)| candidate.path().len())
                .map(|(candidate, ty)| (*ty, candidate.path().len()));
            if let Some((ty, prefix_len)) = ancestor {
                return self.project(ty, &key.path()[prefix_len..]);
            }
            current = frame.parent;
        }
        let declared = self.facts.declared.get(&key.root_symbol()).copied()?;
        self.project(declared, key.path())
    }

    /// Extracts every guard a condition proves, with polarity. `negated` is
    /// the polarity of the program point: `false` extracts the facts for the
    /// condition's truthy branch, `true` for its falsy branch. De Morgan
    /// constrains composition: a conjunction proves both operands on its
    /// truthy side, a disjunction proves both on its falsy side, and the
    /// other two combinations prove nothing individually.
    #[must_use]
    pub fn guards_from(
        &mut self,
        condition: &Expr,
        resolver: &dyn GuardResolver,
        negated: bool,
    ) -> Vec<NarrowingGuard> {
        let mut guards = Vec::new();
        self.collect_guards(condition, resolver, negated, &mut guards);
        guards
    }

    /// Refines one program point by one guard. Undeclared references are a
    /// no-op, keeping the operation total. An equality guard on a
    /// single-segment property path (`shape.kind === "circle"`) additionally
    /// discriminates the root reference's union by that property.
    pub fn apply_guard(&mut self, flow: FlowNodeId, guard: &NarrowingGuard) {
        let key = guard.reference().clone();
        let Some(current) = self.type_at(flow, &key) else {
            return;
        };
        let narrowed = match guard {
            NarrowingGuard::Typeof { name, negated, .. } => {
                self.narrow_typeof(current, *name, *negated)
            }
            NarrowingGuard::Instanceof {
                class_type,
                negated,
                ..
            } => self.narrow_instanceof(current, *class_type, *negated),
            NarrowingGuard::In {
                property, negated, ..
            } => self.narrow_in(current, property, *negated),
            NarrowingGuard::Equality {
                literal, negated, ..
            } => self.narrow_equality(current, *literal, *negated),
            NarrowingGuard::Truthiness { negated, .. } => self.narrow_truthiness(current, *negated),
        };
        if narrowed != current {
            self.facts.frames[flow.index()]
                .facts
                .insert(key.clone(), narrowed);
        }
        if let NarrowingGuard::Equality {
            literal, negated, ..
        } = guard
            && let [segment] = key.path()
        {
            let root = FlowKey::root(key.root_symbol());
            if let Some(root_current) = self.type_at(flow, &root) {
                let root_narrowed =
                    self.narrow_discriminant(root_current, segment, *literal, *negated);
                if root_narrowed != root_current {
                    self.facts.frames[flow.index()]
                        .facts
                        .insert(root, root_narrowed);
                }
            }
        }
    }

    /// Applies a conjunction of guards in order.
    pub fn apply_guards(&mut self, flow: FlowNodeId, guards: &[NarrowingGuard]) {
        for guard in guards {
            self.apply_guard(flow, guard);
        }
    }

    /// Extracts the guards `condition` proves and applies them to `flow` in
    /// one step. `truthy` selects the polarity: the facts that hold when the
    /// condition evaluates truthy, or when it evaluates falsy.
    pub fn narrow_by_condition(
        &mut self,
        flow: FlowNodeId,
        condition: &Expr,
        resolver: &dyn GuardResolver,
        truthy: bool,
    ) {
        let guards = self.guards_from(condition, resolver, !truthy);
        self.apply_guards(flow, &guards);
    }

    /// Narrows to (or away from) the types whose `typeof` is `name`.
    /// `typeof null` is `"object"`, and `void` behaves as `undefined`.
    /// `AppliedClass` instances are runtime objects (`typeof new C() ===
    /// "object"`), so `typeof x === "function"` removes them and `typeof x
    /// === "object"` keeps them. Nominal (`Named`) and generic-object
    /// (`Object`) members remain runtime-opaque and pass both polarities
    /// unchanged.
    #[must_use]
    pub fn narrow_typeof(&mut self, ty: TypeId, name: TypeofName, negated: bool) -> TypeId {
        self.filter(ty, &|table, candidate| match candidate {
            Type::Named(_)
            | Type::Object
            | Type::Keyof(_)
            | Type::IndexedAccess { .. }
            | Type::Record { .. } => Narrow::Keep,
            _ if typeof_matches(table, candidate, name) != negated => Narrow::Keep,
            _ => Narrow::Drop,
        })
    }

    /// Narrows to (or away from) `class_type`. Positive narrowing is the
    /// type intersection: a member already inside the class stays itself, a
    /// member the class fits inside narrows to the class.
    #[must_use]
    pub fn narrow_instanceof(&mut self, ty: TypeId, class_type: TypeId, negated: bool) -> TypeId {
        if negated {
            self.subtract(ty, class_type)
        } else {
            self.intersect(ty, class_type)
        }
    }

    /// Narrows by the `"property" in x` test: positive keeps object members
    /// declaring the property, negative drops them. Members whose property
    /// set is opaque (arrays, functions, nominal and generic objects) pass
    /// both polarities; primitives can only take the negative branch.
    #[must_use]
    pub fn narrow_in(&mut self, ty: TypeId, property: &str, negated: bool) -> TypeId {
        self.filter(ty, &|_, candidate| match candidate {
            Type::ObjectType(object) => {
                let declares = object
                    .properties
                    .iter()
                    .any(|member| member.name() == property);
                if declares != negated {
                    Narrow::Keep
                } else {
                    Narrow::Drop
                }
            }
            Type::Object
            | Type::Function(_)
            | Type::Array(_)
            | Type::Named(_)
            | Type::AppliedClass { .. } => Narrow::Keep,
            _ if negated => Narrow::Keep,
            _ => Narrow::Drop,
        })
    }

    /// Narrows by equality with a literal type. Positive keeps the
    /// intersection (`x === "a"` narrows `string` to `"a"`); negative
    /// removes only the members the literal fully covers (`x !== "a"` drops
    /// the `"a"` member but keeps `string`). A `null | undefined` union
    /// literal models loose `== null`.
    #[must_use]
    pub fn narrow_equality(&mut self, ty: TypeId, literal: TypeId, negated: bool) -> TypeId {
        if negated {
            self.subtract(ty, literal)
        } else {
            self.intersect(ty, literal)
        }
    }

    /// Narrows by truthiness: the truthy branch drops definitely-falsy
    /// members and refines `boolean` to `true`; the falsy branch keeps
    /// possibly-falsy members and refines `boolean` to `false`. Nominal
    /// members are runtime-opaque and pass both polarities.
    #[must_use]
    pub fn narrow_truthiness(&mut self, ty: TypeId, negated: bool) -> TypeId {
        let boolean_replacement = self.table.boolean_literal(!negated);
        self.filter(ty, &|_, candidate| {
            if matches!(candidate, Type::Boolean) {
                return Narrow::Replace(boolean_replacement);
            }
            if negated {
                if possibly_falsy(candidate) {
                    Narrow::Keep
                } else {
                    Narrow::Drop
                }
            } else if definitely_falsy(candidate) {
                Narrow::Drop
            } else {
                Narrow::Keep
            }
        })
    }

    /// Narrows a union of object types by one discriminant property's
    /// literal value. Positive keeps the members whose property type
    /// overlaps the literal; negative drops only the members whose property
    /// type the literal fully covers. Members without modeled properties
    /// pass both polarities; modeled objects lacking the property survive
    /// only the negative.
    #[must_use]
    pub fn narrow_discriminant(
        &mut self,
        ty: TypeId,
        property: &str,
        literal: TypeId,
        negated: bool,
    ) -> TypeId {
        if let Some(view) = self.table.prepare_applied_alias_view(ty)
            && view != ty
        {
            return self.narrow_discriminant(view, property, literal, negated);
        }
        match self.table.get(ty).clone() {
            Type::Error | Type::Intersection(_) | Type::Any | Type::Unknown => ty,
            Type::Union(members) => {
                let mut kept = Vec::with_capacity(members.len());
                for member in members {
                    if matches!(self.table.get(member), Type::AppliedAlias { .. }) {
                        let narrowed = self.narrow_discriminant(member, property, literal, negated);
                        if !matches!(self.table.get(narrowed), Type::Never) {
                            kept.push(narrowed);
                        }
                    } else if self.discriminant_keeps(member, property, literal, negated) {
                        kept.push(member);
                    }
                }
                self.table.union(&kept)
            }
            Type::This { constraint, .. } => {
                let narrowed = self.narrow_discriminant(constraint, property, literal, negated);
                if matches!(self.table.get(narrowed), Type::Never) {
                    narrowed
                } else {
                    ty
                }
            }
            Type::AppliedAlias { .. } => ty,
            _ if self.discriminant_keeps(ty, property, literal, negated) => ty,
            Type::Never
            | Type::Void
            | Type::Null
            | Type::Undefined
            | Type::Boolean
            | Type::Number
            | Type::BigInt
            | Type::String
            | Type::Symbol
            | Type::Object
            | Type::BooleanLiteral(_)
            | Type::NumberLiteral(_)
            | Type::StringLiteral(_)
            | Type::BigIntLiteral(_)
            | Type::Array(_)
            | Type::Tuple(_)
            | Type::ObjectType(_)
            | Type::Function(_)
            | Type::Named(_)
            | Type::AppliedClass { .. }
            | Type::NumericEnum(_)
            | Type::EnumMember { .. }
            | Type::Keyof(_)
            | Type::IndexedAccess { .. }
            | Type::Record { .. }
            | Type::ConstructorType { .. } => self.table.never(),
        }
    }

    /// Types a function literal against a contextual signature. Unannotated
    /// parameters take the contextual parameter at their position (or `any`
    /// when the context has none); annotated parameters keep their
    /// annotation. The return is the body's inferred return, awaited for
    /// `async` literals — promise wrapping is not modeled, so an async
    /// literal's type carries the awaited body type its eventual
    /// `Promise`-returning context is checked against.
    #[must_use]
    pub fn contextual_function(
        &mut self,
        contextual: TypeId,
        parameters: &[Option<TypeId>],
        body_return: TypeId,
        is_async: bool,
    ) -> TypeId {
        if let Some(view) = self.table.prepare_applied_alias_view(contextual)
            && view != contextual
        {
            return self.contextual_function(view, parameters, body_return, is_async);
        }
        let contextual_signature = match self.table.get(contextual) {
            Type::This { constraint, .. } => {
                return self.contextual_function(*constraint, parameters, body_return, is_async);
            }
            Type::Function(signature) => Some(signature.clone()),
            Type::Error
            | Type::Intersection(_)
            | Type::Any
            | Type::Unknown
            | Type::Never
            | Type::Void
            | Type::Null
            | Type::Undefined
            | Type::Boolean
            | Type::Number
            | Type::BigInt
            | Type::String
            | Type::Symbol
            | Type::Object
            | Type::BooleanLiteral(_)
            | Type::NumberLiteral(_)
            | Type::StringLiteral(_)
            | Type::BigIntLiteral(_)
            | Type::Array(_)
            | Type::Tuple(_)
            | Type::Union(_)
            | Type::ObjectType(_)
            | Type::Named(_)
            | Type::AppliedClass { .. }
            | Type::AppliedAlias { .. }
            | Type::NumericEnum(_)
            | Type::EnumMember { .. }
            | Type::Keyof(_)
            | Type::IndexedAccess { .. }
            | Type::Record { .. }
            | Type::ConstructorType { .. } => None,
        };
        let parameters: Vec<FunctionParameter> = parameters
            .iter()
            .enumerate()
            .map(|(index, declared)| {
                let type_id = declared.unwrap_or_else(|| {
                    contextual_signature
                        .as_ref()
                        .and_then(|signature| {
                            signature
                                .parameters()
                                .get(index)
                                .map(FunctionParameter::type_id)
                        })
                        .unwrap_or_else(|| self.table.any())
                });
                FunctionParameter::new(format!("arg{index}"), type_id, false, false)
            })
            .collect();
        let return_type = if is_async {
            self.awaited_type(body_return)
        } else {
            body_return
        };
        self.table
            .function_with_parameters(Vec::new(), parameters, return_type)
    }

    /// The contextual type of one named member position: the property type
    /// of an object contextual type, distributed over unions. `None` when
    /// the context carries no member information (primitives, `any`,
    /// `unknown`, or a union member lacking the property).
    #[must_use]
    pub fn contextual_property_type(&mut self, contextual: TypeId, name: &str) -> Option<TypeId> {
        self.property_type(contextual, name)
    }

    /// The contextual type of one array-element position, distributed over
    /// unions.
    #[must_use]
    pub fn contextual_element_type(&mut self, contextual: TypeId) -> Option<TypeId> {
        if let Some(view) = self.table.prepare_applied_alias_view(contextual)
            && view != contextual
        {
            return self.contextual_element_type(view);
        }
        match self.table.get(contextual).clone() {
            Type::This { constraint, .. } => self.contextual_element_type(constraint),
            Type::Array(element) => Some(element),
            Type::Union(members) => {
                let mut elements = Vec::with_capacity(members.len());
                for member in members {
                    elements.push(self.contextual_element_type(member)?);
                }
                Some(self.table.union(&elements))
            }
            Type::Error
            | Type::Intersection(_)
            | Type::Any
            | Type::Unknown
            | Type::Never
            | Type::Void
            | Type::Null
            | Type::Undefined
            | Type::Boolean
            | Type::Number
            | Type::BigInt
            | Type::String
            | Type::Symbol
            | Type::Object
            | Type::BooleanLiteral(_)
            | Type::NumberLiteral(_)
            | Type::StringLiteral(_)
            | Type::BigIntLiteral(_)
            | Type::Tuple(_)
            | Type::ObjectType(_)
            | Type::Function(_)
            | Type::Named(_)
            | Type::AppliedClass { .. }
            | Type::AppliedAlias { .. }
            | Type::NumericEnum(_)
            | Type::EnumMember { .. }
            | Type::Keyof(_)
            | Type::IndexedAccess { .. }
            | Type::Record { .. }
            | Type::ConstructorType { .. } => None,
        }
    }

    /// The type of an array literal: the normalized union of its element
    /// types as the element type.
    #[must_use]
    pub fn array_literal_type(&mut self, elements: &[TypeId]) -> TypeId {
        let element = self.table.union(elements);
        self.table.array(element)
    }

    /// The `Awaited<T>` of the closed type space: thenables are not modeled,
    /// so awaiting distributes over unions and is the identity otherwise.
    #[must_use]
    pub fn awaited_type(&mut self, ty: TypeId) -> TypeId {
        if let Some(view) = self.table.prepare_applied_alias_view(ty)
            && view != ty
        {
            return self.awaited_type(view);
        }
        match self.table.get(ty).clone() {
            Type::Union(members) => {
                let awaited: Vec<TypeId> = members
                    .iter()
                    .map(|member| self.awaited_type(*member))
                    .collect();
                self.table.union(&awaited)
            }
            Type::Error
            | Type::Intersection(_)
            | Type::Any
            | Type::Unknown
            | Type::Never
            | Type::Void
            | Type::Null
            | Type::Undefined
            | Type::Boolean
            | Type::Number
            | Type::BigInt
            | Type::String
            | Type::Symbol
            | Type::Object
            | Type::BooleanLiteral(_)
            | Type::NumberLiteral(_)
            | Type::StringLiteral(_)
            | Type::BigIntLiteral(_)
            | Type::Array(_)
            | Type::Tuple(_)
            | Type::ObjectType(_)
            | Type::Function(_)
            | Type::Named(_)
            | Type::AppliedClass { .. }
            | Type::AppliedAlias { .. }
            | Type::NumericEnum(_)
            | Type::EnumMember { .. }
            | Type::Keyof(_)
            | Type::IndexedAccess { .. }
            | Type::Record { .. }
            | Type::This { .. }
            | Type::ConstructorType { .. } => ty,
        }
    }

    fn push_frame(
        &mut self,
        parent: Option<FlowNodeId>,
        facts: HashMap<FlowKey, TypeId>,
    ) -> FlowNodeId {
        let id = FlowNodeId(
            u32::try_from(self.facts.frames.len()).expect("flow node count fits in u32"),
        );
        self.facts.frames.push(FlowFrame { parent, facts });
        id
    }

    /// The facts introduced between an ancestor frame and its descendant,
    /// nearest-to-the-descendant first. A frame that does not descend from
    /// the ancestor contributes nothing.
    fn delta_facts(
        &self,
        ancestor: FlowNodeId,
        descendant: FlowNodeId,
    ) -> HashMap<FlowKey, TypeId> {
        let mut facts = HashMap::new();
        let mut current = Some(descendant);
        while let Some(id) = current {
            if let Some(token) = &self.cancel
                && token.is_cancelled()
            {
                return facts;
            }
            if id == ancestor {
                return facts;
            }
            let frame = &self.facts.frames[id.index()];
            for (key, ty) in &frame.facts {
                facts.entry(key.clone()).or_insert(*ty);
            }
            current = frame.parent;
        }
        HashMap::new()
    }

    /// The type of one property access, distributed over unions. `None`
    /// when any member cannot supply the property — the access is then not
    /// flow-trackable through this path.
    fn property_type(&mut self, ty: TypeId, name: &str) -> Option<TypeId> {
        if let Some(view) = self.table.prepare_applied_alias_view(ty)
            && view != ty
        {
            return self.property_type(view, name);
        }
        if let Some(view) = self.table.prepare_applied_class_view(ty) {
            return self.property_type(view, name);
        }
        match self.table.get(ty).clone() {
            Type::Union(members) => {
                let mut found = Vec::with_capacity(members.len());
                for member in members {
                    found.push(self.property_type(member, name)?);
                }
                Some(self.table.union(&found))
            }
            Type::Intersection(members) => {
                let mut found = Vec::new();
                for member in members {
                    if let Some(property) = self.property_type(member, name) {
                        found.push(property);
                    }
                }
                let mut found = found.into_iter();
                let first = found.next()?;
                Some(found.fold(first, |combined, property| {
                    self.intersect(combined, property)
                }))
            }
            Type::AppliedAlias { .. } => None,
            _ => match self.table.read_property_type(ty, name) {
                Some(property) => Some(property),
                None => self.table.property_type(ty, name),
            },
        }
    }
    fn project(&mut self, mut ty: TypeId, path: &[Box<str>]) -> Option<TypeId> {
        for segment in path {
            ty = self.property_type(ty, segment)?;
        }
        Some(ty)
    }

    /// Applies a keep/drop/replace decision member-wise. Opaque types
    /// (`any`, `unknown`, `error`) are returned unrefined, both as whole
    /// types and as union members.
    fn filter(&mut self, ty: TypeId, decide: &dyn Fn(&TypeTable, &Type) -> Narrow) -> TypeId {
        if let Some(view) = self.table.prepare_applied_alias_view(ty)
            && view != ty
        {
            return self.filter(view, decide);
        }
        match self.table.get(ty).clone() {
            Type::This { constraint, .. } => match decide(self.table, self.table.get(constraint)) {
                Narrow::Keep | Narrow::Replace(_) => ty,
                Narrow::Drop => self.table.never(),
            },
            Type::AppliedAlias { .. } => ty,
            Type::Error | Type::Intersection(_) | Type::Any | Type::Unknown => ty,
            Type::Union(members) => {
                let mut kept = Vec::with_capacity(members.len());
                for member in members {
                    if matches!(self.table.get(member), Type::Error) {
                        kept.push(member);
                        continue;
                    }
                    if matches!(self.table.get(member), Type::AppliedAlias { .. }) {
                        let narrowed = self.filter(member, decide);
                        if !matches!(self.table.get(narrowed), Type::Never) {
                            kept.push(narrowed);
                        }
                        continue;
                    }
                    match decide(self.table, self.table.get(member)) {
                        Narrow::Keep => kept.push(member),
                        Narrow::Drop => {}
                        Narrow::Replace(replacement) => kept.push(replacement),
                    }
                }
                self.table.union(&kept)
            }
            Type::Never
            | Type::Void
            | Type::Null
            | Type::Undefined
            | Type::Boolean
            | Type::Number
            | Type::BigInt
            | Type::String
            | Type::Symbol
            | Type::Object
            | Type::BooleanLiteral(_)
            | Type::NumberLiteral(_)
            | Type::StringLiteral(_)
            | Type::BigIntLiteral(_)
            | Type::Array(_)
            | Type::Tuple(_)
            | Type::ObjectType(_)
            | Type::Function(_)
            | Type::Named(_)
            | Type::AppliedClass { .. }
            | Type::NumericEnum(_)
            | Type::EnumMember { .. }
            | Type::Keyof(_)
            | Type::IndexedAccess { .. }
            | Type::Record { .. }
            | Type::ConstructorType { .. } => match decide(self.table, self.table.get(ty)) {
                Narrow::Keep => ty,
                Narrow::Drop => self.table.never(),
                Narrow::Replace(replacement) => replacement,
            },
        }
    }

    /// The intersection of two types in the closed space: `other` when it
    /// fits inside `ty`, `ty` when it fits inside `other`, distributed over
    /// unions on either side, `never` when the two do not overlap. Opaque
    /// inputs are returned unrefined, both as whole types and as union
    /// members.
    fn intersect(&mut self, ty: TypeId, other: TypeId) -> TypeId {
        if matches!(self.table.get(ty), Type::AppliedAlias { .. }) {
            let Some(view) = self.table.prepare_applied_alias_view(ty) else {
                return ty;
            };
            return if view == ty {
                ty
            } else {
                self.intersect(view, other)
            };
        }
        if matches!(self.table.get(other), Type::AppliedAlias { .. }) {
            let Some(view) = self.table.prepare_applied_alias_view(other) else {
                return ty;
            };
            return if view == other {
                ty
            } else {
                self.intersect(ty, view)
            };
        }
        match self.table.get(ty) {
            Type::Error | Type::Any | Type::Unknown | Type::Never => return ty,
            _ => {}
        }
        // A union carrying an `error` member must distribute: the shortcuts
        // below would collapse the union and drop the member.
        if let Type::Union(members) = self.table.get(ty).clone()
            && members
                .iter()
                .any(|member| matches!(self.table.get(*member), Type::Error))
        {
            let parts: Vec<TypeId> = members
                .iter()
                .map(|member| self.intersect(*member, other))
                .collect();
            return self.table.union(&parts);
        }
        if self.table.assignable(other, ty) {
            return other;
        }
        if self.table.assignable(ty, other) {
            return ty;
        }
        match (self.table.get(ty).clone(), self.table.get(other).clone()) {
            (Type::Union(members), _) => {
                let parts: Vec<TypeId> = members
                    .iter()
                    .map(|member| self.intersect(*member, other))
                    .collect();
                self.table.union(&parts)
            }
            (_, Type::Union(members)) => {
                let parts: Vec<TypeId> = members
                    .iter()
                    .map(|member| self.intersect(ty, *member))
                    .collect();
                self.table.union(&parts)
            }
            (
                Type::Error
                | Type::Intersection(_)
                | Type::Any
                | Type::Unknown
                | Type::Never
                | Type::Void
                | Type::Null
                | Type::Undefined
                | Type::Boolean
                | Type::Number
                | Type::BigInt
                | Type::String
                | Type::Symbol
                | Type::Object
                | Type::BooleanLiteral(_)
                | Type::NumberLiteral(_)
                | Type::StringLiteral(_)
                | Type::BigIntLiteral(_)
                | Type::Array(_)
                | Type::Tuple(_)
                | Type::ObjectType(_)
                | Type::Function(_)
                | Type::Named(_)
                | Type::AppliedClass { .. }
                | Type::AppliedAlias { .. }
                | Type::NumericEnum(_)
                | Type::EnumMember { .. }
                | Type::Keyof(_)
                | Type::IndexedAccess { .. }
                | Type::Record { .. }
                | Type::This { .. }
                | Type::ConstructorType { .. },
                _,
            ) => self.table.never(),
        }
    }

    /// Removes the members of `ty` that `excluded` fully covers. Members
    /// wider than the exclusion (`string` minus `"a"`) survive, matching
    /// TypeScript's inability to subtract a value from a primitive. An
    /// opaque exclusion (`any`, `unknown`, `error`) covers nothing
    /// provably, so the input passes through unchanged, and `error` union
    /// members are never dropped.
    fn subtract(&mut self, ty: TypeId, excluded: TypeId) -> TypeId {
        if matches!(self.table.get(excluded), Type::AppliedAlias { .. }) {
            let Some(view) = self.table.prepare_applied_alias_view(excluded) else {
                return ty;
            };
            if view == excluded {
                return ty;
            }
            return self.subtract(ty, view);
        }
        if matches!(self.table.get(ty), Type::AppliedAlias { .. }) {
            let Some(view) = self.table.prepare_applied_alias_view(ty) else {
                return ty;
            };
            if view == ty {
                return ty;
            }
            return self.subtract(view, excluded);
        }
        match self.table.get(excluded) {
            Type::Error | Type::Intersection(_) | Type::Any | Type::Unknown => return ty,
            Type::Never
            | Type::Void
            | Type::Null
            | Type::Undefined
            | Type::Boolean
            | Type::Number
            | Type::BigInt
            | Type::String
            | Type::Symbol
            | Type::Object
            | Type::BooleanLiteral(_)
            | Type::NumberLiteral(_)
            | Type::StringLiteral(_)
            | Type::BigIntLiteral(_)
            | Type::Array(_)
            | Type::Tuple(_)
            | Type::Union(_)
            | Type::ObjectType(_)
            | Type::Function(_)
            | Type::Named(_)
            | Type::AppliedClass { .. }
            | Type::AppliedAlias { .. }
            | Type::NumericEnum(_)
            | Type::EnumMember { .. }
            | Type::Keyof(_)
            | Type::IndexedAccess { .. }
            | Type::Record { .. }
            | Type::This { .. }
            | Type::ConstructorType { .. } => {}
        }
        match self.table.get(ty).clone() {
            Type::Error | Type::Intersection(_) | Type::Any | Type::Unknown | Type::Never => ty,
            Type::Union(members) => {
                let mut kept = Vec::with_capacity(members.len());
                for member in members {
                    if matches!(self.table.get(member), Type::Error)
                        || !self.table.assignable(member, excluded)
                    {
                        kept.push(member);
                    }
                }
                self.table.union(&kept)
            }
            _ if self.table.assignable(ty, excluded) => self.table.never(),
            Type::Void
            | Type::Null
            | Type::Undefined
            | Type::Boolean
            | Type::Number
            | Type::BigInt
            | Type::String
            | Type::Symbol
            | Type::Object
            | Type::BooleanLiteral(_)
            | Type::NumberLiteral(_)
            | Type::StringLiteral(_)
            | Type::BigIntLiteral(_)
            | Type::Array(_)
            | Type::Tuple(_)
            | Type::ObjectType(_)
            | Type::Function(_)
            | Type::Named(_)
            | Type::AppliedClass { .. }
            | Type::AppliedAlias { .. }
            | Type::NumericEnum(_)
            | Type::EnumMember { .. }
            | Type::Keyof(_)
            | Type::IndexedAccess { .. }
            | Type::This { .. }
            | Type::Record { .. }
            | Type::ConstructorType { .. } => ty,
        }
    }

    fn discriminant_keeps(
        &mut self,
        member: TypeId,
        property: &str,
        literal: TypeId,
        negated: bool,
    ) -> bool {
        if matches!(
            self.table.get(member),
            Type::Error | Type::Any | Type::Unknown
        ) {
            return true;
        }
        let property_type = self.property_type(member, property);
        let Some(property_type) = property_type else {
            // A member lacking the discriminant cannot have produced the
            // tested value positively; it always survives the negative.
            return negated;
        };
        if negated {
            !self.table.assignable(property_type, literal)
        } else {
            self.table.assignable(literal, property_type)
                || self.table.assignable(property_type, literal)
        }
    }
    fn collect_guards(
        &mut self,
        expression: &Expr,
        resolver: &dyn GuardResolver,
        negated: bool,
        guards: &mut Vec<NarrowingGuard>,
    ) {
        match expression.data() {
            Expression::Parenthesized(inner) => {
                self.collect_guards(inner, resolver, negated, guards);
            }
            Expression::Unary(unary) if unary.operator == UnaryOperator::Not => {
                self.collect_guards(&unary.argument, resolver, !negated, guards);
            }
            Expression::Binary(binary) => {
                self.collect_binary_guards(binary, resolver, negated, guards);
            }
            Expression::Logical(logical) => {
                let provable = matches!(
                    (logical.operator, negated),
                    (LogicalOperator::And, false) | (LogicalOperator::Or, true)
                );
                if provable {
                    self.collect_guards(&logical.left, resolver, negated, guards);
                    self.collect_guards(&logical.right, resolver, negated, guards);
                }
            }
            _ => {
                if let Some(reference) = flow_key_of(expression, resolver) {
                    guards.push(NarrowingGuard::Truthiness { reference, negated });
                }
            }
        }
    }

    fn collect_binary_guards(
        &mut self,
        binary: &BinaryExpression,
        resolver: &dyn GuardResolver,
        negated: bool,
        guards: &mut Vec<NarrowingGuard>,
    ) {
        match binary.operator {
            BinaryOperator::StrictEqual
            | BinaryOperator::Equal
            | BinaryOperator::StrictNotEqual
            | BinaryOperator::NotEqual => {
                let negated = negated
                    ^ matches!(
                        binary.operator,
                        BinaryOperator::StrictNotEqual | BinaryOperator::NotEqual
                    );
                if let Some(guard) = typeof_guard(&binary.left, &binary.right, resolver, negated)
                    .or_else(|| typeof_guard(&binary.right, &binary.left, resolver, negated))
                {
                    guards.push(guard);
                    return;
                }
                let loose = matches!(
                    binary.operator,
                    BinaryOperator::Equal | BinaryOperator::NotEqual
                );
                if let Some(guard) = self
                    .equality_guard(&binary.left, &binary.right, resolver, negated, loose)
                    .or_else(|| {
                        self.equality_guard(&binary.right, &binary.left, resolver, negated, loose)
                    })
                {
                    guards.push(guard);
                }
            }
            BinaryOperator::Instanceof => {
                if let Some(reference) = flow_key_of(&binary.left, resolver) {
                    let class_type = resolver.expression_type(&binary.right);
                    guards.push(NarrowingGuard::Instanceof {
                        reference,
                        class_type,
                        negated,
                    });
                }
            }
            BinaryOperator::In => {
                if let Expression::Literal(Literal::String(name)) = binary.left.data()
                    && let Some(reference) = flow_key_of(&binary.right, resolver)
                {
                    let property = unquote(resolver.token_text(name.data().token()));
                    guards.push(NarrowingGuard::In {
                        reference,
                        property: property.into(),
                        negated,
                    });
                }
            }
            _ => {}
        }
    }

    /// Builds an equality guard from a reference side and a literal side.
    /// The `undefined` global reads as the `undefined` type; a loose
    /// `== null` or `== undefined` widens the literal to the
    /// `null | undefined` union.
    fn equality_guard(
        &mut self,
        reference_side: &Expr,
        literal_side: &Expr,
        resolver: &dyn GuardResolver,
        negated: bool,
        loose: bool,
    ) -> Option<NarrowingGuard> {
        let reference = flow_key_of(reference_side, resolver)?;
        let mut literal = self
            .literal_type(literal_side, resolver)
            .or_else(|| self.undefined_identifier(literal_side, resolver))?;
        if loose && matches!(self.table.get(literal), Type::Null | Type::Undefined) {
            literal = self
                .table
                .union(&[self.table.null_type(), self.table.undefined_type()]);
        }
        Some(NarrowingGuard::Equality {
            reference,
            literal,
            negated,
        })
    }

    /// The interned literal type of a literal expression.
    fn literal_type(&mut self, expression: &Expr, resolver: &dyn GuardResolver) -> Option<TypeId> {
        match expression.data() {
            Expression::Literal(Literal::String(token)) => {
                let text = resolver.token_text(token.data().token());
                Some(self.table.string_literal_lexeme(text))
            }
            Expression::Literal(Literal::Number(token)) => {
                let text = resolver.token_text(token.data().token());
                Some(self.table.number_literal(text))
            }
            Expression::Literal(Literal::BigInt(token)) => {
                let text = resolver.token_text(token.data().token());
                Some(self.table.bigint_literal(text))
            }
            Expression::Literal(Literal::Boolean(token)) => {
                let value = resolver.token_text(token.data().token()) == "true";
                Some(self.table.boolean_literal(value))
            }
            Expression::Literal(Literal::Null(_)) => Some(self.table.null_type()),
            _ => None,
        }
    }

    fn undefined_identifier(
        &mut self,
        expression: &Expr,
        resolver: &dyn GuardResolver,
    ) -> Option<TypeId> {
        let Expression::Identifier(identifier) = expression.data() else {
            return None;
        };
        if resolver.token_text(identifier.data().token()) == "undefined" {
            Some(self.table.undefined_type())
        } else {
            None
        }
    }
}

/// Extracts a `typeof reference === "name"` guard from one operand order.
fn typeof_guard(
    maybe_typeof: &Expr,
    maybe_name: &Expr,
    resolver: &dyn GuardResolver,
    negated: bool,
) -> Option<NarrowingGuard> {
    let Expression::Unary(unary) = maybe_typeof.data() else {
        return None;
    };
    if unary.operator != UnaryOperator::Typeof {
        return None;
    }
    let Expression::Literal(Literal::String(name)) = maybe_name.data() else {
        return None;
    };
    let name = TypeofName::from_keyword(unquote(resolver.token_text(name.data().token())))?;
    let reference = flow_key_of(&unary.argument, resolver)?;
    Some(NarrowingGuard::Typeof {
        reference,
        name,
        negated,
    })
}

/// The runtime `typeof` strings of the modeled types.
fn typeof_matches(table: &TypeTable, ty: &Type, name: TypeofName) -> bool {
    if let Type::Intersection(members) = ty {
        return members
            .iter()
            .any(|member| typeof_matches(table, table.get(*member), name));
    }
    match name {
        TypeofName::String => matches!(
            ty,
            Type::String
                | Type::StringLiteral(_)
                | Type::EnumMember {
                    string_value: Some(_),
                    ..
                }
        ),
        TypeofName::Number => {
            matches!(
                ty,
                Type::Number
                    | Type::NumberLiteral(_)
                    | Type::NumericEnum(_)
                    | Type::EnumMember {
                        string_value: None,
                        ..
                    }
            )
        }
        TypeofName::BigInt => matches!(ty, Type::BigInt | Type::BigIntLiteral(_)),
        TypeofName::Boolean => matches!(ty, Type::Boolean | Type::BooleanLiteral(_)),
        TypeofName::Symbol => matches!(ty, Type::Symbol),
        TypeofName::Undefined => matches!(ty, Type::Undefined | Type::Void),
        TypeofName::Object => matches!(
            ty,
            Type::ObjectType(_)
                | Type::Array(_)
                | Type::Tuple(_)
                | Type::Null
                | Type::AppliedClass { .. }
        ),
        TypeofName::Function => matches!(ty, Type::Function(_)),
    }
}

/// Members that always evaluate falsy: the nullish types, `false`, zero
/// numeric and bigint literals, and empty string literals.
fn definitely_falsy(ty: &Type) -> bool {
    match ty {
        Type::Null | Type::Undefined | Type::Void => true,
        Type::BooleanLiteral(value) => !value,
        Type::NumberLiteral(text) => number_value(text) == Some(0.0),
        Type::StringLiteral(text) => text.is_empty(),
        Type::EnumMember {
            string_value: Some(value),
            ..
        } => value.is_empty(),
        Type::BigIntLiteral(text) => bigint_literal_is_zero(text),
        _ => false,
    }
}

/// Members that can evaluate falsy: everything definitely falsy plus the
/// primitives that contain a falsy value, numeric enums (zero-valued
/// members), and runtime-opaque nominal types.
fn possibly_falsy(ty: &Type) -> bool {
    match ty {
        Type::Null
        | Type::Undefined
        | Type::Void
        | Type::Boolean
        | Type::Number
        | Type::String
        | Type::BigInt
        | Type::NumericEnum(_)
        | Type::EnumMember {
            string_value: None, ..
        }
        | Type::Named(_)
        | Type::AppliedClass { .. } => true,
        _ => definitely_falsy(ty),
    }
}

fn bigint_literal_is_zero(lexeme: &str) -> bool {
    let Some(digits) = lexeme.strip_suffix('n') else {
        return false;
    };
    let digits = digits
        .strip_prefix("0x")
        .or_else(|| digits.strip_prefix("0X"))
        .or_else(|| digits.strip_prefix("0o"))
        .or_else(|| digits.strip_prefix("0O"))
        .or_else(|| digits.strip_prefix("0b"))
        .or_else(|| digits.strip_prefix("0B"))
        .unwrap_or(digits);
    !digits.is_empty()
        && digits
            .chars()
            .filter(|digit| *digit != '_')
            .all(|digit| digit == '0')
}

/// Strips one pair of matching quotes, or `None` for unquoted text.
fn unquote_if_quoted(text: &str) -> Option<&str> {
    text.strip_prefix('"')
        .and_then(|inner| inner.strip_suffix('"'))
        .or_else(|| {
            text.strip_prefix('\'')
                .and_then(|inner| inner.strip_suffix('\''))
        })
}

/// The text with surrounding quotes removed when present.
fn unquote(text: &str) -> &str {
    unquote_if_quoted(text).unwrap_or(text)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::checker::{PropertyType, SemanticModel};
    use crate::diagnostic::Recovered;
    use crate::source::{ScriptKind, SourceId, SourceText};
    use crate::syntax::{FunctionBody, SourceFile, Statement, Stmt};
    use crate::{parser, scanner};
    use std::sync::Arc;

    fn symbol(id: u32) -> SymbolId {
        SymbolId::new(id)
    }

    // ---- typeof narrowing ---------------------------------------------------

    #[test]
    fn typeof_narrows_union_members_by_keyword_in_both_polarities() {
        let mut table = TypeTable::new();
        let (string, number, null, never, any) = (
            table.string(),
            table.number(),
            table.null_type(),
            table.never(),
            table.any(),
        );
        let union = table.union(&[string, number, null]);
        let number_or_null = table.union(&[number, null]);
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        assert_eq!(
            context.narrow_typeof(union, TypeofName::String, false),
            string
        );
        assert_eq!(
            context.narrow_typeof(union, TypeofName::String, true),
            number_or_null
        );
        // `typeof null === "object"`.
        assert_eq!(
            context.narrow_typeof(union, TypeofName::Object, false),
            null
        );
        // A single matching type stays itself; a mismatching one empties.
        assert_eq!(
            context.narrow_typeof(number, TypeofName::Number, false),
            number
        );
        assert_eq!(
            context.narrow_typeof(number, TypeofName::String, false),
            never
        );
        // Opaque input is never refined.
        assert_eq!(context.narrow_typeof(any, TypeofName::String, false), any);
        assert_eq!(context.narrow_typeof(any, TypeofName::String, true), any);
    }

    // ---- equality narrowing -------------------------------------------------

    #[test]
    fn equality_narrows_to_the_literal_and_subtracts_it_when_negated() {
        let mut table = TypeTable::new();
        let (string, number, null, undefined, any) = (
            table.string(),
            table.number(),
            table.null_type(),
            table.undefined_type(),
            table.any(),
        );
        let (a, b) = (table.string_literal("a"), table.string_literal("b"));
        let union = table.union(&[string, number]);
        let literal_union = table.union(&[a, b]);
        let nullable = table.union(&[string, null]);
        let nullish = table.union(&[null, undefined]);
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        // `x === "a"` narrows a union containing string to the literal.
        assert_eq!(context.narrow_equality(union, a, false), a);
        // `x !== "a"` removes only the exact literal member.
        assert_eq!(context.narrow_equality(literal_union, a, true), b);
        // `x !== "a"` cannot subtract from the primitive: it stays whole.
        assert_eq!(context.narrow_equality(string, a, true), string);
        // Nullability: `x === null` keeps null, `x !== null` removes it.
        assert_eq!(context.narrow_equality(nullable, null, false), null);
        assert_eq!(context.narrow_equality(nullable, null, true), string);
        // A `null | undefined` union literal (loose `== null`) intersects to
        // exactly the nullish members and subtracts both.
        assert_eq!(context.narrow_equality(nullish, nullish, false), nullish);
        assert_eq!(context.narrow_equality(nullable, nullish, true), string);
        // Opaque input is never refined.
        assert_eq!(context.narrow_equality(any, a, false), any);
        assert_eq!(context.narrow_equality(any, a, true), any);
    }

    // ---- in narrowing -------------------------------------------------------

    #[test]
    fn in_narrowing_keeps_members_declaring_the_property() {
        let mut table = TypeTable::new();
        let kinded = table.object_type(vec![PropertyType::new("kind", false, table.string())]);
        let other = table.object_type(vec![PropertyType::new("other", false, table.number())]);
        let union = table.union(&[kinded, other]);
        let (number, never) = (table.number(), table.never());
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        assert_eq!(context.narrow_in(union, "kind", false), kinded);
        assert_eq!(context.narrow_in(union, "kind", true), other);
        // Primitives can only take the negative branch.
        assert_eq!(context.narrow_in(number, "kind", false), never);
        assert_eq!(context.narrow_in(number, "kind", true), number);
    }

    // ---- union discrimination -----------------------------------------------

    #[test]
    fn discriminant_narrowing_filters_union_variants_by_the_literal() {
        let mut table = TypeTable::new();
        let (circle_tag, square_tag) = (
            table.string_literal("circle"),
            table.string_literal("square"),
        );
        let circle = table.object_type(vec![
            PropertyType::new("kind", false, circle_tag),
            PropertyType::new("radius", false, table.number()),
        ]);
        let square = table.object_type(vec![
            PropertyType::new("kind", false, square_tag),
            PropertyType::new("side", false, table.number()),
        ]);
        let tagless = table.object_type(vec![PropertyType::new("other", false, table.number())]);
        let shape = table.union(&[circle, square]);
        let with_tagless = table.union(&[circle, square, tagless]);
        let square_or_tagless = table.union(&[square, tagless]);
        let any = table.any();
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        assert_eq!(
            context.narrow_discriminant(shape, "kind", circle_tag, false),
            circle
        );
        assert_eq!(
            context.narrow_discriminant(shape, "kind", circle_tag, true),
            square
        );
        // Members lacking the discriminant drop positively, survive negatively.
        assert_eq!(
            context.narrow_discriminant(with_tagless, "kind", circle_tag, false),
            circle
        );
        assert_eq!(
            context.narrow_discriminant(with_tagless, "kind", circle_tag, true),
            square_or_tagless
        );
        // Opaque input is never refined.
        assert_eq!(
            context.narrow_discriminant(any, "kind", circle_tag, false),
            any
        );
    }

    #[test]
    fn discriminant_narrowing_filters_intersection_variants() {
        let mut table = TypeTable::new();
        let literal_tag = table.string_literal("literal");
        let other_tag = table.string_literal("other");
        let literal_name = table.object_type(vec![PropertyType::new("name", false, literal_tag)]);
        let literal_value =
            table.object_type(vec![PropertyType::new("value", false, table.number())]);
        let broad_tag = table.union(&[literal_tag, other_tag]);
        let broad_name = table.object_type(vec![PropertyType::new("name", false, broad_tag)]);
        let other_name = table.object_type(vec![PropertyType::new("name", false, other_tag)]);
        let other_value =
            table.object_type(vec![PropertyType::new("other", false, table.string())]);
        let literal_variant = table.intersection(vec![literal_name, literal_value]);
        let other_variant = table.intersection(vec![broad_name, other_name, other_value]);
        let union = table.union(&[literal_variant, other_variant]);
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        assert_eq!(
            context.narrow_discriminant(union, "name", literal_tag, false),
            literal_variant
        );
        assert_eq!(
            context.narrow_discriminant(union, "name", literal_tag, true),
            other_variant
        );
    }

    #[test]
    fn discriminant_narrowing_projects_named_class_members() {
        let mut table = TypeTable::new();
        let literal_symbol = SymbolId::new(401);
        let array_symbol = SymbolId::new(402);
        let literal_tag = table.string_literal("literal");
        let array_tag = table.string_literal("array");
        let number = table.number();
        let literal_body = table.object_type(vec![
            PropertyType::new("name", false, literal_tag),
            PropertyType::new("value", false, number),
        ]);
        let array_body = table.object_type(vec![PropertyType::new("name", false, array_tag)]);
        table.declare_class(literal_symbol, Vec::new());
        table.publish_final_class_template(literal_symbol, literal_body);
        table.declare_class(array_symbol, Vec::new());
        table.publish_final_class_template(array_symbol, array_body);
        let literal = table.named(literal_symbol);
        let array = table.named(array_symbol);
        let terminal = table.union(&[literal, array]);
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        assert_eq!(
            context.narrow_discriminant(terminal, "name", literal_tag, false),
            literal
        );
        assert_eq!(
            context.narrow_discriminant(terminal, "name", literal_tag, true),
            array
        );
    }

    // ---- truthiness narrowing -----------------------------------------------

    #[test]
    fn truthiness_removes_definitely_falsy_and_keeps_possibly_falsy() {
        let mut table = TypeTable::new();
        let (string, null, undefined, boolean, never) = (
            table.string(),
            table.null_type(),
            table.undefined_type(),
            table.boolean(),
            table.never(),
        );
        let (zero, one) = (table.number_literal("0"), table.number_literal("1"));
        let (true_literal, false_literal) =
            (table.boolean_literal(true), table.boolean_literal(false));
        let union = table.union(&[string, null, undefined]);
        let one_or_null = table.union(&[one, null]);
        let zero_or_false = table.union(&[zero, false_literal]);
        let zero_or_string = table.union(&[zero, string]);
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        assert_eq!(context.narrow_truthiness(union, false), string);
        // The falsy branch keeps `string` too: the empty string is falsy.
        assert_eq!(context.narrow_truthiness(union, true), union);
        // A truthy-only literal drops out of the falsy branch.
        assert_eq!(context.narrow_truthiness(one_or_null, true), null);
        // `boolean` refines to the matching literal in both polarities.
        assert_eq!(context.narrow_truthiness(boolean, false), true_literal);
        assert_eq!(context.narrow_truthiness(boolean, true), false_literal);
        // Falsy literals are kept by the falsy branch, dropped by the truthy one.
        assert_eq!(
            context.narrow_truthiness(zero_or_false, true),
            zero_or_false
        );
        assert_eq!(context.narrow_truthiness(zero, false), never);
        assert_eq!(context.narrow_truthiness(zero_or_string, false), string);
    }

    // ---- instanceof narrowing -----------------------------------------------

    #[test]
    fn instanceof_intersects_and_subtracts_nominal_members() {
        let mut table = TypeTable::new();
        let (animal, dog) = (table.named(symbol(1)), table.named(symbol(2)));
        let union = table.union(&[animal, dog]);
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        assert_eq!(context.narrow_instanceof(union, animal, false), animal);
        assert_eq!(context.narrow_instanceof(union, animal, true), dog);
    }

    // ---- flow facts ---------------------------------------------------------

    #[test]
    fn branches_isolate_refinements_and_join_unions_them() {
        let mut table = TypeTable::new();
        let (string, number) = (table.string(), table.number());
        let union = table.union(&[string, number]);
        let key = FlowKey::root(symbol(1));
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);
        context.declare(symbol(1), union);

        let positive = context.branch(FlowNodeId::ROOT);
        context.apply_guard(
            positive,
            &NarrowingGuard::Typeof {
                reference: key.clone(),
                name: TypeofName::String,
                negated: false,
            },
        );
        let negative = context.branch(FlowNodeId::ROOT);
        context.apply_guard(
            negative,
            &NarrowingGuard::Typeof {
                reference: key.clone(),
                name: TypeofName::String,
                negated: true,
            },
        );

        assert_eq!(context.type_at(positive, &key), Some(string));
        assert_eq!(context.type_at(negative, &key), Some(number));
        // The fork point is untouched by either branch.
        assert_eq!(context.type_at(FlowNodeId::ROOT, &key), Some(union));

        let joined = context.join(FlowNodeId::ROOT, &[positive, negative]);
        assert_eq!(context.type_at(joined, &key), Some(union));
    }

    #[test]
    fn join_fills_unrefined_branches_and_undeclared_references_are_noops() {
        let mut table = TypeTable::new();
        let (string, number) = (table.string(), table.number());
        let union = table.union(&[string, number]);
        let key = FlowKey::root(symbol(1));
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);
        context.declare(symbol(1), union);

        let refined = context.branch(FlowNodeId::ROOT);
        context.apply_guard(
            refined,
            &NarrowingGuard::Typeof {
                reference: key.clone(),
                name: TypeofName::String,
                negated: false,
            },
        );
        let untouched = context.branch(FlowNodeId::ROOT);
        let joined = context.join(FlowNodeId::ROOT, &[refined, untouched]);
        // string | (string | number) normalizes back to the declared union.
        assert_eq!(context.type_at(joined, &key), Some(union));
        // Undeclared references are a no-op rather than a panic or a never.
        let ghost = FlowKey::root(symbol(777));
        context.apply_guard(
            joined,
            &NarrowingGuard::Truthiness {
                reference: ghost.clone(),
                negated: false,
            },
        );
        assert_eq!(context.type_at(joined, &ghost), None);
    }

    #[test]
    fn member_write_invalidation_restores_ancestor_and_descendant_baselines() {
        let mut table = TypeTable::new();
        let a = table.string_literal("a");
        let b = table.string_literal("b");
        let kind = table.union(&[a, b]);
        let declared = table.object_type(vec![PropertyType::new("kind", false, kind)]);
        let refined = table.object_type(vec![PropertyType::new("kind", false, a)]);
        let root = FlowKey::root(symbol(1));
        let child = root.clone().child("kind");
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);
        context.declare(symbol(1), declared);

        let flow = context.branch(FlowNodeId::ROOT);
        context.refine(flow, root.clone(), refined);
        context.refine(flow, child.clone(), a);
        context.invalidate(flow, &child);

        assert_eq!(context.type_at(flow, &root), Some(declared));
        assert_eq!(context.type_at(flow, &child), Some(kind));
    }

    #[test]
    fn install_root_packet_round_trips_every_fact() {
        let mut table = TypeTable::new();
        let (string, number) = (table.string(), table.number());
        let union = table.union(&[string, number]);
        let root = FlowKey::root(symbol(1));
        let child = root.clone().child("kind");

        // Take a packet from a real session: a root refinement plus a path
        // refinement over the declared union.
        let mut facts = FlowFacts::new();
        let flow = {
            let mut context = NarrowingContext::new(&mut table, &mut facts);
            context.declare(symbol(1), union);
            let flow = context.branch(FlowNodeId::ROOT);
            context.refine(flow, root.clone(), string);
            context.refine(flow, child.clone(), number);
            flow
        };
        let packet = facts
            .root_packet(flow, symbol(1), None)
            .expect("root_packet")
            .expect("declared root yields a packet");

        // Installing into a fresh fact table must register the root's
        // declared type so the packet → frame → packet round trip is the
        // documented fixpoint.
        let mut restored = FlowFacts::new();
        let installed = restored.install_root_packet(&packet);
        let round_tripped = restored
            .root_packet(installed, symbol(1), None)
            .expect("root_packet")
            .expect("installed packet declares its root");
        assert_eq!(round_tripped, packet);
    }

    // ---- contextual typing --------------------------------------------------

    #[test]
    fn contextual_function_fills_parameters_and_awaits_async_returns() {
        let mut table = TypeTable::new();
        let (number, string, null, any) = (
            table.number(),
            table.string(),
            table.null_type(),
            table.any(),
        );
        let body = table.union(&[string, null]);
        let contextual = table.function(vec![number], table.void());
        // Expected results, interned before the context borrows the table.
        let expected_sync = table.function(vec![number], string);
        let expected_annotated = table.function(vec![string, any], string);
        let expected_async = table.function(vec![number], body);
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        // Unannotated parameters take the contextual parameter type; the
        // return is the body's own type, not the contextual return.
        let sync = context.contextual_function(contextual, &[None], string, false);
        assert_eq!(sync, expected_sync);

        // Annotated parameters keep their annotation; parameters past the
        // contextual arity widen to any.
        let annotated =
            context.contextual_function(contextual, &[Some(string), None], string, false);
        assert_eq!(annotated, expected_annotated);

        // An async literal's return is the awaited body type: unions
        // distribute, everything else is the identity.
        let async_lambda = context.contextual_function(contextual, &[None], body, true);
        assert_eq!(async_lambda, expected_async);
        assert_eq!(context.awaited_type(body), body);
        assert_eq!(context.awaited_type(number), number);
    }

    #[test]
    fn contextual_member_positions_distribute_over_unions() {
        let mut table = TypeTable::new();
        let (number, string) = (table.number(), table.string());
        let object = table.object_type(vec![PropertyType::new("x", false, number)]);
        let other = table.object_type(vec![PropertyType::new("x", false, string)]);
        let union = table.union(&[object, other]);
        let numbers = table.array(number);
        let strings = table.array(string);
        let array_union = table.union(&[numbers, strings]);
        let (one, two) = (table.number_literal("1"), table.number_literal("2"));
        let number_or_string = table.union(&[number, string]);
        let one_or_two = table.union(&[one, two]);
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        assert_eq!(context.contextual_property_type(object, "x"), Some(number));
        assert_eq!(
            context.contextual_property_type(union, "x"),
            Some(number_or_string)
        );
        assert_eq!(context.contextual_property_type(number, "x"), None);
        assert_eq!(context.contextual_element_type(numbers), Some(number));
        assert_eq!(
            context.contextual_element_type(array_union),
            Some(number_or_string)
        );
        assert_eq!(context.contextual_element_type(object), None);

        let literal = context.array_literal_type(&[one, two]);
        assert_eq!(context.contextual_element_type(literal), Some(one_or_two));
    }

    // ---- guard extraction from parsed source --------------------------------

    struct ModelResolver<'a> {
        source: &'a SourceFile,
        model: &'a SemanticModel,
        class_type: TypeId,
    }

    impl GuardResolver for ModelResolver<'_> {
        fn resolve_identifier(&self, identifier: &IdentifierNode) -> Option<SymbolId> {
            self.model.reference(identifier.id())
        }

        fn expression_type(&self, _expression: &Expr) -> TypeId {
            self.class_type
        }

        fn token_text(&self, token: &Token) -> &str {
            self.source.token_text(token).unwrap_or("")
        }
    }

    fn source(text: &str) -> Arc<SourceText> {
        Arc::new(SourceText::new(text).expect("test source fits the per-file budget"))
    }

    fn check_text(text: &str) -> (Recovered<SourceFile>, Recovered<SemanticModel>) {
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source(text),
        ));
        let model = super::super::check(&parsed);
        (parsed, model)
    }

    /// Every `if` test in source order, descending into function bodies,
    /// blocks, and branch statements.
    fn if_tests<'a>(statements: &'a [Stmt], out: &mut Vec<&'a Expr>) {
        for statement in statements {
            match statement.data() {
                Statement::If(if_statement) => {
                    out.push(&if_statement.test);
                    if_tests(std::slice::from_ref(&*if_statement.consequent), out);
                    if let Some(alternate) = &if_statement.alternate {
                        if_tests(std::slice::from_ref(&**alternate), out);
                    }
                }
                Statement::Function(declaration) => {
                    if let Some(FunctionBody::Block(block)) = &declaration.function.body {
                        if_tests(&block.data().statements, out);
                    }
                }
                Statement::Block(block) => if_tests(&block.data().statements, out),
                _ => {}
            }
        }
    }

    #[test]
    fn typeof_guards_extract_from_parsed_conditions_and_refine_a_branch() {
        let (parsed, checked) =
            check_text("function f(x: string | number) { if (typeof x === \"string\") { x; } }");
        let (source_file, model) = (parsed.product(), checked.product());
        let mut tests = Vec::new();
        if_tests(source_file.statements(), &mut tests);
        let [test] = tests.as_slice() else {
            panic!("expected one if test");
        };
        let resolver = ModelResolver {
            source: source_file,
            model,
            class_type: model.types().any(),
        };
        let mut table = model.types().clone();
        let string = table.string();
        let (x, branch_type, root_type) = {
            let mut facts = FlowFacts::new();
            let mut context = NarrowingContext::new(&mut table, &mut facts);
            let guards = context.guards_from(test, &resolver, false);
            let [
                NarrowingGuard::Typeof {
                    reference,
                    name,
                    negated,
                },
            ] = guards.as_slice()
            else {
                panic!("expected one typeof guard, got {guards:?}");
            };
            assert_eq!((*name, *negated), (TypeofName::String, false));

            let x = reference.root_symbol();
            context.declare(x, model.symbol_type(x));
            let branch = context.branch(FlowNodeId::ROOT);
            context.apply_guards(branch, &guards);
            (
                x,
                context.type_at(branch, reference),
                context.type_at(FlowNodeId::ROOT, reference),
            )
        };
        assert_eq!(branch_type, Some(string));
        assert_eq!(root_type, Some(model.symbol_type(x)));
    }

    #[test]
    fn equality_in_instanceof_and_truthiness_guards_extract_and_apply() {
        // Equality against null.
        let (parsed, checked) =
            check_text("function f(x: string | null) { if (x === null) { x; } }");
        let (source_file, model) = (parsed.product(), checked.product());
        let mut tests = Vec::new();
        if_tests(source_file.statements(), &mut tests);
        let resolver = ModelResolver {
            source: source_file,
            model,
            class_type: model.types().any(),
        };
        let mut table = model.types().clone();
        let null = table.null_type();
        let branch_type = {
            let mut facts = FlowFacts::new();
            let mut context = NarrowingContext::new(&mut table, &mut facts);
            let guards = context.guards_from(tests[0], &resolver, false);
            let [
                NarrowingGuard::Equality {
                    reference, negated, ..
                },
            ] = guards.as_slice()
            else {
                panic!("expected one equality guard, got {guards:?}");
            };
            assert!(!negated);
            let x = reference.root_symbol();
            context.declare(x, model.symbol_type(x));
            let branch = context.branch(FlowNodeId::ROOT);
            context.apply_guards(branch, &guards);
            context.type_at(branch, &FlowKey::root(x))
        };
        assert_eq!(branch_type, Some(null));

        // `in` against a declared union.
        let (parsed, checked) =
            check_text("function f(y: { kind: string } | number) { if (\"kind\" in y) { y; } }");
        let (source_file, model) = (parsed.product(), checked.product());
        let mut tests = Vec::new();
        if_tests(source_file.statements(), &mut tests);
        let resolver = ModelResolver {
            source: source_file,
            model,
            class_type: model.types().any(),
        };
        let mut table = model.types().clone();
        {
            let mut facts = FlowFacts::new();
            let mut context = NarrowingContext::new(&mut table, &mut facts);
            let guards = context.guards_from(tests[0], &resolver, false);
            let [
                NarrowingGuard::In {
                    property, negated, ..
                },
            ] = guards.as_slice()
            else {
                panic!("expected one in guard, got {guards:?}");
            };
            assert_eq!(&**property, "kind");
            assert!(!negated);
            let y = guards[0].reference().root_symbol();
            context.declare(y, model.symbol_type(y));
            let branch = context.branch(FlowNodeId::ROOT);
            context.apply_guards(branch, &guards);
            let narrowed = context
                .type_at(branch, &FlowKey::root(y))
                .expect("narrowed");
            assert!(matches!(table.get(narrowed), Type::ObjectType(_)));
        }

        // `instanceof` carries the resolver-typed right operand.
        let (parsed, checked) =
            check_text("class Foo {} function f(x: Foo | null) { if (x instanceof Foo) { x; } }");
        let (source_file, model) = (parsed.product(), checked.product());
        let mut tests = Vec::new();
        if_tests(source_file.statements(), &mut tests);
        let class_type = model.types().any();
        let resolver = ModelResolver {
            source: source_file,
            model,
            class_type,
        };
        let mut table = model.types().clone();
        {
            let mut facts = FlowFacts::new();
            let mut context = NarrowingContext::new(&mut table, &mut facts);
            let guards = context.guards_from(tests[0], &resolver, false);
            let [
                NarrowingGuard::Instanceof {
                    class_type: guard_class,
                    negated,
                    ..
                },
            ] = guards.as_slice()
            else {
                panic!("expected one instanceof guard, got {guards:?}");
            };
            assert_eq!(*guard_class, class_type);
            assert!(!negated);
        }

        // A bare reference is a truthiness guard.
        let (parsed, checked) = check_text("function f(x: string | undefined) { if (x) { x; } }");
        let (source_file, model) = (parsed.product(), checked.product());
        let mut tests = Vec::new();
        if_tests(source_file.statements(), &mut tests);
        let resolver = ModelResolver {
            source: source_file,
            model,
            class_type: model.types().any(),
        };
        let mut table = model.types().clone();
        let string = table.string();
        let branch_type = {
            let mut facts = FlowFacts::new();
            let mut context = NarrowingContext::new(&mut table, &mut facts);
            let guards = context.guards_from(tests[0], &resolver, false);
            let [NarrowingGuard::Truthiness { reference, negated }] = guards.as_slice() else {
                panic!("expected one truthiness guard, got {guards:?}");
            };
            assert!(!negated);
            let x = reference.root_symbol();
            context.declare(x, model.symbol_type(x));
            let branch = context.branch(FlowNodeId::ROOT);
            context.apply_guards(branch, &guards);
            context.type_at(branch, &FlowKey::root(x))
        };
        assert_eq!(branch_type, Some(string));
    }

    #[test]
    fn property_equality_discriminates_the_root_union() {
        let (parsed, checked) = check_text(
            "type Shape = { kind: \"circle\"; radius: number } | { kind: \"square\"; side: number };\n\
             function f(shape: Shape) { if (shape.kind === \"circle\") { shape; } }",
        );
        let (source_file, model) = (parsed.product(), checked.product());
        let mut tests = Vec::new();
        if_tests(source_file.statements(), &mut tests);
        let [test] = tests.as_slice() else {
            panic!("expected one if test");
        };
        let resolver = ModelResolver {
            source: source_file,
            model,
            class_type: model.types().any(),
        };
        let mut table = model.types().clone();
        let (member_type, narrowed_root) = {
            let mut facts = FlowFacts::new();
            let mut context = NarrowingContext::new(&mut table, &mut facts);
            let guards = context.guards_from(test, &resolver, false);
            let [
                NarrowingGuard::Equality {
                    reference,
                    literal,
                    negated,
                },
            ] = guards.as_slice()
            else {
                panic!("expected one equality guard, got {guards:?}");
            };
            assert!(!negated);
            assert_eq!(reference.path().len(), 1);

            let shape = reference.root_symbol();
            context.declare(shape, model.symbol_type(shape));
            let branch = context.branch(FlowNodeId::ROOT);
            context.apply_guards(branch, &guards);
            let member_type = context.type_at(branch, reference).expect("member type");
            // The member access narrows to the literal itself.
            assert_eq!(member_type, *literal);
            let narrowed_root = context
                .type_at(branch, &FlowKey::root(shape))
                .expect("root type");
            (member_type, narrowed_root)
        };
        let _ = member_type;
        // The root discriminates to the circle variant only.
        let Type::ObjectType(object) = table.get(narrowed_root) else {
            panic!("circle variant is an object type");
        };
        assert!(
            object
                .properties
                .iter()
                .any(|property| property.name() == "radius")
        );
        assert!(
            !object
                .properties
                .iter()
                .any(|property| property.name() == "side")
        );
    }

    #[test]
    fn de_morgan_gates_conjunction_and_disjunction() {
        let (parsed, checked) = check_text(
            "function f(a: string | null, b: string | null) {\n\
             \x20   if (a !== null && b !== null) { a; }\n\
             \x20   if (!(a !== null || b !== null)) { b; }\n\
             }",
        );
        let (source_file, model) = (parsed.product(), checked.product());
        let mut tests = Vec::new();
        if_tests(source_file.statements(), &mut tests);
        let [conjunction, negated_disjunction] = tests.as_slice() else {
            panic!("expected two if tests");
        };
        let resolver = ModelResolver {
            source: source_file,
            model,
            class_type: model.types().any(),
        };
        let mut table = model.types().clone();
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        // The truthy side of a conjunction proves both operands.
        let guards = context.guards_from(conjunction, &resolver, false);
        assert_eq!(guards.len(), 2);
        assert!(guards.iter().all(NarrowingGuard::negated));

        // The truthy side of `!(a !== null || b !== null)` is the falsy side
        // of the disjunction: both operands hold positively (`a === null`).
        let guards = context.guards_from(negated_disjunction, &resolver, false);
        assert_eq!(guards.len(), 2);
        assert!(guards.iter().all(|guard| !guard.negated()));

        // The truthy side of a bare disjunction proves nothing by itself.
        let Expression::Unary(unary) = negated_disjunction.data() else {
            panic!("negated test")
        };
        let guards = context.guards_from(&unary.argument, &resolver, false);
        assert!(guards.is_empty());
    }

    // ---- U2.4 review regressions --------------------------------------------

    #[test]
    fn loose_undefined_equality_widens_the_literal_to_nullish() {
        let (parsed, checked) =
            check_text("function f(x: string | null | undefined) { if (x == undefined) { x; } }");
        let (source_file, model) = (parsed.product(), checked.product());
        let mut tests = Vec::new();
        if_tests(source_file.statements(), &mut tests);
        let [test] = tests.as_slice() else {
            panic!("expected one if test");
        };
        let resolver = ModelResolver {
            source: source_file,
            model,
            class_type: model.types().any(),
        };
        let mut table = model.types().clone();
        let nullish = table.union(&[table.null_type(), table.undefined_type()]);
        let branch_type = {
            let mut facts = FlowFacts::new();
            let mut context = NarrowingContext::new(&mut table, &mut facts);
            let guards = context.guards_from(test, &resolver, false);
            let [
                NarrowingGuard::Equality {
                    reference,
                    literal,
                    negated,
                },
            ] = guards.as_slice()
            else {
                panic!("expected one equality guard, got {guards:?}");
            };
            assert!(!negated);
            // Loose `== undefined` widens the literal exactly like `== null`.
            assert_eq!(*literal, nullish);
            let x = reference.root_symbol();
            context.declare(x, model.symbol_type(x));
            let branch = context.branch(FlowNodeId::ROOT);
            context.apply_guards(branch, &guards);
            context.type_at(branch, &FlowKey::root(x))
        };
        assert_eq!(branch_type, Some(nullish));
    }

    #[test]
    fn negative_instanceof_with_an_opaque_class_never_subtracts() {
        let mut table = TypeTable::new();
        let (string, error, any, unknown) = (
            table.string(),
            table.error_type(),
            table.any(),
            table.unknown(),
        );
        let animal = table.named(symbol(1));
        let with_error = table.union(&[animal, error]);
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        // An opaque class operand covers nothing provably: a negative
        // `instanceof` must never subtract it, whatever the checked type.
        assert_eq!(
            context.narrow_instanceof(with_error, error, true),
            with_error
        );
        assert_eq!(context.narrow_instanceof(with_error, any, true), with_error);
        assert_eq!(
            context.narrow_instanceof(with_error, unknown, true),
            with_error
        );
        assert_eq!(context.narrow_instanceof(string, any, true), string);
    }

    #[test]
    fn error_union_members_survive_every_narrowing_decision() {
        let mut table = TypeTable::new();
        let (string, number, null, undefined, error) = (
            table.string(),
            table.number(),
            table.null_type(),
            table.undefined_type(),
            table.error_type(),
        );
        let a = table.string_literal("a");
        let kinded = table.object_type(vec![PropertyType::new("kind", false, string)]);
        let other = table.object_type(vec![PropertyType::new("other", false, number)]);
        let false_literal = table.boolean_literal(false);

        let kinded_or_error = table.union(&[kinded, error]);
        let string_or_error = table.union(&[string, error]);
        let typeof_union = table.union(&[string, number, error]);
        let truthy_union = table.union(&[string, error, null, undefined]);
        let falsy_or_error = table.union(&[string, error, false_literal]);
        let nullable_or_error = table.union(&[string, error, null]);
        // Expected results, interned before the context borrows the table.
        let number_or_error = table.union(&[number, error]);
        let in_union = table.union(&[kinded, other, error]);
        let error_or_null = table.union(&[error, null]);
        let a_or_error = table.union(&[a, error]);

        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        // typeof: the error member passes both polarities.
        assert_eq!(
            context.narrow_typeof(typeof_union, TypeofName::String, false),
            string_or_error
        );
        assert_eq!(
            context.narrow_typeof(typeof_union, TypeofName::String, true),
            number_or_error
        );

        // in: the error member passes both polarities.
        assert_eq!(context.narrow_in(in_union, "kind", false), kinded_or_error);
        assert_eq!(context.narrow_in(kinded_or_error, "kind", true), error);

        // Truthiness: kept in both polarities, alongside whatever survives.
        assert_eq!(
            context.narrow_truthiness(truthy_union, false),
            string_or_error
        );
        assert_eq!(context.narrow_truthiness(truthy_union, true), truthy_union);
        // Literal members refine; the error member is untouched.
        assert_eq!(
            context.narrow_truthiness(falsy_or_error, true),
            falsy_or_error
        );

        // Equality: the error member survives subtraction and intersection.
        assert_eq!(
            context.narrow_equality(nullable_or_error, null, true),
            string_or_error
        );
        assert_eq!(
            context.narrow_equality(nullable_or_error, null, false),
            error_or_null
        );
        assert_eq!(
            context.narrow_equality(string_or_error, a, false),
            a_or_error
        );
        assert_eq!(context.narrow_equality(a_or_error, a, true), error);

        // Instanceof: the error member survives subtraction.
        assert_eq!(
            context.narrow_instanceof(string_or_error, number, true),
            string_or_error
        );
    }
    // ---- AppliedClass typeof classification -------------------------------

    #[test]
    fn typeof_object_keeps_applied_class() {
        let mut table = TypeTable::new();
        let class_symbol = symbol(300);
        let instance_template =
            table.object_type(vec![PropertyType::new("x", false, table.number())]);
        table.declare_class(class_symbol, Vec::new());
        table.publish_final_class_template(class_symbol, instance_template);
        let applied = table.applied_class(class_symbol, Vec::new());
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        // `typeof x === "object"` keeps the AppliedClass instance.
        assert_eq!(
            context.narrow_typeof(applied, TypeofName::Object, false),
            applied
        );
    }

    #[test]
    fn typeof_function_drops_applied_class() {
        let mut table = TypeTable::new();
        let class_symbol = symbol(310);
        let instance_template =
            table.object_type(vec![PropertyType::new("x", false, table.number())]);
        table.declare_class(class_symbol, Vec::new());
        table.publish_final_class_template(class_symbol, instance_template);
        let applied = table.applied_class(class_symbol, Vec::new());
        let never = table.never();
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        // `typeof x === "function"` drops the AppliedClass instance — it is
        // not callable.
        assert_eq!(
            context.narrow_typeof(applied, TypeofName::Function, false),
            never
        );
    }

    #[test]
    fn typeof_function_negated_keeps_applied_class() {
        let mut table = TypeTable::new();
        let class_symbol = symbol(320);
        let instance_template =
            table.object_type(vec![PropertyType::new("x", false, table.number())]);
        table.declare_class(class_symbol, Vec::new());
        table.publish_final_class_template(class_symbol, instance_template);
        let applied = table.applied_class(class_symbol, Vec::new());
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        // `typeof x !== "function"` keeps the AppliedClass instance.
        assert_eq!(
            context.narrow_typeof(applied, TypeofName::Function, true),
            applied
        );
    }

    #[test]
    fn typeof_object_negated_drops_applied_class() {
        let mut table = TypeTable::new();
        let class_symbol = symbol(330);
        let instance_template =
            table.object_type(vec![PropertyType::new("x", false, table.number())]);
        table.declare_class(class_symbol, Vec::new());
        table.publish_final_class_template(class_symbol, instance_template);
        let applied = table.applied_class(class_symbol, Vec::new());
        let never = table.never();
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        // `typeof x !== "object"` drops the AppliedClass instance.
        assert_eq!(
            context.narrow_typeof(applied, TypeofName::Object, true),
            never
        );
    }

    #[test]
    fn typeof_function_splits_union_of_applied_class_and_function() {
        let mut table = TypeTable::new();
        let class_symbol = symbol(340);
        let instance_template =
            table.object_type(vec![PropertyType::new("x", false, table.number())]);
        table.declare_class(class_symbol, Vec::new());
        table.publish_final_class_template(class_symbol, instance_template);
        let applied = table.applied_class(class_symbol, Vec::new());
        let func = table.function(Vec::new(), table.void());
        let union = table.union(&[applied, func]);
        let mut facts = FlowFacts::new();
        let mut context = NarrowingContext::new(&mut table, &mut facts);

        // `typeof x === "function"` keeps only the function member.
        assert_eq!(
            context.narrow_typeof(union, TypeofName::Function, false),
            func
        );
        // `typeof x === "object"` keeps only the AppliedClass member.
        assert_eq!(
            context.narrow_typeof(union, TypeofName::Object, false),
            applied
        );
    }
}
