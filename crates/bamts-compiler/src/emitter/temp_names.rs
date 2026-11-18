//! tsc's names for compiler-generated temporaries.
//!
//! The rewriter writes every temporary as a placeholder: `_t<N>` for a
//! variable, `_tl<N>` for a loop index, `_tp<N>` for a parameter that stands
//! in for a pattern, and `_tr<N>` for a variable whose name nested functions
//! must not reuse. The printer replaces each placeholder the
//! first time it prints it, so names follow print order the way tsc's do:
//! `_a`, `_b`, … per function scope, skipping `_i` and `_n`, with the first loop
//! index of a scope named `_i`. A name the program itself writes is never
//! issued, and neither is a name an inner scope reads from an outer one.

use std::collections::{HashMap, HashSet};

/// Counts that tsc never turns into an `_a`-style name: `i` and `n`.
const SKIPPED_COUNTS: [u32; 2] = [8, 13];

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Plain,
    LoopIndex,
    ReservedBelow,
}

impl Kind {
    fn of(placeholder: &str) -> Self {
        if placeholder.starts_with("_tl") {
            Self::LoopIndex
        } else if placeholder.starts_with("_tr") {
            Self::ReservedBelow
        } else {
            Self::Plain
        }
    }
}

#[derive(Default)]
struct TempScope {
    assigned: HashMap<String, String>,
    captured: HashSet<String>,
    reserved_below: HashSet<String>,
    issued: u32,
    index_taken: bool,
}

pub(super) struct TempNames {
    scopes: Vec<TempScope>,
    reserved: HashSet<String>,
}

impl TempNames {
    pub(super) fn new(reserved: HashSet<String>) -> Self {
        Self {
            scopes: vec![TempScope::default()],
            reserved,
        }
    }

    pub(super) fn enter(&mut self) {
        self.scopes.push(TempScope::default());
    }

    pub(super) fn exit(&mut self) {
        if self.scopes.len() > 1 {
            self.scopes.pop();
        }
    }
    /// How many scopes are open; a parameter-list scope is covered when a
    /// function-body block opens at this depth.
    pub(super) fn depth(&self) -> usize {
        self.scopes.len()
    }

    pub(super) fn is_placeholder(text: &str) -> bool {
        let digits = ["_tl", "_tr", "_tp", "_t"]
            .iter()
            .find_map(|prefix| text.strip_prefix(prefix))
            .unwrap_or("");
        !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit())
    }

    /// Whether `text` names a parameter temporary, which belongs to the
    /// scope of the function it is a parameter of.
    pub(super) fn is_parameter_placeholder(text: &str) -> bool {
        text.starts_with("_tp") && Self::is_placeholder(text)
    }

    /// The final name of `placeholder`: the one a scope already gave it, else
    /// a fresh one from the innermost scope.
    pub(super) fn resolve(&mut self, placeholder: &str) -> String {
        let depth = self.scopes.len() - 1;
        let owner = self
            .scopes
            .iter()
            .rposition(|scope| scope.assigned.contains_key(placeholder));
        match owner {
            Some(owner) => {
                let name = self.scopes[owner].assigned[placeholder].clone();
                if owner < depth {
                    self.scopes[depth].captured.insert(name.clone());
                }
                name
            }
            None => {
                let kind = Kind::of(placeholder);
                let name = self.issue(kind);
                let scope = &mut self.scopes[depth];
                scope.assigned.insert(placeholder.to_owned(), name.clone());
                if kind == Kind::ReservedBelow {
                    scope.reserved_below.insert(name.clone());
                }
                name
            }
        }
    }

    fn issue(&mut self, kind: Kind) -> String {
        let depth = self.scopes.len() - 1;
        let taken_by_outer: HashSet<String> = self
            .scopes
            .iter()
            .flat_map(|scope| scope.reserved_below.iter().cloned())
            .collect();
        let reserved = &self.reserved;
        let scope = &mut self.scopes[depth];
        let free = |name: &str, scope: &TempScope| {
            !reserved.contains(name)
                && !scope.captured.contains(name)
                && !taken_by_outer.contains(name)
        };
        if kind == Kind::LoopIndex && !scope.index_taken && free("_i", scope) {
            scope.index_taken = true;
            return String::from("_i");
        }
        loop {
            let count = scope.issued;
            scope.issued += 1;
            if SKIPPED_COUNTS.contains(&count) {
                continue;
            }
            let name = if count < 26 {
                format!("_{}", char::from(b'a' + count as u8))
            } else {
                format!("_{}", count - 26)
            };
            if free(&name, scope) {
                return name;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn names(reserved: &[&str]) -> TempNames {
        TempNames::new(reserved.iter().map(|name| (*name).to_owned()).collect())
    }

    #[test]
    fn placeholders_get_letters_in_print_order_and_stay_stable() {
        let mut temps = names(&[]);
        assert_eq!(temps.resolve("_t5"), "_a");
        assert_eq!(temps.resolve("_t2"), "_b");
        assert_eq!(temps.resolve("_t5"), "_a");
    }

    #[test]
    fn letters_skip_i_and_n_and_names_the_program_writes() {
        let mut temps = names(&["_c"]);
        let issued: Vec<String> = (0..12)
            .map(|index| temps.resolve(&format!("_t{index}")))
            .collect();
        assert_eq!(
            issued,
            [
                "_a", "_b", "_d", "_e", "_f", "_g", "_h", "_j", "_k", "_l", "_m", "_o"
            ]
        );
    }

    #[test]
    fn after_z_the_counter_continues_with_numbers() {
        let mut temps = names(&[]);
        let issued: Vec<String> = (0..26)
            .map(|index| temps.resolve(&format!("_t{index}")))
            .collect();
        assert_eq!(issued[23], "_z");
        assert_eq!(issued[24], "_0");
        assert_eq!(issued[25], "_1");
    }

    #[test]
    fn the_first_loop_index_of_each_scope_is_i_and_the_next_is_a_letter() {
        let mut temps = names(&[]);
        assert_eq!(temps.resolve("_tl0"), "_i");
        assert_eq!(temps.resolve("_tl1"), "_a");
        temps.enter();
        assert_eq!(temps.resolve("_tl2"), "_i");
        temps.exit();
        temps.enter();
        assert_eq!(temps.resolve("_tl3"), "_i");
    }

    #[test]
    fn an_inner_scope_numbers_from_the_start_but_skips_names_it_reads_from_outside() {
        let mut temps = names(&[]);
        assert_eq!(temps.resolve("_t0"), "_a");
        temps.enter();
        assert_eq!(temps.resolve("_t0"), "_a");
        assert_eq!(temps.resolve("_t1"), "_b");
        temps.exit();
        assert_eq!(temps.resolve("_t2"), "_b");
    }

    #[test]
    fn a_reserved_name_is_skipped_by_every_nested_scope() {
        let mut temps = names(&[]);
        assert_eq!(temps.resolve("_tr0"), "_a");
        temps.enter();
        assert_eq!(temps.resolve("_t1"), "_b");
        assert_eq!(temps.resolve("_tr2"), "_c");
        temps.enter();
        assert_eq!(temps.resolve("_t3"), "_b");
        temps.exit();
        temps.exit();
        assert_eq!(temps.resolve("_t4"), "_b");
    }

    #[test]
    fn only_generated_shapes_are_placeholders() {
        assert!(TempNames::is_placeholder("_t0"));
        assert!(TempNames::is_placeholder("_tl12"));
        assert!(TempNames::is_placeholder("_tr3"));
        assert!(!TempNames::is_placeholder("_t"));
        assert!(!TempNames::is_placeholder("_tx1"));
        assert!(!TempNames::is_placeholder("_this"));
    }
}
