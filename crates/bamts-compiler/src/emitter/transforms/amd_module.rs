//! AMD and UMD: the CommonJS body inside a factory function.
//!
//! `define(["require", "exports", "./a"], function (require, exports, a_1) {...})`
//! lists the dependencies up front and receives them as parameters, so the
//! `const a_1 = require("./a");` lines of the CommonJS body disappear. UMD keeps
//! the CommonJS body and only wraps it so a loader can pick the AMD branch.

use std::collections::BTreeSet;

use crate::emitter::ModuleWrapper;
use crate::syntax::NodeId;

/// One module the factory depends on.
pub(super) struct AmdDependency {
    /// The module specifier with its double quotes.
    pub(super) specifier: String,
    /// The factory parameter that receives the module, when the body reads it.
    pub(super) alias: Option<String>,
}

#[derive(Default)]
pub(super) struct AmdPlan {
    pub(super) umd: bool,
    pub(super) module_name: Option<String>,
    pub(super) dependencies: Vec<AmdDependency>,
    /// `a_1 = __importStar(a_1);` lines, which run before the body.
    pub(super) interop: Vec<String>,
    /// `import x = require(...)` statements the factory parameters replace.
    pub(super) erased_imports: BTreeSet<NodeId>,
}

/// What the leading triple-slash comments of a file ask of the wrapper.
#[derive(Default)]
pub(super) struct SourceDirectives {
    pub(super) dependencies: Vec<(String, Option<String>)>,
    pub(super) module_name: Option<String>,
}

fn attribute<'a>(directive: &'a str, name: &str) -> Option<&'a str> {
    let start = directive.find(&format!("{name}="))? + name.len() + 1;
    let rest = &directive[start..];
    let quote = rest
        .chars()
        .next()
        .filter(|quote| matches!(quote, '\'' | '"'))?;
    let value = &rest[1..];
    value.find(quote).map(|end| &value[..end])
}

enum LeadingLine<'a> {
    Skipped,
    TripleSlash(&'a str),
    Code,
}

fn classify_leading_line<'a>(line: &'a str, inside_block: &mut bool) -> LeadingLine<'a> {
    let line = line.trim();
    if *inside_block {
        *inside_block = !line.contains("*/");
        return LeadingLine::Skipped;
    }
    if let Some(body) = line.strip_prefix("///") {
        return LeadingLine::TripleSlash(body);
    }
    if line.is_empty() || line.starts_with("//") {
        return LeadingLine::Skipped;
    }
    let Some(rest) = line.strip_prefix("/*") else {
        return LeadingLine::Code;
    };
    let Some((_, after)) = rest.rsplit_once("*/") else {
        *inside_block = true;
        return LeadingLine::Skipped;
    };
    if after.trim().is_empty() || after.trim().starts_with("//") {
        LeadingLine::Skipped
    } else {
        LeadingLine::Code
    }
}

/// The `amd-dependency` and `amd-module` directives in the comments that open
/// a file, wherever they sit among the other leading comments.
pub(super) fn source_directives(text: &str) -> SourceDirectives {
    let mut directives = SourceDirectives::default();
    let mut inside_block = false;
    for line in text.lines() {
        let body = match classify_leading_line(line, &mut inside_block) {
            LeadingLine::Skipped => continue,
            LeadingLine::Code => break,
            LeadingLine::TripleSlash(body) => body.trim(),
        };
        if body.starts_with("<amd-dependency") {
            if let Some(path) = attribute(body, "path") {
                directives
                    .dependencies
                    .push((path.to_owned(), attribute(body, "name").map(str::to_owned)));
            }
        } else if body.starts_with("<amd-module")
            && let Some(name) = attribute(body, "name")
        {
            directives.module_name = Some(name.to_owned());
        }
    }
    directives
}

/// `"./a"` out of `require("./a")`.
fn required_specifier(expression: &str) -> Option<&str> {
    let inner = expression.strip_prefix("require(")?.strip_suffix(')')?;
    (inner.starts_with('"') && inner.ends_with('"') && inner.len() >= 2).then_some(inner)
}

/// `(helper, specifier)` out of `__importStar(require("./a"))`.
fn interop_call(expression: &str) -> Option<(&'static str, &str)> {
    for helper in ["__importStar", "__importDefault"] {
        if let Some(inner) = expression
            .strip_prefix(helper)
            .and_then(|rest| rest.strip_prefix('('))
            .and_then(|rest| rest.strip_suffix(')'))
            && let Some(specifier) = required_specifier(inner)
        {
            return Some((helper, specifier));
        }
    }
    None
}

/// The declared name and initializer of `var name = value;`.
fn declaration(line: &str) -> Option<(&str, &str)> {
    let rest = line
        .strip_prefix("var ")
        .or_else(|| line.strip_prefix("const "))?;
    let (name, value) = rest.split_once(" = ")?;
    Some((name, value.strip_suffix(';')?))
}

/// The module of a line that is only `require("m");`, a side-effect import.
fn bare_require(line: &str) -> Option<&str> {
    required_specifier(line.strip_suffix(';')?)
}

/// Records the dependencies of one CommonJS line without changing it, for the
/// UMD wrapper, which lists them but keeps the `require` calls.
pub(super) fn scan_requires(line: &str, plan: &mut AmdPlan) {
    if let Some((name, value)) = declaration(line)
        && let Some(specifier) =
            required_specifier(value).or_else(|| interop_call(value).map(|call| call.1))
    {
        plan.dependencies.push(AmdDependency {
            specifier: specifier.to_owned(),
            alias: Some(name.to_owned()),
        });
        return;
    }
    if let Some(specifier) = bare_require(line) {
        plan.dependencies.push(AmdDependency {
            specifier: specifier.to_owned(),
            alias: None,
        });
        return;
    }
    let mut rest = line;
    while let Some(start) = rest.find("require(\"") {
        let tail = &rest[start + "require(".len()..];
        let Some(end) = tail[1..].find('"') else {
            return;
        };
        plan.dependencies.push(AmdDependency {
            specifier: tail[..end + 2].to_owned(),
            alias: Some(String::new()),
        });
        rest = tail[end + 2..]
            .strip_prefix(')')
            .unwrap_or(&tail[end + 2..]);
    }
}

/// One CommonJS line as the AMD body keeps it, or `None` when the factory
/// parameter replaces it.
pub(super) fn amd_line(
    line: &str,
    plan: &mut AmdPlan,
    mut alias_for: impl FnMut(&str) -> String,
) -> Option<String> {
    if let Some((name, value)) = declaration(line) {
        if let Some(specifier) = required_specifier(value) {
            plan.dependencies.push(AmdDependency {
                specifier: specifier.to_owned(),
                alias: Some(name.to_owned()),
            });
            return None;
        }
        if let Some((helper, specifier)) = interop_call(value) {
            plan.dependencies.push(AmdDependency {
                specifier: specifier.to_owned(),
                alias: Some(name.to_owned()),
            });
            plan.interop.push(format!("{name} = {helper}({name});"));
            return None;
        }
    }
    if let Some(specifier) = bare_require(line) {
        plan.dependencies.push(AmdDependency {
            specifier: specifier.to_owned(),
            alias: None,
        });
        return None;
    }
    let mut kept = String::new();
    let mut rest = line;
    while let Some(start) = rest.find("require(\"") {
        let tail = &rest[start + "require(".len()..];
        let Some(end) = tail[1..].find('"') else {
            break;
        };
        let specifier = &tail[..end + 2];
        let alias = alias_for(specifier);
        plan.dependencies.push(AmdDependency {
            specifier: specifier.to_owned(),
            alias: Some(alias.clone()),
        });
        kept.push_str(&rest[..start]);
        kept.push_str(&alias);
        rest = tail[end + 2..]
            .strip_prefix(')')
            .unwrap_or(&tail[end + 2..]);
    }
    kept.push_str(rest);
    Some(kept)
}

impl AmdPlan {
    /// The wrapper for a module with the given directives.
    pub(super) fn wrapper(
        &self,
        directives: &SourceDirectives,
        inner: String,
        indent: &str,
        newline: &str,
    ) -> ModuleWrapper<'static> {
        let mut aliased: Vec<(&str, &str)> = Vec::new();
        let mut unaliased: Vec<&str> = Vec::new();
        let quoted: Vec<String> = directives
            .dependencies
            .iter()
            .map(|(path, _)| format!("\"{path}\""))
            .collect();
        for ((_, name), path) in directives.dependencies.iter().zip(&quoted) {
            match name {
                Some(name) => aliased.push((path, name)),
                None => unaliased.push(path),
            }
        }
        for dependency in &self.dependencies {
            match &dependency.alias {
                Some(alias) => aliased.push((&dependency.specifier, alias)),
                None => unaliased.push(&dependency.specifier),
            }
        }
        let mut specifiers = vec!["\"require\"", "\"exports\""];
        specifiers.extend(aliased.iter().map(|(specifier, _)| *specifier));
        specifiers.extend(unaliased.iter().copied());
        let list = specifiers.join(", ");
        let name = directives
            .module_name
            .as_ref()
            .or(self.module_name.as_ref())
            .map(|name| format!("\"{name}\", "))
            .unwrap_or_default();
        let head = if self.umd {
            [
                "(function (factory) {".to_owned(),
                format!("{indent}if (typeof module === \"object\" && typeof module.exports === \"object\") {{"),
                format!("{indent}{indent}var v = factory(require, exports);"),
                format!("{indent}{indent}if (v !== undefined) module.exports = v;"),
                format!("{indent}}}"),
                format!("{indent}else if (typeof define === \"function\" && define.amd) {{"),
                format!("{indent}{indent}define({name}[{list}], factory);"),
                format!("{indent}}}"),
                "})(function (require, exports) {".to_owned(),
            ]
            .join(newline)
        } else {
            let mut parameters = vec!["require", "exports"];
            parameters.extend(aliased.iter().map(|(_, alias)| *alias));
            format!(
                "define({name}[{list}], function ({}) {{",
                parameters.join(", ")
            )
        };
        ModuleWrapper {
            head,
            inner,
            hoisted: None,
            mid: String::new(),
            tail: "});".to_owned(),
            body_indent: 0,
        }
    }
}
