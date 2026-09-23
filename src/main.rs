mod frontend;

use frontend::{run_script, run_script_json};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

#[cfg(target_arch = "wasm32")]
#[wasm_bindgen]
pub fn run_wasm(input: &str) -> Result<String, JsValue> {
    run_script(input)
        .map(|lines| lines.join("\n"))
        .map_err(|error| JsValue::from_str(&error))
}

#[cfg(not(target_arch = "wasm32"))]
fn terminal_error(source: &str, error: &str) -> String {
    let Some(rest) = error.strip_prefix("line ") else {
        return format!("error: {error}");
    };
    let Some((line, rest)) = rest.split_once(':') else {
        return format!("error: {error}");
    };
    let Some((column, message)) = rest.split_once(": ") else {
        return format!("error: {error}");
    };
    if line.parse::<usize>().is_err() || column.parse::<usize>().is_err() {
        return format!("error: {error}");
    }
    format!("{source}:{line}:{column}: error: {message}")
}

#[cfg(not(target_arch = "wasm32"))]
fn run_cli(path: Option<&str>, json: bool) -> Result<(), String> {
    let input = if let Some(path) = path {
        std::fs::read_to_string(path)
            .map_err(|error| format!("error: cannot read {path}: {error}"))?
    } else {
        use std::io::Read;
        let mut input = String::new();
        std::io::stdin()
            .read_to_string(&mut input)
            .map_err(|error| format!("error: cannot read stdin: {error}"))?;
        input
    };
    let source = path.unwrap_or("<stdin>");
    if json {
        let (values, diagnostics) =
            run_script_json(&input).map_err(|error| terminal_error(source, &error))?;
        for line in diagnostics {
            eprintln!("{line}");
        }
        for value in values {
            println!(
                "{}",
                serde_json::to_string(&value)
                    .map_err(|error| format!("error: cannot serialize JSON output: {error}"))?
            );
        }
    } else {
        for line in run_script(&input).map_err(|error| terminal_error(source, &error))? {
            println!("{line}");
        }
    }
    Ok(())
}

#[cfg(not(target_arch = "wasm32"))]
fn main() {
    use std::io::IsTerminal;
    let args: Vec<_> = std::env::args().skip(1).collect();
    if !args.is_empty() {
        let mut json = false;
        let mut path = None;
        for arg in &args {
            if arg == "--json" {
                json = true;
            } else if path.is_none() {
                path = Some(arg.as_str());
            } else {
                eprintln!("error: expected at most one input file");
                std::process::exit(1);
            }
        }
        let path = path.filter(|path| *path != "-");
        if let Err(error) = run_cli(path, json) {
            eprintln!("{error}");
            std::process::exit(1);
        }
        return;
    }
    if !std::io::stdin().is_terminal() {
        if let Err(error) = run_cli(None, false) {
            eprintln!("{error}");
            std::process::exit(1);
        }
        return;
    }
    println!(
        "Lambda MicroEgg\n\n\
         Run an S-expression program with:\n  lambda-microegg [--json] FILE\n  lambda-microegg [--json] -\n\n\
         Commands:\n  (reset)\n  (insert [CONTEXT] TERM)\n  (union [CONTEXT] LEFT RIGHT)\n  (guard [CONTEXT] LEFT RIGHT)\n  (rewrite LHS RHS)\n  (birewrite LHS RHS)\n  (match PATTERN)\n  (run LIMIT)\n  (echo VALUE)\n  (fail COMMAND)\n  (extract [CONTEXT] TERM)\n\n\
         Debugging:\n  (print-egraph)\n\n\
         Named binders:\n  (@OP x BODY), x is the nearest binder named x, x@1 is the next outer x\n  Use @lam for lambda calculus; bare lam is an ordinary function symbol\n  $0, $1, ... name variables in the explicit outer context\n\n\
         Application:\n  (f x y) and [f x y] are curried binary application: ((f x) y)\n\n\
         Metavariable occurrences:\n  ?a excludes pattern-local binders; LHS Miller parameters are written outer-to-inner: {{?a x y}}\n  On a rewrite RHS, arguments may be permuted or replaced by terms: {{?a y x}}, {{?a (foo x)}}\n\n\
         Built-ins:\n  (#subst BODY x REPLACEMENT) substitutes REPLACEMENT for x in BODY\n  A free variable may also be named directly: (#subst $0 $0 fred)"
    );
}

#[cfg(target_arch = "wasm32")]
fn main() {}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::terminal_error;

    #[test]
    fn terminal_errors_use_clickable_locations() {
        assert_eq!(
            terminal_error("demo.sexp", "line 12:7: guard failed: a != b"),
            "demo.sexp:12:7: error: guard failed: a != b"
        );
    }

    #[test]
    fn terminal_errors_without_locations_remain_errors() {
        assert_eq!(
            terminal_error("demo.sexp", "unexpected"),
            "error: unexpected"
        );
    }
}
