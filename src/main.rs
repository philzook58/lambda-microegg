mod frontend;

use frontend::run_sexp_script;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

#[cfg(target_arch = "wasm32")]
#[wasm_bindgen]
pub fn run_wasm(input: &str) -> Result<String, JsValue> {
    run_sexp_script(input)
        .map(|lines| lines.join("\n"))
        .map_err(|error| JsValue::from_str(&error))
}

#[cfg(not(target_arch = "wasm32"))]
fn run_sexp_cli(path: Option<&str>) -> Result<(), String> {
    let input = if let Some(path) = path {
        std::fs::read_to_string(path).map_err(|error| format!("cannot read {path}: {error}"))?
    } else {
        use std::io::Read;
        let mut input = String::new();
        std::io::stdin()
            .read_to_string(&mut input)
            .map_err(|error| format!("cannot read stdin: {error}"))?;
        input
    };
    for line in run_sexp_script(&input)? {
        println!("{line}");
    }
    Ok(())
}

#[cfg(not(target_arch = "wasm32"))]
fn main() {
    use std::io::IsTerminal;
    let args: Vec<_> = std::env::args().skip(1).collect();
    if let Some(path) = args.first() {
        let path = (path != "-").then_some(path.as_str());
        if let Err(error) = run_sexp_cli(path) {
            eprintln!("error: {error}");
            std::process::exit(1);
        }
        return;
    }
    if !std::io::stdin().is_terminal() {
        if let Err(error) = run_sexp_cli(None) {
            eprintln!("error: {error}");
            std::process::exit(1);
        }
        return;
    }
    println!(
        "Lambda MicroEgg\n\n\
         Run an S-expression program with:\n  lambda-microegg FILE\n  lambda-microegg -\n\n\
         Commands:\n  (reset)\n  (insert [CONTEXT] TERM)\n  (union [CONTEXT] LEFT RIGHT)\n  (guard [CONTEXT] LEFT RIGHT)\n  (rewrite LHS RHS)\n  (match PATTERN)\n  (run LIMIT)\n  (echo VALUE)\n  (extract [CONTEXT] TERM)\n\n\
         Debugging:\n  (print-egraph)\n\n\
         Named binders:\n  (lam x BODY), x is the nearest binder named x, x@1 is the next outer x\n  $0, $1, ... name variables in the explicit outer context\n\n\
         Miller patterns:\n  ?a excludes pattern-local binders; LHS arguments are written outer-to-inner: (?a x y)\n  On a rewrite RHS, arguments may be permuted or replaced by terms: (?a y x), (?a (foo x))\n\n\
         Built-ins:\n  (#subst BODY x REPLACEMENT) substitutes REPLACEMENT for x in BODY\n  A free variable may also be named directly: (#subst $0 $0 fred)"
    );
}

#[cfg(target_arch = "wasm32")]
fn main() {}
