use lambda_microegg::*;
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

#[derive(Clone, Debug, Eq, PartialEq)]
enum Sexp {
    Atom(String),
    Quoted(String),
    List(Vec<Sexp>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Token {
    Left,
    Right,
    Atom(String, bool),
}

fn lex_sexps(input: &str) -> Result<Vec<Token>, String> {
    let mut chars = input.chars().peekable();
    let mut tokens = vec![];
    while let Some(&ch) = chars.peek() {
        match ch {
            ch if ch.is_whitespace() => {
                chars.next();
            }
            ';' => {
                chars.by_ref().find(|&c| c == '\n');
            }
            '(' => {
                chars.next();
                tokens.push(Token::Left);
            }
            ')' => {
                chars.next();
                tokens.push(Token::Right);
            }
            '"' => {
                chars.next();
                let mut atom = String::new();
                let mut closed = false;
                while let Some(c) = chars.next() {
                    match c {
                        '"' => {
                            closed = true;
                            break;
                        }
                        '\\' => match chars.next() {
                            Some('n') => atom.push('\n'),
                            Some('t') => atom.push('\t'),
                            Some(c @ ('"' | '\\')) => atom.push(c),
                            Some(c) => return Err(format!("unsupported escape \\{c}")),
                            None => return Err("unterminated escape".into()),
                        },
                        c => atom.push(c),
                    }
                }
                if !closed {
                    return Err("unterminated quoted atom".into());
                }
                tokens.push(Token::Atom(atom, true));
            }
            _ => {
                let mut atom = String::new();
                while let Some(&c) = chars.peek() {
                    if c.is_whitespace() || matches!(c, '(' | ')' | ';') {
                        break;
                    }
                    atom.push(c);
                    chars.next();
                }
                tokens.push(Token::Atom(atom, false));
            }
        }
    }
    Ok(tokens)
}

fn parse_sexps(input: &str) -> Result<Vec<Sexp>, String> {
    fn one(tokens: &[Token], cursor: &mut usize) -> Result<Sexp, String> {
        match tokens.get(*cursor) {
            Some(Token::Atom(atom, quoted)) => {
                *cursor += 1;
                Ok(if *quoted {
                    Sexp::Quoted(atom.clone())
                } else {
                    Sexp::Atom(atom.clone())
                })
            }
            Some(Token::Left) => {
                *cursor += 1;
                let mut items = vec![];
                while !matches!(tokens.get(*cursor), Some(Token::Right)) {
                    if *cursor == tokens.len() {
                        return Err("unclosed '('".into());
                    }
                    items.push(one(tokens, cursor)?);
                }
                *cursor += 1;
                Ok(Sexp::List(items))
            }
            Some(Token::Right) => Err("unexpected ')'".into()),
            None => Err("unexpected end of input".into()),
        }
    }

    let tokens = lex_sexps(input)?;
    let mut cursor = 0;
    let mut forms = vec![];
    while cursor < tokens.len() {
        forms.push(one(&tokens, &mut cursor)?);
    }
    Ok(forms)
}

fn atom_of(sexp: &Sexp) -> Result<&str, String> {
    match sexp {
        Sexp::Atom(atom) | Sexp::Quoted(atom) => Ok(atom),
        Sexp::List(_) => Err("expected an atom".into()),
    }
}

fn namespaced_name(atom: &str) -> (&str, usize) {
    atom.rsplit_once('@')
        .and_then(|(name, index)| index.parse().ok().map(|index| (name, index)))
        .unwrap_or((atom, 0))
}

/// Resolve `x` or `x@n` among binders named `x`, counting from the inside.
/// Returns the ordinary de Bruijn index and the binder's outer-to-inner slot.
fn resolve_binder(atom: &str, binders: &[String]) -> Option<(usize, usize)> {
    let (name, namespace_index) = namespaced_name(atom);
    let slot = binders
        .iter()
        .enumerate()
        .rev()
        .filter(|(_, binder)| binder.as_str() == name)
        .nth(namespace_index)?
        .0;
    Some((binders.len() - 1 - slot, slot))
}

fn binder_name(sexp: &Sexp) -> Result<&str, String> {
    let Sexp::Atom(name) = sexp else {
        return Err("binder must be an unquoted name".into());
    };
    let has_namespace_index = name
        .rsplit_once('@')
        .is_some_and(|(_, suffix)| suffix.parse::<usize>().is_ok());
    if name.is_empty() || name.starts_with(['?', '$']) || has_namespace_index {
        return Err(format!("invalid lambda binder '{name}'"));
    }
    Ok(name)
}

fn subst_binder_name(sexp: &Sexp) -> Result<&str, String> {
    if let Sexp::Atom(name) = sexp
        && name
            .strip_prefix('$')
            .is_some_and(|index| index.parse::<usize>().is_ok())
    {
        return Ok(name);
    }
    binder_name(sexp)
}

fn add_sexp_term(eg: &mut EGraph, sexp: &Sexp, ctx: usize) -> Result<Id, String> {
    fn go(
        eg: &mut EGraph,
        sexp: &Sexp,
        outer_ctx: usize,
        binders: &mut Vec<String>,
    ) -> Result<Id, String> {
        let ctx = outer_ctx + binders.len();
        if ctx > 7 {
            return Err("packed IDs support at most 7 context variables".into());
        }
        match sexp {
            Sexp::Quoted(atom) => Ok(eg.atom(atom, ctx)),
            Sexp::Atom(atom) if resolve_binder(atom, binders).is_some() => {
                let (_, slot) = resolve_binder(atom, binders).unwrap();
                Ok(eg.var(ctx, outer_ctx + slot))
            }
            Sexp::Atom(atom) if atom.starts_with('$') => {
                let index = atom[1..]
                    .parse::<usize>()
                    .map_err(|_| format!("invalid outer-context variable '{atom}'"))?;
                if index >= outer_ctx {
                    return Err(format!(
                        "{atom} is out of scope in outer context {outer_ctx}"
                    ));
                }
                Ok(eg.var(ctx, index))
            }
            Sexp::Atom(atom) if atom.starts_with('?') => {
                Err(format!("pattern variable '{atom}' used in a term"))
            }
            Sexp::Atom(atom) => Ok(eg.atom(atom, ctx)),
            Sexp::List(items) => {
                let Some(head) = items.first() else {
                    return Err("empty term list".into());
                };
                let op = atom_of(head)?;
                if let Some(op) = op.strip_prefix('@') {
                    if op.is_empty() || items.len() != 3 {
                        return Err("(@OP NAME BODY) takes a binder name and body".into());
                    }
                    let name = binder_name(&items[1])?.to_owned();
                    binders.push(name);
                    let body = go(eg, &items[2], outer_ctx, binders);
                    binders.pop();
                    let body = eg.lam(body?);
                    return Ok(eg.app(op, vec![body]));
                }
                if op == "lam" {
                    if items.len() != 3 {
                        return Err("(lam NAME BODY) takes a binder name and body".into());
                    }
                    let name = binder_name(&items[1])?.to_owned();
                    binders.push(name);
                    let body = go(eg, &items[2], outer_ctx, binders);
                    binders.pop();
                    return Ok(eg.lam(body?));
                }
                if op == "#subst" {
                    if items.len() != 4 {
                        return Err(
                            "(#subst BODY NAME REPLACEMENT) takes a body, binder, and replacement"
                                .into(),
                        );
                    }
                    let name = subst_binder_name(&items[2])?.to_owned();
                    binders.push(name);
                    let body = go(eg, &items[1], outer_ctx, binders);
                    binders.pop();
                    let body = body?;
                    let replacement = go(eg, &items[3], outer_ctx, binders)?;
                    return Ok(eg.substitute(&body, ctx, &replacement));
                }
                if items.len() < 2 {
                    return Err(format!("application '({op} ...)' needs an argument"));
                }
                let children = items[1..]
                    .iter()
                    .map(|item| go(eg, item, outer_ctx, binders))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(eg.app(op, children))
            }
        }
    }

    if ctx > 7 {
        return Err("packed IDs support at most 7 context variables".into());
    }
    go(eg, sexp, ctx, &mut vec![])
}

fn sexp_pattern(sexp: &Sexp) -> Result<Pattern, String> {
    fn go(sexp: &Sexp, binders: &mut Vec<String>) -> Result<Pattern, String> {
        match sexp {
            Sexp::Quoted(atom) => Ok(Pattern::atom(atom)),
            Sexp::Atom(atom) if atom.starts_with('?') && atom.len() > 1 => {
                Ok(Pattern::Var(atom.as_str().into(), vec![]))
            }
            Sexp::Atom(atom) if resolve_binder(atom, binders).is_some() => {
                let (index, _) = resolve_binder(atom, binders).unwrap();
                Ok(Pattern::Bound(index))
            }
            Sexp::Atom(atom) if atom.starts_with('$') => {
                let index = atom[1..]
                    .parse::<usize>()
                    .map_err(|_| format!("invalid outer-context variable '{atom}'"))?;
                Ok(Pattern::Coord(index))
            }
            Sexp::Atom(atom) => Ok(Pattern::atom(atom)),
            Sexp::List(items) => {
                let Some(head) = items.first() else {
                    return Err("empty pattern list".into());
                };
                let op = atom_of(head)?;
                if matches!(head, Sexp::Atom(_)) && op.starts_with('?') && op.len() > 1 {
                    let mut bound = Vec::with_capacity(items.len() - 1);
                    for argument in &items[1..] {
                        let argument = atom_of(argument)?;
                        let Some((index, _)) = resolve_binder(argument, binders) else {
                            return Err(format!(
                                "Miller metavariable '{op}' argument '{argument}' is not a pattern binder"
                            ));
                        };
                        if bound.contains(&index) {
                            return Err(format!(
                                "Miller metavariable '{op}' repeats bound variable {argument}"
                            ));
                        }
                        bound.push(index);
                    }
                    return Ok(Pattern::miller(op, bound));
                }
                if let Some(op) = op.strip_prefix('@') {
                    if op.is_empty() || items.len() != 3 {
                        return Err("(@OP NAME PATTERN) takes a binder name and body".into());
                    }
                    let name = binder_name(&items[1])?.to_owned();
                    binders.push(name);
                    let body = go(&items[2], binders);
                    binders.pop();
                    return Ok(Pattern::app(op, vec![Pattern::Lam(Box::new(body?))]));
                }
                if op == "lam" {
                    if items.len() != 3 {
                        return Err("(lam NAME PATTERN) takes a binder name and body".into());
                    }
                    let name = binder_name(&items[1])?.to_owned();
                    binders.push(name);
                    let body = go(&items[2], binders);
                    binders.pop();
                    return Ok(Pattern::Lam(Box::new(body?)));
                }
                if op == "#subst" {
                    if items.len() != 4 {
                        return Err(
                            "(#subst BODY NAME REPLACEMENT) takes a body, binder, and replacement"
                                .into(),
                        );
                    }
                    let name = subst_binder_name(&items[2])?.to_owned();
                    binders.push(name);
                    let body = go(&items[1], binders);
                    binders.pop();
                    let replacement = go(&items[3], binders)?;
                    return Ok(Pattern::Subst(Box::new(body?), Box::new(replacement)));
                }
                if items.len() < 2 {
                    return Err(format!("pattern '({op} ...)' needs an argument"));
                }
                let children = items[1..]
                    .iter()
                    .map(|item| go(item, binders))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Pattern::app(op, children))
            }
        }
    }
    go(sexp, &mut vec![])
}

fn sexp_match_pattern(sexp: &Sexp) -> Result<Pattern, String> {
    let pattern = sexp_pattern(sexp)?;
    pattern.validate_match_pattern()?;
    Ok(pattern)
}

fn command_term<'a>(items: &'a [Sexp], command: &str) -> Result<(usize, &'a Sexp), String> {
    match items {
        [_, term] => Ok((0, term)),
        [_, context, term] => {
            let context = atom_of(context)?
                .parse::<usize>()
                .map_err(|_| format!("{command} context must be a nonnegative integer"))?;
            if context > 7 {
                return Err("packed IDs support at most 7 context variables".into());
            }
            Ok((context, term))
        }
        _ => Err(format!("wrong number of arguments to '{command}'")),
    }
}

fn command_terms<'a>(
    items: &'a [Sexp],
    command: &str,
) -> Result<(usize, &'a Sexp, &'a Sexp), String> {
    match items {
        [_, left, right] => Ok((0, left, right)),
        [_, context, left, right] => {
            let context = atom_of(context)?
                .parse::<usize>()
                .map_err(|_| format!("{command} context must be a nonnegative integer"))?;
            if context > 7 {
                return Err("packed IDs support at most 7 context variables".into());
            }
            Ok((context, left, right))
        }
        _ => Err(format!("wrong number of arguments to '{command}'")),
    }
}

fn comment_lines(text: &str) -> String {
    text.split('\n')
        .map(|line| format!("; {line}"))
        .collect::<Vec<_>>()
        .join("\n")
}

fn run_sexp_script(input: &str) -> Result<Vec<String>, String> {
    let mut eg = EGraph::new();
    let mut rules = vec![];
    let mut output = vec![];
    for (command_index, form) in parse_sexps(input)?.iter().enumerate() {
        let Sexp::List(items) = form else {
            return Err(format!("command {} must be a list", command_index + 1));
        };
        let Some(head) = items.first() else {
            return Err(format!("command {} is empty", command_index + 1));
        };
        let command = atom_of(head)?;
        let output_start = output.len();
        match command {
            "reset" if items.len() == 1 => {
                eg = EGraph::new();
                rules.clear();
                output.push("reset".into());
            }
            "insert" if matches!(items.len(), 2 | 3) => {
                let (ctx, term) = command_term(items, "insert")?;
                let id = add_sexp_term(&mut eg, term, ctx)?;
                output.push(format!("inserted {}", id.show()));
            }
            "union" if matches!(items.len(), 3 | 4) => {
                let (ctx, left, right) = command_terms(items, "union")?;
                let left = add_sexp_term(&mut eg, left, ctx)?;
                let right = add_sexp_term(&mut eg, right, ctx)?;
                let changed = eg.union(&left, &right);
                eg.rebuild();
                output.push(if changed {
                    "unioned".into()
                } else {
                    "already equivalent".into()
                });
            }
            "guard" if matches!(items.len(), 3 | 4) => {
                let (ctx, left, right) = command_terms(items, "guard")?;
                let left = add_sexp_term(&mut eg, left, ctx)?;
                let right = add_sexp_term(&mut eg, right, ctx)?;
                eg.rebuild();
                if !eg.equivalent(&left, &right) {
                    let left = eg.extract(&left).map_or_else(
                        || "<no finite term>".into(),
                        |term| term.display_in(ctx).to_string(),
                    );
                    let right = eg.extract(&right).map_or_else(
                        || "<no finite term>".into(),
                        |term| term.display_in(ctx).to_string(),
                    );
                    return Err(format!("guard failed: {left} != {right}"));
                }
                output.push("guard passed".into());
            }
            "rewrite" if items.len() == 3 => {
                rules.push((sexp_match_pattern(&items[1])?, sexp_pattern(&items[2])?));
                output.push(format!("rewrite {} added", rules.len()));
            }
            "match" if items.len() == 2 => {
                let pattern = sexp_match_pattern(&items[1])?;
                let matches = eg.search(&pattern);
                if matches.is_empty() {
                    output.push("no matches".into());
                }
                for (index, (context, subst)) in matches.into_iter().enumerate() {
                    let bindings: Vec<_> = subst
                        .bindings()
                        .map(|(name, binding)| (name.to_owned(), binding.clone()))
                        .collect();
                    let mut rendered = Vec::with_capacity(bindings.len());
                    for (name, binding) in bindings {
                        let term = eg.extract(&binding.body()).ok_or_else(|| {
                            format!("binding {name} has no finite extractable term")
                        })?;
                        let parameters: Vec<_> = (0..binding.arity())
                            .map(|index| format!("x{index}"))
                            .collect();
                        let kept_parameters: Vec<_> = binding
                            .kept()
                            .into_iter()
                            .map(|index| parameters[index].clone())
                            .collect();
                        let body = term
                            .display_with_root_binders(binding.top_ctx(), &kept_parameters)
                            .to_string();
                        let value = if parameters.is_empty() {
                            body
                        } else {
                            format!("mlam {} {body}", parameters.join(" "))
                        };
                        rendered.push(format!("{name} = {value}"));
                    }
                    output.push(format!(
                        "match {} ctx{context} |-> {{{}}}",
                        index + 1,
                        rendered.join(", ")
                    ));
                }
            }
            "run" if items.len() == 2 => {
                let limit = atom_of(&items[1])?
                    .parse::<usize>()
                    .map_err(|_| "run limit must be a nonnegative integer".to_string())?;
                let mut rounds = 0;
                while rounds < limit {
                    let changed = eg.saturate_limit(&rules, 1) > 0;
                    if !changed {
                        break;
                    }
                    rounds += 1;
                }
                output.push(format!(
                    "ran {rounds} rounds: {} classes, {} e-nodes",
                    eg.class_count(),
                    eg.node_count()
                ));
            }
            "echo" if items.len() == 2 => output.push(atom_of(&items[1])?.to_owned()),
            "print-egraph" if items.len() == 1 => output.push(eg.dump()),
            "extract" if matches!(items.len(), 2 | 3) => {
                let (ctx, term) = command_term(items, "extract")?;
                let id = add_sexp_term(&mut eg, term, ctx)?;
                let term = eg
                    .extract(&id)
                    .ok_or_else(|| "class has no finite extractable term".to_string())?;
                output.push(term.display_in(ctx).to_string());
            }
            "reset" | "insert" | "union" | "guard" | "rewrite" | "match" | "run" | "echo"
            | "print-egraph" | "extract" => {
                return Err(format!("wrong number of arguments to '{command}'"));
            }
            _ => return Err(format!("unknown command '{command}'")),
        }
        if command != "extract" {
            for item in &mut output[output_start..] {
                *item = comment_lines(item);
            }
        }
    }
    Ok(output)
}

#[cfg(target_arch = "wasm32")]
#[wasm_bindgen]
pub fn run_wasm(input: &str) -> Result<String, JsValue> {
    run_sexp_script(input)
        .map(|lines| lines.join("\n"))
        .map_err(|error| JsValue::from_str(&error))
}

#[cfg(not(target_arch = "wasm32"))]
fn bench_ac(n: usize) {
    let mut eg = EGraph::new();
    let atoms: Vec<_> = (0..n).map(|i| eg.atom(&format!("x{i}"), 0)).collect();
    let mut input = atoms[0];
    for atom in &atoms[1..] {
        input = eg.app("+", vec![input, *atom]);
    }
    let mut goal = atoms[n - 1];
    for atom in atoms[..n - 1].iter().rev() {
        goal = eg.app("+", vec![goal, *atom]);
    }
    let var = |s: &str| Pattern::Var(s.into(), vec![]);
    let plus = |a, b| Pattern::app("+", vec![a, b]);
    let rules = [
        (
            plus(plus(var("?a"), var("?b")), var("?c")),
            plus(var("?a"), plus(var("?b"), var("?c"))),
        ),
        (plus(var("?a"), var("?b")), plus(var("?b"), var("?a"))),
    ];
    let start = Instant::now();
    let rounds = eg.saturate(&rules);
    let elapsed = start.elapsed();
    let classes = eg.class_count();
    let nodes = eg.node_count();
    println!(
        "AC({n}): {rounds} rounds, {classes} classes, {nodes} e-nodes, {} raw IDs allocated, {elapsed:?}",
        eg.raw_id_count()
    );
    assert!(eg.equivalent(&input, &goal));
    assert_eq!(classes, (1 << n) - 1);
    assert_eq!(
        nodes,
        3usize.pow(n as u32) - 2usize.pow((n + 1) as u32) + 1 + n
    );
}

#[cfg(not(target_arch = "wasm32"))]
fn print_beta_result(label: &str, eg: &mut EGraph, term: &Id) {
    let rounds = eg.saturate_beta();
    let result = eg.extract(term).expect("beta class has no finite term");
    println!(
        "{label}\n  => {}  ({rounds} saturation rounds)",
        result.display_in(term.ctx())
    );
}

#[cfg(not(target_arch = "wasm32"))]
fn beta_examples() {
    {
        let mut eg = EGraph::new();
        let outer_x = eg.var(3, 1);
        let inner_lambda = eg.lam(outer_x);
        let function = eg.lam(inner_lambda);
        let free_y = eg.var(1, 0);
        let term = eg.app("app", vec![function, free_y]);
        print_beta_result("y |- (λx. λz. x) y", &mut eg, &term);
    }
    {
        let mut eg = EGraph::new();
        let outer_x = eg.var(2, 0);
        let inner_lambda = eg.lam(outer_x);
        let function = eg.lam(inner_lambda);
        let z = eg.var(1, 0);
        let identity = eg.lam(z);
        let term = eg.app("app", vec![function, identity]);
        print_beta_result("(λx. λy. x) (λz. z)", &mut eg, &term);
    }
    {
        let mut eg = EGraph::new();
        let a = eg.atom("a", 1);
        let constant_function = eg.lam(a);
        let omega_var = eg.var(1, 0);
        let omega_body = eg.app("app", vec![omega_var, omega_var]);
        let delta = eg.lam(omega_body);
        let omega = eg.app("app", vec![delta, delta]);
        let term = eg.app("app", vec![constant_function, omega]);
        print_beta_result("(λx. a) ((λw. w w) (λw. w w))", &mut eg, &term);
    }
    {
        let mut eg = EGraph::new();
        let inner_y = eg.var(2, 1);
        let inner_identity = eg.lam(inner_y);
        let outer_x = eg.var(1, 0);
        let body = eg.app("app", vec![inner_identity, outer_x]);
        let term = eg.lam(body);
        print_beta_result("λx. (λy. y) x", &mut eg, &term);
    }
    {
        let mut eg = EGraph::new();
        let x = eg.var(1, 0);
        let xx = eg.app("app", vec![x, x]);
        let duplicator = eg.lam(xx);
        let y = eg.var(1, 0);
        let identity = eg.lam(y);
        let term = eg.app("app", vec![duplicator, identity]);
        print_beta_result("(λx. x x) (λy. y)", &mut eg, &term);
    }
}

#[cfg(not(target_arch = "wasm32"))]
fn bench_lambda_under() {
    let mut eg = EGraph::new();
    let four = eg.atom("4", 1);
    let inner_y = eg.var(2, 1);
    let inner_identity = eg.lam(inner_y);
    let inner_redex = eg.app("app", vec![inner_identity, four]);
    let sum = eg.app("+", vec![four, inner_redex]);
    let term = eg.lam(sum);
    let fold_four_plus_four = [(
        Pattern::app("+", vec![Pattern::atom("4"), Pattern::atom("4")]),
        Pattern::atom("8"),
    )];

    let start = Instant::now();
    let beta_rounds = eg.saturate_beta();
    let fold_rounds = eg.saturate(&fold_four_plus_four);
    let elapsed = start.elapsed();
    let result = eg.extract(&term).unwrap();
    assert_eq!(result.to_string(), "(lam 8)");
    println!(
        "egg lambda_under port: {beta_rounds} beta rounds, {fold_rounds} fold rounds, {} classes, {} e-nodes, {elapsed:?}",
        eg.class_count(),
        eg.node_count()
    );
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
    if args.iter().any(|arg| arg == "--bench-ac7") {
        bench_ac(7);
        return;
    }
    if args.iter().any(|arg| arg == "--bench-ac10") {
        bench_ac(10);
        return;
    }
    if args.iter().any(|arg| arg == "--beta-examples") {
        beta_examples();
        return;
    }
    if args.iter().any(|arg| arg == "--bench-lambda-under") {
        bench_lambda_under();
        return;
    }
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
         Miller patterns:\n  ?a excludes pattern-local binders; (?a x ...) admits listed named binders\n\n\
         Built-ins:\n  (#subst BODY x REPLACEMENT) substitutes REPLACEMENT for x in BODY\n  A local coordinate may also be named directly: (#subst $0 $0 fred)\n\n\
         Benchmarks: --bench-ac7, --bench-ac10, --bench-lambda-under\n\
         Lambda examples: --beta-examples"
    );
}

#[cfg(target_arch = "wasm32")]
fn main() {}

#[cfg(test)]
mod tests {
    use super::*;

    fn egg_simple_rules() -> Vec<(Pattern, Pattern)> {
        let var = |name: &str| Pattern::Var(name.into(), vec![]);
        let app = |op, left, right| Pattern::app(op, vec![left, right]);
        vec![
            (
                app("+", var("?a"), var("?b")),
                app("+", var("?b"), var("?a")),
            ),
            (
                app("*", var("?a"), var("?b")),
                app("*", var("?b"), var("?a")),
            ),
            (app("+", var("?a"), Pattern::atom("0")), var("?a")),
            (app("*", var("?a"), Pattern::atom("0")), Pattern::atom("0")),
            (app("*", var("?a"), Pattern::atom("1")), var("?a")),
        ]
    }
    #[test]
    fn sexp_frontend_runs_insert_rewrite_run_extract() {
        let output = run_sexp_script(
            r#"
                ; Commands may be separated by arbitrary whitespace.
                (insert (+ a 0))
                (rewrite (+ ?x 0) ?x)
                (run 10)
                (extract (+ a 0))
            "#,
        )
        .unwrap();
        assert_eq!(output.last().unwrap(), "a");
        assert!(output[2].starts_with("; ran 1 rounds:"));
    }
    #[test]
    fn sexp_frontend_rewrites_under_a_binder() {
        let output = run_sexp_script(
            r#"
                (insert (lam x (f a)))
                (rewrite (f ?x) ?x)
                (run 10)
                (extract (lam x (f a)))
            "#,
        )
        .unwrap();
        assert_eq!(output.last().unwrap(), "(lam x0 a)");
    }
    #[test]
    fn sexp_frontend_parses_context_variables_and_reports_scope_errors() {
        let output = run_sexp_script("(insert (lam x x)) (extract (lam x x))").unwrap();
        assert_eq!(output.last().unwrap(), "(lam x0 x0)");
        assert!(
            run_sexp_script("(insert $0)")
                .unwrap_err()
                .contains("out of scope")
        );
    }
    #[test]
    fn named_binders_support_shadowing_and_namespaced_indices() {
        let output = run_sexp_script(
            r#"
                (insert (lam x (lam x x)))
                (extract (lam x (lam x x)))
                (insert (lam x (lam x x@1)))
                (extract (lam x (lam x x@1)))
            "#,
        )
        .unwrap();
        assert_eq!(output[1], "(lam x0 (lam x1 x1))");
        assert_eq!(output[3], "(lam x0 (lam x1 x0))");
    }
    #[test]
    fn dollar_variables_always_refer_to_the_outer_context() {
        let output =
            run_sexp_script("(insert 1 (lam x (pair $0 x))) (extract 1 (lam x (pair $0 x)))")
                .unwrap();
        assert_eq!(output.last().unwrap(), "(lam x0 (pair $0 x0))");
    }
    #[test]
    fn named_output_quotes_atoms_that_would_be_captured() {
        let output = run_sexp_script("(insert (lam x x0)) (extract (lam x x0))").unwrap();
        assert_eq!(output.last().unwrap(), "(lam x0 \"x0\")");
    }
    #[test]
    fn lambda_names_are_alpha_irrelevant() {
        let output = run_sexp_script("(guard (lam x x) (lam y y))").unwrap();
        assert_eq!(output, ["; guard passed"]);
    }
    #[test]
    fn sexp_frontend_honors_zero_run_limit() {
        let output =
            run_sexp_script("(insert (f a)) (rewrite (f ?x) ?x) (run 0) (extract (f a))").unwrap();
        assert_eq!(output[2], "; ran 0 rounds: 2 classes, 2 e-nodes");
        assert_eq!(output.last().unwrap(), "(f a)");
    }
    #[test]
    fn sexp_reset_clears_terms_and_rewrite_rules() {
        let output = run_sexp_script(
            r#"
                (insert old)
                (rewrite (f ?x) ?x)
                (reset)
                (match ?x)
                (insert (f a))
                (run 4)
                (extract (f a))
            "#,
        )
        .unwrap();
        assert_eq!(output[2], "; reset");
        assert_eq!(output[3], "; no matches");
        assert_eq!(output.last().unwrap(), "(f a)");
    }
    #[test]
    fn sexp_reset_clears_substitution_rewrites() {
        let output = run_sexp_script(
            r#"
                (rewrite (app (lam x (?body x)) ?arg) (#subst (?body x) x ?arg))
                (reset)
                (insert (app (lam x x) a))
                (run 4)
                (extract (app (lam x x) a))
            "#,
        )
        .unwrap();
        assert_eq!(output.last().unwrap(), "(app (lam x0 x0) a)");
    }
    #[test]
    fn sexp_reset_rejects_arguments() {
        assert_eq!(
            run_sexp_script("(reset now)").unwrap_err(),
            "wrong number of arguments to 'reset'"
        );
    }
    #[test]
    fn sexp_union_equates_two_terms() {
        let output = run_sexp_script("(union (f a) b) (extract (f a))").unwrap();
        assert_eq!(output, ["; unioned", "b"]);
    }
    #[test]
    fn sexp_union_supports_an_ambient_context() {
        let output = run_sexp_script("(union 1 (f $0) $0) (extract 1 (f $0))").unwrap();
        assert_eq!(output, ["; unioned", "$0"]);
    }
    #[test]
    fn sexp_union_reports_existing_equality() {
        let output = run_sexp_script("(union a a)").unwrap();
        assert_eq!(output, ["; already equivalent"]);
    }
    #[test]
    fn sexp_subst_builtin_is_available_in_insert_and_outer_contexts() {
        let output = run_sexp_script(
            r#"
                (insert 0 (#subst $0 $0 fred))
                (guard (#subst $0 $0 fred) fred)
                (insert 1 (#subst (pair $0 x) x a))
                (extract 1 (pair $0 a))
            "#,
        )
        .unwrap();
        assert_eq!(output[1], "; guard passed");
        assert_eq!(output.last().unwrap(), "(pair $0 a)");
    }
    #[test]
    fn sexp_subst_builtin_is_available_in_union() {
        let output = run_sexp_script(
            r#"
                (union (#subst (f x) x a) b)
                (guard (f a) b)
            "#,
        )
        .unwrap();
        assert_eq!(output, ["; unioned", "; guard passed"]);
    }
    #[test]
    fn sexp_guard_accepts_an_established_equality() {
        let output = run_sexp_script("(union (f a) b) (guard (f a) b)").unwrap();
        assert_eq!(output, ["; unioned", "; guard passed"]);
    }
    #[test]
    fn sexp_guard_checks_equality_after_saturation() {
        let output =
            run_sexp_script("(insert (* a 0)) (rewrite (* ?x 0) 0) (run 4) (guard (* a 0) 0)")
                .unwrap();
        assert_eq!(output.last().unwrap(), "; guard passed");
    }
    #[test]
    fn sexp_guard_supports_an_ambient_context() {
        let output = run_sexp_script("(union 1 (f $0) $0) (guard 1 (f $0) $0)").unwrap();
        assert_eq!(output.last().unwrap(), "; guard passed");
    }
    #[test]
    fn sexp_guard_fails_the_script_for_unequal_terms() {
        let error = run_sexp_script("(guard (f a) b)").unwrap_err();
        assert_eq!(error, "guard failed: (f a) != b");
    }
    #[test]
    fn sexp_match_prints_every_extracted_substitution() {
        let output = run_sexp_script(
            r#"
                (insert (f a))
                (insert (f b))
                (match (f ?x))
            "#,
        )
        .unwrap();
        assert_eq!(
            &output[2..],
            ["; match 1 ctx0 |-> {?x = a}", "; match 2 ctx0 |-> {?x = b}"]
        );
    }
    #[test]
    fn sexp_match_prints_miller_substitutions() {
        let output = run_sexp_script(
            r#"
                (insert (lam x x))
                (match (lam x ?a))
                (match (lam x (?a x)))
            "#,
        )
        .unwrap();
        assert_eq!(output[1], "; no matches");
        assert_eq!(output[2], "; match 1 ctx0 |-> {?a = mlam x0 x0}");
    }
    #[test]
    fn sexp_match_prints_miller_parameters_on_the_right() {
        let output = run_sexp_script(
            r#"
                (insert (lam x (lam y (pair x y))))
                (match (lam x (lam y (?a x y))))
            "#,
        )
        .unwrap();
        assert_eq!(
            output[1],
            "; match 1 ctx0 |-> {?a = mlam x0 x1 (pair x0 x1)}"
        );
    }
    #[test]
    fn generic_binder_sugar_factors_only_independent_sum_terms() {
        let output = run_sexp_script(
            r#"
                (insert
                  (@sum i (@sum j (@sum k (* (a i j) (a j k))))))
                (rewrite
                  (@sum k (* (?f k) ?c))
                  (* ?c (@sum k (?f k))))
                (rewrite
                  (@sum k (* ?c (?f k)))
                  (* ?c (@sum k (?f k))))
                (run 10)
                (guard
                  (@sum i (@sum j (@sum k (* (a i j) (a j k)))))
                  (@sum i (@sum j (* (a i j) (@sum k (a j k))))))
            "#,
        )
        .unwrap();
        assert_eq!(output.last().unwrap(), "; guard passed");

        let output = run_sexp_script(
            r#"
                (insert (@sum i (* (a i) (b i))))
                (match (@sum i (* ?c (?f i))))
            "#,
        )
        .unwrap();
        assert_eq!(output.last().unwrap(), "; no matches");
    }
    #[test]
    fn a_bare_metavariable_can_leave_a_generic_binder() {
        let output = run_sexp_script(
            r#"
                (insert (@sum i c))
                (rewrite (@sum i ?c) (* ?c (@sum i 1)))
                (run 4)
                (guard (@sum i c) (* c (@sum i 1)))
            "#,
        )
        .unwrap();
        assert_eq!(output.last().unwrap(), "; guard passed");
    }
    #[test]
    fn sexp_match_extracts_the_best_equivalent_binding() {
        let output = run_sexp_script(
            r#"
                (insert (g (* a 0)))
                (rewrite (* ?x 0) 0)
                (run 4)
                (match (g ?x))
            "#,
        )
        .unwrap();
        assert_eq!(output.last().unwrap(), "; match 1 ctx0 |-> {?x = 0}");
    }
    #[test]
    fn sexp_match_prints_each_total_context() {
        let output = run_sexp_script(
            r#"
                (insert (f a))
                (insert 1 (f $0))
                (match (f ?x))
            "#,
        )
        .unwrap();
        assert_eq!(
            &output[2..],
            [
                "; match 1 ctx0 |-> {?x = a}",
                "; match 2 ctx1 |-> {?x = $0}"
            ]
        );
    }
    #[test]
    fn sexp_match_miller_arguments_are_relative_to_pattern_lambdas() {
        let output = run_sexp_script(
            r#"
                (insert 1 (lam x (pair $0 x)))
                (match (lam x (pair ?top (?a x))))
            "#,
        )
        .unwrap();
        assert_eq!(output[1], "; match 1 ctx1 |-> {?top = $0, ?a = mlam x0 x0}");
    }
    #[test]
    fn sexp_print_egraph_shows_classes_nodes_and_lifts() {
        let output = run_sexp_script("(insert 1 (lam x (pair $0 x))) (print-egraph)").unwrap();
        assert_eq!(
            output[1],
            concat!(
                "; egraph: 3 classes, 3 e-nodes\n",
                "; e0 = ctx1 |-> $0\n",
                ";   e0 <- var\n",
                "; e1 = ctx2 |-> (pair $0 $1)\n",
                ";   e1 <- (pair l_10(e0) l_01(e0))\n",
                "; e2 = ctx1 |-> (lam x0 (pair $0 x0))\n",
                ";   e2 <- (lam e1)",
            )
        );
    }
    #[test]
    fn sexp_print_egraph_handles_an_empty_graph_and_rejects_arguments() {
        assert_eq!(
            run_sexp_script("(print-egraph)").unwrap(),
            ["; egraph: 0 classes, 0 e-nodes"]
        );
        assert_eq!(
            run_sexp_script("(print-egraph extra)").unwrap_err(),
            "wrong number of arguments to 'print-egraph'"
        );
    }
    #[test]
    fn sexp_echo_emits_quoted_strings_and_atoms() {
        assert_eq!(
            run_sexp_script(r#"(echo "hello world") (echo done)"#).unwrap(),
            ["; hello world", "; done"]
        );
        assert_eq!(
            run_sexp_script("(echo)").unwrap_err(),
            "wrong number of arguments to 'echo'"
        );
        assert_eq!(
            run_sexp_script("(echo (not an atom))").unwrap_err(),
            "expected an atom"
        );
    }
    #[test]
    fn packed_lift_limit() {
        let last = Lift::select(7, 6);
        assert_eq!(last.cod(), 7);
        assert_eq!(last.dom(), 1);
        assert!(last.get(6));
        assert_eq!(Lift::identity(7).compose(&last), last);
        assert_eq!(std::mem::size_of::<Id>(), 4);
    }
    #[test]
    fn fat_ids_hide_identity_lifts() {
        let mut eg = EGraph::new();
        let atom = eg.atom("a", 0);
        let variable = eg.var(1, 0);
        assert_eq!(atom.show(), "e0");
        assert_eq!(variable.show(), "e1");
        assert_eq!(atom.in_context(1).unwrap().show(), "l_0(e0)");
    }
    #[test]
    fn alpha_equivalence_and_shadowing() {
        let mut eg = EGraph::new();
        let var_x = eg.var(1, 0);
        let var_y = eg.var(1, 0);
        let id_x = eg.lam(var_x);
        let id_y = eg.lam(var_y);
        assert!(eg.equivalent(&id_x, &id_y));
        let outer_var = eg.var(2, 0);
        let inner_var = eg.var(2, 1);
        let outer_inner_lam = eg.lam(outer_var);
        let inner_inner_lam = eg.lam(inner_var);
        let outer = eg.lam(outer_inner_lam);
        let inner = eg.lam(inner_inner_lam);
        assert!(!eg.equivalent(&outer, &inner));
    }
    #[test]
    fn free_variable_survives_binder() {
        let mut eg = EGraph::new();
        let free = eg.var(2, 0);
        let bound = eg.var(2, 1);
        let lam_free = eg.lam(free);
        let lam_bound = eg.lam(bound);
        assert_eq!(lam_free.lift().bits(), "1");
        assert_eq!(lam_bound.lift().bits(), "0");
        assert!(!eg.equivalent(&lam_free, &lam_bound));
    }
    #[test]
    fn lift_pull_and_redundant_variable() {
        let mut eg = EGraph::new();
        let x = eg.var(2, 0);
        let y = eg.var(2, 1);
        let z = eg.atom("0", 2);
        let xz = eg.app("*", vec![x, z]);
        let yz = eg.app("*", vec![y, z]);
        assert_eq!(xz.lift().bits(), "10");
        assert_eq!(yz.lift().bits(), "01");
        eg.union(&xz, &z);
        eg.union(&yz, &z);
        eg.rebuild();
        assert!(eg.equivalent(&xz, &yz));
        assert_eq!(eg.find(&xz).lift().bits(), "00");
    }
    #[test]
    fn binder_rebuild_after_union() {
        let mut eg = EGraph::new();
        let x = eg.var(1, 0);
        let z = eg.atom("0", 1);
        let xz = eg.app("*", vec![x, z]);
        let lam_xz = eg.lam(xz);
        let lam_z = eg.lam(z);
        eg.union(&xz, &z);
        eg.rebuild();
        assert!(eg.equivalent(&lam_xz, &lam_z));
    }
    #[test]
    fn ordinary_congruence_after_union() {
        let mut eg = EGraph::new();
        let a = eg.atom("a", 0);
        let b = eg.atom("b", 0);
        let fa = eg.app("f", vec![a]);
        let fb = eg.app("f", vec![b]);
        assert!(!eg.equivalent(&fa, &fb));
        eg.union(&a, &b);
        eg.rebuild();
        assert!(eg.equivalent(&fa, &fb));
    }
    #[test]
    fn match_and_rewrite_x_times_zero() {
        let mut eg = EGraph::new();
        let x = eg.var(2, 0);
        let y = eg.var(2, 1);
        let zero = eg.atom("0", 2);
        let xz = eg.app("*", vec![x, zero]);
        let yz = eg.app("*", vec![y, zero]);
        let lhs = Pattern::app(
            "*",
            vec![Pattern::Var("?x".into(), vec![]), Pattern::atom("0")],
        );
        let x_matches = eg.ematch(&lhs, &xz);
        let y_matches = eg.ematch(&lhs, &yz);
        assert_eq!(x_matches.len(), 1);
        assert_eq!(y_matches.len(), 1);
        assert!(eg.equivalent(&x_matches[0]["?x"].body(), &x));
        assert!(eg.equivalent(&y_matches[0]["?x"].body(), &y));
        assert!(eg.rewrite_once(&lhs, &Pattern::atom("0")) > 0);
        assert!(eg.equivalent(&xz, &zero));
        assert!(eg.equivalent(&yz, &zero));
        // Explicit lifted enumeration can inspect both redundant placements;
        // ordinary rewriting stays on the single canonical zero enode.
        assert_eq!(eg.ematch(&lhs, &zero).len(), 1);
        let after = eg.ematch_lifted(&lhs, &zero);
        assert!(after.iter().any(|s| eg.equivalent(&s["?x"].body(), &x)));
        assert!(after.iter().any(|s| eg.equivalent(&s["?x"].body(), &y)));
    }
    #[test]
    fn match_two_variables_and_repeated_variable() {
        let mut eg = EGraph::new();
        let x = eg.var(2, 0);
        let y = eg.var(2, 1);
        let xy = eg.app("*", vec![x, y]);
        let two = Pattern::app(
            "*",
            vec![
                Pattern::Var("?a".into(), vec![]),
                Pattern::Var("?b".into(), vec![]),
            ],
        );
        let matches = eg.ematch(&two, &xy);
        assert_eq!(matches.len(), 1);
        assert!(eg.equivalent(&matches[0]["?a"].body(), &x));
        assert!(eg.equivalent(&matches[0]["?b"].body(), &y));
        let repeated = Pattern::app(
            "*",
            vec![
                Pattern::Var("?a".into(), vec![]),
                Pattern::Var("?a".into(), vec![]),
            ],
        );
        assert!(eg.ematch(&repeated, &xy).is_empty());
        let swapped = Pattern::app(
            "*",
            vec![
                Pattern::Var("?b".into(), vec![]),
                Pattern::Var("?a".into(), vec![]),
            ],
        );
        assert!(eg.rewrite_once(&two, &swapped) > 0);
        let yx = eg.app("*", vec![y, x]);
        assert!(eg.equivalent(&xy, &yx));
    }
    #[test]
    fn match_inside_lambda() {
        let mut eg = EGraph::new();
        let bound = eg.var(1, 0);
        let zero = eg.atom("0", 1);
        let body = eg.app("*", vec![bound, zero]);
        let lam = eg.lam(body);
        let pat = Pattern::Lam(Box::new(Pattern::app(
            "*",
            vec![Pattern::Var("?body".into(), vec![0]), Pattern::atom("0")],
        )));
        let matches = eg.ematch(&pat, &lam);
        assert_eq!(matches.len(), 1);
        assert!(eg.equivalent(&matches[0]["?body"].body(), &bound));
    }
    #[test]
    fn contextual_metavariable_crosses_an_unused_binder() {
        let mut eg = EGraph::new();
        let a = eg.atom("a", 0);
        let a_under_binder = eg.atom("a", 1);
        let lam_a = eg.lam(a_under_binder);
        let term = eg.app("pair", vec![a, lam_a]);
        let pattern = Pattern::app(
            "pair",
            vec![
                Pattern::Var("?x".into(), vec![]),
                Pattern::Lam(Box::new(Pattern::Var("?x".into(), vec![]))),
            ],
        );

        let matches = eg.ematch(&pattern, &term);
        assert_eq!(matches.len(), 1);
        assert!(eg.equivalent(&matches[0]["?x"].body(), &a));
    }
    #[test]
    fn contextual_metavariable_cannot_capture_a_binder() {
        let mut eg = EGraph::new();
        let a = eg.atom("a", 0);
        let bound = eg.var(1, 0);
        let lam_bound = eg.lam(bound);
        let term = eg.app("pair", vec![a, lam_bound]);
        let pattern = Pattern::app(
            "pair",
            vec![
                Pattern::Var("?x".into(), vec![]),
                Pattern::Lam(Box::new(Pattern::Var("?x".into(), vec![]))),
            ],
        );

        assert!(eg.ematch(&pattern, &term).is_empty());
    }
    #[test]
    fn contextual_metavariable_can_be_inserted_under_a_binder() {
        let mut eg = EGraph::new();
        let a = eg.atom("a", 0);
        let lhs = Pattern::Var("?x".into(), vec![]);
        let rhs = Pattern::Lam(Box::new(Pattern::Var("?x".into(), vec![])));
        let subst = eg.ematch(&lhs, &a).pop().unwrap();
        let result = eg.try_instantiate(&rhs, 0, &subst).unwrap();
        let expected_body = eg.atom("a", 1);
        let expected = eg.lam(expected_body);

        assert!(eg.equivalent(&result, &expected));
    }
    #[test]
    fn context_extension_and_restriction_follow_dependencies() {
        let mut eg = EGraph::new();
        let x = eg.var(1, 0);
        let x_in_three = x.in_context(3).unwrap();
        assert_eq!(x_in_three.lift().bits(), "100");
        assert_eq!(x_in_three.in_context(1), Some(x));

        let newest = eg.var(3, 2);
        assert!(newest.in_context(2).is_none());

        let constant = eg.atom("c", 3);
        assert_eq!(constant.lift().bits(), "000");
        assert!(constant.in_context(0).is_some());
    }
    #[test]
    fn redundant_binding_matches_through_an_equivalent_constant() {
        let mut eg = EGraph::new();
        let x = eg.var(1, 0);
        let zero = eg.atom("0", 1);
        let sub_xx = eg.app("sub", vec![x, x]);
        eg.union(&zero, &sub_xx);
        eg.rebuild();
        let term = eg.app("f", vec![x, zero]);
        let pattern = Pattern::app(
            "f",
            vec![
                Pattern::Var("?x".into(), vec![]),
                Pattern::app(
                    "sub",
                    vec![
                        Pattern::Var("?x".into(), vec![]),
                        Pattern::Var("?x".into(), vec![]),
                    ],
                ),
            ],
        );

        let matches = eg.ematch_lifted(&pattern, &term);
        assert!(!matches.is_empty());
        assert!(matches.iter().all(|s| eg.equivalent(&s["?x"].body(), &x)));
    }
    #[test]
    fn substitute_an_arbitrary_context_coordinate() {
        let mut eg = EGraph::new();
        let x = eg.var(3, 0);
        let y = eg.var(3, 1);
        let z = eg.var(3, 2);
        let body = eg.app("triple", vec![x, y, z]);
        let left = eg.var(2, 0);
        let right = eg.var(2, 1);
        let replacement = eg.app("pair", vec![left, right]);

        let result = eg.substitute(&body, 1, &replacement);
        let expected = eg.app("triple", vec![left, replacement, right]);
        assert!(eg.equivalent(&result, &expected));
    }
    #[test]
    fn substitute_under_a_binder_without_capture() {
        let mut eg = EGraph::new();
        let outer = eg.var(2, 0);
        let inner = eg.var(2, 1);
        let body = eg.app("pair", vec![outer, inner]);
        let term = eg.lam(body);
        let replacement = eg.atom("a", 0);

        let result = eg.substitute(&term, 0, &replacement);
        let a_under_binder = eg.atom("a", 1);
        let remaining_bound = eg.var(1, 0);
        let expected_body = eg.app("pair", vec![a_under_binder, remaining_bound]);
        let expected = eg.lam(expected_body);
        assert!(eg.equivalent(&result, &expected));
    }
    #[test]
    fn substitution_prunes_the_var_times_zero_cycle() {
        let mut eg = EGraph::new();
        let x = eg.var(1, 0);
        let zero = eg.atom("0", 1);
        let x_times_zero = eg.app("*", vec![x, zero]);
        eg.union(&x_times_zero, &zero);
        eg.rebuild();
        let body = eg.app("pair", vec![x, x_times_zero]);
        let replacement = eg.atom("a", 0);

        let result = eg.substitute(&body, 0, &replacement);
        let zero_closed = eg.atom("0", 0);
        let expected = eg.app("pair", vec![replacement, zero_closed]);
        assert!(eg.equivalent(&result, &expected));
    }
    #[test]
    fn substitution_memoizes_a_genuinely_recursive_eclass() {
        let mut eg = EGraph::new();
        let x = eg.var(1, 0);
        let fx = eg.app("f", vec![x]);
        eg.union(&x, &fx);
        eg.rebuild();
        let a = eg.atom("a", 0);

        let result = eg.substitute(&x, 0, &a);
        let fa = eg.app("f", vec![a]);
        assert!(eg.equivalent(&result, &a));
        assert!(eg.equivalent(&result, &fa));
    }
    #[test]
    fn substitution_detects_a_cycle_lifted_through_a_binder() {
        let mut eg = EGraph::new();
        let x = eg.var(1, 0);
        let x_under_binder = x.in_context(2).unwrap();
        let lambda_x = eg.lam(x_under_binder);
        eg.union(&x, &lambda_x);
        eg.rebuild();
        let a = eg.atom("a", 0);

        let result = eg.substitute(&x, 0, &a);
        let a_under_binder = eg.atom("a", 1);
        let lambda_a = eg.lam(a_under_binder);
        assert!(eg.equivalent(&result, &a));
        assert!(eg.equivalent(&result, &lambda_a));
    }
    #[test]
    fn extract_prefers_zero_from_the_var_times_zero_class() {
        let mut eg = EGraph::new();
        let x = eg.var(1, 0);
        let zero = eg.atom("0", 1);
        let x_times_zero = eg.app("*", vec![x, zero]);
        eg.union(&x_times_zero, &zero);

        assert_eq!(eg.extract(&x_times_zero), Some(Term::Atom("0".into())));
    }
    #[test]
    fn extract_skips_a_recursive_enode() {
        let mut eg = EGraph::new();
        let a = eg.atom("a", 0);
        let fa = eg.app("f", vec![a]);
        eg.union(&a, &fa);

        assert_eq!(eg.extract(&a), Some(Term::Atom("a".into())));
    }
    #[test]
    fn extract_reconstructs_variable_placements_under_binders() {
        let mut eg = EGraph::new();
        let outer = eg.var(2, 0);
        let inner = eg.var(2, 1);
        let pair = eg.app("pair", vec![outer, inner]);
        let term = eg.lam(pair);

        assert_eq!(eg.extract(&term).unwrap().to_string(), "(lam (pair $0 $1))");
    }
    #[test]
    fn extract_accepts_a_custom_monotone_cost() {
        fn weighted_size(term: &Term) -> usize {
            match term {
                Term::Var(_) => 1,
                Term::Atom(name) if name.as_str() == "expensive" => 100,
                Term::Atom(_) => 1,
                Term::App(_, children) => 1 + children.iter().map(weighted_size).sum::<usize>(),
                Term::Lam(body) => 1 + weighted_size(body),
            }
        }

        let mut eg = EGraph::new();
        let expensive = eg.atom("expensive", 0);
        let cheap = eg.atom("cheap", 0);
        let wrapped = eg.app("wrap", vec![cheap]);
        eg.union(&expensive, &wrapped);

        assert_eq!(
            eg.extract_with(&expensive, weighted_size)
                .unwrap()
                .to_string(),
            "(wrap cheap)"
        );
    }
    #[test]
    fn beta_avoids_capture_when_the_argument_is_free() {
        let mut eg = EGraph::new();
        // In y |- (λx. λy'. x) y, the argument y must remain the outer
        // coordinate rather than becoming captured by y'.
        let outer_x = eg.var(3, 1);
        let inner_lambda = eg.lam(outer_x);
        let function = eg.lam(inner_lambda);
        let free_y = eg.var(1, 0);
        let redex = eg.app("app", vec![function, free_y]);

        eg.saturate_beta();
        assert_eq!(eg.extract(&redex).unwrap().to_string(), "(lam $0)");
        let expected_free_y = eg.var(2, 0);
        let expected = eg.lam(expected_free_y);
        assert!(eg.equivalent(&redex, &expected));
        let captured_y = eg.var(2, 1);
        let incorrect = eg.lam(captured_y);
        assert!(!eg.equivalent(&redex, &incorrect));
    }
    #[test]
    fn beta_does_not_shift_a_lambda_argument() {
        let mut eg = EGraph::new();
        // Slotted's t_shift regression: (λx. λy. x) (λz. z).
        let outer_x = eg.var(2, 0);
        let inner_lambda = eg.lam(outer_x);
        let function = eg.lam(inner_lambda);
        let z = eg.var(1, 0);
        let identity = eg.lam(z);
        let redex = eg.app("app", vec![function, identity]);

        eg.saturate_beta();
        assert_eq!(eg.extract(&redex).unwrap().to_string(), "(lam (lam $1))");
        let expected_z = eg.var(2, 1);
        let expected_identity = eg.lam(expected_z);
        let expected = eg.lam(expected_identity);
        assert!(eg.equivalent(&redex, &expected));
    }
    #[test]
    fn beta_discards_an_omega_argument_and_terminates() {
        let mut eg = EGraph::new();
        let a = eg.atom("a", 1);
        let constant_function = eg.lam(a);
        let omega_var = eg.var(1, 0);
        let omega_body = eg.app("app", vec![omega_var, omega_var]);
        let delta = eg.lam(omega_body);
        let omega = eg.app("app", vec![delta, delta]);
        let redex = eg.app("app", vec![constant_function, omega]);

        eg.saturate_beta();
        assert_eq!(eg.extract(&redex), Some(Term::Atom("a".into())));
    }
    #[test]
    fn beta_handles_the_alpha_shared_self_recursive_class() {
        let mut eg = EGraph::new();
        // λx. (λy. y) x reduces to λx. x. With alpha sharing, the class can
        // also contain a representation that refers back to itself.
        let inner_y = eg.var(2, 1);
        let inner_identity = eg.lam(inner_y);
        let outer_x = eg.var(1, 0);
        let body = eg.app("app", vec![inner_identity, outer_x]);
        let term = eg.lam(body);

        eg.saturate_beta();
        assert_eq!(eg.extract(&term).unwrap().to_string(), "(lam $0)");
        let expected_x = eg.var(1, 0);
        let expected = eg.lam(expected_x);
        assert!(eg.equivalent(&term, &expected));
    }
    #[test]
    fn beta_reduces_multiple_steps_after_self_application() {
        let mut eg = EGraph::new();
        // (λx. x x) (λy. y) -> (λy. y) (λy. y) -> λy. y.
        let x = eg.var(1, 0);
        let xx = eg.app("app", vec![x, x]);
        let duplicator = eg.lam(xx);
        let y = eg.var(1, 0);
        let identity = eg.lam(y);
        let term = eg.app("app", vec![duplicator, identity]);

        eg.saturate_beta();
        assert_eq!(eg.extract(&term).unwrap().to_string(), "(lam $0)");
        assert!(eg.equivalent(&term, &identity));
    }
    #[test]
    fn egg_simple_tests() {
        let rules = egg_simple_rules();

        let mut eg = EGraph::new();
        let zero = eg.atom("0", 0);
        let forty_two = eg.atom("42", 0);
        let term = eg.app("*", vec![zero, forty_two]);
        eg.saturate(&rules);
        assert_eq!(eg.extract(&term), Some(Term::Atom("0".into())));

        let mut eg = EGraph::new();
        let zero = eg.atom("0", 0);
        let one = eg.atom("1", 0);
        let foo = eg.atom("foo", 0);
        let product = eg.app("*", vec![one, foo]);
        let term = eg.app("+", vec![zero, product]);
        eg.saturate(&rules);
        assert_eq!(eg.extract(&term), Some(Term::Atom("foo".into())));
    }
    #[test]
    fn egg_math_associate_adds() {
        let mut eg = EGraph::new();
        let atoms: Vec<_> = (1..=7).map(|n| eg.atom(&n.to_string(), 0)).collect();
        let mut input = atoms[6];
        for atom in atoms[..6].iter().rev() {
            input = eg.app("+", vec![*atom, input]);
        }
        let var = |name: &str| Pattern::Var(name.into(), vec![]);
        let plus = |left, right| Pattern::app("+", vec![left, right]);
        let rules = [
            (plus(var("?a"), var("?b")), plus(var("?b"), var("?a"))),
            (
                plus(var("?a"), plus(var("?b"), var("?c"))),
                plus(plus(var("?a"), var("?b")), var("?c")),
            ),
        ];

        eg.saturate(&rules);
        assert_eq!(eg.class_count(), 127);
        assert_eq!(eg.node_count(), 1939);
        let mut goal = atoms[0];
        for atom in atoms[1..].iter() {
            goal = eg.app("+", vec![*atom, goal]);
        }
        assert!(eg.equivalent(&input, &goal));
    }
    #[test]
    fn egg_lambda_under() {
        let mut eg = EGraph::new();
        let four = eg.atom("4", 1);
        let inner_y = eg.var(2, 1);
        let inner_identity = eg.lam(inner_y);
        let inner_redex = eg.app("app", vec![inner_identity, four]);
        let sum = eg.app("+", vec![four, inner_redex]);
        let term = eg.lam(sum);

        eg.saturate_beta();
        let fold_four_plus_four = [(
            Pattern::app("+", vec![Pattern::atom("4"), Pattern::atom("4")]),
            Pattern::atom("8"),
        )];
        eg.saturate(&fold_four_plus_four);
        assert_eq!(eg.extract(&term).unwrap().to_string(), "(lam 8)");
    }
    #[test]
    fn egg_lambda_compose_beta_core() {
        let mut eg = EGraph::new();
        let f = eg.var(3, 0);
        let g = eg.var(3, 1);
        let x = eg.var(3, 2);
        let gx = eg.app("app", vec![g, x]);
        let fgx = eg.app("app", vec![f, gx]);
        let compose_x = eg.lam(fgx);
        let compose_g = eg.lam(compose_x);
        let compose = eg.lam(compose_g);

        let y = eg.var(1, 0);
        let one = eg.atom("1", 1);
        let add_one_body = eg.app("+", vec![y, one]);
        let add_one = eg.lam(add_one_body);
        let partial = eg.app("app", vec![compose, add_one]);
        let twice = eg.app("app", vec![partial, add_one]);

        eg.saturate_beta();
        assert_eq!(
            eg.extract(&twice).unwrap().to_string(),
            "(lam (+ (+ $0 1) 1))"
        );
    }
    #[test]
    fn identical_binders_in_sibling_lambdas_match_one_metavariable() {
        let mut eg = EGraph::new();
        let left_bound = eg.var(1, 0);
        let right_bound = eg.var(1, 0);
        let left = eg.lam(left_bound);
        let right = eg.lam(right_bound);
        let term = eg.app("pair", vec![left, right]);
        let pattern = Pattern::app(
            "pair",
            vec![
                Pattern::Lam(Box::new(Pattern::Var("?body".into(), vec![0]))),
                Pattern::Lam(Box::new(Pattern::Var("?body".into(), vec![0]))),
            ],
        );

        assert_eq!(eg.ematch(&pattern, &term).len(), 1);
    }
    #[test]
    fn enumerate_alternative_enodes_in_one_class() {
        let mut eg = EGraph::new();
        let a = eg.atom("a", 0);
        let b = eg.atom("b", 0);
        let aa = eg.app("f", vec![a, a]);
        let bb = eg.app("f", vec![b, b]);
        eg.union(&aa, &bb);
        eg.rebuild();
        let repeated = Pattern::app(
            "f",
            vec![
                Pattern::Var("?v".into(), vec![]),
                Pattern::Var("?v".into(), vec![]),
            ],
        );
        let matches = eg.ematch(&repeated, &aa);
        assert_eq!(matches.len(), 2);
        assert!(matches.iter().any(|s| eg.equivalent(&s["?v"].body(), &a)));
        assert!(matches.iter().any(|s| eg.equivalent(&s["?v"].body(), &b)));
    }
    #[test]
    fn equating_two_placements_of_one_raw_id_uses_the_equalizer() {
        let mut eg = EGraph::new();
        let x = eg.var(2, 0);
        let y = eg.var(2, 1);
        let fx = eg.app("f", vec![x]);
        let fy = eg.app("f", vec![y]);

        assert_eq!(fx.raw(), fy.raw());
        assert!(eg.union(&fx, &fy));
        eg.rebuild();
        assert!(eg.equivalent(&fx, &fy));
        assert_eq!(eg.find(&fx).lift().bits(), "00");
    }
    #[test]
    fn rebuild_reports_a_count_neutral_canonical_change() {
        let mut eg = EGraph::new();
        let x = eg.var(1, 0);
        let zero = eg.atom("0", 1);
        let _fx = eg.app("f", vec![x]);
        eg.union(&x, &zero);
        let classes_before = eg.class_count();

        assert!(eg.rebuild());
        assert_eq!(eg.class_count(), classes_before);
    }
    #[test]
    fn concrete_coordinates_in_patterns_respect_binders() {
        let output = run_sexp_script(
            "(insert (lam x (f x))) (rewrite (lam x (f x)) (lam x x)) (run 4) (extract (lam x (f x)))",
        )
        .unwrap();
        assert_eq!(output.last().unwrap(), "(lam x0 x0)");
    }
    #[test]
    fn miller_metavariable_must_name_a_captured_binder() {
        let mut eg = EGraph::new();
        let bound = eg.var(1, 0);
        let term = eg.lam(bound);
        let bare = sexp_pattern(&parse_sexps("(lam x ?a)").unwrap()[0]).unwrap();
        let allowed = sexp_pattern(&parse_sexps("(lam x (?a x))").unwrap()[0]).unwrap();

        assert!(eg.ematch(&bare, &term).is_empty());
        let matches = eg.ematch(&allowed, &term);
        assert_eq!(matches.len(), 1);
        assert!(eg.equivalent(&matches[0]["?a"].body(), &bound));
    }
    #[test]
    fn sexp_frontend_uses_miller_binder_lists() {
        let output = run_sexp_script(
            r#"
                (insert (lam x x))
                (rewrite (lam x ?a) misses)
                (rewrite (lam x (?a x)) matches)
                (run 4)
                (extract (lam x x))
            "#,
        )
        .unwrap();
        assert_eq!(output.last().unwrap(), "matches");
    }
    #[test]
    fn miller_metavariable_implicitly_keeps_the_top_scope() {
        let mut eg = EGraph::new();
        let outer = eg.var(1, 0);
        let outer_under_binder = outer.in_context(2).unwrap();
        let term = eg.lam(outer_under_binder);
        let pattern = sexp_pattern(&parse_sexps("(lam x ?a)").unwrap()[0]).unwrap();

        let matches = eg.ematch(&pattern, &term);
        assert_eq!(matches.len(), 1);
        assert!(eg.equivalent(&matches[0]["?a"].body(), &outer));
    }
    #[test]
    fn miller_arguments_can_select_a_later_nested_binder() {
        let mut eg = EGraph::new();
        let inner = eg.var(2, 1);
        let inner_lambda = eg.lam(inner);
        let term = eg.lam(inner_lambda);
        let pattern = sexp_pattern(&parse_sexps("(lam x (lam y (?f y)))").unwrap()[0]).unwrap();

        let subst = eg.ematch(&pattern, &term).pop().unwrap();
        let rebuilt = eg.try_instantiate(&pattern, 0, &subst).unwrap();
        assert!(eg.equivalent(&rebuilt, &term));
    }
    #[test]
    fn miller_indices_count_outward_from_the_nearest_pattern_binder() {
        let mut eg = EGraph::new();
        let outer = eg.var(2, 0);
        let inner_lambda = eg.lam(outer);
        let term = eg.lam(inner_lambda);
        let pattern = sexp_pattern(&parse_sexps("(lam x (lam y (?f x)))").unwrap()[0]).unwrap();

        let subst = eg.ematch(&pattern, &term).pop().unwrap();
        let rebuilt = eg.try_instantiate(&pattern, 0, &subst).unwrap();
        assert!(eg.equivalent(&rebuilt, &term));
    }
    #[test]
    fn miller_arguments_must_be_distinct_bound_variables() {
        assert!(
            sexp_pattern(&parse_sexps("(lam x (?a x x))").unwrap()[0])
                .unwrap_err()
                .contains("repeats")
        );
        let mut eg = EGraph::new();
        let bound = eg.var(1, 0);
        let _term = eg.lam(bound);
        assert!(
            sexp_pattern(&parse_sexps("(lam x (?a y))").unwrap()[0])
                .unwrap_err()
                .contains("not a pattern binder")
        );
    }
    #[test]
    fn miller_rhs_application_can_permute_parameters() {
        let output = run_sexp_script(
            r#"
                (insert (lam x (lam y (pair x y))))
                (rewrite
                    (lam x (lam y (?a x y)))
                    (lam x (lam y (?a y x))))
                (run 4)
                (guard
                    (lam x (lam y (pair x y)))
                    (lam x (lam y (pair y x))))
            "#,
        )
        .unwrap();
        assert_eq!(output.last().unwrap(), "; guard passed");
    }
    #[test]
    fn miller_permutation_preserves_the_implicit_top_context() {
        let output = run_sexp_script(
            r#"
                (insert 1 (lam x (lam y (triple $0 x y))))
                (rewrite
                    (lam x (lam y (?a x y)))
                    (lam x (lam y (?a y x))))
                (run 4)
                (guard 1
                    (lam x (lam y (triple $0 x y)))
                    (lam x (lam y (triple $0 y x))))
            "#,
        )
        .unwrap();
        assert_eq!(output.last().unwrap(), "; guard passed");
    }
    #[test]
    fn miller_rhs_application_ignores_dropped_parameters() {
        let output = run_sexp_script(
            r#"
                (insert (lam x (lam y x)))
                (rewrite
                    (lam x (lam y (?a x y)))
                    (lam x (lam y (?a y x))))
                (run 4)
                (guard (lam x (lam y x)) (lam x (lam y y)))
            "#,
        )
        .unwrap();
        assert_eq!(output.last().unwrap(), "; guard passed");

        let mut eg = EGraph::new();
        let x = eg.var(2, 0);
        let inner = eg.lam(x);
        let term = eg.lam(inner);
        let pattern = sexp_pattern(&parse_sexps("(lam x (lam y (?a x y)))").unwrap()[0]).unwrap();
        let subst = eg.ematch(&pattern, &term).pop().unwrap();
        assert_eq!(subst["?a"].arity(), 2);
        assert_eq!(subst["?a"].kept().as_slice(), [0]);
        assert_eq!(subst["?a"].body().ctx(), 1);
    }
    #[test]
    fn twisted_nonlinear_miller_pattern_is_rejected_statically() {
        let error = run_sexp_script(
            r#"
                (insert (lam x (lam y (pair (f x y) (f y x)))))
                (match (lam x (lam y (pair (?a x y) (?a y x)))))
            "#,
        )
        .unwrap_err();
        assert!(error.contains("twisted nonlinear Miller metavariable '?a'"));

        let rewrite_error =
            run_sexp_script("(rewrite (lam x (lam y (pair (?a x y) (?a y x)))) ok)").unwrap_err();
        assert!(rewrite_error.contains("twisted nonlinear Miller metavariable '?a'"));
    }
    #[test]
    fn nonlinear_miller_occurrences_with_the_same_order_are_allowed() {
        let pattern = sexp_pattern(
            &parse_sexps("(lam x (lam y (lam z (pair (?a x y) (?a y z)))))").unwrap()[0],
        )
        .unwrap();
        pattern.validate_match_pattern().unwrap();
    }
    #[test]
    fn nonlinear_miller_occurrences_must_have_consistent_arity() {
        let pattern =
            sexp_pattern(&parse_sexps("(lam x (lam y (pair (?a x) (?a x y))))").unwrap()[0])
                .unwrap();
        assert!(
            pattern
                .validate_match_pattern()
                .unwrap_err()
                .contains("inconsistent arity")
        );
    }
    #[test]
    fn miller_permutation_memoizes_recursive_eclasses() {
        let mut eg = EGraph::new();
        let x = eg.var(2, 0);
        let y = eg.var(2, 1);
        let pair = eg.app("pair", vec![x, y]);
        let recursive = eg.app("f", vec![pair]);
        eg.union(&pair, &recursive);
        eg.rebuild();

        let inner = eg.lam(pair);
        let term = eg.lam(inner);
        let lhs = sexp_pattern(&parse_sexps("(lam x (lam y (?a x y)))").unwrap()[0]).unwrap();
        let rhs = sexp_pattern(&parse_sexps("(lam x (lam y (?a y x)))").unwrap()[0]).unwrap();
        assert!(eg.rewrite_once(&lhs, &rhs) > 0);

        let swapped = eg.app("pair", vec![y, x]);
        let inner = eg.lam(swapped);
        let expected = eg.lam(inner);
        assert!(eg.equivalent(&term, &expected));
    }
    #[test]
    fn sexp_subst_builtin_is_available_on_rewrite_right_hand_sides() {
        let output = run_sexp_script(
            r#"
                (insert 1 (app (lam x x) $0))
                (rewrite (app (lam x (?body x)) ?arg) (#subst (?body x) x ?arg))
                (run 6)
                (extract 1 (app (lam x x) $0))
            "#,
        )
        .unwrap();
        assert_eq!(output.last().unwrap(), "$0");
    }
    #[test]
    fn printed_quoted_atoms_round_trip() {
        let mut eg = EGraph::new();
        let id = add_sexp_term(&mut eg, &parse_sexps("\"a b\"").unwrap()[0], 0).unwrap();
        let printed = eg.extract(&id).unwrap().to_string();
        assert_eq!(printed, "\"a b\"");
        let reparsed = add_sexp_term(&mut eg, &parse_sexps(&printed).unwrap()[0], 0).unwrap();
        assert!(eg.equivalent(&id, &reparsed));
    }
    #[test]
    fn overly_deep_frontend_context_is_an_error() {
        assert!(
            run_sexp_script("(insert 8 a)")
                .unwrap_err()
                .contains("at most 7")
        );
    }
}
