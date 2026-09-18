use lambda_microegg::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Sexp {
    Atom(String),
    Quoted(String),
    List(Vec<Sexp>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Token {
    Left(Location),
    Right(Location),
    Atom(String, bool, Location),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Location {
    line: usize,
    column: usize,
}

impl Location {
    fn error(self, message: impl std::fmt::Display) -> String {
        format!("line {}:{}: {message}", self.line, self.column)
    }
}

fn lex_sexps(input: &str) -> Result<Vec<Token>, String> {
    let mut chars = input.chars().peekable();
    let mut tokens = vec![];
    let mut line = 1;
    let mut column = 1;
    while let Some(&ch) = chars.peek() {
        match ch {
            ch if ch.is_whitespace() => {
                chars.next();
                if ch == '\n' {
                    line += 1;
                    column = 1;
                } else {
                    column += 1;
                }
            }
            ';' => {
                for c in chars.by_ref() {
                    if c == '\n' {
                        line += 1;
                        column = 1;
                        break;
                    }
                    column += 1;
                }
            }
            '(' => {
                chars.next();
                tokens.push(Token::Left(Location { line, column }));
                column += 1;
            }
            ')' => {
                chars.next();
                tokens.push(Token::Right(Location { line, column }));
                column += 1;
            }
            '"' => {
                let start = Location { line, column };
                chars.next();
                column += 1;
                let mut atom = String::new();
                let mut closed = false;
                while let Some(c) = chars.next() {
                    match c {
                        '"' => {
                            column += 1;
                            closed = true;
                            break;
                        }
                        '\\' => {
                            let escape = Location { line, column };
                            column += 1;
                            match chars.next() {
                                Some('n') => {
                                    atom.push('\n');
                                    column += 1;
                                }
                                Some('t') => {
                                    atom.push('\t');
                                    column += 1;
                                }
                                Some(c @ ('"' | '\\')) => {
                                    atom.push(c);
                                    column += 1;
                                }
                                Some(c) => {
                                    return Err(
                                        escape.error(format_args!("unsupported escape \\{c}"))
                                    );
                                }
                                None => return Err(escape.error("unterminated escape")),
                            }
                        }
                        c => {
                            if c == '\n' {
                                line += 1;
                                column = 1;
                            } else {
                                column += 1;
                            }
                            atom.push(c);
                        }
                    }
                }
                if !closed {
                    return Err(start.error("unterminated quoted atom"));
                }
                tokens.push(Token::Atom(atom, true, start));
            }
            _ => {
                let start = Location { line, column };
                let mut atom = String::new();
                while let Some(&c) = chars.peek() {
                    if c.is_whitespace() || matches!(c, '(' | ')' | ';') {
                        break;
                    }
                    atom.push(c);
                    chars.next();
                    column += 1;
                }
                tokens.push(Token::Atom(atom, false, start));
            }
        }
    }
    Ok(tokens)
}

fn parse_sexps_with_locations(input: &str) -> Result<Vec<(Location, Sexp)>, String> {
    fn one(tokens: &[Token], cursor: &mut usize) -> Result<Sexp, String> {
        match tokens.get(*cursor) {
            Some(Token::Atom(atom, quoted, _)) => {
                *cursor += 1;
                Ok(if *quoted {
                    Sexp::Quoted(atom.clone())
                } else {
                    Sexp::Atom(atom.clone())
                })
            }
            Some(Token::Left(location)) => {
                let location = *location;
                *cursor += 1;
                let mut items = vec![];
                while !matches!(tokens.get(*cursor), Some(Token::Right(_))) {
                    if *cursor == tokens.len() {
                        return Err(location.error("unclosed '('"));
                    }
                    items.push(one(tokens, cursor)?);
                }
                *cursor += 1;
                Ok(Sexp::List(items))
            }
            Some(Token::Right(location)) => Err(location.error("unexpected ')'")),
            None => Err(Location { line: 1, column: 1 }.error("unexpected end of input")),
        }
    }

    let tokens = lex_sexps(input)?;
    let mut cursor = 0;
    let mut forms = vec![];
    while cursor < tokens.len() {
        let location = match &tokens[cursor] {
            Token::Left(location) | Token::Right(location) | Token::Atom(_, _, location) => {
                *location
            }
        };
        forms.push((location, one(&tokens, &mut cursor)?));
    }
    Ok(forms)
}

#[cfg(test)]
#[allow(dead_code)] // Used by the integration-test crate, not the binary's test harness.
pub fn parse_sexps(input: &str) -> Result<Vec<Sexp>, String> {
    parse_sexps_with_locations(input).map(|forms| forms.into_iter().map(|(_, form)| form).collect())
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

pub fn add_sexp_term(eg: &mut EGraph, sexp: &Sexp, ctx: usize) -> Result<Id, String> {
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

pub fn sexp_pattern(sexp: &Sexp) -> Result<Pattern, String> {
    fn go(sexp: &Sexp, binders: &mut Vec<String>) -> Result<Pattern, String> {
        match sexp {
            Sexp::Quoted(atom) => Ok(Pattern::atom(atom)),
            Sexp::Atom(atom) if atom.starts_with('?') && atom.len() > 1 => {
                Ok(Pattern::MetaVar(atom.as_str().into(), vec![]))
            }
            Sexp::Atom(atom) if resolve_binder(atom, binders).is_some() => {
                let (index, _) = resolve_binder(atom, binders).unwrap();
                Ok(Pattern::BVar(index.into()))
            }
            Sexp::Atom(atom) if atom.starts_with('$') => {
                let index = atom[1..]
                    .parse::<usize>()
                    .map_err(|_| format!("invalid outer-context variable '{atom}'"))?;
                Ok(Pattern::FVar(index.into()))
            }
            Sexp::Atom(atom) => Ok(Pattern::atom(atom)),
            Sexp::List(items) => {
                let Some(head) = items.first() else {
                    return Err("empty pattern list".into());
                };
                let op = atom_of(head)?;
                if matches!(head, Sexp::Atom(_)) && op.starts_with('?') && op.len() > 1 {
                    let arguments = items[1..]
                        .iter()
                        .map(|argument| go(argument, binders))
                        .collect::<Result<_, _>>()?;
                    return Ok(Pattern::MetaVar(op.into(), arguments));
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

pub fn sexp_match_pattern(sexp: &Sexp) -> Result<Pattern, String> {
    fn check_order(sexp: &Sexp, binders: &mut Vec<String>) -> Result<(), String> {
        let Sexp::List(items) = sexp else {
            return Ok(());
        };
        let Some(Sexp::Atom(head)) = items.first() else {
            return Ok(());
        };
        if head.starts_with('?') && head.len() > 1 {
            let resolved: Option<Vec<_>> = items[1..]
                .iter()
                .map(|argument| {
                    let Sexp::Atom(name) = argument else {
                        return None;
                    };
                    let (_, slot) = resolve_binder(name, binders)?;
                    Some((slot, name))
                })
                .collect();
            if let Some(mut arguments) = resolved
                && !arguments.iter().enumerate().any(|(i, (slot, _))| {
                    arguments[..i].iter().any(|(previous, _)| previous == slot)
                })
                && !arguments.windows(2).all(|pair| pair[0].0 < pair[1].0)
            {
                arguments.sort_unstable_by_key(|(slot, _)| *slot);
                let correct = arguments
                    .iter()
                    .map(|(_, name)| name.as_str())
                    .collect::<Vec<_>>()
                    .join(" ");
                return Err(format!(
                    "Miller metavariable '{head}' arguments are out of order; write ({head} {correct}) on the match left-hand side, then permute its arguments on the rewrite right-hand side if needed"
                ));
            }
            return Ok(());
        }
        if (head == "lam" || head.starts_with('@'))
            && items.len() == 3
            && let Ok(name) = binder_name(&items[1])
        {
            binders.push(name.to_owned());
            let result = check_order(&items[2], binders);
            binders.pop();
            return result;
        }
        for child in &items[1..] {
            check_order(child, binders)?;
        }
        Ok(())
    }

    check_order(sexp, &mut vec![])?;
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

fn run_command(
    form: &Sexp,
    command_index: usize,
    eg: &mut EGraph,
    rules: &mut Vec<Rewrite>,
    output: &mut Vec<String>,
) -> Result<(), String> {
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
            *eg = EGraph::new();
            rules.clear();
            output.push("reset".into());
        }
        "insert" if matches!(items.len(), 2 | 3) => {
            let (ctx, term) = command_term(items, "insert")?;
            let id = add_sexp_term(eg, term, ctx)?;
            output.push(format!("inserted {}", id.show()));
        }
        "union" if matches!(items.len(), 3 | 4) => {
            let (ctx, left, right) = command_terms(items, "union")?;
            let left = add_sexp_term(eg, left, ctx)?;
            let right = add_sexp_term(eg, right, ctx)?;
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
            let left = add_sexp_term(eg, left, ctx)?;
            let right = add_sexp_term(eg, right, ctx)?;
            eg.rebuild();
            if !eg.equivalent(&left, &right) {
                let left = eg.extract(&left).map_or_else(
                    || "<no finite term>".into(),
                    |term| term.display().to_string(),
                );
                let right = eg.extract(&right).map_or_else(
                    || "<no finite term>".into(),
                    |term| term.display().to_string(),
                );
                return Err(format!("guard failed: {left} != {right}"));
            }
            output.push("guard passed".into());
        }
        "rewrite" if items.len() == 3 => {
            rules.push(Rewrite::new(
                sexp_match_pattern(&items[1])?,
                sexp_pattern(&items[2])?,
            )?);
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
                    .map(|(name, binding)| (name.to_owned(), *binding))
                    .collect();
                let mut rendered = Vec::with_capacity(bindings.len());
                for (name, binding) in bindings {
                    let arity = binding
                        .ctx()
                        .checked_sub(context)
                        .ok_or_else(|| format!("binding {name} has an invalid context"))?;
                    let term = eg
                        .extract(&binding)
                        .ok_or_else(|| format!("binding {name} has no finite extractable term"))?;
                    let parameters: Vec<_> = (0..arity).map(|index| format!("x{index}")).collect();
                    let body = term.display_with_root_binders(&parameters).to_string();
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
            let stats = eg.run(rules, limit);
            output.push(format!(
                        "ran {} rounds, {} unions: {} classes, {} e-nodes\nmatch {:?}, apply {:?}, rebuild {:?}",
                        stats.rounds,
                        stats.unions,
                        eg.class_count(),
                        eg.node_count(),
                        stats.match_time,
                        stats.apply_time,
                        stats.rebuild_time,
                    ));
        }
        "echo" if items.len() == 2 => output.push(atom_of(&items[1])?.to_owned()),
        "fail" if items.len() == 2 => {
            // Expected failures are transactional: even a command that
            // mutates before rejecting its input leaves no trace.
            let mut trial_eg = eg.clone();
            let mut trial_rules = rules.clone();
            let mut trial_output = vec![];
            match run_command(
                &items[1],
                command_index,
                &mut trial_eg,
                &mut trial_rules,
                &mut trial_output,
            ) {
                Ok(()) => return Err("wrapped command succeeded".into()),
                Err(error) => output.push(format!("failed as expected: {error}")),
            }
        }
        "print-egraph" if items.len() == 1 => output.push(eg.dump()),
        "extract" if matches!(items.len(), 2 | 3) => {
            let (ctx, term) = command_term(items, "extract")?;
            let id = add_sexp_term(eg, term, ctx)?;
            let term = eg
                .extract(&id)
                .ok_or_else(|| "class has no finite extractable term".to_string())?;
            output.push(term.display().to_string());
        }
        "reset" | "insert" | "union" | "guard" | "rewrite" | "match" | "run" | "echo" | "fail"
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
    Ok(())
}

pub fn run_sexp_script(input: &str) -> Result<Vec<String>, String> {
    let mut eg = EGraph::new();
    let mut rules = vec![];
    let mut output = vec![];
    for (command_index, (location, form)) in
        parse_sexps_with_locations(input)?.into_iter().enumerate()
    {
        run_command(&form, command_index, &mut eg, &mut rules, &mut output)
            .map_err(|error| location.error(error))?;
    }
    Ok(output)
}
