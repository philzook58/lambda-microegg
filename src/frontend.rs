use lambda_microegg::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Delimiter {
    Paren,
    Bracket,
    Brace,
}

impl Delimiter {
    fn open(self) -> char {
        match self {
            Self::Paren => '(',
            Self::Bracket => '[',
            Self::Brace => '{',
        }
    }
    fn close(self) -> char {
        match self {
            Self::Paren => ')',
            Self::Bracket => ']',
            Self::Brace => '}',
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum SyntaxKind {
    Atom {
        text: String,
        quoted: bool,
    },
    Group {
        delimiter: Delimiter,
        items: Vec<Syntax>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Syntax {
    kind: SyntaxKind,
    location: Location,
}

impl Syntax {
    fn locate(&self, error: String) -> String {
        if error.starts_with("line ") {
            error
        } else {
            self.location.error(error)
        }
    }
    fn group(&self, delimiter: Delimiter) -> Option<&[Syntax]> {
        match &self.kind {
            SyntaxKind::Group {
                delimiter: found,
                items,
            } if *found == delimiter => Some(items),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Token {
    Left(Delimiter, Location),
    Right(Delimiter, Location),
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

fn lex(input: &str) -> Result<Vec<Token>, String> {
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
            '(' | '[' | '{' => {
                chars.next();
                let delimiter = match ch {
                    '(' => Delimiter::Paren,
                    '[' => Delimiter::Bracket,
                    '{' => Delimiter::Brace,
                    _ => unreachable!(),
                };
                tokens.push(Token::Left(delimiter, Location { line, column }));
                column += 1;
            }
            ')' | ']' | '}' => {
                chars.next();
                let delimiter = match ch {
                    ')' => Delimiter::Paren,
                    ']' => Delimiter::Bracket,
                    '}' => Delimiter::Brace,
                    _ => unreachable!(),
                };
                tokens.push(Token::Right(delimiter, Location { line, column }));
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
                    if c.is_whitespace() || matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | ';') {
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

fn parse_syntax(input: &str) -> Result<Vec<Syntax>, String> {
    fn one(tokens: &[Token], cursor: &mut usize) -> Result<Syntax, String> {
        match tokens.get(*cursor) {
            Some(Token::Atom(atom, quoted, location)) => {
                let location = *location;
                *cursor += 1;
                Ok(Syntax {
                    kind: SyntaxKind::Atom {
                        text: atom.clone(),
                        quoted: *quoted,
                    },
                    location,
                })
            }
            Some(Token::Left(delimiter, location)) => {
                let delimiter = *delimiter;
                let location = *location;
                *cursor += 1;
                let mut items = vec![];
                loop {
                    match tokens.get(*cursor) {
                        Some(Token::Right(found, _)) if *found == delimiter => break,
                        Some(Token::Right(found, found_location)) => {
                            return Err(found_location.error(format_args!(
                                "expected '{}', found '{}'",
                                delimiter.close(),
                                found.close()
                            )));
                        }
                        None => {
                            return Err(
                                location.error(format_args!("unclosed '{}'", delimiter.open()))
                            );
                        }
                        _ => items.push(one(tokens, cursor)?),
                    }
                }
                *cursor += 1;
                Ok(Syntax {
                    kind: SyntaxKind::Group { delimiter, items },
                    location,
                })
            }
            Some(Token::Right(close, location)) => {
                Err(location.error(format_args!("unexpected '{}'", close.close())))
            }
            None => Err(Location { line: 1, column: 1 }.error("unexpected end of input")),
        }
    }

    let tokens = lex(input)?;
    let mut cursor = 0;
    let mut forms = vec![];
    while cursor < tokens.len() {
        forms.push(one(&tokens, &mut cursor)?);
    }
    Ok(forms)
}

#[cfg(test)]
#[allow(dead_code)] // Used by the integration-test crate, not the binary's test harness.
pub fn parse_forms(input: &str) -> Result<Vec<Syntax>, String> {
    parse_syntax(input)
}

fn atom_of(syntax: &Syntax) -> Result<&str, String> {
    match &syntax.kind {
        SyntaxKind::Atom { text, .. } => Ok(text),
        SyntaxKind::Group { .. } => Err(syntax.location.error("expected an atom")),
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

fn binder_name(syntax: &Syntax) -> Result<&str, String> {
    let SyntaxKind::Atom {
        text: name,
        quoted: false,
    } = &syntax.kind
    else {
        return Err(syntax.location.error("binder must be an unquoted name"));
    };
    let has_namespace_index = name
        .rsplit_once('@')
        .is_some_and(|(_, suffix)| suffix.parse::<usize>().is_ok());
    if name.is_empty() || name.starts_with(['?', '$']) || has_namespace_index {
        return Err(syntax
            .location
            .error(format!("invalid binder name '{name}'")));
    }
    Ok(name)
}

fn subst_binder_name(syntax: &Syntax) -> Result<&str, String> {
    if let SyntaxKind::Atom {
        text: name,
        quoted: false,
    } = &syntax.kind
        && name
            .strip_prefix('$')
            .is_some_and(|index| index.parse::<usize>().is_ok())
    {
        return Ok(name);
    }
    binder_name(syntax)
}

pub fn add_syntax_term(eg: &mut EGraph, syntax: &Syntax, ctx: usize) -> Result<Id, String> {
    fn go(
        eg: &mut EGraph,
        syntax: &Syntax,
        outer_ctx: usize,
        binders: &mut Vec<String>,
    ) -> Result<Id, String> {
        let ctx = outer_ctx + binders.len();
        if ctx > 31 {
            return Err(syntax
                .location
                .error("thinnings support at most 31 context variables"));
        }
        let result = match &syntax.kind {
            SyntaxKind::Atom { text: atom, quoted } if *quoted => Ok(eg.atom(atom, ctx)),
            SyntaxKind::Atom {
                text: atom,
                quoted: false,
            } if let Some((_, slot)) = resolve_binder(atom, binders) => {
                Ok(eg.var(ctx, outer_ctx + slot))
            }
            SyntaxKind::Atom {
                text: atom,
                quoted: false,
            } if atom.starts_with('$') => match atom[1..].parse::<usize>() {
                Err(_) => Err(format!("invalid outer-context variable '{atom}'")),
                Ok(index) if index >= outer_ctx => Err(format!(
                    "{atom} is out of scope in outer context {outer_ctx}"
                )),
                Ok(index) => Ok(eg.var(ctx, index)),
            },
            SyntaxKind::Atom {
                text: atom,
                quoted: false,
            } if atom.starts_with('?') => Err(format!("pattern variable '{atom}' used in a term")),
            SyntaxKind::Atom { text: atom, .. } => Ok(eg.atom(atom, ctx)),
            SyntaxKind::Group {
                delimiter: Delimiter::Brace,
                ..
            } => Err("metavariable occurrence used in a term".into()),
            SyntaxKind::Group {
                delimiter: Delimiter::Bracket,
                items,
            } => bracket(eg, items, outer_ctx, binders),
            SyntaxKind::Group {
                delimiter: Delimiter::Paren,
                items,
            } => paren(eg, items, outer_ctx, binders),
        };
        result.map_err(|error| syntax.locate(error))
    }

    /// `[FUNCTION ARGUMENT ...]`. Errors are returned unlocated so that the
    /// caller attaches this group's own position rather than the command's.
    fn bracket(
        eg: &mut EGraph,
        items: &[Syntax],
        outer_ctx: usize,
        binders: &mut Vec<String>,
    ) -> Result<Id, String> {
        if items.len() < 2 {
            return Err("application '[FUNCTION ARGUMENT ...]' needs an argument".into());
        }
        let (function, arguments) = items.split_first().unwrap();
        let mut application = go(eg, function, outer_ctx, binders)?;
        for argument in arguments {
            let argument = go(eg, argument, outer_ctx, binders)?;
            application = eg.app(application, argument);
        }
        Ok(application)
    }

    /// `(OP ...)`, `(@OP NAME BODY)`, or `(#subst BODY NAME REPLACEMENT)`.
    fn paren(
        eg: &mut EGraph,
        items: &[Syntax],
        outer_ctx: usize,
        binders: &mut Vec<String>,
    ) -> Result<Id, String> {
        let ctx = outer_ctx + binders.len();
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
            return Ok(eg.binder(op, body?));
        }
        if op == "#subst" {
            if items.len() != 4 {
                return Err(
                    "(#subst BODY NAME REPLACEMENT) takes a body, binder, and replacement".into(),
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
        Ok(eg.apps(op, children))
    }

    if ctx > 31 {
        return Err("thinnings support at most 31 context variables".into());
    }
    go(eg, syntax, ctx, &mut vec![])
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum PatternMode {
    MatchLhs,
    Template,
}

fn parse_pattern(syntax: &Syntax, mode: PatternMode) -> Result<Pattern, String> {
    fn go(
        syntax: &Syntax,
        mode: PatternMode,
        binders: &mut Vec<String>,
    ) -> Result<Pattern, String> {
        let result = match &syntax.kind {
            SyntaxKind::Atom { text: atom, quoted } if *quoted => Ok(Pattern::atom(atom)),
            SyntaxKind::Atom {
                text: atom,
                quoted: false,
            } if atom.starts_with('?') && atom.len() > 1 => {
                Ok(Pattern::MetaVar(atom.as_str().into(), vec![]))
            }
            SyntaxKind::Atom {
                text: atom,
                quoted: false,
            } if let Some((index, _)) = resolve_binder(atom, binders) => {
                Ok(Pattern::BVar(index.into()))
            }
            SyntaxKind::Atom {
                text: atom,
                quoted: false,
            } if atom.starts_with('$') => {
                let index = atom[1..]
                    .parse::<usize>()
                    .map_err(|_| format!("invalid outer-context variable '{atom}'"))?;
                Ok(Pattern::FVar(index.into()))
            }
            SyntaxKind::Atom { text: atom, .. } => Ok(Pattern::atom(atom)),
            SyntaxKind::Group {
                delimiter: Delimiter::Brace,
                items,
            } => {
                let Some(name_syntax) = items.first() else {
                    return Err(syntax
                        .location
                        .error("metavariable occurrence must start with ?NAME"));
                };
                let name = atom_of(name_syntax)?;
                if !matches!(&name_syntax.kind, SyntaxKind::Atom { quoted: false, .. })
                    || !name.starts_with('?')
                    || name.len() == 1
                {
                    return Err(syntax
                        .location
                        .error("metavariable occurrence must start with ?NAME"));
                }
                if mode == PatternMode::MatchLhs {
                    let mut resolved = Vec::with_capacity(items.len() - 1);
                    for argument in &items[1..] {
                        let SyntaxKind::Atom {
                            text,
                            quoted: false,
                        } = &argument.kind
                        else {
                            return Err(argument.location.error(format!(
                                "match metavariable '{name}' may only be applied to bound variables"
                            )));
                        };
                        let Some((_, slot)) = resolve_binder(text, binders) else {
                            return Err(argument.location.error(format!(
                                "match metavariable '{name}' may only be applied to bound variables"
                            )));
                        };
                        if resolved.iter().any(|(previous, _)| *previous == slot) {
                            return Err(argument.location.error(format!(
                                "Miller metavariable '{name}' repeats a pattern binder"
                            )));
                        }
                        resolved.push((slot, text));
                    }
                    if !resolved.windows(2).all(|pair| pair[0].0 < pair[1].0) {
                        resolved.sort_unstable_by_key(|(slot, _)| *slot);
                        let correct = resolved
                            .iter()
                            .map(|(_, name)| name.as_str())
                            .collect::<Vec<_>>()
                            .join(" ");
                        return Err(syntax.location.error(format!(
                            "Miller metavariable '{name}' arguments are out of order; write {{{name} {correct}}} on the match left-hand side, then permute its arguments on the rewrite right-hand side if needed"
                        )));
                    }
                }
                let arguments = items[1..]
                    .iter()
                    .map(|argument| go(argument, mode, binders))
                    .collect::<Result<_, _>>()?;
                Ok(Pattern::MetaVar(name.into(), arguments))
            }
            SyntaxKind::Group {
                delimiter: Delimiter::Bracket,
                items,
            } => {
                if items.len() < 2 {
                    return Err(syntax
                        .location
                        .error("application '[FUNCTION ARGUMENT ...]' needs an argument"));
                }
                let mut terms = items.iter();
                let mut application = go(terms.next().unwrap(), mode, binders)?;
                for argument in terms {
                    application = Pattern::app(application, go(argument, mode, binders)?);
                }
                Ok(application)
            }
            SyntaxKind::Group {
                delimiter: Delimiter::Paren,
                items,
            } => {
                let Some(head) = items.first() else {
                    return Err(syntax.location.error("empty pattern list"));
                };
                let op = atom_of(head)?;
                if op.starts_with('?') {
                    return Err(head.location.error(format!(
                        "metavariable '{op}' is not allowed in application head position; use {{{op} ...}} for a Miller metavariable occurrence or [{op} ...] for a curried application pattern"
                    )));
                }
                if let Some(op) = op.strip_prefix('@') {
                    if op.is_empty() || items.len() != 3 {
                        return Err(syntax
                            .location
                            .error("(@OP NAME PATTERN) takes a binder name and body"));
                    }
                    let name = binder_name(&items[1])?.to_owned();
                    binders.push(name);
                    let body = go(&items[2], mode, binders);
                    binders.pop();
                    return Ok(Pattern::binder(op, body?));
                }
                if op == "#subst" {
                    if items.len() != 4 {
                        return Err(syntax.location.error(
                            "(#subst BODY NAME REPLACEMENT) takes a body, binder, and replacement",
                        ));
                    }
                    let name = subst_binder_name(&items[2])?.to_owned();
                    binders.push(name);
                    let body = go(&items[1], mode, binders);
                    binders.pop();
                    let replacement = go(&items[3], mode, binders)?;
                    return Ok(Pattern::Subst(Box::new(body?), Box::new(replacement)));
                }
                if items.len() < 2 {
                    return Err(syntax
                        .location
                        .error(format!("pattern '({op} ...)' needs an argument")));
                }
                let children = items[1..]
                    .iter()
                    .map(|item| go(item, mode, binders))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Pattern::apps(op, children))
            }
        };
        result.map_err(|error| syntax.locate(error))
    }
    go(syntax, mode, &mut vec![])
}

pub fn syntax_pattern(syntax: &Syntax) -> Result<Pattern, String> {
    parse_pattern(syntax, PatternMode::Template)
}

pub fn syntax_match_pattern(syntax: &Syntax) -> Result<Pattern, String> {
    let pattern = parse_pattern(syntax, PatternMode::MatchLhs)?;
    pattern
        .validate_match_pattern()
        .map_err(|error| syntax.locate(error))?;
    Ok(pattern)
}

/// Split `(COMMAND [CONTEXT] ARG..)` into its ambient context, which defaults
/// to 0 when omitted, and exactly `arity` remaining argument forms.
fn command_context<'a>(
    items: &'a [Syntax],
    command: &str,
    arity: usize,
) -> Result<(usize, &'a [Syntax]), String> {
    let arguments = &items[1..];
    if arguments.len() == arity {
        return Ok((0, arguments));
    }
    let [context, arguments @ ..] = arguments else {
        return Err(format!("wrong number of arguments to '{command}'"));
    };
    if arguments.len() != arity {
        return Err(format!("wrong number of arguments to '{command}'"));
    }
    let location = context.location;
    let context = atom_of(context)?
        .parse::<usize>()
        .map_err(|_| location.error(format!("{command} context must be a nonnegative integer")))?;
    if context > 31 {
        return Err(location.error("thinnings support at most 31 context variables"));
    }
    Ok((context, arguments))
}

fn command_term<'a>(items: &'a [Syntax], command: &str) -> Result<(usize, &'a Syntax), String> {
    let (context, [term]) = command_context(items, command, 1)? else {
        unreachable!("command_context returned the requested arity")
    };
    Ok((context, term))
}

fn command_terms<'a>(
    items: &'a [Syntax],
    command: &str,
) -> Result<(usize, &'a Syntax, &'a Syntax), String> {
    let (context, [left, right]) = command_context(items, command, 2)? else {
        unreachable!("command_context returned the requested arity")
    };
    Ok((context, left, right))
}

fn comment_lines(text: &str) -> String {
    text.split('\n')
        .map(|line| format!("; {line}"))
        .collect::<Vec<_>>()
        .join("\n")
}

fn in_context(context: usize, value: impl std::fmt::Display) -> String {
    if context == 0 {
        value.to_string()
    } else {
        format!("ctx{context} |-> {value}")
    }
}

fn run_command(
    form: &Syntax,
    command_index: usize,
    eg: &mut EGraph,
    rules: &mut Vec<Rewrite>,
    output: &mut Vec<String>,
) -> Result<(), String> {
    let Some(items) = form.group(Delimiter::Paren) else {
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
            let id = add_syntax_term(eg, term, ctx)?;
            output.push(format!("inserted {}", id.show()));
        }
        "union" if matches!(items.len(), 3 | 4) => {
            let (ctx, left, right) = command_terms(items, "union")?;
            let left = add_syntax_term(eg, left, ctx)?;
            let right = add_syntax_term(eg, right, ctx)?;
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
            let left = add_syntax_term(eg, left, ctx)?;
            let right = add_syntax_term(eg, right, ctx)?;
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
                syntax_match_pattern(&items[1])?,
                syntax_pattern(&items[2])?,
            )?);
            output.push(format!("rewrite {} added", rules.len()));
        }
        "birewrite" if items.len() == 3 => {
            // Both sides are used as a left-hand side, so both must be
            // observable match patterns. Requiring each to be a valid
            // template for the other additionally forces the two sides to
            // bind exactly the same metavariables at the same arities.
            let left = syntax_match_pattern(&items[1])?;
            let right = syntax_match_pattern(&items[2])?;
            let forward = Rewrite::new(left.clone(), right.clone())?;
            let backward = Rewrite::new(right, left)?;
            rules.push(forward);
            rules.push(backward);
            output.push(format!(
                "birewrite {} and {} added",
                rules.len() - 1,
                rules.len()
            ));
        }
        "match" if items.len() == 2 => {
            let pattern = syntax_match_pattern(&items[1])?;
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
                    let extra_context = binding
                        .ctx()
                        .checked_sub(context)
                        .ok_or_else(|| format!("binding {name} has an invalid context"))?;
                    let term = eg
                        .extract(&binding)
                        .ok_or_else(|| format!("binding {name} has no finite extractable term"))?;
                    rendered.push(format!(
                        "{name} = {}",
                        in_context(extra_context, term.display())
                    ));
                }
                output.push(format!(
                    "match {}: {}",
                    index + 1,
                    in_context(context, format_args!("{{{}}}", rendered.join(", ")))
                ));
            }
        }
        "run" if items.len() == 2 => {
            let limit = atom_of(&items[1])?.parse::<usize>().map_err(|_| {
                items[1]
                    .location
                    .error("run limit must be a nonnegative integer")
            })?;
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
            let id = add_syntax_term(eg, term, ctx)?;
            let term = eg
                .extract(&id)
                .ok_or_else(|| "class has no finite extractable term".to_string())?;
            output.push(term.display().to_string());
        }
        "reset" | "insert" | "union" | "guard" | "rewrite" | "birewrite" | "match" | "run"
        | "echo" | "fail" | "print-egraph" | "extract" => {
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

pub fn run_script(input: &str) -> Result<Vec<String>, String> {
    let mut eg = EGraph::new();
    let mut rules = vec![];
    let mut output = vec![];
    for (command_index, form) in parse_syntax(input)?.into_iter().enumerate() {
        run_command(&form, command_index, &mut eg, &mut rules, &mut output)
            .map_err(|error| form.locate(error))?;
    }
    Ok(output)
}
