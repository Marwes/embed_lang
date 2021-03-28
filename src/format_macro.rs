//! Implementation of the `format!` macro
use gluon_codegen::Trace;

use crate::{
    base::{
        ast::{self, AstClone, SpannedExpr},
        pos,
        symbol::{Symbol, Symbols},
        types::TypeCache,
    },
    parser::parse_expr,
    vm::macros::{self, Error, Macro, MacroExpander, MacroFuture, MacroResult},
};

/**
 * Format macro with expressions embedded in the format string.
 *
 * ```ignore
 * let x = 1
 * let foo = "foo"
 * format! "x is {x}, x + 1 is {x+1}, foo is {foo} and {foo:?}"
 * ```
 *
 *   ==> x is 1, x + 1 is 2, foo is foo and "foo"
 */
#[derive(Trace)]
#[gluon(crate_name = "vm")]
pub struct Format;

fn expr_from_path<'ast>(
    arena: &mut ast::OwnedArena<'ast, Symbol>,
    symbols: &mut Symbols,
    span: pos::Span<pos::ByteIndex>,
    path_head: &str,
    path_tail: &[&str],
) -> SpannedExpr<'ast, Symbol> {
    let mut head = pos::spanned(
        span,
        ast::Expr::Ident(ast::TypedIdent::new(symbols.simple_symbol(path_head))),
    );

    for &item in path_tail {
        head = pos::spanned(
            span,
            ast::Expr::Projection(
                arena.alloc(head),
                symbols.simple_symbol(item),
                Default::default(),
            ),
        );
    }

    head
}

async fn run_import<'a, 'ast>(
    importer: &dyn Macro,
    env: &mut MacroExpander<'a>,
    symbols: &mut Symbols,
    arena: &mut ast::OwnedArena<'ast, Symbol>,
    span: pos::Span<pos::ByteIndex>,
    path: &[&str],
) -> MacroResult<'ast> {
    let (path_head, path_tail) = match path {
        [head, tail @ ..] => (head, tail),
        _ => return Err(Error::message("run_import for empty path")),
    };

    let path = expr_from_path(arena, symbols, span, path_head, path_tail);
    let args = arena.alloc_extend(vec![path]);

    match importer.expand(env, symbols, arena, args).await? {
        macros::LazyMacroResult::Done(res) => Ok(res),
        macros::LazyMacroResult::Lazy(f) => f().await,
    }
}

impl Macro for Format {
    fn expand<'r, 'a: 'r, 'b: 'r, 'c: 'r, 'ast: 'r>(
        &self,
        env: &'b mut MacroExpander<'a>,
        symbols: &'c mut Symbols,
        arena: &'b mut ast::OwnedArena<'ast, Symbol>,
        args: &'b mut [SpannedExpr<'ast, Symbol>],
    ) -> MacroFuture<'r, 'ast> {
        Box::pin(async move {
            let arg = match args {
                [arg] => (arg),
                _ => return Err(Error::message(format!("format! expects 1 argument"))),
            };

            let span = arg.span;
            let sp = |e: ast::Expr<'ast, Symbol>| pos::spanned(span, e);

            let import = env
                .vm
                .get_macros()
                .get("import")
                .ok_or_else(|| Error::message(format!("format! cannot find import macro")))?;

            let show_module =
                run_import(&*import, env, symbols, arena, span, &["std", "show"]).await?;
            let show_module = arena.alloc(show_module);
            let show_func = arena.alloc(sp(ast::Expr::Projection(
                show_module,
                symbols.simple_symbol("show"),
                Default::default(),
            )));

            let display_module =
                run_import(&*import, env, symbols, arena, span, &["std", "display"]).await?;
            let display_module = arena.alloc(display_module);
            let display_func = sp(ast::Expr::Projection(
                display_module,
                symbols.simple_symbol("display"),
                Default::default(),
            ));

            let semigroup_module =
                run_import(&*import, env, symbols, arena, span, &["std", "semigroup"]).await?;
            let semigroup_module = arena.alloc(semigroup_module);
            let append_func = sp(ast::Expr::Projection(
                semigroup_module,
                symbols.simple_symbol("append"),
                Default::default(),
            ));

            let format_string = match &arg.value {
                ast::Expr::Literal(ast::Literal::String(text)) => text,
                _ => return Err(Error::message(format!("format! expects a string argument"))),
            };

            let app1 = |func: &ast::SpannedExpr<'ast, Symbol>, e: ast::SpannedExpr<'ast, Symbol>| {
                let func = arena.alloc(func.ast_clone(arena.borrow()));

                sp(ast::Expr::App {
                    func,
                    implicit_args: arena.alloc_extend(vec![]),
                    args: arena.alloc_extend(vec![e]),
                })
            };

            let app_exprs = |lhs, rhs| {
                let func = arena.alloc(append_func.ast_clone(arena.borrow()));

                sp(ast::Expr::App {
                    func,
                    implicit_args: arena.alloc_extend(vec![]),
                    args: arena.alloc_extend(vec![lhs, rhs]),
                })
            };

            let literal_expr = |val: String| sp(ast::Expr::Literal(ast::Literal::String(val)));

            let type_cache = TypeCache::new();

            let mut remaining = format_string.as_str();

            let mut result_expr = None;

            while let Some(find_result) = find_expr(remaining)? {
                remaining = find_result.remaining;

                let sub_expr = {
                    let value = parse_expr(
                        arena.borrow(),
                        symbols,
                        &type_cache,
                        find_result.expr.expr,
                    )
                    .map_err(|err| {
                        Error::message(format!("format! could not parse subexpression: {}", err))
                    })?
                    .value;

                    pos::spanned(
                        span.subspan(
                            pos::ByteOffset(find_result.expr_start as i64),
                            pos::ByteOffset(find_result.expr_end as i64),
                        ),
                        value,
                    )
                };

                let formatted_sub_expr = match find_result.expr.modifier {
                    FormatModifier::Display => app1(&display_func, sub_expr),
                    FormatModifier::Debug => app1(&show_func, sub_expr),
                };

                let part_expr = app_exprs(
                    literal_expr(find_result.prefix.to_owned()),
                    formatted_sub_expr,
                );

                result_expr = match result_expr.take() {
                    None => Some(part_expr),
                    Some(prev_expr) => Some(app_exprs(prev_expr, part_expr)),
                };
            }

            let result_expr = match result_expr.take() {
                None => literal_expr(remaining.to_owned()),
                Some(result_expr) => {
                    if remaining.is_empty() {
                        result_expr
                    } else {
                        app_exprs(result_expr, literal_expr(remaining.to_owned()))
                    }
                }
            };

            Ok(result_expr.into())
        })
    }
}

const OPEN_BRACE: &'static str = "{";
const CLOSE_BRACE: &'static str = "}";

enum FormatModifier {
    Display,
    Debug,
}

struct FormatExpr<'a> {
    expr: &'a str,
    modifier: FormatModifier,
}

struct FindExprResult<'a> {
    prefix: &'a str,
    expr: FormatExpr<'a>,
    remaining: &'a str,
    expr_start: usize,
    expr_end: usize,
}

fn parse_format_expr<'a>(contents: &'a str) -> Result<FormatExpr<'a>, Error> {
    let mut split_iter = contents.split(":");

    match (split_iter.next(), split_iter.next(), split_iter.next()) {
        (Some(expr), Some(fmt), None) => {
            if fmt == "?" {
                Ok(FormatExpr {
                    expr,
                    modifier: FormatModifier::Debug,
                })
            } else {
                Err(Error::message(format!(
                    "Unrecognized format specifier: {}",
                    fmt
                )))
            }
        }
        (Some(expr), None, None) => Ok(FormatExpr {
            expr,
            modifier: FormatModifier::Display,
        }),
        _ => Err(Error::message(format!(
            "At most one colon allowed in format subexpression",
        ))),
    }
}

fn find_expr<'a>(format_str: &'a str) -> Result<Option<FindExprResult<'a>>, Error> {
    let open_ix = match format_str.find(OPEN_BRACE) {
        None => return Ok(None),
        Some(ix) => ix,
    };

    let close_ix = match format_str.find(CLOSE_BRACE) {
        Some(ix) if ix < open_ix => {
            return Err(Error::message(format!(
                "Mismatched braces in format! string"
            )))
        }
        None => 
            return Err(Error::message(format!(
                "Mismatched braces in format! string"
            ))),
        Some(ix) => ix,
    };

    let prefix = &format_str[..open_ix];
    let expr_start = OPEN_BRACE.len() + open_ix;
    let expr_end = close_ix;
    let brace_end = close_ix + CLOSE_BRACE.len();

    let expr = parse_format_expr(&format_str[expr_start..expr_end])?;

    let remaining = &format_str[brace_end..];

    Ok(Some(FindExprResult {
        prefix,
        expr,
        remaining,
        expr_start,
        expr_end,
    }))
}
