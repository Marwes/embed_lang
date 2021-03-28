//! Implementation of the `lens!` macro.

use gluon_codegen::Trace;

use crate::{
    base::{
        ast::{self, AstClone, SpannedExpr},
        pos,
        symbol::{Symbol, Symbols},
        types,
    },
    vm::macros::{self, Macro, MacroExpander, MacroFuture},
};

/// Macro for deriving field accessor lenses
///
/// ```ignore
/// let lens = import! std.lens
///
/// type MyRecord = {
///     x: Int,
///     y: String
/// }
///
/// let _x = lens! lens MyRecord x
/// let _y = lens! lens MyRecord y
/// ```
#[derive(Trace)]
#[gluon(crate_name = "vm")]
pub struct DeriveLens;

impl Macro for DeriveLens {
    fn expand<'r, 'a: 'r, 'b: 'r, 'c: 'r, 'ast: 'r>(
        &self,
        _env: &'b mut MacroExpander<'a>,
        _symbols: &'c mut Symbols,
        arena: &'b mut ast::OwnedArena<'ast, Symbol>,
        args: &'b mut [SpannedExpr<'ast, Symbol>],
    ) -> MacroFuture<'r, 'ast> {
        Box::pin(async move {
            let (module_arg, typ_arg, field_arg) = match args {
                [module, typ, field] => (module, typ, field),
                _ => return Err(macros::Error::message(format!("lens! expects 3 arguments"))),
            };

            let mut symbols = Symbols::new();

            let typ = match &typ_arg.value {
                ast::Expr::Ident(id) => id.clone(),
                _ => {
                    return Err(macros::Error::message(format!(
                        "lens! expects an identifier as the second argument"
                    )))
                }
            };

            let field_ident = match &field_arg.value {
                ast::Expr::Ident(id) => id.clone(),
                _ => {
                    return Err(macros::Error::message(format!(
                        "lens! expects an identifier as the third argument"
                    )))
                }
            };

            let struct_var = ast::TypedIdent::new(symbols.simple_symbol("s"));
            let get_var = ast::TypedIdent::new(symbols.simple_symbol("get"));
            let set_var = ast::TypedIdent::new(symbols.simple_symbol("set"));

            let span = field_arg.span;

            let struct_ast_type = || {
                ast::AstType::new_no_loc(
                    arena.borrow(),
                    types::Type::Ident(ast::TypedIdent {
                        name: typ.name.clone(),
                        typ: Default::default(),
                    }),
                )
            };

            let hole_type = || ast::AstType::new_no_loc(arena.borrow(), types::Type::Hole);

            let func_type = |a, b| {
                ast::AstType::new_no_loc(
                    arena.borrow(),
                    types::Type::Function(types::ArgType::Explicit, a, b),
                )
            };

            let get_binding = arena.alloc(ast::ValueBinding {
                metadata: Default::default(),
                name: pos::spanned(span, ast::Pattern::Ident(get_var.clone())),
                typ: Some(func_type(struct_ast_type(), hole_type())),
                resolved_type: Default::default(),
                args: arena.alloc_extend(vec![ast::Argument {
                    arg_type: types::ArgType::Explicit,
                    name: pos::spanned(span, struct_var.clone()),
                }]),
                expr: pos::spanned(
                    span,
                    ast::Expr::Projection(
                        arena.alloc(pos::spanned(span, ast::Expr::Ident(struct_var.clone()))),
                        field_ident.name.clone(),
                        field_ident.typ.clone(),
                    ),
                ),
            });

            let set_binding = arena.alloc(ast::ValueBinding {
                metadata: Default::default(),
                name: pos::spanned(span, ast::Pattern::Ident(set_var.clone())),
                typ: Some(func_type(
                    hole_type(),
                    func_type(struct_ast_type(), struct_ast_type()),
                )),
                resolved_type: Default::default(),
                args: arena.alloc_extend(vec![
                    ast::Argument {
                        arg_type: types::ArgType::Explicit,
                        name: pos::spanned(span, field_ident.clone()),
                    },
                    ast::Argument {
                        arg_type: types::ArgType::Explicit,
                        name: pos::spanned(span, struct_var.clone()),
                    },
                ]),
                expr: pos::spanned(
                    span,
                    ast::Expr::Record {
                        typ: Default::default(),
                        types: &mut [],
                        exprs: arena.alloc_extend(vec![ast::ExprField {
                            metadata: Default::default(),
                            name: pos::spanned(span, field_ident.name.clone()),
                            value: None,
                        }]),
                        base: Some(
                            arena.alloc(pos::spanned(span, ast::Expr::Ident(struct_var.clone()))),
                        ),
                    },
                ),
            });

            let lens_module = arena.alloc((*module_arg).ast_clone(arena.borrow()));

            let make_func = arena.alloc(pos::spanned(
                span,
                ast::Expr::Projection(
                    lens_module,
                    symbols.simple_symbol("make"),
                    Default::default(),
                ),
            ));

            let make_expr = arena.alloc(pos::spanned(
                span,
                ast::Expr::App {
                    func: make_func,
                    implicit_args: &mut [],
                    args: arena.alloc_extend(vec![
                        pos::spanned(span, ast::Expr::Ident(get_var)),
                        pos::spanned(span, ast::Expr::Ident(set_var)),
                    ]),
                },
            ));

            let result = pos::spanned(
                span,
                ast::Expr::LetBindings(
                    ast::ValueBindings::Plain(set_binding),
                    arena.alloc(pos::spanned(
                        span,
                        ast::Expr::LetBindings(ast::ValueBindings::Plain(get_binding), make_expr),
                    )),
                ),
            );

            Ok(result.into())
        })
    }
}
