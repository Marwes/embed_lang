#![allow(unused)]

use std::marker::PhantomData;

use crate::base::{
    ast::{
        self, walk_mut_alias, walk_mut_ast_type, walk_mut_expr, walk_mut_pattern, Alternative,
        Argument, Array, AstType, DisplayEnv, Do, Expr, ExprField, IdentEnv, Lambda, Literal,
        MutVisitor, Pattern, RootExpr, Sp, SpannedAlias, SpannedAstType, SpannedExpr, SpannedIdent,
        SpannedPattern, TypeBinding, TypedIdent, ValueBinding,
    },
    error::Errors,
    kind::Kind,
    metadata::{BaseMetadata, Comment, CommentType, Metadata},
    mk_ast_arena,
    pos::{self, BytePos, HasSpan, Span, Spanned},
    types::{Alias, AliasData, ArcType, Field, Generic, KindedIdent, Type, TypeCache, TypeContext},
};
use crate::parser::{
    infix::{Fixity, OpMeta, OpTable, Reparser},
    parse_partial_expr, Error, ParseErrors,
};

pub struct MockEnv<T>(PhantomData<T>);

impl<T> MockEnv<T> {
    pub fn new() -> MockEnv<T> {
        MockEnv(PhantomData)
    }
}

impl<T: AsRef<str>> DisplayEnv for MockEnv<T> {
    type Ident = T;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
        ident.as_ref()
    }
}

impl<T> IdentEnv for MockEnv<T>
where
    T: AsRef<str> + for<'a> From<&'a str>,
{
    fn from_str(&mut self, s: &str) -> Self::Ident {
        T::from(s)
    }
}

/// MutVisitor that clears spans.
pub struct ModifySpan<F>(F);

impl<'a, F> MutVisitor<'a, '_> for ModifySpan<F>
where
    F: FnMut(Span<BytePos>) -> Span<BytePos>,
{
    type Ident = String;

    fn visit_expr(&mut self, e: &mut SpannedExpr<Self::Ident>) {
        e.span = (self.0)(e.span);
        walk_mut_expr(self, e);
    }

    fn visit_pattern(&mut self, p: &mut SpannedPattern<Self::Ident>) {
        p.span = (self.0)(p.span);
        walk_mut_pattern(self, &mut p.value);
    }

    fn visit_spanned_typed_ident(&mut self, id: &mut SpannedIdent<Self::Ident>) {
        id.span = (self.0)(id.span);
        self.visit_ident(&mut id.value)
    }

    fn visit_alias(&mut self, alias: &mut SpannedAlias<Self::Ident>) {
        alias.span = (self.0)(alias.span);
        walk_mut_alias(self, alias);
    }

    fn visit_spanned_ident(&mut self, s: &mut Spanned<Self::Ident, BytePos>) {
        s.span = (self.0)(s.span);
    }

    fn visit_ast_type(&mut self, s: &mut AstType<Self::Ident>) {
        *s.span_mut() = (self.0)(s.span());
        walk_mut_ast_type(self, s);
    }
}

pub fn parse_string<'env, 'input>(
    symbols: &'env mut dyn IdentEnv<Ident = String>,
    input: &'input str,
) -> Result<RootExpr<String>, (Option<RootExpr<String>>, ParseErrors)> {
    mk_ast_arena!(arena);
    match parse_partial_expr(arena.borrow(), symbols, &TypeCache::default(), input) {
        Ok(expr) => {
            let expr = arena.alloc(expr);
            Ok(RootExpr::new(arena.clone(), expr))
        }
        Err((expr, err)) => Err((
            expr.map(|expr| {
                let expr = arena.alloc(expr);
                RootExpr::new(arena.clone(), expr)
            }),
            err,
        )),
    }
}

pub fn parse(input: &str) -> Result<RootExpr<String>, (Option<RootExpr<String>>, ParseErrors)> {
    let mut symbols = MockEnv::new();

    let mut expr = parse_string(&mut symbols, input)?;
    let op_table = OpTable::new(
        vec![
            ("*", OpMeta::new(7, Fixity::Left)),
            ("/", OpMeta::new(7, Fixity::Left)),
            ("%", OpMeta::new(7, Fixity::Left)),
            ("+", OpMeta::new(6, Fixity::Left)),
            ("-", OpMeta::new(6, Fixity::Left)),
            (":", OpMeta::new(5, Fixity::Right)),
            ("++", OpMeta::new(5, Fixity::Right)),
            ("&&", OpMeta::new(3, Fixity::Right)),
            ("||", OpMeta::new(2, Fixity::Right)),
            ("$", OpMeta::new(0, Fixity::Right)),
            ("==", OpMeta::new(4, Fixity::Left)),
            ("/=", OpMeta::new(4, Fixity::Left)),
            ("<", OpMeta::new(4, Fixity::Left)),
            (">", OpMeta::new(4, Fixity::Left)),
            ("<=", OpMeta::new(4, Fixity::Left)),
            (">=", OpMeta::new(4, Fixity::Left)),
            // Hack for some library operators
            ("<<", OpMeta::new(9, Fixity::Right)),
            (">>", OpMeta::new(9, Fixity::Left)),
            ("<|", OpMeta::new(0, Fixity::Right)),
            ("|>", OpMeta::new(0, Fixity::Left)),
        ]
        .into_iter()
        .map(|(s, op)| (s.to_string(), op)),
    );

    expr.with_arena(|arena, expr| {
        let mut reparser = Reparser::new(arena.borrow(), op_table, &mut symbols);
        reparser.reparse(expr)
    })
    .map_err(|err| {
        (
            None,
            err.into_iter()
                .map(|err| err.map(Error::from))
                .collect::<ParseErrors>(),
        )
    })?;
    Ok(expr)
}

/// Clears spans of the expression.
pub fn clear_span(mut expr: RootExpr<String>) -> RootExpr<String> {
    ModifySpan(|_| Span::default()).visit_expr(expr.expr_mut());
    expr
}

/// Start all positions from 0
pub fn zero_index(mut expr: RootExpr<String>) -> RootExpr<String> {
    ModifySpan(|span: Span<BytePos>| -> Span<BytePos> {
        Span::new(
            (span.start().to_usize() as u32 - 1).into(),
            (span.end().to_usize() as u32 - 1).into(),
        )
    })
    .visit_expr(expr.expr_mut());
    expr
}

macro_rules! parse_new {
    ($input:expr) => {{
        // Replace windows line endings so that byte positions match up on multiline expressions
        let input = $input.replace("\r\n", "\n");
        parse(&input).unwrap_or_else(|(_, err)| {
            let mut source = base::source::CodeMap::new();
            source.add_filemap("test".into(), input.clone());
            panic!("{}", crate::base::error::InFile::new(source, err))
        })
    }};
}

macro_rules! parse_zero_index {
    ($input:expr) => {{
        zero_index(parse_new!($input))
    }};
}

macro_rules! parse_clear_span {
    ($input:expr) => {{
        clear_span(parse_new!($input))
    }};
}

pub fn intern(s: &str) -> String {
    String::from(s)
}

pub type SpExpr<'ast> = SpannedExpr<'ast, String>;

pub fn no_loc<T>(value: T) -> Spanned<T, BytePos> {
    pos::spanned(Span::default(), value)
}

pub fn binop<'ast>(
    arena: ast::ArenaRef<'_, 'ast, String>,
    l: SpExpr<'ast>,
    s: &str,
    r: SpExpr<'ast>,
) -> SpExpr<'ast> {
    no_loc(Expr::Infix {
        lhs: arena.alloc(l),
        op: no_loc(TypedIdent::new(intern(s))),
        rhs: arena.alloc(r),
        implicit_args: Default::default(),
    })
}

pub fn int<'a>(i: i64) -> SpExpr<'a> {
    no_loc(Expr::Literal(Literal::Int(i)))
}

pub fn string<'a>(s: &str) -> SpExpr<'a> {
    no_loc(Expr::Literal(Literal::String(s.into())))
}

pub fn let_<'ast>(
    arena: ast::ArenaRef<'_, 'ast, String>,
    s: &str,
    e: SpExpr<'ast>,
    b: SpExpr<'ast>,
) -> SpExpr<'ast> {
    let_a(arena, s, &[], e, b)
}

pub fn let_a<'ast>(
    arena: ast::ArenaRef<'_, 'ast, String>,
    s: &str,
    args: &[&str],
    e: SpExpr<'ast>,
    b: SpExpr<'ast>,
) -> SpExpr<'ast> {
    no_loc(Expr::let_binding(
        arena,
        ValueBinding {
            metadata: BaseMetadata::default(),
            name: no_loc(Pattern::Ident(TypedIdent::new(intern(s)))),
            typ: None,
            resolved_type: Type::hole(),
            args: arena.alloc_extend(
                args.iter()
                    .map(|i| Argument::explicit(no_loc(TypedIdent::new(intern(i))))),
            ),
            expr: e,
        },
        b,
    ))
}

pub fn do_<'ast>(
    arena: ast::ArenaRef<'_, 'ast, String>,
    s: &str,
    e: SpExpr<'ast>,
    b: SpExpr<'ast>,
) -> SpExpr<'ast> {
    do_2(
        arena,
        Some(no_loc(Pattern::Ident(TypedIdent::new(intern(s))))),
        e,
        b,
    )
}

pub fn do_2<'ast>(
    arena: ast::ArenaRef<'_, 'ast, String>,
    id: Option<SpannedPattern<'ast, String>>,
    e: SpExpr<'ast>,
    b: SpExpr<'ast>,
) -> SpExpr<'ast> {
    no_loc(Expr::Do(arena.alloc(Do {
        id,
        typ: None,
        bound: arena.alloc(e),
        body: arena.alloc(b),
        flat_map_id: None,
    })))
}

pub fn id(s: &str) -> SpExpr<'_> {
    no_loc(Expr::Ident(TypedIdent::new(intern(s))))
}

pub fn typ<'ast>(mut arena: ast::ArenaRef<'_, 'ast, String>, s: &str) -> AstType<'ast, String> {
    assert!(s.len() != 0);
    match s.parse() {
        Ok(b) => arena.builtin(b),
        Err(()) if s.starts_with(char::is_lowercase) => generic_ty(arena, s),
        Err(()) => arena.ident(KindedIdent::new(intern(s))),
    }
}

pub fn generic_ty<'ast>(
    mut arena: ast::ArenaRef<'_, 'ast, String>,
    s: &str,
) -> AstType<'ast, String> {
    arena.generic(generic(s))
}

pub fn generic(s: &str) -> Generic<String> {
    Generic::new(intern(s), Kind::hole())
}

pub fn app<'ast>(
    arena: ast::ArenaRef<'_, 'ast, String>,
    e: SpExpr<'ast>,
    args: Vec<SpExpr<'ast>>,
) -> SpExpr<'ast> {
    no_loc(Expr::App {
        func: arena.alloc(e),
        implicit_args: Default::default(),
        args: arena.alloc_extend(args),
    })
}

pub fn if_else<'ast>(
    arena: ast::ArenaRef<'_, 'ast, String>,
    p: SpExpr<'ast>,
    if_true: SpExpr<'ast>,
    if_false: SpExpr<'ast>,
) -> SpExpr<'ast> {
    no_loc(Expr::IfElse(
        arena.alloc(p),
        arena.alloc(if_true),
        arena.alloc(if_false),
    ))
}

pub fn case<'ast>(
    arena: ast::ArenaRef<'_, 'ast, String>,
    e: SpExpr<'ast>,
    alts: Vec<(Pattern<'ast, String>, SpExpr<'ast>)>,
) -> SpExpr<'ast> {
    no_loc(Expr::Match(
        arena.alloc(e),
        arena.alloc_extend(alts.into_iter().map(|(p, e)| Alternative {
            pattern: no_loc(p),
            expr: e,
        })),
    ))
}

pub fn lambda<'ast>(
    arena: ast::ArenaRef<'_, 'ast, String>,
    name: &str,
    args: Vec<String>,
    body: SpExpr<'ast>,
) -> SpExpr<'ast> {
    no_loc(Expr::Lambda(Lambda {
        id: TypedIdent::new(intern(name)),
        args: arena.alloc_extend(
            args.into_iter()
                .map(|id| Argument::explicit(no_loc(TypedIdent::new(id)))),
        ),
        body: arena.alloc(body),
    }))
}

pub fn type_decl<'ast>(
    arena: ast::ArenaRef<'_, 'ast, String>,
    name: String,
    args: Vec<Generic<String>>,
    typ: AstType<'ast, String>,
    body: SpExpr<'ast>,
) -> SpExpr<'ast> {
    type_decls(
        arena,
        vec![TypeBinding {
            metadata: BaseMetadata::default(),
            name: no_loc(name.clone()),
            alias: no_loc(AliasData::new(name, arena.alloc_extend(args), typ)),
            finalized_alias: None,
        }],
        body,
    )
}

pub fn type_decls<'ast>(
    arena: ast::ArenaRef<'_, 'ast, String>,
    binds: Vec<TypeBinding<'ast, String>>,
    body: SpExpr<'ast>,
) -> SpExpr<'ast> {
    no_loc(Expr::TypeBindings(
        arena.alloc_extend(binds),
        arena.alloc(body),
    ))
}

pub fn record<'ast>(
    arena: ast::ArenaRef<'_, 'ast, String>,
    fields: Vec<(String, Option<SpExpr<'ast>>)>,
) -> SpExpr<'ast> {
    record_a(arena, Vec::new(), fields)
}

pub fn record_a<'ast>(
    arena: ast::ArenaRef<'_, 'ast, String>,
    types: Vec<(String, Option<ArcType<String>>)>,
    fields: Vec<(String, Option<SpExpr<'ast>>)>,
) -> SpExpr<'ast> {
    no_loc(Expr::Record {
        typ: Type::hole(),
        types: arena.alloc_extend(types.into_iter().map(|(name, value)| ExprField {
            metadata: BaseMetadata::default(),
            name: no_loc(name),
            value: value,
        })),
        exprs: arena.alloc_extend(fields.into_iter().map(|(name, value)| ExprField {
            metadata: BaseMetadata::default(),
            name: no_loc(name),
            value: value,
        })),
        base: None,
    })
}

pub fn field_access<'ast>(
    arena: ast::ArenaRef<'_, 'ast, String>,
    expr: SpExpr<'ast>,
    field: &str,
) -> SpExpr<'ast> {
    no_loc(Expr::Projection(
        arena.alloc(expr),
        intern(field),
        Type::hole(),
    ))
}

pub fn array<'ast>(
    arena: ast::ArenaRef<'_, 'ast, String>,
    fields: Vec<SpExpr<'ast>>,
) -> SpExpr<'ast> {
    no_loc(Expr::Array(Array {
        typ: Type::hole(),
        exprs: arena.alloc_extend(fields),
    }))
}

pub fn error<'ast>() -> SpExpr<'ast> {
    no_loc(Expr::Error(None))
}

pub fn alias<'ast, Id>(
    arena: ast::ArenaRef<'_, 'ast, Id>,
    name: Id,
    args: Vec<Generic<Id>>,
    typ: AstType<'ast, Id>,
) -> Spanned<AliasData<Id, AstType<'ast, Id>>, BytePos> {
    no_loc(AliasData::new(name, arena.alloc_extend(args), typ))
}

pub fn line_comment(s: &str) -> Metadata {
    Metadata {
        comment: Some(Comment {
            typ: CommentType::Line,
            content: s.into(),
        }),
        ..Metadata::default()
    }
}

pub fn variant<'ast, Id>(
    mut arena: ast::ArenaRef<'_, 'ast, Id>,
    enum_type: &str,
    arg: &str,
    types: impl IntoIterator<
        Item = AstType<'ast, Id>,
        IntoIter = impl DoubleEndedIterator<Item = AstType<'ast, Id>>,
    >,
) -> Field<Sp<Id>, AstType<'ast, Id>>
where
    Id: Clone + AsRef<str> + for<'a> From<&'a str>,
{
    Field::ctor_with(
        &mut arena,
        TypedIdent {
            name: enum_type.into(),
            typ: Kind::typ(),
        },
        pos::spanned(Default::default(), arg.into()),
        types,
    )
}

pub fn alias_variant<'s, 'ast, Id>(
    mut arena: ast::ArenaRef<'_, 'ast, Id>,
    s: &str,
    params: &[&str],
    args: impl IntoIterator<
        Item = (
            &'s str,
            impl IntoIterator<
                Item = AstType<'ast, Id>,
                IntoIter = impl DoubleEndedIterator<Item = AstType<'ast, Id>>,
            >,
        ),
    >,
) -> AstType<'ast, Id>
where
    Id: Clone + AsRef<str> + for<'a> From<&'a str>,
{
    let variants = arena.clone().variant(
        arena.alloc_extend(
            args.into_iter()
                .map(|(arg, types)| variant(arena, s, arg, types))
                .collect::<Vec<_>>(),
        ),
    );
    Alias::new_with(
        &mut arena.clone(),
        s.into(),
        arena.alloc_extend(
            params
                .iter()
                .cloned()
                .map(|g| Generic::new(g.into(), Kind::hole())),
        ),
        variants,
    )
    .into_type()
}

// The expected tokens aren't very interesting since they may change fairly often
pub fn remove_expected(errors: ParseErrors) -> ParseErrors {
    let f = |mut err: Spanned<Error, _>| {
        match err.value {
            Error::UnexpectedToken(_, ref mut expected)
            | Error::UnexpectedEof(ref mut expected) => expected.clear(),
            _ => (),
        }
        err.span = Span::default();
        err
    };
    ParseErrors::from(errors.into_iter().map(f).collect::<Vec<_>>())
}

#[macro_export]
macro_rules! test_parse {
    ($test_name: ident, $text: expr, $expected: expr $(,)?) => {
        #[test]
        fn $test_name() {
            let _ = ::env_logger::try_init();
            let text = $text;
            let e = parse_clear_span!(text);
            mk_ast_arena!(arena);
            let _: &Arena<String> = &*arena;
            fn call<A, R>(a: A, f: impl FnOnce(A) -> R) -> R {
                f(a)
            }
            assert_eq!(*e.expr(), call(arena.borrow(), $expected));
        }
    };
}

#[macro_export]
macro_rules! test_parse_error {
    ($test_name: ident, $text: expr, $expected: expr, $expected_error: expr $(,)?) => {
        #[test]
        fn $test_name() {
            let _ = ::env_logger::try_init();
            let text = $text;
            let result = parse(text);
            assert!(
                result.is_err(),
                "Expected error but got expression: {:#?}",
                result.unwrap()
            );
            let (expr, err) = result.unwrap_err();
            let expr = clear_span(expr.expect("Recovered expression"));
            mk_ast_arena!(arena);
            fn call<A, R>(a: A, f: impl FnOnce(A) -> R) -> R {
                f(a)
            }
            assert_eq!(*expr.expr(), call(arena.borrow(), $expected));

            assert_eq!(remove_expected(err), ParseErrors::from($expected_error));
        }
    };
}
