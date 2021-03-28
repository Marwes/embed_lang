#![allow(unused_macros)]
#![allow(dead_code)]

extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_parser as parser;

use self::{
    base::{
        ast::{DisplayEnv, Expr, IdentEnv, KindedIdent, RootExpr, SpannedExpr, TypedIdent},
        error::{Errors, InFile},
        kind::{ArcKind, Kind, KindEnv},
        metadata::{Metadata, MetadataEnv},
        pos::{BytePos, Spanned},
        source,
        symbol::{Name, Symbol, SymbolData, SymbolModule, SymbolRef, Symbols},
        types::{self, Alias, ArcType, Field, Generic, PrimitiveEnv, Type, TypeCache, TypeEnv},
    },
    check::{
        metadata, rename,
        typecheck::{self, Typecheck},
    },
    parser::{parse_partial_root_expr, reparse_infix, ParseErrors},
};

use {collect_mac::collect, quick_error::quick_error};

pub use self::base::types::TypeExt;

use std::{cell::RefCell, fmt, iter::FromIterator, marker::PhantomData, rc::Rc, sync::Arc};

quick_error! {
    /// Representation of all possible errors that can occur when interacting with the `vm` crate
    #[derive(Debug, PartialEq)]
    pub enum Error {
        Check(err: InFile<typecheck::HelpError<Symbol>>) {
            display("{}", err)
            from()
        }
        Parser(err: InFile<parser::Error>) {
            display("{}", err)
            from()
        }
    }
}

impl Error {
    pub fn unwrap_check(self) -> InFile<typecheck::HelpError<Symbol>> {
        match self {
            Error::Parser(ref err) => panic!("{}", err),
            Error::Check(err) => err,
        }
    }
}
/// Returns a reference to the interner stored in TLD
pub fn get_local_interner() -> Rc<RefCell<Symbols>> {
    thread_local!(static INTERNER: Rc<RefCell<Symbols>>
    = Rc::new(RefCell::new(Symbols::new())));

    INTERNER.with(|interner| interner.clone())
}

#[allow(dead_code)]
pub fn intern_unscoped(s: &str) -> Symbol {
    let i = get_local_interner();
    let mut i = i.borrow_mut();

    i.simple_symbol(s)
}

pub fn intern(s: &str) -> Symbol {
    let interner = get_local_interner();
    let mut interner = interner.borrow_mut();

    if s.starts_with(char::is_lowercase) {
        interner.symbol(SymbolData::<&Name>::from(s))
    } else {
        SymbolModule::new("test".into(), &mut interner).scoped_symbol(s)
    }
}

pub fn parse_new(s: &str) -> Result<RootExpr<Symbol>, (Option<RootExpr<Symbol>>, ParseErrors)> {
    let symbols = get_local_interner();
    let mut symbols = symbols.borrow_mut();
    let mut module = SymbolModule::new("test".into(), &mut symbols);
    parse_partial_root_expr(&mut module, &TypeCache::new(), s)
}

#[allow(dead_code)]
pub fn typecheck(text: &str) -> Result<ArcType, Error> {
    let (_, t) = typecheck_expr(text);
    t
}

pub struct MockEnv {
    bool: Alias<Symbol, ArcType>,
}

impl MockEnv {
    pub fn new() -> MockEnv {
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();

        MockEnv {
            bool: {
                let bool_sym = interner.simple_symbol("Bool");
                let bool_ty = Type::app(
                    Type::ident(KindedIdent {
                        name: bool_sym.clone(),
                        typ: Kind::typ(),
                    }),
                    collect![],
                );
                Alias::new(bool_sym, Vec::new(), bool_ty)
            },
        }
    }
}

impl KindEnv for MockEnv {
    fn find_kind(&self, id: &SymbolRef) -> Option<ArcKind> {
        match id.definition_name() {
            "Bool" => Some(Kind::typ()),
            _ => None,
        }
    }
}

impl TypeEnv for MockEnv {
    type Type = ArcType;
    fn find_type(&self, id: &SymbolRef) -> Option<ArcType> {
        match id.definition_name() {
            "False" | "True" => Some(self.bool.as_type().clone()),
            _ => None,
        }
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<Alias<Symbol, ArcType>> {
        match id.definition_name() {
            "Bool" => Some(self.bool.clone()),
            _ => None,
        }
    }
}

impl PrimitiveEnv for MockEnv {
    fn get_bool(&self) -> ArcType {
        self.bool.as_type().clone()
    }
}

impl MetadataEnv for MockEnv {
    fn get_metadata(&self, _id: &SymbolRef) -> Option<Arc<Metadata>> {
        None
    }
}

#[allow(dead_code)]
pub struct MockIdentEnv<T>(PhantomData<T>);

#[allow(dead_code)]
impl<T> MockIdentEnv<T> {
    pub fn new() -> MockIdentEnv<T> {
        MockIdentEnv(PhantomData)
    }
}

impl<T: AsRef<str>> DisplayEnv for MockIdentEnv<T> {
    type Ident = T;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
        ident.as_ref()
    }
}

impl<T> IdentEnv for MockIdentEnv<T>
where
    T: AsRef<str> + for<'a> From<&'a str>,
{
    fn from_str(&mut self, s: &str) -> Self::Ident {
        T::from(s)
    }
}

pub(crate) fn in_file_error<E>(text: &str, errors: Errors<Spanned<E, BytePos>>) -> InFile<E>
where
    E: fmt::Display,
{
    let mut source = source::CodeMap::new();
    source.add_filemap("test".into(), text.into());
    InFile::new(source, errors)
}

pub fn typecheck_expr_expected(
    text: &str,
    expected: Option<&ArcType>,
) -> (RootExpr<Symbol>, Result<ArcType, Error>) {
    let mut expr = match parse_new(text) {
        Ok(expr) => expr,
        Err((expr, err)) => {
            let err = in_file_error(text, err);
            return (expr.unwrap_or_else(|| panic!("{}", err)), Err(err.into()));
        }
    };

    let env = MockEnv::new();
    let interner = get_local_interner();
    let mut interner = interner.borrow_mut();

    let source = source::FileMap::new("test".into(), text.to_string());
    let result = {
        let (arena, expr) = expr.arena_expr();
        let arena = arena.borrow();

        rename::rename(
            &source,
            &mut SymbolModule::new("test".into(), &mut interner),
            arena,
            expr,
        );
        let (_, mut metadata) = metadata::metadata(&env, &expr);
        reparse_infix(arena, &metadata, &*interner, expr).unwrap_or_else(|err| panic!("{}", err));

        let mut tc = Typecheck::new(
            "test".into(),
            &mut interner,
            &env,
            &TypeCache::new(),
            &mut metadata,
            arena,
        );

        tc.typecheck_expr_expected(expr, expected)
    };

    (expr, result.map_err(|err| in_file_error(text, err).into()))
}

pub fn typecheck_expr(text: &str) -> (RootExpr<Symbol>, Result<ArcType, Error>) {
    typecheck_expr_expected(text, None)
}

#[allow(dead_code)]
pub fn typecheck_partial_expr(
    text: &str,
) -> (
    RootExpr<Symbol>,
    Result<ArcType, InFile<typecheck::HelpError<Symbol>>>,
) {
    let mut expr = match parse_new(text) {
        Ok(e) => e,
        Err((Some(e), _)) => e,
        Err((None, err)) => panic!("{}", err),
    };

    let env = MockEnv::new();
    let interner = get_local_interner();
    let mut interner = interner.borrow_mut();

    let source = source::FileMap::new("test".into(), text.to_string());

    let result = {
        let (arena, expr) = expr.arena_expr();
        let arena = arena.borrow();

        rename::rename(
            &source,
            &mut SymbolModule::new("test".into(), &mut interner),
            arena,
            expr,
        );

        let (_, mut metadata) = metadata::metadata(&env, &expr);

        reparse_infix(arena, &metadata, &*interner, expr).unwrap_or_else(|err| panic!("{}", err));

        let mut tc = Typecheck::new(
            "test".into(),
            &mut interner,
            &env,
            &TypeCache::new(),
            &mut metadata,
            arena,
        );
        tc.typecheck_expr(expr)
    };

    (expr, result.map_err(|err| in_file_error(text, err)))
}

#[allow(dead_code)]
pub fn typ(s: &str) -> ArcType {
    assert!(s.len() != 0);
    typ_a(s, Kind::typ(), Vec::new())
}

pub fn typ_a<T>(s: &str, kind: ArcKind, args: Vec<T>) -> T
where
    T: TypeExt<Id = Symbol, SpannedId = Symbol> + From<Type<Symbol, T>>,
    T::Types: FromIterator<T> + Extend<T>,
{
    assert!(s.len() != 0);

    match s.parse() {
        Ok(b) => Type::builtin(b),
        Err(()) if s.starts_with(char::is_lowercase) => {
            Type::generic(Generic::new(intern(s), Kind::typ()))
        }
        Err(()) => {
            if args.len() == 0 {
                Type::ident(KindedIdent {
                    name: intern(s),
                    typ: kind,
                })
            } else {
                Type::app(
                    Type::ident(KindedIdent {
                        name: intern(s),
                        typ: kind,
                    }),
                    args.into_iter().collect(),
                )
            }
        }
    }
}

#[allow(dead_code)]
pub fn alias(s: &str, args: &[&str], typ: ArcType) -> ArcType {
    alias_implicit(s, args, typ, false)
}

pub fn alias_implicit(s: &str, args: &[&str], typ: ArcType, is_implicit: bool) -> ArcType {
    assert!(s.len() != 0);
    Type::alias_implicit(
        intern(s),
        args.iter()
            .map(|id| Generic::new(intern(id), Kind::typ()))
            .collect(),
        typ,
        is_implicit,
    )
}

pub fn variant(enum_type: &str, arg: &str, types: &[ArcType]) -> Field<Symbol, ArcType> {
    let arg = intern_unscoped(arg);
    Field::ctor(
        TypedIdent {
            name: intern_unscoped(enum_type),
            typ: Kind::typ(),
        },
        arg,
        types.iter().cloned(),
    )
}

pub fn alias_variant(s: &str, params: &[&str], args: &[(&str, &[ArcType])]) -> ArcType {
    alias_variant_implicit(s, params, args, false)
}

pub fn alias_variant_implicit(
    s: &str,
    params: &[&str],
    args: &[(&str, &[ArcType])],
    is_implicit: bool,
) -> ArcType {
    let variants = Type::variant(
        args.iter()
            .map(|(arg, types)| variant(s, arg, types))
            .collect(),
    );
    alias_implicit(s, params, variants, is_implicit)
}

/// Replace the variable at the `rest` part of a record for easier equality checks
#[allow(dead_code)]
pub fn close_record(typ: ArcType) -> ArcType {
    types::walk_move_type(typ, &mut |typ: &ArcType| match **typ {
        Type::ExtendRow {
            ref fields,
            ref rest,
        } => match **rest {
            Type::ExtendRow { .. } => None,
            _ => Some(Type::extend_row(fields.clone(), Type::empty_row())),
        },
        _ => None,
    })
}

#[macro_export]
macro_rules! assert_failed {
    ($lhs:expr, $rhs:expr, $lhs_value:expr, $rhs_value:expr) => {
        panic!(
            r#"Assertion failed: `({} == {})`
        left: `{}`,
        right: `{}`"#,
            stringify!($lhs),
            stringify!($rhs),
            $lhs_value,
            $rhs_value
        )
    };
}

#[macro_export]
macro_rules! assert_req {
    ($lhs:expr, $rhs:expr) => {
        match ($lhs, $rhs) {
            (Ok(lhs), Ok(rhs)) => {
                if lhs != rhs {
                    assert_failed!($lhs, $rhs, lhs, rhs)
                }
            }
            (Err(lhs), Err(rhs)) => {
                if lhs != rhs {
                    assert_failed!($lhs, $rhs, lhs, rhs)
                }
            }
            (Ok(lhs), Err(rhs)) => assert_failed!($lhs, $rhs, lhs, rhs),
            (Err(lhs), Ok(rhs)) => assert_failed!($lhs, $rhs, lhs, rhs),
        }
    };
}

#[macro_export]
macro_rules! assert_eq2 {
    ($lhs:expr, $rhs:expr) => {{
        let ref lhs = $lhs;
        let ref rhs = $rhs;
        if lhs != rhs {
            assert_failed!($lhs, $rhs, lhs, rhs)
        }
    }};
}

macro_rules! test_check {
    ($name:ident, $source:expr, $typ:expr) => {
        #[test]
        fn $name() {
            let _ = env_logger::try_init();
            let text = $source;
            let result = support::typecheck(text);
            assert_req!(result.map(|x| x.to_string()), Ok($typ.to_string()));
        }
    };
}

macro_rules! test_check_err {
    ($name:ident, $source:expr, $($id: pat),+ $(,)? $(=> $ty: expr)?) => {
        #[test]
        fn $name() {
            let _ = env_logger::try_init();
            let text = $source;
            let (expr, result) = support::typecheck_expr(text);
            assert_err!([$source] result, $($id),+);
            $(
                use crate::base::ast::Typed;
                assert_eq!(expr.expr().env_type_of(&crate::base::ast::EmptyEnv::default()).to_string(), $ty);
            )?
            let _ = expr;
        }
    };
}

macro_rules! assert_err {
    ($e: expr, $($id: pat),+) => {
        assert_err!([""] $e, $($id),+)
    };
    ([$text: expr] $e: expr, $($id: pat),+) => {{
        #[allow(unused_imports)]
        use crate::check::{
            typecheck::TypeError::*,
            unify::Error::{TypeMismatch, Substitution, Other},
            substitution::Error::Occurs,
            unify_type::TypeError::FieldMismatch
        };

        match $e {
            Ok(x) => assert!(false, "Expected error, got {}", x),
            Err(err) => {
                let errors = match err {
                    $crate::support::Error::Parser(ref err) => panic!("{}", err),
                    $crate::support::Error::Check(err) => err.into_errors(),
                };
                let mut iter = (&errors).into_iter();
                $(
                match iter.next() {
                    Some(&crate::base::pos::Spanned { value: crate::base::error::Help { error: $id, .. }, .. }) => (),
                    _ => {
                        if $text.is_empty() {
                            assert!(
                                false,
                                "Found errors:\n{}\nbut expected {}",
                                errors,
                                stringify!($id)
                            )
                        } else {
                            assert!(
                                false,
                                "Found errors:\n{}\nbut expected {}",
                                crate::support::in_file_error($text, errors),
                                stringify!($id)
                            )
                        }
                    }
                }
                )+
                assert!(iter.count() == 0, "Found more errors than expected\n{}", errors);
            }
        }
    }}
}

macro_rules! count {
    ($e: pat) => {
        1
    };
    ($e: pat, $($id: pat),+) => {
        1 + count!($($id),+)
    }
}

macro_rules! assert_unify_err {
    ($e: expr, $($id: pat),+) => {
        assert_multi_unify_err!($e, [$($id),+])
    }
}

macro_rules! assert_multi_unify_err {
    ($e: expr, $( [ $( $id: pat ),+ ] ),+) => {{
        #[allow(unused_imports)]
        use crate::check::{
            typecheck::TypeError::*,
            unify::Error::{TypeMismatch, Substitution, Other},
            substitution::Error::Occurs,
            unify_type::TypeError::{FieldMismatch, UnableToGeneralize, SelfRecursiveAlias, MissingFields}
        };

        match $e {
            Ok(x) => assert!(false, "Expected error, got {}", x),
            Err(err) => {
                let errors = match err {
                    $crate::support::Error::Parser(ref err) => panic!("{}", err),
                    $crate::support::Error::Check(err) => err.into_errors(),
                };
                let mut errors_iter = (&errors).into_iter().enumerate();
                $(
                match errors_iter.next() {
                    Some((i, error)) => {
                        match error.value.error {
                            Unification(_, _, ref errors) => {
                                let mut iter = errors.iter();
                                let expected_count = count!($($id),+);
                                $(
                                match iter.next() {
                                    Some(&$id) => (),
                                    Some(error2) => {
                                        assert!(false,
                                            "Found errors at {}:\n{}\nExpected:\n{}\nFound:\n{:?}",
                                            i,
                                            error,
                                            stringify!($id),
                                            error2
                                        );
                                    }
                                    None => {
                                        assert!(false,
                                            "Found {} errors but expected {} than expected at {}.\n\
                                            Errors:\n{}\nbut expected {}",
                                            errors.len(),
                                            expected_count,
                                            i,
                                            error,
                                            stringify!($id)
                                        );
                                    }
                                }
                                )+
                                let count = iter.count();
                                assert!(count == 0,
                                        "Found {} more errors than expected at {}\n{}",
                                        count,
                                        i,
                                        error);
                            }
                            _ => assert!(false,
                                        "Found errors at {}:\n\
                                        {}\nbut expected an unification error",
                                        i,
                                        error)
                        }
                    }
                    None => ()
                }
                )+
                assert!(errors_iter.count() == 0,
                        "Found more unification errors than expected\n{}",
                        errors);
            }
        }
    }}
}

pub fn print_ident_types(expr: &SpannedExpr<Symbol>) {
    struct Visitor;
    impl<'a> base::ast::Visitor<'_, 'a> for Visitor {
        type Ident = Symbol;

        fn visit_expr(&mut self, expr: &SpannedExpr<'a, Symbol>) {
            match expr.value {
                Expr::Ident(ref id) => {
                    println!("{} : {}", id.name, id.typ);
                }
                _ => base::ast::walk_expr(self, expr),
            }
        }
    }
    base::ast::Visitor::visit_expr(&mut Visitor, &expr)
}
