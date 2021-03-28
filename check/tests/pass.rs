#[macro_use]
extern crate pretty_assertions;
#[macro_use]
extern crate collect_mac;

extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_parser as parser;

use crate::base::{
    ast::{self, KindedIdent, Typed},
    kind::Kind,
    types::{Alias, AliasData, ArcType, Field, Generic, Type, TypeExt},
};

use crate::support::*;

#[macro_use]
#[allow(unused_macros)]
mod support;

macro_rules! assert_pass {
    ($e:expr) => {{
        if !$e.is_ok() {
            panic!("assert_pass: {}", $e.unwrap_err());
        }
    }};
}

/// Converts `Type::Alias` into the easy to construct `Type::Ident` variants to make the expected
/// types easier to write
fn make_ident_type(typ: ArcType) -> ArcType {
    use crate::base::types::walk_move_type;
    walk_move_type(typ, &mut |typ: &ArcType| match **typ {
        Type::Alias(ref alias) => Some(Type::ident(KindedIdent {
            name: alias.name.clone(),
            typ: alias.kind(&Default::default()).into_owned(),
        })),
        _ => None,
    })
}

#[test]
fn function_type_new() {
    let text = r"
\x -> x #Int+ 1
";
    let result = support::typecheck(text);

    assert_req!(result, Ok(Type::function(vec![typ("Int")], typ("Int"))));
}

#[test]
fn char_literal() {
    let _ = env_logger::try_init();

    let text = r"
'a'
";
    let result = support::typecheck(text);
    let expected = Ok(Type::char());

    assert_eq!(result, expected);
}

#[test]
fn byte_literal() {
    let _ = env_logger::try_init();

    let text = r"
1b
";
    let result = support::typecheck(text);
    let expected = Ok(Type::byte());

    assert_eq!(result, expected);
}

#[test]
fn function_2_args() {
    let _ = env_logger::try_init();

    let text = r"
\x y -> 1 #Int+ x #Int+ y
";
    let result = support::typecheck(text);
    let expected = Ok(Type::function(vec![typ("Int"), typ("Int")], typ("Int")));

    assert_eq!(result, expected);
}

#[test]
fn type_decl() {
    let _ = env_logger::try_init();

    let text = r"
type Test = { x: Int }
let t : Test = { x = 0 }
t
";
    let result = support::typecheck(text);
    let expected = Ok(alias(
        "Test",
        &[],
        Type::record(vec![], vec![Field::new(intern("x"), typ("Int"))]),
    ));

    assert_eq!(result, expected);
}

#[test]
fn type_decl_multiple() {
    let _ = env_logger::try_init();

    let text = r"
rec
type Test = Int -> Int
type Test2 = | Test2 Test
in Test2 (\x -> x #Int+ 2)
";
    let result = support::typecheck(text);
    let test = AliasData::new(
        intern("Test"),
        vec![],
        Type::function(vec![typ("Int")], typ("Int")),
    );
    let test2 = AliasData::new(
        intern("Test2"),
        vec![],
        Type::variant(vec![support::variant("Test2", "Test2", &[typ("Test")])]),
    );
    let expected = Ok(Alias::group(vec![test, test2])[1].as_type().clone());

    assert_req!(result, expected);
}

#[test]
fn record_type_simple() {
    let _ = env_logger::try_init();

    let text = r"
type T = { y: Int } in
let f: T -> Int = \x -> x.y
let t: T = { y = f { y = 123 } }
t
";
    let result = support::typecheck(text);
    let expected = Ok(alias(
        "T",
        &[],
        Type::record(vec![], vec![Field::new(intern("y"), typ("Int"))]),
    ));

    assert_eq!(result, expected);
}

#[test]
fn let_binding_type() {
    let _ = env_logger::try_init();

    let env = MockEnv::new();
    let text = r"
let f: a -> b -> a = \x y -> x in f 1.0 ()
";
    let (expr, result) = support::typecheck_expr(text);
    let expected = Ok(typ("Float"));

    assert_req!(result, expected);
    match expr.expr().value {
        ast::Expr::LetBindings(ref bindings, _) => {
            assert_eq!(
                bindings[0].expr.env_type_of(&env).to_string(),
                "a -> b -> a"
            );
        }
        _ => assert!(false),
    }
}
#[test]
fn let_binding_recursive() {
    let _ = env_logger::try_init();

    let text = r"
let fac x = if x #Int== 0 then 1 else x #Int* fac (x #Int- 1) in fac
";
    let (_, result) = support::typecheck_expr(text);
    let expected = Ok(Type::function(vec![typ("Int")], typ("Int")));

    assert_eq!(result, expected);
}
#[test]
fn let_binding_mutually_recursive() {
    let _ = env_logger::try_init();

    let text = r"
rec
let f x = if x #Int< 0
      then x
      else g x
let g x = f (x #Int- 1)
in g 5
";
    let (_, result) = support::typecheck_expr(text);

    assert_req!(result.map(|t| t.to_string()), Ok("Int"));
}

macro_rules! assert_match {
    ($i:expr, $p:pat => $e:expr) => {
        match $i {
            $p => $e,
            ref x => assert!(false, "Expected {}, found {:?}", stringify!($p), x),
        }
    };
}

#[test]
fn let_binding_general_mutually_recursive() {
    let _ = env_logger::try_init();

    let text = r"
rec
let test x = (1 #Int+ 2) #Int+ test2 x
let test2 x = 2 #Int+ test x
in test2 1";
    let (expr, result) = support::typecheck_expr(text);
    let expected = Ok(typ("Int"));

    assert_req!(result, expected);
    assert_match!(expr.expr().value, ast::Expr::LetBindings(ref binds, _) => {
        assert_eq!(binds.len(), 2);
        assert_match!(**binds[0].resolved_type.remove_forall(), Type::Function(_, ref arg, _) => {
            assert_match!(**arg, Type::Generic(_) => ())
        });
        assert_match!(**binds[1].resolved_type.remove_forall(), Type::Function(_, ref arg, _) => {
            assert_match!(**arg, Type::Generic(_) => ())
        });
    });
}

#[test]
fn primitive_error() {
    let _ = env_logger::try_init();

    let text = r"
1 #Int== 2.2
";
    let result = support::typecheck(text);

    assert!(result.is_err());
}

#[test]
fn binop_as_function() {
    let _ = env_logger::try_init();

    let text = r"
#[infix(left, 1)]
let (+) = \x y -> x #Int+ y
in 1 + 2
";
    let result = support::typecheck(text);
    let expected = Ok(typ("Int"));

    assert_req!(result, expected);
}

#[test]
fn adt() {
    let _ = env_logger::try_init();

    let text = r"
type Option a = | None | Some a
in Some 1
";
    let result = support::typecheck(text);
    let expected = Ok(support::typ_a(
        "Option",
        Kind::function(Kind::typ(), Kind::typ()),
        vec![typ("Int")],
    ));

    assert_req!(result.map(make_ident_type), expected);
}

#[test]
fn case_constructor() {
    let _ = env_logger::try_init();

    let text = r"
type Option a = | None | Some a
in match Some 1 with
    | Some x -> x
    | None -> 2
";
    let result = support::typecheck(text);
    let expected = Ok(typ("Int"));

    assert_req!(result, expected);
}

#[test]
fn real_type() {
    let _ = env_logger::try_init();

    let text = r"
type Eq a = {
    (==) : a -> a -> Bool
} in

let eq_Int: Eq Int = {
    (==) = \l r -> l #Int== r
}
in eq_Int
";
    let result = support::typecheck(text);
    let bool = Type::alias(
        support::intern_unscoped("Bool"),
        Vec::new(),
        Type::ident(KindedIdent {
            name: support::intern_unscoped("Bool"),
            typ: Kind::typ(),
        }),
    );
    let eq = alias(
        "Eq",
        &["a"],
        Type::record(
            vec![],
            vec![Field::new(
                support::intern_unscoped("=="),
                Type::function(vec![typ("a"), typ("a")], bool),
            )],
        ),
    );
    let expected = Ok(Type::app(eq, collect![typ("Int")]));

    assert_eq!(result, expected);
}

#[test]
fn functor_option() {
    let _ = env_logger::try_init();

    let text = r"
type Functor f = {
    map : forall a b . (a -> b) -> f a -> f b
} in
type Option a = | None | Some a in
let option_Functor: Functor Option = {
    map = \f x -> match x with
                    | Some y -> Some (f y)
                    | None -> None
}
in option_Functor.map (\x -> x #Int- 1) (Some 2)
";
    let result = support::typecheck(text);
    let option = support::alias_variant("Option", &["a"], &[("None", &[]), ("Some", &[typ("a")])]);

    let expected = Ok(Type::app(option, collect![typ("Int")]));

    assert_req!(result, expected);
}

#[test]
fn app_app_unify() {
    let _ = env_logger::try_init();

    let text = r"
type Monad m = {
    (>>=): forall a b. m a -> (a -> m b) -> m b,
    return: forall a. a -> m a
}

type Test a = | T a

let monad_Test: Monad Test = {
    (>>=) = \ta f ->
        match ta with
            | T a -> f a,
    return = \x -> T x
}

#[infix(left, 1)]
let (>>=) = monad_Test.(>>=)

let test: Test () = T 1 >>= \x -> monad_Test.return ()

test
";
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let expected = Ok(Type::app(
        support::alias_variant("Test", &["a"], &[("T", &[typ("a")])]),
        collect![Type::unit()],
    ));

    assert_req!(result, expected);
}

#[test]
fn function_operator_type() {
    let _ = env_logger::try_init();

    let text = r"
let f x: ((->) Int Int) = x #Int+ 1
f
";
    let result = support::typecheck(text);
    let expected = Ok(Type::app(
        Type::function_builtin(),
        collect![typ("Int"), typ("Int")],
    ));

    assert_eq!(result, expected);
}

#[test]
fn function_operator_partially_applied() {
    let _ = env_logger::try_init();

    let text = r"
type Test f = {
    test: f Int
}
let function_test: Test ((->) a) = {
    test = \x -> 1
}
function_test.test
";
    let result = support::typecheck(text);
    let expected = Ok("forall a . a -> Int".to_string());

    assert_req!(result.map(|typ| typ.to_string()), expected);
}

#[test]
fn type_alias_function() {
    let _ = env_logger::try_init();

    let text = r"
type Fn a b = a -> b
in
let f: Fn String Int = \x -> 123
in f
";
    let result = support::typecheck(text);
    let function = alias("Fn", &["a", "b"], Type::function(vec![typ("a")], typ("b")));
    let args = collect![typ("String"), typ("Int")];
    let expected = Ok(Type::app(function, args));

    assert_req!(result, expected);
}

#[test]
fn infer_mutually_recursive() {
    let _ = env_logger::try_init();

    let text = r"
rec
let id x = x
let const x = \_ -> x
in

let c: a -> b -> a = const
c
";
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn error_mutually_recursive() {
    let _ = env_logger::try_init();

    let text = r"
rec
let id x = x
let const x = \_ -> x
in const #Int+ 1
";
    let result = support::typecheck(text);
    assert!(result.is_err(), "{}", result.unwrap());
}

#[test]
fn partial_function_unify() {
    let _ = env_logger::try_init();

    let text = r"
type Monad m = {
    (>>=) : m a -> (a -> m b) -> m b,
    return : a -> m a
} in
type State s a = s -> { value: a, state: s }
in
#[infix(left, 1)]
let (>>=) m f: State s a -> (a -> State s b) -> State s b =
    \state ->
        let { value, state } = m state
        let m2 = f value
        in m2 state
in
let return value: a -> State s a = \state -> { value, state }
in
let monad_State: Monad (State s) = { (>>=), return }
in { monad_State }
";
    let result = support::typecheck(text);

    assert_pass!(result);
}

/// Test that not all fields are required when unifying record patterns
#[test]
fn partial_pattern() {
    let _ = env_logger::try_init();

    let text = r#"
let { y } = { x = 1, y = "" }
in y
"#;
    let result = support::typecheck(text);
    let expected = Ok(typ("String"));

    assert_eq!(result, expected);
}

#[test]
fn type_pattern() {
    let _ = env_logger::try_init();

    let text = r#"
type Test = | Test String Int in { Test, x = 1 }
"#;
    let result = support::typecheck(text);
    let test = Type::variant(vec![support::variant(
        "Test",
        "Test",
        &[typ("String"), typ("Int")],
    )]);
    let types = vec![Field {
        name: support::intern_unscoped("Test"),
        typ: Alias::new(intern("Test"), Vec::new(), test),
    }];
    let fields = vec![Field {
        name: intern("x"),
        typ: typ("Int"),
    }];
    let expected = Ok(Type::record(types, fields));

    assert_req!(result.map(support::close_record), expected);
}

#[test]
fn unify_variant() {
    let _ = env_logger::try_init();

    let text = r#"
type Test a = | Test a
Test 1
"#;
    let result = support::typecheck(text);
    let expected = Ok(support::typ_a(
        "Test",
        Kind::function(Kind::typ(), Kind::typ()),
        vec![typ("Int")],
    ));

    assert_req!(result.map(make_ident_type), expected);
}

#[test]
fn unify_transformer() {
    let _ = env_logger::try_init();

    let text = r#"
type Test a = | Test a
type Id a = | Id a
type IdT m a = m (Id a)
let return x: a -> IdT Test a = Test (Id x)
return 1
"#;
    let result = support::typecheck(text);
    let test = support::alias_variant("Test", &["a"], &[("Test", &[typ("a")])]);
    let m = Generic::new(intern("m"), Kind::function(Kind::typ(), Kind::typ()));

    let id = support::alias_variant("Id", &["a"], &[("Id", &[typ("a")])]);
    let id_t = Type::alias(
        intern("IdT"),
        vec![m.clone(), Generic::new(intern("a"), Kind::typ())],
        Type::app(
            Type::generic(m),
            collect![Type::app(id, collect![typ("a")])],
        ),
    );
    let expected = Ok(Type::app(id_t, collect![test, typ("Int")]));

    assert_req!(result, expected);
}

#[test]
fn normalize_function_type() {
    let _ = env_logger::try_init();

    let text = r#"
type Cat cat = {
    id : forall a . cat a a,
}
let cat: Cat (->) = {
    id = \x -> x,
}
let { id } = cat
let { id } = cat
let test f: (a -> m b) -> m b = test f
test id
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn mutually_recursive_types() {
    let _ = env_logger::try_init();

    let text = r#"
rec
type Tree a = | Empty | Node (Data a) (Data a)
type Data a = { value: a, tree: Tree a }
in
let rhs : Data Int = {
    value = 123,
    tree = Node { value = 0, tree = Empty } { value = 42, tree = Empty }
}
in Node { value = 1, tree = Empty } rhs
"#;
    let result = support::typecheck(text);
    let expected = Ok(support::typ_a(
        "Tree",
        Kind::function(Kind::typ(), Kind::typ()),
        vec![typ("Int")],
    ));

    assert_req!(result.map(make_ident_type), expected);
}

#[test]
fn field_access_through_multiple_aliases() {
    let _ = env_logger::try_init();

    let text = r#"
rec
type Test1 = { x: Int }
type Test2 = Test1
in

let t: Test2 = { x = 1 }

t.x
"#;
    let result = support::typecheck(text);
    let expected = Ok(typ("Int"));

    assert_eq!(result, expected);
}

#[test]
fn unify_equal_hkt_aliases() {
    let _ = env_logger::try_init();

    let text = r#"
type M a = | M a
type M2 a = M a
type HKT m = { x: m Int }
in
let eq: a -> a -> Int = \x y -> 1
let t: HKT M = { x = M 1 }
let u: HKT M2 = t
in eq t u
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn as_pattern() {
    let _ = env_logger::try_init();

    let text = r#"
match 1 with
| x@y -> x #Int+ y
"#;
    let result = support::typecheck(text);
    let expected = Ok(Type::int());

    assert_req!(result, expected);
}

#[test]
fn as_pattern_record() {
    let _ = env_logger::try_init();

    let text = r#"
match { y = 1 } with
| x@{ y } -> x
"#;
    let result = support::typecheck(text);
    let fields = vec![Field::new(intern("y"), typ("Int"))];
    let expected = Ok(Type::record(vec![], fields));

    assert_req!(result, expected);
}

#[test]
fn do_expression_simple() {
    let _ = env_logger::try_init();

    let text = r#"
type Test a = { x : a }
let flat_map f x = { x = f x.x }
let test x: a -> Test a = { x }

do x = test 1
test ""
"#;
    let result = support::typecheck(text);
    let expected = Ok(Type::app(
        alias(
            "Test",
            &["a"],
            Type::record(vec![], vec![Field::new(intern("x"), typ("a"))]),
        ),
        collect![typ("String")],
    ));

    assert_req!(result.map(support::close_record), expected);
}

#[test]
fn do_expression_use_binding() {
    let _ = env_logger::try_init();

    let text = r#"
type Test a = { x : a }
let flat_map f x : (a -> Test b) -> Test a -> Test b = f x.x
let test x : a -> Test a = { x }

do x = test 1
test (x #Int+ 2)
"#;
    let result = support::typecheck(text);
    let expected = Ok(Type::app(
        alias(
            "Test",
            &["a"],
            Type::record(vec![], vec![Field::new(intern("x"), typ("a"))]),
        ),
        collect![typ("Int")],
    ));

    assert_req!(result.map(support::close_record), expected);
}

test_check! {
do_expression_bind_scope,
r#"
type Test a = { x : a }
let flat_map f x : (a -> Test b) -> Test a -> Test b = f x.x
let test x : a -> Test a = { x }

let f y : () -> Test Int =
    do y = test 1
    test (y #Int+ 2)
f
"#,
"() -> test.Test Int"
}

#[test]
fn eq_unresolved_constraint_bug() {
    let _ = env_logger::try_init();

    let text = r#"
type Eq a = { (==) : a -> a -> Bool }
type List a = | Nil | Cons a (List a)

#[infix(left, 1)]
let (==): Int -> Int -> Bool = \x y -> True

let eq a : Eq a -> Eq (List a) =
    #[infix(left, 1)]
    let (==) l r : List a -> List a -> Bool =
        match (l, r) with
        | (Cons x xs, Cons y ys) -> a.(==) x y
        | _ -> False
    { (==) }
()
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn pattern_match_nested_parameterized_type() {
    let _ = env_logger::try_init();

    let text = r#"
type Test a = | Test a
match Test { x = 1 } with
| Test { x } -> x
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn expected_type_do_not_override_actual_type_for_returned_type() {
    let text = "1";
    let (_, result) = support::typecheck_expr_expected(text, Some(&Type::hole()));

    assert_req!(result, Ok(typ("Int")));
}

#[test]
fn expected_type_do_not_override_actual_type_for_returned_type_array() {
    let text = "[1]";
    let (_, result) = support::typecheck_expr_expected(text, Some(&Type::hole()));

    assert_req!(result.map(|t| t.to_string()), Ok("Array Int"));
}

#[test]
fn dont_guess_record_type() {
    let _ = env_logger::try_init();

    let text = r#"
type Test = { a : Int, b : String }
type Test2 = { a : Int, b : Int }

let x : Test = { a = 0, b = "" }
()
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn generalize_function_in_record_and_array() {
    let _ = env_logger::try_init();

    let text = r#"
let string x : String -> String = x
let a: Array { f : String -> String } = [
    { f = \x -> x },
    { f = \x -> string x },
]
a
"#;
    let result = support::typecheck(text);

    assert_req!(
        result.map(|t| t.to_string()),
        Ok("Array { f : String -> String }")
    );
}

#[test]
fn forward_aliased_type() {
    let _ = env_logger::try_init();

    let text = r#"
let { Test } =
    type Test2 = | A Int
    type Test = Test2
    { Test }
A 1
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn dont_shadow_more_generalize_variant_issue_548() {
    let _ = env_logger::try_init();

    let text = r#"
type Test a = | Test a
type TestInt = Test Int

Test ""
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn dont_shadow_more_generalize_variant_2_issue_548() {
    let _ = env_logger::try_init();

    let text = r#"
type Test a b = | Test a b
type TestInt b = Test Int b

Test "" 1
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn allow_more_generalize_variant_to_be_used_despite_specialized_imported_first() {
    let _ = env_logger::try_init();

    let text = r#"
let record =
    type Test a = | Test a
    type TestInt = Test Int
    { Test, TestInt }

let { TestInt } = record
let { Test } = record

Test ""
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn array_expr_gets_type_assigned_without_expected_type_issue_555() {
    let _ = env_logger::try_init();

    let text = r#"
[1]
"#;
    let (expr, result) = support::typecheck_expr(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
    assert_eq!(expr.env_type_of(&MockEnv::new()).to_string(), "Array Int");
}

#[test]
fn dont_panic_on_partially_applied_aliased_function() {
    let _ = env_logger::try_init();

    let text = r#"
type Function a b = a -> b
type Function2 b = Function Int b

let f : Function2 (Int -> Int) = \x -> \y -> y

f 1 2
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn resolve_through_aliased_function_type() {
    let _ = env_logger::try_init();

    let text = r#"

let any x = any x
let map : (a -> b) -> f a -> f b = any ()

type Wrap a = | Wrap a
type Deserializer i a = i -> { value : a, input : i }
type ValueDeserializer a = Deserializer Int a

let option a : ValueDeserializer a -> ValueDeserializer (Wrap a) = \input ->
    (map Wrap a) input

()
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn consider_the_type_of_the_splat_record() {
    let _ = env_logger::try_init();

    let text = r#"
{
    y = 3,
    ..
    { x = 1, y = 2 }
}
"#;
    let result = support::typecheck(text);

    assert_req!(result.map(|t| t.to_string()), Ok("{ x : Int, y : Int }"));
}

test_check! {
    higher_ranked_variant_function,
    r#"
type TestCase =
    | Test (forall r . r -> r)
Test
    "#,
    "(forall r . r -> r) -> test.TestCase"
}

test_check! {
    higher_ranked_variant_function_dont_leak_to_siblings,
    r#"
type TestCase =
    | Test (forall r . r -> r)
    | Group String
Group
    "#,
    "String -> test.TestCase"
}

#[test]
fn infix_env_type_of() {
    let _ = env_logger::try_init();

    let text = r#"
#[infix(left, 4)]
let (+) x y : a -> a -> a = y
2 + 2
"#;
    let (expr, result) = support::typecheck_expr(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
    assert_eq!(expr.env_type_of(&MockEnv::new()).to_string(), "Int");
}

test_check! {
    partially_applied_alias_def,
    r#"
type Test a b = (a, b)
type Test2 = Test Int
let x : Test2 String = (1, "")
x
    "#,
    "test.Test2 String"
}

test_check! {
    alias_reduction_stack_must_be_cleared_between_function_arguments,
    r#"
type StateT s m a = s -> m { value : a, state : s }

#[implicit]
type Alternative f = {
    or : forall a . f a -> f a -> f a,
}

let any x = any x

#[infix(left, 4)]
let (<*>) : f (a -> b) -> f a -> f b = any ()

#[infix(right, 9)]
let (<<) : (b -> c) -> (a -> b) -> a -> c = any ()

let alternative ?alt : [Alternative m] -> Alternative (StateT s m) =
    let or sra srb = alt.or << sra <*> srb
    { or }

()
    "#,
    "()"
}

test_check! {
match_a_function,
r#"
type Test a = | Test a

let f x a : Test (a -> a) -> a -> a =
    match x with
    | Test y -> y a
()
"#,
"()"
}

test_check! {
match_recursive,
r#"
#[implicit]
type Eq a = { (==) : a -> a -> Bool }

#[infix(left, 4)]
let (==) ?eq : [Eq a] -> a -> a -> Bool = eq.(==)

type Recursive a =
    | End a
    | Rec a (Recursive a)

rec let eq_Recursive : [Eq a] -> Eq (Recursive a) =
    rec let eq l r : Recursive a -> Recursive a -> _ =
        match (l, r) with
        | (End l, End r) -> l == r
        | (Rec l arg_l, Rec r arg_r) -> l == r && eq arg_l arg_r
        | _ -> False
    { (==) = eq }

()
"#,
"()"
}

test_check! {
    do_unification_arguments_first,
    r#"
let any x = any x

let foldl : forall a b . (b -> a -> b) -> b -> f a -> b = any ()

type List a = | Cons a (List a) | Nil

let flat_map f x = Nil

do writer = Nil
match writer with
| Cons _ _ ->
    let _ = foldl (\x y -> x) "" writer
    Nil
| Nil -> Cons "" Nil
    "#,
    "test.List String"
}

test_check! {
    issue_842,
    r#"
type Digit a =
    | One a
    | Two a a

type Node b =
    | Node2 b b

type FingerTree c =
    | Empty
    | Single c
    | Deep (Digit c) (FingerTree (Node c)) (Digit c)

type View d =
    | Nil
    | View d (FingerTree d)

rec
let viewl xs : FingerTree e -> View e =
    match xs with
    | Empty -> Nil
    | Single x -> View x Empty
    | Deep (One a) deeper suffix ->
        match viewl deeper with
        | View (Node2 b c) rest -> View a (Deep (Two b c) rest suffix)
        | Nil ->
            match suffix with
            | One w -> View a (Single w)
in

viewl
    "#,
    "forall a . test.FingerTree a -> test.View a"
}

test_check! {
    do_type_signature,
    r#"
type List a = | Cons a (List a) | Nil

let flat_map f x : (a -> List b) -> List a -> List b = Nil

do writer : String = Nil
Cons 0 Nil
    "#,
    "test.List Int"
}
