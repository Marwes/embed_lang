#[macro_use]
extern crate pretty_assertions;

extern crate gluon_completion as completion;

#[macro_use]
mod support;

use crate::support::*;

use gluon::{
    base::{pos::BytePos, source::Source, types::Type},
    import::add_extern_module,
    record, vm,
    vm::{
        api::{FunctionRef, Hole, OpaqueValue, ValueRef, IO},
        channel::Sender,
        thread::Thread,
        ExternModule,
    },
    Error, ThreadExt,
};
use gluon_codegen::{Getable, Pushable, VmType};

test_expr! { pass_function_value,
r"
let lazy: () -> Int = \x -> 42 in
let test: (() -> Int) -> Int = \f -> f () #Int+ 10
in test lazy
",
52i32
}

test_expr! { lambda,
r"
let y = 100 in
let f = \x -> y #Int+ x #Int+ 1
in f(22)
",
123i32
}

test_expr! { add_operator,
r"
#[infix(left, 6)]
let (+) = \x y -> x #Int+ y in 1 + 2 + 3
",
6i32
}

test_expr! { divide_int,
r" 120 #Int/ 4
",
30i32
}

test_expr! { divide_float,
r" 120.0 #Float/ 4.0
",
30.0f64
}

test_expr! { infix_propagates,
r"
#[infix(left, 6)]
let (+) = \x y -> x #Int+ y
let { (+) = (++) } = { (+) }
1 ++ 2 ++ 3
",
6i32
}

#[test]
fn record() {
    let _ = ::env_logger::try_init();
    let text = r"
{ x = 0, y = 1.0, z = {} }
";
    let vm = make_vm();
    let value = run_expr::<OpaqueValue<&Thread, Hole>>(&vm, text);
    match value.get_ref() {
        ValueRef::Data(data) => {
            assert_eq!(data.get(0).unwrap(), ValueRef::Int(0));
            assert_eq!(data.get(1).unwrap(), ValueRef::Float(1.0));
            match &data.get(2).unwrap() {
                ValueRef::Data(data) if data.len() == 0 => (),
                _ => panic!(),
            }
        }
        _ => panic!(),
    }
}

#[test]
fn add_record() {
    let _ = ::env_logger::try_init();
    let text = r"
type T = { x: Int, y: Int } in
let add = \l r -> { x = l.x #Int+ r.x, y = l.y #Int+ r.y } in
add { x = 0, y = 1 } { x = 1, y = 1 }
";
    let vm = make_vm();
    let value = run_expr::<OpaqueValue<&Thread, Hole>>(&vm, text);
    match value.get_ref() {
        ValueRef::Data(data) => {
            assert_eq!(data.get(0).unwrap(), ValueRef::Int(1));
            assert_eq!(data.get(1).unwrap(), ValueRef::Int(2));
        }
        _ => panic!(),
    }
}

#[test]
fn script() {
    let _ = ::env_logger::try_init();
    let text = r"
type T = { x: Int, y: Int } in
let add l r = { x = l.x #Int+ r.x, y = l.y #Int+ r.y } in
let sub l r = { x = l.x #Int- r.x, y = l.y #Int- r.y } in
{ T, add, sub }
";
    let vm = make_vm();
    load_script(&vm, "vec", text).unwrap_or_else(|err| panic!("{}", err));

    let script = r#"
let { T, add, sub } = import! vec
in add { x = 10, y = 5 } { x = 1, y = 2 }
"#;
    let value = run_expr::<OpaqueValue<&Thread, Hole>>(&vm, script);
    match value.get_ref() {
        ValueRef::Data(data) => {
            assert_eq!(data.get(0), Some(ValueRef::Int(11)));
            assert_eq!(data.get(1), Some(ValueRef::Int(7)));
        }
        _ => panic!(),
    }
}
#[test]
fn adt() {
    let _ = ::env_logger::try_init();
    let text = r"
type Option a = | None | Some a
in Some 1
";
    let vm = make_vm();
    let value = run_expr::<OpaqueValue<&Thread, Hole>>(&vm, text);
    match value.get_ref() {
        ValueRef::Data(ref data) if data.tag() == 1 && data.get(0) == Some(ValueRef::Int(1)) => (),
        _ => panic!("{:?}", value),
    }
}

test_expr! { recursive_function,
r"
rec let fib x =
    if x #Int< 3
    then 1
    else fib (x #Int- 1) #Int+ fib (x #Int- 2)
in fib 7
",
13i32
}

test_expr! { mutually_recursive_function,
r"
rec
let f x = if x #Int< 0
      then x
      else g x
let g x = f (x #Int- 1)
in g 3
",
-1
}

test_expr! { no_capture_self_function,
r"
let x = 2 in
let f y = x
in f 4
",
2i32
}

test_expr! { primitive_char_eq,
r"
'a' #Char== 'a'
",
true
}

test_expr! { primitive_char_lt,
r"
'a' #Char< 'a'
",
false
}

test_expr! { primitive_byte_arithmetic,
r"
let x = 100b #Byte+ 13b
x #Byte* 2b #Byte/ 3b
",
75u8
}

test_expr! { primitive_byte_eq,
r"
100b #Byte== 100b
",
true
}

test_expr! { primitive_byte_lt,
r"
100b #Byte< 100b
",
false
}

test_expr! { prelude overloaded_compare_int,
r"
99 < 100
",
true
}

test_expr! { prelude overloaded_compare_float,
r"
99.0 < 100.0
",
true
}

test_expr! { implicit_call_without_type_in_scope,
r"
let int @ { ? } = import! std.int
let prelude @ { (==) } = import! std.prelude
99 == 100
",
false
}

test_expr! { partial_application1,
r"
let f x y = x #Int+ y in
let g = f 10
in g 2 #Int+ g 3
",
25i32
}

test_expr! { partial_application2,
r"
let f x y z = x #Int+ y #Int+ z in
let g = f 10 in
let h = g 20
in h 2 #Int+ g 10 3
",
55i32
}

test_expr! { to_many_args_application,
r"
let f x = \y -> x #Int+ y in
let g = f 20
in f 10 2 #Int+ g 3
",
35i32
}

test_expr! { to_many_args_partial_application_twice,
r"
let f x = \y z -> x #Int+ y #Int+ z in
let g = f 20 5
in f 10 2 1 #Int+ g 2
",
40i32
}

test_expr! { excess_arguments_larger_than_stack,
r#"
let f a b c = c
(\x -> f) 1 2 3 4
"#,
4i32
}

test_expr! { char,
r#"
'a'
"#,
'a'
}

test_expr! { prelude handle_fields_being_ignored_in_optimize,
    r#"
let large_record = { x = 1, y = 2 }
large_record.x
"#,
1
}

test_expr! { any zero_argument_variant_is_int,
r#"
type Test = | A Int | B
B
"#,
ValueRef::tag(1)
}

test_expr! { any marshalled_option_none_is_int,
r#"
let string_prim = import! std.string.prim
string_prim.find "a" "b"
"#,
ValueRef::tag(0)
}

test_expr! { any marshalled_ordering_is_int,
r#"
let { string_compare } = import! std.prim
string_compare "a" "b"
"#,
ValueRef::tag(0)
}

test_expr! { discriminant_value,
r#"
type Variant a = | A | B Int | C String
let prim = import! std.prim
prim.discriminant_value (C "")
"#,
2
}

test_expr! { unit_expr,
r#"
let x = ()
let y = 1
in y
"#,
1i32
}

test_expr! { return_unit,
"()",
()
}

test_expr! { let_not_in_tail_position,
r#"
1 #Int+ (let x = 2 in x)
"#,
3i32
}

test_expr! { field_access_not_in_tail_position,
r#"
let id x = x
in (id { x = 1 }).x
"#,
1i32
}

test_expr! { module_function,
r#"
let string_prim = import! std.string.prim
let x = string_prim.len "test" in x
"#,
4i32
}

test_expr! { prelude true_branch_not_affected_by_false_branch,
r#"
let { Bool } = import! std.bool
if True then
    let x = 1
    x
else
    0
"#,
1i32
}

test_expr! { prelude and_operator_stack,
r#"
let { Bool } = import! std.bool
let b = True && True
let b2 = False
b
"#,
true
}

test_expr! { prelude or_operator_stack,
r#"
let { Bool } = import! std.bool
let b = False || True
let b2 = False
b
"#,
true
}

test_expr! { overload_resolution_with_record_pattern,
r#"
let f =
    \x g ->
        let { x } = g x
        x
f 0 (\r -> { x = r #Int+ 1 })
"#,
1i32
}

test_expr! { record_base_duplicate_fields,
r#"
{ x = "" ..  { x = 1 } }.x
"#,
"".to_string()
}

test_expr! { record_base_duplicate_fields2,
r#"
{ x = "" ..  { x = 1, y = 2 } }.y
"#,
2
}

test_expr! { record_base_duplicate_fields_different_order,
r#"
{ z = 3.0, y = "y", x = "x" ..  { x = 1, y = 2 } }.x
"#,
String::from("x")
}

test_expr! { load_simple,
r#"
let _ = import! std.foldable
()
"#,
()
}

test_expr! { load_option,
r#"
let _ = import! std.option
()
"#,
()
}

test_expr! { load_applicative,
r#"
let _ = import! std.applicative
()
"#,
()
}

test_expr! { prelude do_expression_option_some,
r#"
let { monad = { flat_map } } = import! std.option
do x = Some 1
Some (x + 2)
"#,
Some(3)
}

test_expr! { prelude do_expression_option_none,
r#"
let { monad = { flat_map } } = import! std.option
do x = None
Some 1
"#,
None::<i32>
}

test_expr! { function_with_implicit_argument_from_record,
r#"
let f ?t x: [Int] -> () -> Int = t
let x @ { ? } =
    #[implicit]
    let test = 1
    { test }
f ()
"#,
1
}

test_expr! { prelude not_equal_operator,
r#"
1 /= 2
"#,
true
}

test_expr! { implicit_argument_selection1,
r#"
#[implicit]
type Test = | Test ()
let f y: [a] -> a -> () = ()
let i = Test ()
f (Test ())
"#,
()
}

test_expr! { prelude implicit_argument_selection2,
r#"
let string = import! std.string
let { append } = string.semigroup
#[infix(left, 6)]
let (++) = append

let equality l r : [Eq a] -> a -> a -> String =
    if l == r then " == " else " != "

let cmp l r : [Show a] -> [Eq a] -> a -> a -> String =
    (show l) ++ (equality l r) ++ (show r)

cmp 5 6
"#,
String::from("5 != 6")
}

#[test]
fn rename_types_after_binding() {
    let _ = ::env_logger::try_init();

    let text = r#"
let list = import! std.list
let { List } = list

let eq_list: Eq (List Int) = list.eq
in Cons 1 Nil == Nil
"#;
    let vm = make_vm();
    let (result, _) = vm
        .run_expr::<bool>("<top>", text)
        .unwrap_or_else(|err| panic!("{}", err));
    let expected = false;

    assert_eq!(result, expected);
}

#[test]
fn record_splat_ice() {
    let _ = ::env_logger::try_init();

    let text = r#"
let large_record = { x = 1 }
{
    field = 123,
    ..
    large_record
}
"#;
    let vm = make_vm();
    vm.get_database_mut().implicit_prelude(false);
    let result = vm.run_expr::<OpaqueValue<&Thread, Hole>>("example", text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn test_implicit_prelude() {
    let _ = ::env_logger::try_init();
    let text = r#"1.0 + 3.0 - 2.0"#;
    let vm = make_vm();
    vm.run_expr::<OpaqueValue<&Thread, Hole>>("<top>", text)
        .unwrap_or_else(|err| panic!("{}", err));
}

#[test]
fn access_field_through_vm() {
    let _ = ::env_logger::try_init();
    let text = r#" { x = 0, inner = { y = 1.0 } } "#;
    let vm = make_vm();
    load_script(&vm, "test", text).unwrap_or_else(|err| panic!("{}", err));
    let test_x = vm.get_global("test.x");
    assert_eq!(test_x, Ok(0));
    let test_inner_y = vm.get_global("test.inner.y");
    assert_eq!(test_inner_y, Ok(1.0));
}

#[test]
fn access_operator_without_parentheses() {
    let _ = ::env_logger::try_init();
    let vm = make_vm();
    vm.run_expr::<OpaqueValue<&Thread, Hole>>("example", r#" import! std.prelude "#)
        .unwrap();
    let result: Result<FunctionRef<fn(i32, i32) -> i32>, _> =
        vm.get_global("std.prelude.num_Int.+");
    assert!(result.is_err());
}

#[test]
fn get_binding_with_alias_type() {
    let _ = ::env_logger::try_init();
    let text = r#"
        type Test = Int
        let x: Test = 0
        { Test, x }
        "#;
    let vm = make_vm();
    load_script(&vm, "test", text).unwrap_or_else(|err| panic!("{}", err));
    let test_x = vm.get_global("test.x");
    assert_eq!(test_x, Ok(0));
}

#[test]
fn get_binding_with_generic_params() {
    let _ = ::env_logger::try_init();

    let vm = make_vm();
    run_expr::<OpaqueValue<&Thread, Hole>>(&vm, r#" import! std.function "#);
    let mut id: FunctionRef<fn(String) -> String> = vm
        .get_global("std.function.id")
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(id.call("test".to_string()), Ok("test".to_string()));
}

#[test]
fn test_prelude() {
    let _ = ::env_logger::try_init();
    let vm = make_vm();
    run_expr::<OpaqueValue<&Thread, Hole>>(&vm, r#" import! std.prelude "#);
}

#[test]
fn access_types_by_path() {
    let _ = ::env_logger::try_init();

    let vm = make_vm();
    run_expr::<OpaqueValue<&Thread, Hole>>(&vm, r#" import! std.option "#);
    run_expr::<OpaqueValue<&Thread, Hole>>(&vm, r#" import! std.result "#);

    assert!(vm.find_type_info("std.option.Option").is_ok());
    assert!(vm.find_type_info("std.result.Result").is_ok());

    let text = r#" type T a = | T a in { x = 0, inner = { T, y = 1.0 } } "#;
    load_script(&vm, "test", text).unwrap_or_else(|err| panic!("{}", err));
    let result = vm.find_type_info("test.inner.T");
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn opaque_value_type_mismatch() {
    let _ = ::env_logger::try_init();
    let vm = make_vm();

    vm.get_database_mut().implicit_prelude(false);

    vm.run_expr::<()>("<top>", "let _ = import! std.channel in ()")
        .unwrap();

    let expr = r#"
let { sender, receiver } = channel 0
let _ = send sender 1
sender
"#;
    let result = vm.run_expr::<OpaqueValue<&Thread, Sender<f64>>>("<top>", expr);
    match result {
        Err(Error::Typecheck(..)) => (),
        Err(err) => panic!("Unexpected error `{}`", err),
        Ok(_) => panic!("Expected an error"),
    }
}

#[test]
fn invalid_string_slice_dont_panic() {
    let _ = ::env_logger::try_init();
    let text = r#"
let string = import! std.string
let s = "åäö"
string.slice s 1 (string.len s)
"#;
    let vm = make_vm();
    let result = vm.run_expr::<String>("<top>", text);
    match result {
        Err(Error::VM(..)) => (),
        Err(err) => panic!("Unexpected error `{}`", err),
        Ok(_) => panic!("Expected an error"),
    }
}

#[test]
fn arithmetic_over_flow_dont_panic() {
    let _ = ::env_logger::try_init();
    let text = r#"
let int = import! std.int
int.max_value * 2
"#;
    let vm = make_vm();
    let result = vm.run_expr::<i32>("<top>", text);
    match result {
        Err(Error::VM(vm::Error::Message(ref err))) if err.contains("overflow") => (),
        Err(err) => panic!("Unexpected error `{}`", err),
        Ok(_) => panic!("Expected an error"),
    }
}

#[test]
fn partially_applied_constructor_is_lambda() {
    let _ = ::env_logger::try_init();
    let vm = make_vm();

    let result = vm.run_expr::<FunctionRef<fn(i32) -> Option<i32>>>(
        "test",
        r#"let { Option } = import! std.option in Some"#,
    );
    assert!(result.is_ok(), "{}", result.err().unwrap());
    assert_eq!(result.unwrap().0.call(123), Ok(Some(123)));
}

#[test]
fn stacktrace() {
    use gluon::vm::stack::StacktraceFrame;
    let _ = ::env_logger::try_init();
    let text = r#"
let end _ = 1 + error "test"
rec
let f x =
    if x == 0 then
        3 + end ()
    else
        1 + g (x - 1)
let g x = 1 + f (x / 2)
in
g 10
"#;
    let vm = make_vm();
    vm.get_database_mut().set_optimize(false);
    let result = vm.run_expr::<i32>("<top>", text);
    match result {
        Err(Error::VM(vm::Error::Panic(_, Some(stacktrace)))) => {
            let g = stacktrace.frames[0].as_ref().unwrap().name.clone();
            assert_eq!(g.declared_name(), "g");
            let f = stacktrace.frames[1].as_ref().unwrap().name.clone();
            let end = stacktrace.frames[6].as_ref().unwrap().name.clone();
            let error = stacktrace.frames[7].as_ref().unwrap().name.clone();
            assert_eq!(
                stacktrace.frames,
                vec![
                    // Removed due to being a tail call
                    // Some(StacktraceFrame { name: f.clone(), line: 9 }),
                    Some(StacktraceFrame {
                        name: g.clone(),
                        line: Some(8.into()),
                    }),
                    Some(StacktraceFrame {
                        name: f.clone(),
                        line: Some(7.into()),
                    }),
                    Some(StacktraceFrame {
                        name: g.clone(),
                        line: Some(8.into()),
                    }),
                    Some(StacktraceFrame {
                        name: f.clone(),
                        line: Some(7.into()),
                    }),
                    Some(StacktraceFrame {
                        name: g.clone(),
                        line: Some(8.into()),
                    }),
                    Some(StacktraceFrame {
                        name: f.clone(),
                        line: Some(5.into()),
                    }),
                    Some(StacktraceFrame {
                        name: end.clone(),
                        line: Some(1.into()),
                    }),
                    Some(StacktraceFrame {
                        name: error.clone(),
                        line: None,
                    }),
                ]
            );
        }
        Err(err) => panic!("Unexpected error `{}`", err),
        Ok(_) => panic!("Expected an error"),
    }
}

#[tokio::test]
async fn completion_with_prelude() {
    let _ = ::env_logger::try_init();
    let vm = make_vm_async().await;

    let source = r#"
let prelude  = import! std.prelude
let { Option } = import! std.option
let { Num } = prelude
let { Lazy, lazy } = import! std.lazy

rec
type Stream_ a =
    | Value a (Stream a)
    | Empty
type Stream a = Lazy (Stream_ a)
in

let from f : (Int -> Option a) -> Stream a =
        rec let from_ i =
                lazy (\_ ->
                    match f i with
                        | Some x -> Value x (from_ (i + 1))
                        | None -> Empty
                )
        in from_ 0

{ from }
"#;

    let (expr, _) = vm
        .typecheck_str_async("example", source, None)
        .await
        .unwrap_or_else(|err| panic!("{}", err));

    let lines = vm.get_database().get_filemap("example").expect("file_map");
    let result = completion::find(
        &vm.get_env(),
        lines.span(),
        &expr.expr(),
        lines.byte_index(16.into(), 29.into()).unwrap(),
    )
    .map(|either| either.right().unwrap());
    assert_eq!(result, Ok(Type::int()));
}

#[tokio::test]
async fn completion_with_prelude_at_0() {
    let _ = ::env_logger::try_init();
    let vm = make_vm_async().await;

    let expr = "1";

    let (expr, _) = vm
        .typecheck_str_async("example", expr, None)
        .await
        .unwrap_or_else(|err| panic!("{}", err));

    let file_map = vm.get_database().get_filemap("example").expect("file_map");
    let result = completion::find(
        &vm.get_env(),
        file_map.span(),
        &expr.expr(),
        BytePos::from(0),
    )
    .map(|either| either.right().unwrap());
    assert_eq!(result, Ok(Type::int()));
}

#[tokio::test]
async fn suggestion_from_implicit_prelude() {
    let _ = ::env_logger::try_init();
    let vm = make_vm_async().await;

    let expr = "1 ";

    let (expr, _) = vm
        .typecheck_str_async("example", expr, None)
        .await
        .unwrap_or_else(|err| panic!("{}", err));

    let lines = vm.get_database().get_filemap("example").expect("file_map");
    let result = completion::suggest(
        &vm.get_env(),
        lines.span(),
        &expr.expr(),
        lines.byte_index(0.into(), 2.into()).unwrap(),
    );
    assert!(!result.is_empty());
}

/// Would cause panics in `Source` as the spans from the implicit prelude were used with the
/// `Source` from the normal expression
#[tokio::test]
async fn dont_use_the_implicit_prelude_span_in_the_top_expr() {
    let _ = ::env_logger::try_init();
    let vm = make_vm_async().await;

    let expr = "1";

    vm.typecheck_str_async("example", expr, Some(&Type::float()))
        .await
        .unwrap_err();
}

#[test]
fn deep_clone_partial_application() {
    let _ = ::env_logger::try_init();
    let vm = gluon::VmBuilder::new().build();

    let child = vm.new_thread().unwrap();

    assert_eq!(child.allocated_memory(), 0);

    child.get_database_mut().set_implicit_prelude(false);
    let result = child.run_expr::<OpaqueValue<&Thread, Hole>>(
        "test",
        r#"
                let f x y = y
                f 1
            "#,
    );
    assert!(result.is_ok(), "{}", result.err().unwrap());

    let global_memory_without_closures = vm.global_env().gc.lock().unwrap().allocated_memory();
    let memory_for_closures = child.allocated_memory();

    vm.get_database_mut().set_global(
        "test",
        Type::hole(),
        Default::default(),
        &result.unwrap().0.into_inner(),
    );

    let global_memory_with_closures = vm.global_env().gc.lock().unwrap().allocated_memory();

    assert_eq!(
        global_memory_without_closures + memory_for_closures,
        global_memory_with_closures
    );
}

test_expr! { prelude issue_601,
r"
let { wrap } = import! std.applicative
let { flat_map } = import! std.monad

type Id a = a
let id_functor: Functor Id = {
    map = \f x -> f x,
}
let id_applicative: Applicative Id = {
    functor = id_functor,
    apply = \f x -> f x,
    wrap = \x -> x,
}
let id_monad: Monad Id = {
    applicative = id_applicative,
    flat_map = \f x -> f x,
}

let foo: [Functor f] -> Id () = ()

let bar: Id () =
    do _ = foo
    wrap ()

in ()
",
()
}

test_expr! { recursive_record,
r#"
rec
let x = { y }
let y = { z = 2 }
x.y.z
"#,
2
}

test_expr! { recursive_variant,
r#"
type List a = | Nil | Cons a (List a)
rec let ones = Cons 1 ones
in
match ones with
| Cons x xs -> x
| Nil -> 2
"#,
1
}

test_expr! { recursive_implicit,
r#"
rec
type Test = | Test Test2 | Nil
type Test2 = | Test2 Test
in

#[implicit]
type Size a = { size : a -> Int }

let size ?s : [Size a] -> a -> Int = s.size

rec
let size_test : Size Test =
    let size_ x =
        match x with
        | Test t -> 1 #Int+ size t
        | Nil -> 0
    { size = size_ }
let size_test2 : Size Test2 =
    let size_ x =
        match x with
        | Test2 t -> 1 #Int+ size t
    { size = size_ }
in

size (Test (Test2 (Test (Test2 Nil))))
"#,
4
}

test_expr! { prelude thread_join,
r#"
let thread = import! std.thread
let io @ { ? } = import! std.io
let { wrap, (*>) } = import! std.applicative
let { (>>=) } = import! std.monad
let { id } = import! std.function
do t = thread.new_thread ()

thread.join (io.println "test" *> wrap 123) (thread.spawn_on t (wrap "abc") >>= id)
"#,
IO::Value((123, "abc".to_string()))
}

test_expr! { category_bug,
r"
let { Category } = import! std.category

let category : Category (->) = {
    id = \x -> x,
    compose = \f g x -> f (g x),
}

1
",
1i32
}

test_expr! { load_io_skolem_bug,
r"
let io_prim @ { IO } = import! std.io.prim

type Monad (m : Type -> Type) = {
    flat_map : forall a b . (a -> m b) -> m a -> m b
}

let monad : Monad IO = {
    flat_map = io_prim.flat_map,
}

1
",
1i32
}

test_expr! { lift_effect_skolem_bug,
r"

let _ = import! std.effect.lift

1
",
1i32
}

test_expr! { use_bool,
r"
let { Bool } = import! std.types

True
",
true
}

test_expr! {
recursive_eff_arr,
r#"
rec
type Eff (r : Type -> Type) a =
    | Pure a
    | Impure : forall x . Arr r x a -> Eff r a

type Arr r a b = a -> Eff r b
in

type Writer r a = .. r

let tell : Eff [| writer : Writer | r |] () =
    Impure Pure

()
"#,
()
}

test_expr! { issue_863,
r"
let { (<|) } = import! std.function

let g f x = x
let f a =
    g a <| f a
{ f }
"
}

#[derive(Clone, Debug, VmType, Pushable, Getable)]
enum E1 {
    S1(S),
}

#[derive(Clone, Debug, VmType, Pushable, Getable)]
struct S {
    e: E2,
}

#[derive(Clone, Debug, VmType, Pushable, Getable)]
enum E2 {
    Num(i32),
}

#[test]
fn issue_901() {
    let _ = ::env_logger::try_init();
    let text = r"
let { E1, S, E2 } = import! test
let e1 = S1 { e = Num 3 }
()
";
    let vm = make_vm();
    add_extern_module(&vm, "test", |vm| {
        ExternModule::new(
            vm,
            record! {
                type E1 => E1,
                type S => S,
                type E2 => E2,
            },
        )
    });
    run_expr::<OpaqueValue<&Thread, Hole>>(&vm, text);
}
