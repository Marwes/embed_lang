#[macro_use]
extern crate gluon_codegen;
extern crate gluon;
extern crate serde;
#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate gluon_vm;

mod init;

use gluon::vm::api::{self, generic::A, OpaqueValue};
use gluon::vm::{self, ExternModule};
use gluon::{import, Compiler, RootedThread, Thread};
use init::new_vm;

#[derive(Pushable, VmType, Serialize, Deserialize)]
#[gluon(vm_type = "types.Struct")]
struct Struct {
    string: String,
    number: u32,
    vec: Vec<f64>,
}

fn load_struct_mod(vm: &Thread) -> vm::Result<ExternModule> {
    let module = record! {
        new_struct => primitive!(1, new_struct),
    };

    ExternModule::new(vm, module)
}

fn new_struct(_: ()) -> Struct {
    Struct {
        string: "hello".to_owned(),
        number: 1,
        vec: vec![1.0, 2.0, 3.0],
    }
}

#[test]
fn normal_struct() {
    let vm = new_vm();
    let compiler = Compiler::new();

    // must be generated by hand because of bug in make_source (see #542)
    let src = r#"
        type Struct = { string: String, number: Int, vec: Array Float }
        { Struct }
    "#;

    compiler.load_script(&vm, "types", &src).unwrap();
    import::add_extern_module(&vm, "functions", load_struct_mod);

    let script = r#"
        let { Struct } = import! types
        let { new_struct } = import! functions
        let { assert } = import! std.test
        let { index, len } = import! std.array
        
        let { string, number, vec } = new_struct ()

        assert (string == "hello")
        assert (number == 1)
        assert (len vec == 3)
        assert (index vec 0 == 1.0)
        assert (index vec 1 == 2.0)
        assert (index vec 2 == 3.0)
    "#;

    if let Err(why) = compiler.run_expr::<()>(&vm, "test", script) {
        panic!("{}", why);
    }
}

#[derive(Pushable, VmType)]
#[gluon(vm_type = "types.GenericStruct")]
struct GenericStruct<T> {
    generic: T,
    other: u32,
}

fn load_generic_struct_mod(vm: &Thread) -> vm::Result<ExternModule> {
    let module = record! {
        new_generic_struct => primitive!(1, new_generic_struct),
    };

    ExternModule::new(vm, module)
}

fn new_generic_struct(
    arg: OpaqueValue<RootedThread, A>,
) -> GenericStruct<OpaqueValue<RootedThread, A>> {
    GenericStruct {
        generic: arg,
        other: 2012,
    }
}

#[test]
fn generic_struct() {
    let vm = new_vm();
    let compiler = Compiler::new();

    let src = r#"
        type GenericStruct a = { generic: a, other: u32 }
        { GenericStruct }
    "#;

    compiler.load_script(&vm, "types", &src).unwrap();
    import::add_extern_module(&vm, "functions", load_generic_struct_mod);

    let script = r#"
        let { GenericStruct } = import! types
        let { new_generic_struct } = import! functions
        let { assert } = import! std.test

        let { generic, other } = new_generic_struct "hi rust"

        assert (generic == "hi rust")
        assert (other == 2012)

        let { generic, other } = new_generic_struct 3.14

        assert (generic == 3.14)
        assert (other == 2012)
    "#;

    if let Err(why) = compiler.run_expr::<()>(&vm, "test", script) {
        panic!("{}", why);
    }
}

#[derive(Pushable, VmType, Serialize, Deserialize)]
#[gluon(vm_type = "types.LifetimeStruct")]
struct LifetimeStruct<'a> {
    string: &'a str,
    other: f64,
}

fn load_lifetime_struct_mod(vm: &Thread) -> vm::Result<ExternModule> {
    let module = record! {
        new_lifetime_struct => primitive!(1, new_lifetime_struct),
    };

    ExternModule::new(vm, module)
}

fn new_lifetime_struct<'a>(_: ()) -> LifetimeStruct<'a> {
    LifetimeStruct {
        string: "I'm borrowed",
        other: 6.6,
    }
}

#[test]
fn lifetime_struct() {
    let vm = new_vm();
    let compiler = Compiler::new();

    // make_source doesn't work with borrowed strings
    let src = r#"
        type LifetimeStruct = { string: String, other: Float }
        { LifetimeStruct }
    "#;

    compiler.load_script(&vm, "types", &src).unwrap();
    import::add_extern_module(&vm, "functions", load_lifetime_struct_mod);

    let script = r#"
        let { LifetimeStruct } = import! types
        let { new_lifetime_struct } = import! functions
        let { assert } = import! std.test

        let { string, other } = new_lifetime_struct ()

        assert (string == "I'm borrowed")
        assert (other == 6.6)
    "#;

    if let Err(why) = compiler.run_expr::<()>(&vm, "test", script) {
        panic!("{}", why);
    }
}

#[derive(Pushable, VmType, Serialize, Deserialize)]
#[gluon(vm_type = "types.Enum")]
enum Enum {
    Nothing,
    Tuple(u32, u32),
    Struct { key: String, value: String },
}

fn load_enum_mod(vm: &Thread) -> vm::Result<ExternModule> {
    let module = record! {
        new_enum => primitive!(1, new_enum),
    };

    ExternModule::new(vm, module)
}

fn new_enum(tag: u32) -> Enum {
    match tag {
        0 => Enum::Nothing,
        1 => Enum::Tuple(1920, 1080),
        _ => Enum::Struct {
            key: "under the doormat".to_owned(),
            value: "lots of gold".to_owned(),
        },
    }
}

#[test]
fn normal_enum() {
    let vm = new_vm();
    let compiler = Compiler::new();

    let src = api::typ::make_source::<Enum>(&vm).unwrap();
    compiler.load_script(&vm, "types", &src).unwrap();
    import::add_extern_module(&vm, "functions", load_enum_mod);

    let script = r#"
        let { Enum } = import! types
        let { new_enum } = import! functions
        let { assert } = import! std.test

        let assert_enum enum tag =
            let actual_tag =
                match enum with
                | Nothing -> 0
                | Tuple x y ->
                    assert (x == 1920)
                    assert (y == 1080)
                    1
                | Struct key value ->
                    assert (key == "under the doormat")
                    assert (value == "lots of gold")
                    2
            
            assert (tag == actual_tag)
        
        assert_enum (new_enum 0) 0
        assert_enum (new_enum 1) 1
        assert_enum (new_enum 2) 2
    "#;

    if let Err(why) = compiler.run_expr::<()>(&vm, "test", script) {
        panic!("{}", why);
    }
}
