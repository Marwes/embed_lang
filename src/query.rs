use std::{
    borrow::Cow,
    result::Result as StdResult,
    sync::{Arc, Mutex, MutexGuard},
};

use salsa::Database;

use {
    base::{
        ast::{self, Expr, SpannedExpr, TypedIdent},
        error::Errors,
        fnv::FnvMap,
        kind::{ArcKind, KindEnv},
        metadata::{Metadata, MetadataEnv},
        pos::BytePos,
        symbol::{Name, Symbol, SymbolRef},
        types::{Alias, ArcType, NullInterner, PrimitiveEnv, Type, TypeEnv, TypeExt},
    },
    vm::{
        self,
        api::ValueRef,
        compiler::{CompilerEnv, Variable},
        macros,
        thread::{RootedThread, Thread},
        vm::Global,
        Variants,
    },
};

use crate::{compiler_pipeline::*, Compiler, Error, Result, Settings};

#[derive(Default)]
pub(crate) struct State {
    pub(crate) code_map: codespan::CodeMap,
    pub(crate) index_map: FnvMap<String, BytePos>,
    pub(crate) errors: Errors<Error>,
    pub(crate) module_states: FnvMap<String, usize>,
}

impl State {
    pub fn update_filemap<S>(&mut self, file: &str, source: S) -> Option<Arc<codespan::FileMap>>
    where
        S: Into<String>,
    {
        let index_map = &mut self.index_map;
        let code_map = &mut self.code_map;
        index_map
            .get(file)
            .cloned()
            .and_then(|i| code_map.update(i, source.into()))
            .map(|file_map| {
                index_map.insert(file.into(), file_map.span().start());
                file_map
            })
    }

    pub fn get_filemap(&self, file: &str) -> Option<&Arc<codespan::FileMap>> {
        self.index_map
            .get(file)
            .and_then(move |i| self.code_map.find_file(*i))
    }

    #[doc(hidden)]
    pub fn add_filemap<S>(&mut self, file: &str, source: S) -> Arc<codespan::FileMap>
    where
        S: AsRef<str> + Into<String>,
    {
        match self.get_filemap(file) {
            Some(file_map) if file_map.src() == source.as_ref() => return file_map.clone(),
            _ => (),
        }
        let file_map = self.code_map.add_filemap(
            codespan::FileName::virtual_(file.to_string()),
            source.into(),
        );
        self.index_map.insert(file.into(), file_map.span().start());
        file_map
    }
}

#[salsa::database(CompileStorage)]
pub struct CompilerDatabase {
    runtime: salsa::Runtime<CompilerDatabase>,
    pub(crate) state: Arc<Mutex<State>>,
    // This is only set after calling snapshot on `Import`. `Import` itself can't contain a
    // `RootedThread` as that would create a cycle
    pub(crate) thread: Option<RootedThread>,
}

impl crate::query::CompilationBase for CompilerDatabase {
    fn compiler(&self) -> &Self {
        self
    }

    fn thread(&self) -> &Thread {
        self.thread
            .as_ref()
            .expect("Thread was not set in the compiler")
    }

    fn new_module(&self, module: String, contents: &str) {
        let mut state = self.state();
        state.add_filemap(&module, &contents[..]);
        state
            .module_states
            .entry(module)
            .and_modify(|v| *v += 1)
            .or_default();
    }
    fn report_errors(&self, error: &mut Iterator<Item = Error>) {
        self.state().errors.extend(error);
    }
}

impl salsa::Database for CompilerDatabase {
    fn salsa_runtime(&self) -> &salsa::Runtime<Self> {
        &self.runtime
    }
}

impl salsa::ParallelDatabase for CompilerDatabase {
    fn snapshot(&self) -> salsa::Snapshot<Self> {
        salsa::Snapshot::new(Self {
            runtime: self.runtime.snapshot(self),
            state: self.state.clone(),
            thread: self.thread.clone(),
        })
    }
}

impl CompilerDatabase {
    pub(crate) fn new_base(thread: Option<RootedThread>) -> CompilerDatabase {
        let mut compiler = CompilerDatabase {
            state: Default::default(),
            runtime: Default::default(),
            thread,
        };
        compiler.set_compiler_settings(Default::default());
        compiler.set_module_states(Default::default());
        compiler
    }

    pub(crate) fn state(&self) -> MutexGuard<State> {
        self.state.lock().unwrap()
    }

    pub fn code_map(&self) -> codespan::CodeMap {
        self.state().code_map.clone()
    }

    pub fn update_filemap<S>(&self, file: &str, source: S) -> Option<Arc<codespan::FileMap>>
    where
        S: Into<String>,
    {
        self.state().update_filemap(file, source)
    }

    pub fn get_filemap(&self, file: &str) -> Option<Arc<codespan::FileMap>> {
        self.state().get_filemap(file).cloned()
    }

    #[doc(hidden)]
    pub fn add_filemap<S>(&self, file: &str, source: S) -> Arc<codespan::FileMap>
    where
        S: AsRef<str> + Into<String>,
    {
        self.state().add_filemap(file, source)
    }

    pub(crate) fn collect_garbage(&self) {
        let strategy = salsa::SweepStrategy::default()
            .discard_values()
            .sweep_all_revisions();

        self.query(ModuleTextQuery).sweep(strategy);
        self.query(TypecheckedModuleQuery).sweep(strategy);
        self.query(CompiledModuleQuery).sweep(strategy);
    }
}

pub(crate) trait CompilationBase: salsa::Database {
    fn compiler(&self) -> &CompilerDatabase;
    fn thread(&self) -> &Thread;
    fn new_module(&self, module: String, contents: &str);
    fn report_errors(&self, error: &mut Iterator<Item = Error>);
}

#[salsa::query_group(CompileStorage)]
pub(crate) trait Compilation: CompilationBase {
    #[salsa::input]
    fn compiler_settings(&self) -> Settings;

    #[salsa::input]
    fn module_states(&self) -> Arc<FnvMap<String, usize>>;

    fn module_state(&self, module: String) -> usize;

    fn module_text(&self, module: String) -> StdResult<Arc<Cow<'static, str>>, Error>;

    fn typechecked_module(
        &self,
        module: String,
        expected_type: Option<ArcType>,
    ) -> StdResult<TypecheckValue<Arc<SpannedExpr<Symbol>>>, Error>;

    fn compiled_module(
        &self,
        module: String,
    ) -> StdResult<CompileValue<Arc<SpannedExpr<Symbol>>>, Error>;

    #[salsa::cycle]
    fn import(&self, module: String) -> StdResult<Expr<Symbol>, Error>;

    fn globals(&self) -> Arc<FnvMap<String, Global>>;

    #[salsa::volatile]
    fn global(&self, name: String) -> Option<Global>;
}

fn module_state(db: &impl Compilation, module: String) -> usize {
    db.module_states().get(&module).cloned().unwrap_or_default()
}

fn module_text(db: &impl Compilation, module: String) -> StdResult<Arc<Cow<'static, str>>, Error> {
    // We just need to depend on updates to the state, we don't care what it is
    db.module_state(module.clone());

    let mut filename = module.replace(".", "/");
    filename.push_str(".glu");

    let contents = Arc::new(
        crate::get_import(db.thread())
            .get_module_source(&module, &filename)
            .map_err(macros::Error::new)?,
    );
    db.new_module(module, &contents);
    Ok(contents)
}

fn typechecked_module(
    db: &impl Compilation,
    module: String,
    expected_type: Option<ArcType>,
) -> StdResult<TypecheckValue<Arc<SpannedExpr<Symbol>>>, Error> {
    let text = db.module_text(module.clone())?;

    let thread = db.thread();
    text.typecheck_expected(
        &mut Compiler::new().module_compiler(db.compiler()),
        thread,
        &module,
        &text,
        expected_type.as_ref(),
    )
    .map(|value| value.map(Arc::new))
    .map_err(|(_, err)| err)
}

fn compiled_module(
    db: &impl Compilation,
    module: String,
) -> StdResult<CompileValue<Arc<SpannedExpr<Symbol>>>, Error> {
    let text = db.module_text(module.clone())?;
    let value = db.typechecked_module(module.clone(), None)?;

    let thread = db.thread();
    value.compile(
        &mut Compiler::new().module_compiler(db.compiler()),
        thread,
        &module,
        &text,
        None::<ArcType>,
    )
}

fn import(db: &impl Compilation, modulename: String) -> StdResult<Expr<Symbol>, Error> {
    let compiler = db.compiler();
    let thread = db.thread();

    let name = Symbol::from(if modulename.starts_with('@') {
        modulename.clone()
    } else {
        format!("@{}", modulename)
    });
    let result = crate::get_import(thread)
        .load_module(
            &mut Compiler::new().module_compiler(compiler),
            thread,
            &name,
        )
        .map_err(|(_, err)| err);

    compiler.collect_garbage();

    result?;

    Ok(Expr::Ident(TypedIdent::new(name)))
}

fn globals(db: &impl Compilation) -> Arc<FnvMap<String, Global>> {
    let compiler = db.compiler();
    let vm = db.thread();
    let globals = db
        .module_states()
        .keys()
        .map(|name| {
            let compile_value = db.compiled_module(name.clone());
            let execute_value = Executable::load_script(
                compile_value,
                &mut Compiler::new().module_compiler(compiler),
                vm,
                &name,
                "",
                None,
            )
            .expect("ICE: Script loading failed unexpectedly");

            Global {
                id: execute_value.id,
                typ: execute_value.typ,
                metadata: execute_value.metadata,
                value: execute_value.value,
            }
        })
        .collect();
    Arc::new(globals)
}

fn global(db: &impl Compilation, name: String) -> Option<Global> {
    db.globals().get(&name).cloned()
}

impl CompilerEnv for CompilerDatabase {
    fn find_var(&self, id: &Symbol) -> Option<(Variable<Symbol>, ArcType)> {
        self.global(id.definition_name().into())
            .map(|g| (Variable::UpVar(g.id.clone()), g.typ.clone()))
    }
}

impl KindEnv for CompilerDatabase {
    fn find_kind(&self, type_name: &SymbolRef) -> Option<ArcKind> {
        None
    }
}

impl TypeEnv for CompilerDatabase {
    type Type = ArcType;

    fn find_type(&self, id: &SymbolRef) -> Option<ArcType> {
        self.global(id.definition_name().into())
            .map(|g| g.typ.clone())
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<Alias<Symbol, ArcType>> {
        None
    }
}

impl PrimitiveEnv for CompilerDatabase {
    fn get_bool(&self) -> ArcType {
        self.find_type_info("std.types.Bool")
            .expect("std.types.Bool")
    }
}

impl MetadataEnv for CompilerDatabase {
    fn get_metadata(&self, id: &SymbolRef) -> Option<Arc<Metadata>> {
        self.global(id.definition_name().into())
            .map(|g| g.metadata.clone())
    }
}

fn map_cow_option<T, U, F>(cow: Cow<T>, f: F) -> Option<Cow<U>>
where
    T: Clone,
    U: Clone,
    F: FnOnce(&T) -> Option<&U>,
{
    match cow {
        Cow::Borrowed(b) => f(b).map(Cow::Borrowed),
        Cow::Owned(o) => f(&o).map(|u| Cow::Owned(u.clone())),
    }
}

impl CompilerDatabase {
    pub fn find_type_info(&self, name: &str) -> Result<Cow<Alias<Symbol, ArcType>>> {
        let name = Name::new(name);
        let module_str = name.module().as_str();
        if module_str == "" {
            return match self.type_infos.id_to_type.get(name.as_str()) {
                Some(alias) => Ok(Cow::Borrowed(alias)),
                None => Err(vm::Error::UndefinedBinding(name.as_str().into()).into()),
            };
        }
        let (_, typ) = self.get_binding(name.module().as_str())?;
        let maybe_type_info = map_cow_option(typ.clone(), |typ| {
            let field_name = name.name();
            typ.type_field_iter()
                .find(|field| field.name.as_ref() == field_name.as_str())
                .map(|field| &field.typ)
        });
        maybe_type_info.ok_or_else(move || {
            vm::Error::UndefinedField(typ.into_owned(), name.name().as_str().into()).into()
        })
    }

    fn get_global<'s, 'n>(&'s self, name: &'n str) -> Option<(&'n Name, Global)> {
        let mut module = Name::new(name.trim_start_matches('@'));
        let global;
        // Try to find a global by successively reducing the module path
        // Input: "x.y.z.w"
        // Test: "x.y.z"
        // Test: "x.y"
        // Test: "x"
        // Test: -> Error
        loop {
            if module.as_str() == "" {
                return None;
            }
            if let Some(g) = self.global(module.as_str().into()) {
                global = g;
                break;
            }
            module = module.module();
        }
        let remaining_offset = ::std::cmp::min(name.len(), module.as_str().len() + 1); //Add 1 byte for the '.'
        let remaining_fields = Name::new(&name[remaining_offset..]);
        Some((remaining_fields, global))
    }

    pub fn get_binding(&self, name: &str) -> Result<(Variants, Cow<ArcType>)> {
        use crate::base::resolve;

        let (remaining_fields, global) = self
            .get_global(name)
            .ok_or_else(|| vm::Error::UndefinedBinding(name.into()))?;

        if remaining_fields.as_str().is_empty() {
            // No fields left
            return Ok((
                unsafe { Variants::new(&global.value) },
                Cow::Borrowed(&global.typ),
            ));
        }

        let mut typ = Cow::Borrowed(&global.typ);
        let mut value = unsafe { Variants::new(&global.value) };

        for mut field_name in remaining_fields.components() {
            if field_name.starts_with('(') && field_name.ends_with(')') {
                field_name = &field_name[1..field_name.len() - 1];
            } else if field_name.contains(ast::is_operator_char) {
                return Err(vm::Error::Message(format!(
                    "Operators cannot be used as fields \
                     directly. To access an operator field, \
                     enclose the operator with parentheses \
                     before passing it in. (test.(+) instead of \
                     test.+)"
                ))
                .into());
            }
            typ = match typ {
                Cow::Borrowed(typ) => resolve::remove_aliases_cow(self, &mut NullInterner, typ),
                Cow::Owned(typ) => {
                    Cow::Owned(resolve::remove_aliases(self, &mut NullInterner, typ))
                }
            };
            // HACK Can't return the data directly due to the use of cow on the type
            let next_type = map_cow_option(typ.clone(), |typ| {
                typ.row_iter()
                    .enumerate()
                    .find(|&(_, field)| field.name.as_ref() == field_name)
                    .map(|(index, field)| match value.as_ref() {
                        ValueRef::Data(data) => {
                            value = data.get_variant(index).unwrap();
                            &field.typ
                        }
                        _ => ice!("Unexpected value {:?}", value),
                    })
            });
            typ = next_type.ok_or_else(move || {
                vm::Error::UndefinedField(typ.into_owned(), field_name.into())
            })?;
        }
        Ok((value, typ))
    }

    pub fn get_metadata(&self, name_str: &str) -> Result<Arc<Metadata>> {
        self.get_metadata_(name_str)
            .ok_or_else(|| vm::Error::MetadataDoesNotExist(name_str.into()).into())
    }

    fn get_metadata_(&self, name_str: &str) -> Option<Arc<Metadata>> {
        let (remaining, global) = self.get_global(name_str)?;

        let mut metadata = &global.metadata;
        for field_name in remaining.components() {
            metadata = metadata.module.get(field_name)?
        }
        Some(metadata.clone())
    }
}
