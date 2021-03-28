//! This crate contains contains the implementation for the gluon programming language.
//!
//! Gluon is a programming language suitable for embedding in an existing application to extend its
//! behaviour. For information about how to use this library the best resource currently is the
//! [tutorial](http://gluon-lang.org/book/index.html) which contains examples
//! on how to write gluon programs as well as how to run them using this library.
#![doc(html_root_url = "https://docs.rs/gluon/0.17.2")] // # GLUON
#![recursion_limit = "128"]
#[cfg(test)]
extern crate env_logger;

pub extern crate either;
#[macro_use]
extern crate log;
#[macro_use]
extern crate quick_error;

#[cfg(feature = "serde_derive_state")]
#[macro_use]
extern crate serde_derive_state;
#[cfg(feature = "serde")]
extern crate serde_state as serde;

#[macro_use]
pub extern crate gluon_base as base;
pub extern crate gluon_check as check;
extern crate gluon_format as format;
pub extern crate gluon_parser as parser;
#[macro_use]
extern crate gluon_codegen;
#[macro_use]
pub extern crate gluon_vm as vm;

pub use salsa;

macro_rules! try_future {
    ($e:expr) => {
        try_future!($e, Box::pin)
    };
    ($e:expr, $f:expr) => {
        match $e {
            Ok(x) => x,
            Err(err) => return $f(::futures::future::err(err.into())),
        }
    };
}

pub mod compiler_pipeline;
#[macro_use]
pub mod import;
pub mod lift_io;
#[doc(hidden)]
pub mod query;
pub mod std_lib;

pub use crate::vm::{
    field_decl, primitive, record, record_p, record_type,
    thread::{RootedThread, Thread},
};

use either::Either;

use std as real_std;
use std::{
    env, error::Error as StdError, fmt, path::PathBuf, result::Result as StdResult, sync::Arc,
};

use crate::base::{
    ast::{self, OwnedExpr, SpannedExpr},
    error::{Errors, InFile},
    filename_to_module,
    metadata::Metadata,
    pos::{BytePos, Span, Spanned},
    source::FileId,
    symbol::{Symbol, Symbols},
    types::{ArcType, TypeCache},
};

use crate::format::Formatter;

use crate::vm::{
    api::{Getable, Hole, OpaqueValue, VmType},
    compiler::CompiledModule,
    macros,
};

use crate::{
    compiler_pipeline::*,
    import::{add_extern_module, add_extern_module_with_deps, DefaultImporter, Import},
    query::{AsyncCompilation, Compilation, CompilationBase, CompilerDatabase},
};

quick_error! {
/// Error type wrapping all possible errors that can be generated from gluon
#[derive(Debug, Eq, PartialEq, Hash, Clone)]
#[allow(deprecated)]
pub enum Error {
    /// Error found when parsing gluon code
    Parse(err: InFile<parser::Error>) {
        display("{}", err)
        from()
    }
    /// Error found when typechecking gluon code
    Typecheck(err: InFile<check::typecheck::HelpError<Symbol>>) {
        display("{}", err)
        from()
    }
    /// Error found when performing an IO action such as loading a file
    IO(err: IoError) {
        display("{}", err)
        from()
    }
    /// Error found when executing code in the virtual machine
    VM(err: crate::vm::Error) {
        display("{}", err)
        from()
    }
    /// Error found when expanding macros
    Macro(err: InFile<macros::Error>) {
        display("{}", err)
        from()
    }
    Other(err: macros::Error) {
        display("{}", err)
        from()
    }
    /// Multiple errors where found
    Multiple(err: Errors<Error>) {
        display("{}", err)
    }
}
}

impl From<std::io::Error> for Error {
    fn from(err: std::io::Error) -> Self {
        Error::IO(err.into())
    }
}

impl Error {
    pub fn merge(self, other: Self) -> Self {
        match (self, other) {
            (Error::Multiple(mut errors), Error::Multiple(err)) => {
                errors.extend(err);
                Error::Multiple(errors)
            }
            (Error::Multiple(mut errors), err) | (err, Error::Multiple(mut errors)) => {
                errors.push(err);
                Error::Multiple(errors)
            }
            (l, r) => Error::Multiple(vec![l, r].into_iter().collect()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct IoError(Arc<std::io::Error>);

impl fmt::Display for IoError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl StdError for IoError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        self.0.source()
    }
}

impl<E> From<E> for IoError
where
    std::io::Error: From<E>,
{
    fn from(err: E) -> Self {
        IoError(Arc::new(err.into()))
    }
}

impl Eq for IoError {}

impl PartialEq for IoError {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(&*self.0, &*other.0)
    }
}

impl std::hash::Hash for IoError {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        (&*self.0 as *const std::io::Error).hash(state)
    }
}

impl base::error::AsDiagnostic for Error {
    fn as_diagnostic(
        &self,
        _map: &base::source::CodeMap,
    ) -> codespan_reporting::diagnostic::Diagnostic<FileId> {
        codespan_reporting::diagnostic::Diagnostic::error().with_message(self.to_string())
    }
}

impl From<String> for Error {
    fn from(s: String) -> Self {
        Error::VM(s.into())
    }
}

impl From<Errors<Spanned<macros::Error, BytePos>>> for Error {
    fn from(mut errors: Errors<Spanned<macros::Error, BytePos>>) -> Error {
        if errors.len() == 1 {
            let err = errors.pop().unwrap();
            match err.value.downcast::<Error>() {
                Ok(err) => *err,
                Err(err) => Error::Other(err),
            }
        } else {
            Error::Multiple(
                errors
                    .into_iter()
                    .map(|err| match err.value.downcast::<Error>() {
                        Ok(err) => *err,
                        Err(err) => Error::Other(err),
                    })
                    .collect(),
            )
        }
    }
}

impl From<Errors<Error>> for Error {
    fn from(mut errors: Errors<Error>) -> Error {
        if errors.len() == 1 {
            errors.pop().unwrap()
        } else {
            errors = errors
                .into_iter()
                .flat_map(|err| match err {
                    Error::Multiple(errors) => Either::Left(errors.into_iter()),
                    err => Either::Right(Some(err).into_iter()),
                })
                .collect();

            Error::Multiple(errors)
        }
    }
}

impl Error {
    pub fn emit_string(&self) -> ::std::io::Result<String> {
        let mut output = Vec::new();
        self.emit(&mut codespan_reporting::term::termcolor::NoColor::new(
            &mut output,
        ))?;
        Ok(String::from_utf8(output).unwrap())
    }

    pub fn emit(
        &self,
        writer: &mut dyn codespan_reporting::term::termcolor::WriteColor,
    ) -> ::std::io::Result<()> {
        match self {
            Error::Parse(err) => err.emit(writer),
            Error::Typecheck(err) => err.emit(writer),
            Error::IO(err) => write!(writer, "{}", err),
            Error::VM(err) => write!(writer, "{}", err),
            Error::Macro(err) => err.emit(writer),
            Error::Other(err) => write!(writer, "{}", err),
            Error::Multiple(errors) => {
                for err in errors {
                    err.emit(writer)?;
                }
                Ok(())
            }
        }
    }
}

/// Type alias for results returned by gluon
pub type Result<T> = StdResult<T, Error>;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Settings {
    pub implicit_prelude: bool,
    pub emit_debug_info: bool,
    pub full_metadata: bool,
    pub use_standard_lib: bool,
    pub optimize: bool,
    pub run_io: bool,
}

impl Default for Settings {
    fn default() -> Self {
        Self {
            implicit_prelude: true,
            emit_debug_info: true,
            full_metadata: false,
            use_standard_lib: true,
            optimize: true,
            run_io: false,
        }
    }
}

#[doc(hidden)]
pub trait IntoDb<'a, 'b> {
    fn into_db(self) -> salsa::OwnedDb<'a, dyn Compilation + 'b>;
}

impl<'a, 'b> IntoDb<'a, 'b> for &'a mut salsa::OwnedDb<'_, dyn Compilation + 'b> {
    fn into_db(self) -> salsa::OwnedDb<'a, dyn Compilation + 'b> {
        self.into()
    }
}

impl<'a, 'b> IntoDb<'a, 'b> for salsa::OwnedDb<'a, dyn Compilation + 'b> {
    fn into_db(self) -> salsa::OwnedDb<'a, dyn Compilation + 'b> {
        self
    }
}

impl<'a, 'b> IntoDb<'a, 'b> for &'a mut salsa::Snapshot<CompilerDatabase> {
    fn into_db(self) -> salsa::OwnedDb<'a, dyn Compilation + 'b> {
        salsa::cast_owned_db!(salsa::OwnedDb::<CompilerDatabase>::from(self) => &mut dyn Compilation)
    }
}

pub struct ModuleCompiler<'a, 'b> {
    pub database: salsa::OwnedDb<'a, dyn Compilation + 'b>,
    symbols: Symbols,
}

impl<'a, 'b> ModuleCompiler<'a, 'b> {
    fn new(database: impl IntoDb<'a, 'b>) -> Self {
        Self {
            database: database.into_db(),
            symbols: Symbols::default(),
        }
    }
}

impl<'a, 'b> std::ops::Deref for ModuleCompiler<'a, 'b> {
    type Target = salsa::OwnedDb<'a, dyn Compilation + 'b>;
    fn deref(&self) -> &Self::Target {
        &self.database
    }
}

impl std::ops::DerefMut for ModuleCompiler<'_, '_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.database
    }
}

macro_rules! option {
($(#[$attr:meta])* $name: ident $set_name: ident : $typ: ty) => {
    $(#[$attr])*
    pub fn $name(mut self, $name: $typ) -> Self {
        self.$name = $name;
        self
    }

    pub fn $set_name(&mut self, $name: $typ) {
        self.$name = $name;
    }
};
}

macro_rules! runtime_option {
($(#[$attr:meta])* $name: ident $set_name: ident : $typ: ty) => {
    $(#[$attr])*
    pub fn $name(mut self, $name: $typ) -> Self {
        self.$set_name($name);
        self
    }

    pub fn $set_name(&mut self, $name: $typ) {
        let mut settings = self.compiler_settings();
        settings.$name = $name;
        self.set_compiler_settings(settings);
    }
};
}

impl import::DatabaseMut {
    runtime_option! {
        /// Sets whether the implicit prelude should be include when compiling a file using this
        /// compiler (default: true)
        implicit_prelude set_implicit_prelude: bool
    }

    runtime_option! {
        /// Sets whether the compiler should emit debug information such as source maps and variable
        /// names.
        /// (default: true)
        emit_debug_info set_emit_debug_info: bool
    }

    runtime_option! {
        /// Sets whether full metadata is required
        /// (default: false)
        full_metadata set_full_metadata: bool
    }

    runtime_option! {
        /// Sets whether internal standard library is searched for requested modules
        /// (default: true)
        use_standard_lib set_use_standard_lib: bool
    }

    runtime_option! {
        /// Whether the bytecode should be optimized
        /// (default: true)
        optimize set_optimize: bool
    }

    runtime_option! {
        /// Sets whether `IO` expressions are evaluated.
        /// (default: false)
        run_io set_run_io: bool
    }
}

/// Extension trait which provides methods to load and execute gluon code

#[async_trait::async_trait]
pub trait ThreadExt: Send + Sync {
    fn get_database(&self) -> salsa::Snapshot<CompilerDatabase>;
    fn get_database_mut(&self) -> import::DatabaseMut;

    fn run_io(&self, run: bool) {
        self.get_database_mut().run_io(run);
    }

    #[doc(hidden)]
    fn thread(&self) -> &Thread;

    fn module_compiler<'a, 'b>(&'a self, database: impl IntoDb<'a, 'b>) -> ModuleCompiler<'a, 'b> {
        ModuleCompiler::new(database)
    }

    /// Parse `expr_str`, returning an expression if successful
    fn parse_expr(
        &self,
        type_cache: &TypeCache<Symbol, ArcType>,
        file: &str,
        expr_str: &str,
    ) -> StdResult<OwnedExpr<Symbol>, InFile<parser::Error>> {
        Ok(self.parse_partial_expr(type_cache, file, expr_str)?)
    }

    /// Parse `input`, returning an expression if successful
    fn parse_partial_expr(
        &self,
        type_cache: &TypeCache<Symbol, ArcType>,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<OwnedExpr<Symbol>, InFile<parser::Error>> {
        let vm = self.thread();
        parse_expr(
            &mut ModuleCompiler::new(&mut vm.get_database()),
            type_cache,
            file,
            expr_str,
        )
    }

    /// Parse and typecheck `expr_str` returning the typechecked expression and type of the
    /// expression
    async fn typecheck_expr(
        &self,
        file: &str,
        expr_str: &str,
        expr: &mut OwnedExpr<Symbol>,
    ) -> Result<ArcType> {
        let vm = self.thread();
        Ok(expr
            .typecheck_expected(
                &mut ModuleCompiler::new(&mut vm.get_database()),
                vm,
                file,
                expr_str,
                None,
            )
            .await
            .map(|result| result.typ)?)
    }

    fn typecheck_str(
        &self,
        file: &str,
        expr_str: &str,
        expected_type: Option<&ArcType>,
    ) -> Result<(Arc<OwnedExpr<Symbol>>, ArcType)> {
        futures::executor::block_on(self.typecheck_str_async(file, expr_str, expected_type))
    }

    async fn typecheck_str_async(
        &self,
        file: &str,
        expr_str: &str,
        expected_type: Option<&ArcType>,
    ) -> Result<(Arc<OwnedExpr<Symbol>>, ArcType)> {
        let vm = self.thread();
        {
            let mut db = vm.get_database_mut();
            db.add_module(file.into(), expr_str.into());
        }
        let mut db = vm.get_database();

        let TypecheckValue { expr, typ, .. } = db
            .typechecked_source_module(file.into(), expected_type.cloned())
            .await?;

        // Ensure the type is stored in the database so we can collect typechecked_module later
        db.module_type(file.into(), None).await?;
        db.module_metadata(file.into(), None).await?;

        Ok((expr, typ))
    }

    /// Compiles `expr` into a function which can be added and run by the `vm`
    async fn compile_script(
        &self,
        filename: &str,
        expr_str: &str,
        expr: &OwnedExpr<Symbol>,
    ) -> Result<CompiledModule> {
        let vm = self.thread();
        TypecheckValue {
            expr,
            typ: vm.global_env().type_cache().hole(),
            metadata: Default::default(),
            metadata_map: Default::default(),
        }
        .compile(
            &mut ModuleCompiler::new(&mut vm.get_database()),
            vm,
            filename,
            expr_str,
            (),
        )
        .await
        .map(|result| result.module)
    }

    /// Compiles the source code `expr_str` into bytecode serialized using `serializer`
    #[cfg(feature = "serialization")]
    async fn compile_to_bytecode<S>(
        &self,
        name: &str,
        expr_str: &str,
        serializer: S,
    ) -> StdResult<S::Ok, Either<Error, S::Error>>
    where
        S: serde::Serializer + Send,
        S::Error: 'static,
    {
        let thread = self.thread();
        compile_to(
            expr_str,
            &mut ModuleCompiler::new(&mut thread.get_database()),
            &thread,
            name,
            expr_str,
            None,
            serializer,
        )
        .await
    }

    /// Loads bytecode from a `Deserializer` and stores it into the module `name`.
    ///
    /// `load_script` is equivalent to `compile_to_bytecode` followed by `load_bytecode`
    #[cfg(feature = "serialization")]
    async fn load_bytecode<'vm, D, E>(&self, name: &str, deserializer: D) -> Result<()>
    where
        D: for<'de> serde::Deserializer<'de, Error = E> + Send,
        E: Send + Sync,
    {
        let thread = self.thread();
        Precompiled(deserializer)
            .load_script(
                &mut ModuleCompiler::new(&mut thread.get_database()),
                thread,
                name,
                "",
                (),
            )
            .await
    }

    /// Parses and typechecks `expr_str` followed by extracting metadata from the created
    /// expression
    async fn extract_metadata(
        &self,
        file: &str,
        expr_str: &str,
    ) -> Result<(Arc<OwnedExpr<Symbol>>, ArcType, Arc<Metadata>)> {
        use crate::check::metadata;

        let module_name = filename_to_module(file);
        let vm = self.thread();
        {
            let mut db = vm.get_database_mut();
            db.add_module(module_name.clone(), expr_str.into());
        }

        let mut db = vm.get_database();

        let TypecheckValue {
            expr,
            typ,
            metadata,
            ..
        } = db
            .typechecked_source_module(module_name.clone(), None)
            .await?;

        // Ensure the type is stored in the database so we can collect typechecked_module later
        db.module_type(module_name.clone(), None).await?;
        db.module_metadata(module_name.clone(), None).await?;

        if db.compiler_settings().full_metadata {
            Ok((expr, typ, metadata))
        } else {
            let (metadata, _) = metadata::metadata(&vm.get_env(), &expr.expr());
            Ok((expr, typ, metadata))
        }
    }

    /// Compiles `input` and if it is successful runs the resulting code and stores the resulting
    /// value in the vm.
    ///
    /// If at any point the function fails the resulting error is returned and nothing is added to
    /// the VM.
    fn load_script(&self, filename: &str, input: &str) -> Result<()> {
        futures::executor::block_on(self.load_script_async(filename, input))
    }

    async fn load_script_async(&self, filename: &str, input: &str) -> Result<()> {
        let module_name = filename_to_module(filename);

        let vm = self.thread();
        {
            let mut db = vm.get_database_mut();
            db.add_module(module_name.clone(), input.into());
        }
        let mut db = vm.get_database();

        db.import(module_name)
            .await
            .map(|_| ())
            .map_err(|err| err.error)
    }

    /// Loads `filename` and compiles and runs its input by calling `load_script`
    fn load_file<'vm>(&'vm self, filename: &str) -> Result<()> {
        futures::executor::block_on(self.load_file_async(filename))
    }

    async fn load_file_async<'vm>(&self, filename: &str) -> Result<()> {
        let vm = self.thread();
        // Use the import macro's path resolution if it exists so that we mimick the import
        // macro as close as possible
        let import = get_import(vm);
        let module_name = Symbol::from(format!("@{}", filename_to_module(filename)));
        import
            .load_module(
                &mut ModuleCompiler::new(&mut import.snapshot(vm.root_thread())),
                vm,
                &module_name,
            )
            .await?;
        Ok(())
    }

    /// Compiles and runs the expression in `expr_str`. If successful the value from running the
    /// expression is returned
    ///
    /// # Examples
    ///
    /// Import from gluon's standard library and evaluate a string
    ///
    /// ```
    /// # use gluon::{new_vm, ThreadExt};
    /// # fn main() {
    /// # // Workaround stack overflow on appveyor
    /// # std::thread::Builder::new().stack_size(2_000_000).spawn(move || {
    /// let vm = new_vm();
    /// let (result, _) = vm
    ///     .run_expr::<String>(
    ///         "example",
    ///         " let string  = import! \"std/string.glu\" in string.trim \"  Hello world  \t\" "
    ///     )
    ///     .unwrap();
    /// assert_eq!(result, "Hello world");
    /// }).unwrap().join().unwrap()
    /// # }
    /// ```
    ///
    fn run_expr<'vm, T>(&'vm self, name: &str, expr_str: &str) -> Result<(T, ArcType)>
    where
        T: for<'value> Getable<'vm, 'value> + VmType + Send + 'vm,
    {
        futures::executor::block_on(self.run_expr_async(name, expr_str))
    }

    /// Compiles and runs the expression in `expr_str`. If successful the value from running the
    /// expression is returned
    ///
    /// # Examples
    ///
    /// Import from gluon's standard library and evaluate a string
    ///
    /// ```
    /// # use gluon::{new_vm_async, ThreadExt};
    /// # use gluon::base::types::Type;
    /// # #[tokio::main]
    /// # async fn main() {
    /// let vm = new_vm_async().await;
    /// let result = vm
    ///     .run_expr_async::<String>("example",
    ///         " let string  = import! \"std/string.glu\" in string.trim \"    Hello world  \t\" ")
    ///     .await
    ///     .unwrap();
    /// let expected = ("Hello world".to_string(), Type::string());
    ///
    /// assert_eq!(result, expected);
    /// }
    /// ```
    ///
    async fn run_expr_async<'vm, T>(&'vm self, name: &str, expr_str: &str) -> Result<(T, ArcType)>
    where
        T: for<'value> Getable<'vm, 'value> + VmType + Send + 'vm,
    {
        let vm = self.thread();
        let expected = T::make_type(&vm);

        let execute_value = expr_str
            .run_expr(
                &mut ModuleCompiler::new(&mut vm.get_database()),
                vm,
                name,
                expr_str,
                Some(&expected),
            )
            .await?;
        Ok((
            T::from_value(vm, execute_value.value.get_variant()),
            execute_value.typ,
        ))
    }

    fn format_expr(&self, formatter: &mut Formatter, file: &str, input: &str) -> Result<String> {
        futures::executor::block_on(self.format_expr_async(formatter, file, input))
    }

    async fn format_expr_async(
        &self,
        formatter: &mut Formatter,
        file: &str,
        input: &str,
    ) -> Result<String> {
        fn has_format_disabling_errors(file: &str, err: &Error) -> bool {
            match *err {
                Error::Multiple(ref errors) => errors
                    .iter()
                    .any(|err| has_format_disabling_errors(file, err)),
                Error::Parse(ref err) => err.source_name() == file,
                _ => false,
            }
        }

        let thread = self.thread();
        let mut db = thread.get_database();
        let mut compiler = ModuleCompiler::new(&mut db);
        let compiler = &mut compiler;

        let expr = match input.reparse_infix(compiler, thread, file, input).await {
            Ok(expr) => expr.expr,
            Err(Salvage {
                value: Some(expr),
                error,
            }) => {
                if has_format_disabling_errors(file, &error) {
                    return Err(error);
                }
                expr.expr
            }
            Err(Salvage { value: None, error }) => return Err(error),
        };

        let file_map = db.get_filemap(file).unwrap();
        let expr = skip_implicit_prelude(file_map.span(), &expr.expr());
        Ok(formatter.pretty_expr(&*file_map, expr))
    }
}

fn skip_implicit_prelude<'a, 'ast>(
    span: Span<BytePos>,
    mut l: &'a SpannedExpr<'ast, Symbol>,
) -> &'a SpannedExpr<'ast, Symbol> {
    loop {
        match l.value {
            ast::Expr::LetBindings(_, ref e) if !span.contains(l.span) => l = e,
            _ => break l,
        }
    }
}

impl ThreadExt for Thread {
    fn get_database(&self) -> salsa::Snapshot<CompilerDatabase> {
        self.global_env()
            .get_capability(self)
            .expect("Database is missing")
    }
    fn get_database_mut(&self) -> import::DatabaseMut {
        self.global_env()
            .get_capability(self)
            .expect("Database is missing")
    }
    fn thread(&self) -> &Thread {
        self
    }
}

fn get_import(vm: &Thread) -> Arc<dyn import::ImportApi> {
    vm.get_macros()
        .get_capability::<Arc<dyn import::ImportApi>>(vm)
        .unwrap_or_else(|| panic!("Missing import macro"))
}

impl ModuleCompiler<'_, '_> {
    pub fn mut_symbols(&mut self) -> &mut Symbols {
        &mut self.symbols
    }

    fn include_implicit_prelude<'ast>(
        &mut self,
        arena: ast::ArenaRef<'_, 'ast, Symbol>,
        type_cache: &TypeCache<Symbol, ArcType>,
        name: &str,
        expr: &mut SpannedExpr<'ast, Symbol>,
    ) {
        use std::mem;
        if name == "std.prelude" {
            return;
        }

        let prelude_expr = parse_expr_inner(arena, self, type_cache, "", PRELUDE).unwrap();
        let original_expr = mem::replace(expr, prelude_expr);

        // Replace the 0 in the prelude with the actual expression
        fn assign_last_body<'ast>(
            mut l: &mut SpannedExpr<'ast, Symbol>,
            original_expr: SpannedExpr<'ast, Symbol>,
        ) {
            while let ast::Expr::LetBindings(_, ref mut e) = l.value {
                l = e;
            }
            *l = original_expr;
        }
        assign_last_body(expr, original_expr);
    }
}

pub const PRELUDE: &'static str = r#"
let __implicit_prelude = import! std.prelude
let { IO, Num, Eq, Ord, Show, Functor, Applicative, Monad, Option, Bool, ? } = __implicit_prelude

let { (+), (-), (*), (/), negate, (==), (/=), (<), (<=), (>=), (>), (++), show, not, flat_map, (<|) } = __implicit_prelude

let { ? } = import! std.bool

let { ? } = import! std.option

let { ? } = import! std.float

let { ? } = import! std.int

let { ? } = import! std.string

let { ? } = import! std.array

let { error } = import! std.prim

let __error = error
let __string_eq: String -> String -> Bool = (==)

in ()
"#;

#[derive(Default)]
pub struct VmBuilder {
    import_paths: Option<Vec<PathBuf>>,
}

impl VmBuilder {
    pub fn new() -> VmBuilder {
        VmBuilder::default()
    }

    option! {
        /// (default: ["."])
        import_paths set_import_paths: Option<Vec<PathBuf>>
    }

    pub fn build(self) -> RootedThread {
        futures::executor::block_on(self.build_inner(None))
    }

    pub async fn build_async(self) -> RootedThread {
        #[allow(unused_mut, unused_assignments)]
        let mut spawner = None;

        #[cfg(feature = "tokio")]
        {
            struct TokioSpawn;
            impl futures::task::Spawn for TokioSpawn {
                fn spawn_obj(
                    &self,
                    future: futures::task::FutureObj<'static, ()>,
                ) -> StdResult<(), futures::task::SpawnError> {
                    tokio::spawn(future);
                    Ok(())
                }
            }
            spawner = Some(Box::new(TokioSpawn) as Box<dyn futures::task::Spawn + Send + Sync>);
        }

        self.build_inner(spawner).await
    }

    async fn build_inner(
        self,
        spawner: Option<Box<dyn futures::task::Spawn + Send + Sync>>,
    ) -> RootedThread {
        let vm = RootedThread::with_global_state(
            crate::vm::vm::GlobalVmStateBuilder::new()
                .spawner(spawner)
                .build(),
        );

        {
            let macros = vm.get_macros();

            {
                let import = Import::new(DefaultImporter);
                if let Some(import_paths) = self.import_paths {
                    import.set_paths(import_paths);
                }

                if let Ok(gluon_path) = env::var("GLUON_PATH") {
                    import.add_path(gluon_path);
                }
                macros.insert(String::from("import"), import);
            }

            macros.insert(String::from("lift_io"), lift_io::LiftIo);
        }

        add_extern_module_with_deps(
            &vm,
            "std.prim",
            crate::vm::primitives::load,
            vec!["std.types".into()],
        );

        vm.run_expr_async::<OpaqueValue<RootedThread, Hole>>(
            "",
            r#"//@NO-IMPLICIT-PRELUDE
                    let _ = import! std.types
                    let _ = import! std.prim
                    ()
                "#,
        )
        .await
        .unwrap_or_else(|err| panic!("{}", err));

        let deps: &[(_, fn(&Thread) -> _)] = &[
            ("std.byte.prim", crate::vm::primitives::load_byte),
            ("std.int.prim", crate::vm::primitives::load_int),
            ("std.float.prim", crate::vm::primitives::load_float),
            ("std.string.prim", crate::vm::primitives::load_string),
            ("std.fs.prim", crate::vm::primitives::load_fs),
            ("std.char.prim", crate::vm::primitives::load_char),
            ("std.char.prim", crate::vm::primitives::load_char),
            ("std.thread.prim", crate::vm::channel::load_thread),
            ("std.io.prim", crate::std_lib::io::load),
        ];
        for (name, load_fn) in deps {
            add_extern_module_with_deps(&vm, name, load_fn, vec!["std.types".into()]);
        }

        add_extern_module_with_deps(
            &vm,
            "std.path.prim",
            crate::vm::primitives::load_path,
            vec!["std.path.types".into()],
        );

        add_extern_module_with_deps(
            &vm,
            "std.st.reference.prim",
            crate::vm::reference::st::load,
            vec!["std.reference".into()],
        );

        let deps: &[(_, fn(&Thread) -> _)] = &[
            ("std.array.prim", crate::vm::primitives::load_array),
            ("std.lazy.prim", crate::vm::lazy::load),
            ("std.reference.prim", crate::vm::reference::load),
            ("std.channel.prim", crate::vm::channel::load_channel),
            ("std.debug.prim", crate::vm::debug::load),
            ("std.process.prim", crate::std_lib::process::load),
            ("std.env.prim", crate::std_lib::env::load),
            ("std.time.prim", crate::std_lib::time::load),
        ];
        for (name, load_fn) in deps {
            add_extern_module(&vm, name, load_fn);
        }

        add_extern_module(
            &vm,
            "std.effect.st.string.prim",
            crate::vm::primitives::load_string_buf,
        );

        add_extern_module_if!(
            #[cfg(feature = "serialization")],
            available_if = "gluon is compiled with the 'serialization' feature",
            dependencies = ["std.json"],
            args(&vm, "std.json.prim", crate::vm::api::json::load)
        );

        add_extern_module_if!(
            #[cfg(feature = "regex")],
            available_if = "gluon is compiled with the 'regex' feature",
            dependencies = ["std.regex.types"],
            args(&vm, "std.regex.prim", crate::std_lib::regex::load)
        );

        add_extern_module_if!(
            #[cfg(feature = "web")],
            available_if = "gluon is compiled with the 'web' feature",
            args(&vm, "std.http.prim_types", crate::std_lib::http::load_types)
        );

        add_extern_module_if!(
            #[cfg(feature = "web")],
            available_if = "gluon is compiled with the 'web' feature",
            dependencies = ["std.http.types"],
            args(&vm, "std.http.prim", crate::std_lib::http::load)
        );

        add_extern_module_if!(
            #[cfg(all(feature = "random", not(target_arch = "wasm32")))],
            available_if = "gluon is compiled with the 'random' feature and is not targeting WASM",
            args(&vm, "std.random.prim", crate::std_lib::random::load)
        );

        vm
    }
}

/// Creates a new virtual machine with support for importing other modules and with all primitives
/// loaded.
pub fn new_vm() -> RootedThread {
    VmBuilder::default().build()
}

pub async fn new_vm_async() -> RootedThread {
    VmBuilder::default().build_async().await
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn implicit_prelude() {
        let _ = ::env_logger::try_init();

        let thread = new_vm();
        thread.get_database_mut().set_implicit_prelude(false);
        thread
            .run_expr::<()>("prelude", PRELUDE)
            .unwrap_or_else(|err| panic!("{}", err));
    }
}
