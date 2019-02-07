//! Module providing the building blocks to create macros and expand them.
use std::{
    any::{Any, TypeId},
    error::Error as StdError,
    fmt, mem,
    sync::{Arc, RwLock},
};

use futures::{stream, Future, Stream};

use codespan_reporting::Diagnostic;

use crate::base::{
    ast::{self, Expr, MutVisitor, SpannedExpr, ValueBindings},
    error::{AsDiagnostic, Errors as BaseErrors},
    fnv::FnvMap,
    pos,
    pos::{BytePos, Spanned},
    symbol::{Symbol, Symbols},
};

use crate::thread::Thread;

pub type SpannedError = Spanned<Error, BytePos>;
pub type Errors = BaseErrors<SpannedError>;
pub type MacroFuture = Box<Future<Item = SpannedExpr<Symbol>, Error = Error> + Send>;

pub trait MacroError: ::mopa::Any + StdError + AsDiagnostic + Send + Sync + 'static {
    fn clone_error(&self) -> Error;
    fn eq_error(&self, other: &MacroError) -> bool;
    fn hash_error(&self, hash: &mut std::hash::Hasher);
}
mopafy!(MacroError);

impl<T> MacroError for T
where
    T: Clone + PartialEq + std::hash::Hash + AsDiagnostic + StdError + Send + Sync + 'static,
{
    fn clone_error(&self) -> Error {
        Error(Box::new(self.clone()))
    }
    fn eq_error(&self, other: &MacroError) -> bool {
        other
            .downcast_ref::<Self>()
            .map_or(false, |other| self == other)
    }
    fn hash_error(&self, mut hash: &mut std::hash::Hasher) {
        self.hash(&mut hash)
    }
}

#[derive(Debug)]
pub struct Error(Box<MacroError>);

impl StdError for Error {
    fn description(&self) -> &str {
        self.0.description()
    }
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        self.0.source()
    }
}

impl AsDiagnostic for Error {
    fn as_diagnostic(&self) -> Diagnostic {
        self.0.as_diagnostic()
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Clone for Error {
    fn clone(&self) -> Self {
        self.0.clone_error()
    }
}

impl Eq for Error {}

impl PartialEq for Error {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq_error(&*other.0)
    }
}

impl std::hash::Hash for Error {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        self.0.hash_error(state)
    }
}

impl Error {
    pub fn new<E>(err: E) -> Self
    where
        E: MacroError,
    {
        Self(Box::new(err))
    }

    pub fn message(s: impl Into<String>) -> Error {
        #[derive(Debug, Eq, PartialEq, Clone, Hash)]
        struct StringError(String);

        impl StdError for StringError {
            fn description(&self) -> &str {
                &self.0
            }
        }

        impl fmt::Display for StringError {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                fmt::Display::fmt(&self.0, f)
            }
        }

        impl AsDiagnostic for StringError {
            fn as_diagnostic(&self) -> Diagnostic {
                Diagnostic::new_error(self.to_string())
            }
        }

        Self::new(StringError(s.into()))
    }

    pub fn downcast<T>(self) -> Result<Box<T>, Self>
    where
        T: MacroError,
    {
        self.0.downcast().map_err(Self)
    }
}

/// A trait which abstracts over macros.
///
/// A macro is similiar to a function call but is run at compile time instead of at runtime.
pub trait Macro: ::mopa::Any + Send + Sync {
    fn get_capability<T>(&self) -> Option<Box<T>>
    where
        Self: Sized,
        T: ?Sized + Any,
    {
        self.get_capability_impl(TypeId::of::<T>()).map(|b| {
            *b.downcast::<Box<T>>()
                .ok()
                .expect("get_capability_impl return an unexpected type")
        })
    }

    fn get_capability_impl(&self, id: TypeId) -> Option<Box<Any>> {
        let _ = id;
        None
    }

    fn expand(&self, env: &mut MacroExpander, args: Vec<SpannedExpr<Symbol>>) -> MacroFuture;
}

mopafy!(Macro);

impl<M> Macro for Box<M>
where
    M: Macro + ?Sized,
{
    fn get_capability_impl(&self, id: TypeId) -> Option<Box<Any>> {
        (**self).get_capability_impl(id)
    }

    fn expand(&self, env: &mut MacroExpander, args: Vec<SpannedExpr<Symbol>>) -> MacroFuture {
        (**self).expand(env, args)
    }
}

impl<M> Macro for Arc<M>
where
    M: Macro + ?Sized,
{
    fn get_capability_impl(&self, id: TypeId) -> Option<Box<Any>> {
        (**self).get_capability_impl(id)
    }

    fn expand(&self, env: &mut MacroExpander, args: Vec<SpannedExpr<Symbol>>) -> MacroFuture {
        (**self).expand(env, args)
    }
}

/// Type containing macros bound to symbols which can be applied on an AST expression to transform
/// it.
#[derive(Default)]
pub struct MacroEnv {
    macros: RwLock<FnvMap<String, Arc<Macro>>>,
}

impl MacroEnv {
    /// Creates a new `MacroEnv`
    pub fn new() -> MacroEnv {
        MacroEnv {
            macros: RwLock::new(FnvMap::default()),
        }
    }

    /// Inserts a `Macro` which acts on any occurance of `symbol` when applied to an expression.
    pub fn insert<M>(&self, name: String, mac: M)
    where
        M: Macro + 'static,
    {
        self.macros.write().unwrap().insert(name, Arc::new(mac));
    }

    /// Retrieves the macro bound to `symbol`
    pub fn get(&self, name: &str) -> Option<Arc<Macro>> {
        self.macros.read().unwrap().get(name).cloned()
    }

    pub fn get_capabilities<T>(&self) -> Vec<Box<T>>
    where
        T: ?Sized + Any,
    {
        let macros = self.macros.read().unwrap();
        macros
            .values()
            .filter_map(|mac| mac.get_capability::<T>())
            .collect()
    }

    /// Runs the macros in this `MacroEnv` on `expr` using `env` as the context of the expansion
    pub fn run(
        &self,
        vm: &Thread,
        user_data: &Any,
        symbols: &mut Symbols,
        expr: &mut SpannedExpr<Symbol>,
    ) -> Result<(), Errors> {
        let mut expander = MacroExpander::new(vm, user_data);
        expander.run(symbols, expr);
        expander.finish()
    }
}

pub struct MacroExpander<'a> {
    pub state: FnvMap<String, Box<Any>>,
    pub vm: &'a Thread,
    pub errors: Errors,
    pub user_data: &'a Any,
    macros: &'a MacroEnv,
}

impl<'a> MacroExpander<'a> {
    pub fn new(vm: &'a Thread, user_data: &'a Any) -> MacroExpander<'a> {
        MacroExpander {
            vm: vm,

            state: FnvMap::default(),
            macros: vm.get_macros(),
            user_data,
            errors: Errors::new(),
        }
    }

    pub fn finish(self) -> Result<(), Errors> {
        if self.errors.has_errors() {
            Err(self.errors)
        } else {
            Ok(())
        }
    }

    pub fn run(&mut self, symbols: &mut Symbols, expr: &mut SpannedExpr<Symbol>) {
        {
            let exprs = {
                let mut visitor = MacroVisitor {
                    expander: self,
                    symbols,
                    exprs: Vec::new(),
                };
                visitor.visit_expr(expr);
                visitor.exprs
            };
            let _ = stream::futures_ordered(exprs.into_iter().map(move |(expr, future)| {
                future.then(move |result| -> Result<_, ()> {
                    match result {
                        Ok(mut replacement) => {
                            replacement.span = expr.span;
                            replace_expr(expr, replacement);
                            Ok(None)
                        }
                        Err(err) => {
                            let expr_span = expr.span;
                            replace_expr(expr, pos::spanned(expr_span, Expr::Error(None)));

                            Ok(Some(pos::spanned(expr.span, err)))
                        }
                    }
                })
            }))
            .for_each(|err| -> Result<(), ()> {
                if let Some(err) = err {
                    self.errors.push(err);
                }
                Ok(())
            })
            .wait();
        }
        if self.errors.has_errors() {
            info!("Macro errors: {}", self.errors);
        }
    }
}

fn replace_expr(expr: &mut SpannedExpr<Symbol>, new: SpannedExpr<Symbol>) {
    let expr_span = expr.span;
    let original = mem::replace(expr, pos::spanned(expr_span, Expr::Error(None)));
    *expr = pos::spanned(
        expr.span,
        Expr::MacroExpansion {
            original: Box::new(original),
            replacement: Box::new(new),
        },
    );
}

struct MacroVisitor<'a: 'b, 'b, 'c> {
    expander: &'b mut MacroExpander<'a>,
    symbols: &'c mut Symbols,
    exprs: Vec<(&'c mut SpannedExpr<Symbol>, MacroFuture)>,
}

impl<'a, 'b, 'c> MutVisitor<'c> for MacroVisitor<'a, 'b, 'c> {
    type Ident = Symbol;

    fn visit_expr(&mut self, expr: &'c mut SpannedExpr<Symbol>) {
        let replacement = match expr.value {
            Expr::App {
                ref mut implicit_args,
                func: ref mut id,
                ref mut args,
            } => match id.value {
                Expr::Ident(ref id) if id.name.as_ref().ends_with('!') => {
                    if !implicit_args.is_empty() {
                        self.expander.errors.push(pos::spanned(
                            expr.span,
                            Error::message("Implicit arguments are not allowed on macros"),
                        ));
                    }

                    let name = id.name.as_ref();
                    match self.expander.macros.get(&name[..name.len() - 1]) {
                        // FIXME Avoid cloning args
                        Some(m) => Some(m.expand(self.expander, args.clone())),
                        None => None,
                    }
                }
                _ => None,
            },
            Expr::TypeBindings(ref binds, ref mut body) => {
                let generated_bindings = binds
                    .iter()
                    .flat_map(|bind| {
                        if let Some(derive) = bind
                            .metadata
                            .attributes
                            .iter()
                            .find(|attr| attr.name == "derive")
                        {
                            match crate::derive::generate(self.symbols, derive, bind) {
                                Ok(x) => x,
                                Err(err) => {
                                    self.expander.errors.push(pos::spanned(bind.name.span, err));
                                    Vec::new()
                                }
                            }
                        } else {
                            Vec::new()
                        }
                    })
                    .collect::<Vec<_>>();
                if !generated_bindings.is_empty() {
                    let next_expr = mem::replace(body, Default::default());
                    body.value =
                        Expr::LetBindings(ValueBindings::Recursive(generated_bindings), next_expr);
                }
                None
            }
            _ => None,
        };
        if let Some(future) = replacement {
            self.exprs.push((expr, future));
        } else {
            ast::walk_mut_expr(self, expr);
        }
    }
}
