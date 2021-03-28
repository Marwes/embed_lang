use std::{
    borrow::{Borrow, Cow},
    cell::RefCell,
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    iter::FromIterator,
    iter::{self, FusedIterator},
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
    rc::Rc,
    sync::Arc,
};

use {
    itertools::Itertools,
    pretty::{Arena, Doc, DocAllocator, DocBuilder},
    smallvec::SmallVec,
};

use gluon_codegen::AstClone;

use crate::{
    ast::{AstClone, EmptyEnv, HasMetadata, IdentEnv},
    fnv::FnvMap,
    kind::{ArcKind, Kind, KindCache, KindEnv},
    merge::{merge, merge_collect},
    metadata::Metadata,
    pos::{BytePos, HasSpan, Span, Spanned},
    source::Source,
    symbol::{Name, Symbol, SymbolRef},
};

#[cfg(feature = "serde")]
use crate::{
    serde::{de::DeserializeState, ser::SerializeState},
    serialization::{SeSeed, Seed},
};

use self::pretty_print::Printer;
pub use self::{
    flags::Flags,
    pretty_print::{Filter, TypeFormatter},
};
pub use crate::ast::KindedIdent;

mod flags;
pub mod pretty_print;

macro_rules! forward_eq_hash {
    (<$($param: ident),*> for $typ: ty { $field: ident }) => {
        impl<$($param),*> Eq for $typ where $($param : Eq),* {}

        impl<$($param),*> PartialEq for $typ
            where $($param : PartialEq),*
        {
            fn eq(&self, other: &Self) -> bool {
                self.$field == other.$field
            }
        }

        impl<$($param),*> Hash for $typ
        where $($param : Hash),*
        {
            fn hash<H>(&self, state: &mut H)
            where
                H: std::hash::Hasher,
            {
                self.$field.hash(state)
            }
        }
    }
}

pub trait AsId<Id>
where
    Id: ?Sized,
{
    fn as_id(&self) -> &Id;
}

impl<Id> AsId<Id> for Id
where
    Id: ?Sized,
{
    fn as_id(&self) -> &Id {
        self
    }
}

impl<T, Pos> AsId<T> for Spanned<T, Pos> {
    fn as_id(&self) -> &T {
        &self.value
    }
}

/// Trait for values which contains typed values which can be refered by name
pub trait TypeEnv: KindEnv {
    type Type;
    /// Returns the type of the value bound at `id`
    fn find_type(&self, id: &SymbolRef) -> Option<Self::Type>;

    /// Returns information about the type `id`
    fn find_type_info(&self, id: &SymbolRef) -> Option<Alias<Symbol, Self::Type>>;
}

impl<'a, T: ?Sized + TypeEnv> TypeEnv for &'a T {
    type Type = T::Type;

    fn find_type(&self, id: &SymbolRef) -> Option<Self::Type> {
        (**self).find_type(id)
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<Alias<Symbol, Self::Type>> {
        (**self).find_type_info(id)
    }
}

impl TypeEnv for EmptyEnv<Symbol> {
    type Type = ArcType;

    fn find_type(&self, _id: &SymbolRef) -> Option<ArcType> {
        None
    }

    fn find_type_info(&self, _id: &SymbolRef) -> Option<Alias<Symbol, ArcType>> {
        None
    }
}

/// Trait which is a `TypeEnv` which also provides access to the type representation of some
/// primitive types
pub trait PrimitiveEnv: TypeEnv {
    fn get_bool(&self) -> ArcType;
}

impl<'a, T: ?Sized + PrimitiveEnv> PrimitiveEnv for &'a T {
    fn get_bool(&self) -> ArcType {
        (**self).get_bool()
    }
}

type_cache! {
    TypeCache(Id, T)
    where [T: TypeExt<Id = Id>, T::Types: Default + Extend<T>,]
    (kind_cache: crate::kind::KindCache)
    { T, Type }
    hole opaque error int byte float string char
    function_builtin array_builtin unit empty_row
}

impl<Id, T> TypeCache<Id, T>
where
    T: TypeExt<Id = Id> + From<Type<Id, T>> + Clone,
    T::Types: Default + Extend<T>,
{
    pub fn function<I>(&self, args: I, ret: T) -> T
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: DoubleEndedIterator<Item = T>,
    {
        args.into_iter().rev().fold(ret, |body, arg| {
            T::from(Type::Function(ArgType::Explicit, arg, body))
        })
    }

    pub fn function_implicit<I>(&self, args: I, ret: T) -> T
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: DoubleEndedIterator<Item = T>,
    {
        args.into_iter().rev().fold(ret, |body, arg| {
            T::from(Type::Function(ArgType::Implicit, arg, body))
        })
    }

    pub fn tuple<S, I>(&self, symbols: &mut S, elems: I) -> T
    where
        S: ?Sized + IdentEnv<Ident = Id>,
        T::SpannedId: From<Id>,
        I: IntoIterator<Item = T>,
    {
        let fields: Vec<_> = elems
            .into_iter()
            .enumerate()
            .map(|(i, typ)| Field {
                name: symbols.from_str(&format!("_{}", i)).into(),
                typ,
            })
            .collect();
        if fields.is_empty() {
            self.unit()
        } else {
            self.record(vec![], fields)
        }
    }

    pub fn variant(&self, fields: Vec<Field<T::SpannedId, T>>) -> T {
        self.poly_variant(fields, self.empty_row())
    }

    pub fn poly_variant(&self, fields: Vec<Field<T::SpannedId, T>>, rest: T) -> T {
        Type::poly_variant(fields, rest)
    }

    pub fn record(
        &self,
        types: Vec<Field<T::SpannedId, Alias<Id, T>>>,
        fields: Vec<Field<T::SpannedId, T>>,
    ) -> T {
        Type::poly_record(types, fields, self.empty_row())
    }

    pub fn effect(&self, fields: Vec<Field<T::SpannedId, T>>) -> T {
        self.poly_effect(fields, self.empty_row())
    }

    pub fn poly_effect(&self, fields: Vec<Field<T::SpannedId, T>>, rest: T) -> T {
        Type::poly_effect(fields, rest)
    }

    pub fn array(&self, typ: T) -> T {
        Type::app(self.array_builtin(), collect![typ])
    }
}

impl<Id, T> TypeCache<Id, T>
where
    T: TypeExt<Id = Id> + Clone,
    T::Types: Default + Extend<T> + FromIterator<T>,
{
    pub fn builtin_type(&self, typ: BuiltinType) -> T {
        match typ {
            BuiltinType::String => self.string(),
            BuiltinType::Byte => self.byte(),
            BuiltinType::Char => self.char(),
            BuiltinType::Int => self.int(),
            BuiltinType::Float => self.float(),
            BuiltinType::Array => self.array_builtin(),
            BuiltinType::Function => self.function_builtin(),
        }
    }
}

/// All the builtin types of gluon
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
pub enum BuiltinType {
    /// Unicode string
    String,
    /// Unsigned byte
    Byte,
    /// Character
    Char,
    /// Integer number
    Int,
    /// Floating point number
    Float,
    /// Type constructor for arrays, `Array a : Type -> Type`
    Array,
    /// Type constructor for functions, `(->) a b : Type -> Type -> Type`
    Function,
}

impl BuiltinType {
    pub fn symbol(self) -> &'static SymbolRef {
        SymbolRef::new(self.to_str())
    }
}

impl ::std::str::FromStr for BuiltinType {
    type Err = ();
    fn from_str(x: &str) -> Result<BuiltinType, ()> {
        let t = match x {
            "Int" => BuiltinType::Int,
            "Byte" => BuiltinType::Byte,
            "Float" => BuiltinType::Float,
            "String" => BuiltinType::String,
            "Char" => BuiltinType::Char,
            "Array" => BuiltinType::Array,
            "->" => BuiltinType::Function,
            _ => return Err(()),
        };
        Ok(t)
    }
}

impl BuiltinType {
    pub fn to_str(self) -> &'static str {
        match self {
            BuiltinType::String => "String",
            BuiltinType::Byte => "Byte",
            BuiltinType::Char => "Char",
            BuiltinType::Int => "Int",
            BuiltinType::Float => "Float",
            BuiltinType::Array => "Array",
            BuiltinType::Function => "->",
        }
    }
}

#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "SeSeed"))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "Seed<Id, T>"))]
#[cfg_attr(feature = "serde_derive", serde(de_parameters = "Id, T"))]
pub struct TypeVariable {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub kind: ArcKind,
    pub id: u32,
}

forward_eq_hash! { <> for TypeVariable { id } }

#[derive(Clone, Debug, AstClone)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "Seed<Id, T>"))]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(deserialize = "
           Id: DeserializeState<'de, Seed<Id, T>> + Clone + ::std::any::Any"))
)]
#[cfg_attr(feature = "serde_derive", serde(de_parameters = "T"))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "SeSeed"))]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(serialize = "Id: SerializeState<SeSeed>"))
)]
pub struct Skolem<Id> {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub name: Id,
    pub id: u32,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub kind: ArcKind,
}

forward_eq_hash! { <Id> for Skolem<Id> { id } }

/// FIXME Distinguish generic id's so we only need to compare them by `id` (currently they will get
/// the wrong kind assigned to them otherwise)
#[derive(Clone, Debug, Eq, PartialEq, Hash, AstClone)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "Seed<Id, T>"))]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(deserialize = "
           Id: DeserializeState<'de, Seed<Id, T>> + Clone + ::std::any::Any"))
)]
#[cfg_attr(feature = "serde_derive", serde(de_parameters = "T"))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "SeSeed"))]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(serialize = "Id: SerializeState<SeSeed>"))
)]
pub struct Generic<Id> {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub id: Id,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub kind: ArcKind,
}

impl<Id> Generic<Id> {
    pub fn new(id: Id, kind: ArcKind) -> Generic<Id> {
        Generic { id, kind }
    }
}

/// An alias is wrapper around `Type::Alias`, allowing it to be cheaply converted to a type and
/// dereferenced to `AliasRef`
#[derive(Clone, Debug, Eq, PartialEq, Hash, AstClone)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "Seed<Id, T>"))]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(deserialize = "
           T: DeserializeState<'de, Seed<Id, T>> + TypePtr<Id = Id> + Clone + From<Type<Id, T>> + ::std::any::Any,
           Id: DeserializeState<'de, Seed<Id, T>> + Clone + ::std::any::Any"))
)]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "SeSeed"))]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(serialize = "T: SerializeState<SeSeed> + TypePtr<Id = Id>"))
)]
pub struct Alias<Id, T> {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    _typ: T,
    #[cfg_attr(feature = "serde_derive", serde(skip))]
    _marker: PhantomData<Id>,
}

impl<Id, T> Deref for Alias<Id, T>
where
    T: TypePtr<Id = Id>,
{
    type Target = AliasRef<Id, T>;

    fn deref(&self) -> &Self::Target {
        match *self._typ {
            Type::Alias(ref alias) => alias,
            _ => unreachable!(),
        }
    }
}

impl<Id, T> DerefMut for Alias<Id, T>
where
    T: TypePtr<Id = Id> + DerefMut<Target = Type<Id, T>>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        match *self._typ {
            Type::Alias(ref mut alias) => alias,
            _ => unreachable!(),
        }
    }
}

impl<Id, T> From<AliasData<Id, T>> for Alias<Id, T>
where
    T: TypeExt<Id = Id> + From<Type<Id, T>>,
    T::Types: Clone + Default + Extend<T>,
{
    fn from(data: AliasData<Id, T>) -> Alias<Id, T> {
        Alias {
            _typ: Type::alias(data.name, data.args, data.typ),
            _marker: PhantomData,
        }
    }
}

impl<Id, T> From<AliasRef<Id, T>> for Alias<Id, T>
where
    T: TypePtr<Id = Id> + From<Type<Id, T>>,
{
    fn from(data: AliasRef<Id, T>) -> Alias<Id, T> {
        Alias {
            _typ: Type::Alias(data).into(),
            _marker: PhantomData,
        }
    }
}

impl<Id, T> AsRef<T> for Alias<Id, T> {
    fn as_ref(&self) -> &T {
        &self._typ
    }
}

impl<Id, T> Alias<Id, T>
where
    T: TypePtr<Id = Id>,
{
    pub fn new_with(
        context: &mut (impl TypeContext<Id, T> + ?Sized),
        name: Id,
        args: T::Generics,
        typ: T,
    ) -> Self {
        Alias {
            _typ: context.alias(name, args, typ),
            _marker: PhantomData,
        }
    }
}

impl<Id, T> Alias<Id, T>
where
    T: TypeExt<Id = Id> + From<Type<Id, T>>,
    T::Types: Clone + Default + Extend<T>,
{
    pub fn new(name: Id, args: T::Generics, typ: T) -> Alias<Id, T> {
        Alias {
            _typ: Type::alias(name, args, typ),
            _marker: PhantomData,
        }
    }

    pub fn group(group: Vec<AliasData<Id, T>>) -> Vec<Alias<Id, T>> {
        let group = Arc::<[_]>::from(group);
        (0..group.len())
            .map(|index| Alias {
                _typ: T::from(Type::Alias(AliasRef {
                    index,
                    group: group.clone(),
                })),
                _marker: PhantomData,
            })
            .collect()
    }
}

impl<Id, T> Alias<Id, T> {
    pub fn as_type(&self) -> &T {
        &self._typ
    }

    pub fn into_type(self) -> T {
        self._typ
    }
}

impl<Id, T> Alias<Id, T>
where
    T: TypeExt<Id = Id> + Clone,
    T::Types: Clone + Default + Extend<T>,
    T::Generics: Clone,
    T::Fields: Clone,
    Id: Clone + PartialEq,
    T::SpannedId: Clone + PartialEq,
{
    /// Returns the actual type of the alias
    pub fn typ(&self, interner: &mut impl TypeContext<Id, T>) -> Cow<T> {
        match *self._typ {
            Type::Alias(ref alias) => alias.typ(interner),
            _ => unreachable!(),
        }
    }

    pub fn unpack_canonical_alias<'b>(
        &'b self,
        canonical_alias_type: &'b T,
        mut un_alias: impl FnMut(&'b AliasRef<Id, T>) -> Cow<'b, T>,
    ) -> (Cow<'b, [Generic<Id>]>, &'b AliasRef<Id, T>, Cow<'b, T>) {
        match **canonical_alias_type {
            Type::App(ref func, _) => match **func {
                Type::Alias(ref alias) => (Cow::Borrowed(&[]), alias, un_alias(alias)),
                _ => (Cow::Borrowed(&[]), &**self, Cow::Borrowed(func)),
            },
            Type::Alias(ref alias) => (Cow::Borrowed(&[]), alias, un_alias(alias)),
            Type::Forall(ref params, ref typ) => {
                let mut params = Cow::Borrowed(&params[..]);
                let (more_params, canonical_alias, inner_type) =
                    self.unpack_canonical_alias(typ, un_alias);
                if !more_params.is_empty() {
                    params.to_mut().extend(more_params.iter().cloned());
                }
                (params, canonical_alias, inner_type)
            }
            _ => (
                Cow::Borrowed(&[]),
                &**self,
                Cow::Borrowed(canonical_alias_type),
            ),
        }
    }
}

/// Data for a type alias. Probably you want to use `Alias` instead of this directly as Alias allows
/// for cheap conversion back into a type as well.
#[derive(Clone, AstClone)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "Seed<Id, T>"))]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(
        deserialize = "
           T: DeserializeState<'de, Seed<Id, T>> + TypePtr<Id = Id> + Clone + From<Type<Id, T>> + ::std::any::Any,
           Id: DeserializeState<'de, Seed<Id, T>> + Clone + ::std::any::Any,
           T::Generics: Default + Extend<Generic<Id>> + Clone,
           ",
        serialize = "
            T: TypePtr<Id = Id> + SerializeState<SeSeed>,
            Id: SerializeState<SeSeed>,
            "
    ))
)]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "SeSeed"))]
#[gluon(ast_clone_bounds = "T::Generics: AstClone<'ast, Id>")]
pub struct AliasRef<Id, T>
where
    T: TypePtr<Id = Id>,
{
    /// Name of the Alias
    index: usize,
    #[cfg_attr(
        feature = "serde_derive",
        serde(deserialize_state_with = "crate::serialization::deserialize_group")
    )]
    #[cfg_attr(
        feature = "serde_derive",
        serde(serialize_state_with = "crate::serialization::shared::serialize")
    )]
    /// The other aliases defined in this group
    pub group: Arc<[AliasData<Id, T>]>,
}

impl<Id, T> fmt::Debug for AliasRef<Id, T>
where
    Id: fmt::Debug,
    T: TypePtr<Id = Id> + fmt::Debug,
    AliasData<Id, T>: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<Id, T> Eq for AliasRef<Id, T>
where
    T: TypePtr<Id = Id>,
    AliasData<Id, T>: Eq,
{
}
impl<Id, T> PartialEq for AliasRef<Id, T>
where
    T: TypePtr<Id = Id>,
    AliasData<Id, T>: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}
impl<Id, T> Hash for AliasRef<Id, T>
where
    T: TypePtr<Id = Id>,
    AliasData<Id, T>: Hash,
{
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        (**self).hash(state)
    }
}

impl<Id, T> AliasRef<Id, T>
where
    T: TypePtr<Id = Id>,
{
    pub fn try_get_alias_mut(&mut self) -> Option<&mut AliasData<Id, T>> {
        let index = self.index;
        Arc::get_mut(&mut self.group).map(|group| &mut group[index])
    }
    pub(crate) fn try_get_alias(&self) -> Option<&AliasData<Id, T>> {
        let index = self.index;
        Some(&self.group[index])
    }

    #[doc(hidden)]
    pub fn new(index: usize, group: Arc<[AliasData<Id, T>]>) -> Self {
        AliasRef { index, group }
    }

    #[doc(hidden)]
    pub fn index(&self) -> usize {
        self.index
    }
}

impl<Id, T> AliasRef<Id, T>
where
    T: TypeExt<Id = Id> + Clone,
    T::Types: Clone + Default + Extend<T>,
    T::Generics: Clone,
    T::Fields: Clone,
    Id: Clone + PartialEq,
    T::SpannedId: Clone + PartialEq,
{
    pub fn typ(&self, interner: &mut impl TypeContext<Id, T>) -> Cow<T> {
        match self.typ_(interner, &self.typ) {
            Some(typ) => Cow::Owned(typ),
            None => Cow::Borrowed(&self.typ),
        }
    }

    fn typ_(&self, interner: &mut impl TypeContext<Id, T>, typ: &T) -> Option<T> {
        if !typ.flags().intersects(Flags::HAS_IDENTS) {
            return None;
        }
        match **typ {
            Type::Ident(ref id) => {
                // Replace `Ident` with the alias it resolves to so that a `TypeEnv` is not
                // needed to resolve the type later on
                let replacement = self
                    .group
                    .iter()
                    .position(|alias| alias.name == id.name)
                    .map(|index| {
                        interner.intern(Type::Alias(AliasRef {
                            index,
                            group: self.group.clone(),
                        }))
                    });
                if replacement.is_none() {
                    info!("Alias group were not able to resolve an identifier");
                }
                replacement
            }
            _ => walk_move_type_opt(
                typ,
                &mut InternerVisitor::control(interner, |interner, typ: &T| {
                    self.typ_(interner, typ)
                }),
            ),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, AstClone)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "Seed<Id, T>"))]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(deserialize = "
           T: TypePtr<Id = Id> + Clone + From<Type<Id, T>> + ::std::any::Any + DeserializeState<'de, Seed<Id, T>>,
           T::Generics: Default + Extend<Generic<Id>>,
           Id: DeserializeState<'de, Seed<Id, T>> + Clone + ::std::any::Any"))
)]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "SeSeed"))]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(serialize = "
            T: TypePtr<Id = Id> + SerializeState<SeSeed>,
            Id: SerializeState<SeSeed>,
            "))
)]
#[gluon(ast_clone_bounds = "T::Generics: AstClone<'ast, Id>")]
pub struct AliasData<Id, T: TypePtr<Id = Id>> {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub name: Id,
    #[cfg_attr(
        feature = "serde_derive",
        serde(state_with = "crate::serialization::seq")
    )]
    args: T::Generics,
    /// The type that is being aliased
    #[cfg_attr(feature = "serde_derive", serde(state))]
    typ: T,
    pub is_implicit: bool,
}

impl<Id, T> AliasData<Id, T>
where
    T: TypePtr<Id = Id>,
{
    /// Returns the type aliased by `self` with out `Type::Ident` resolved to their actual
    /// `Type::Alias` representation
    pub fn unresolved_type(&self) -> &T {
        &self.typ
    }

    pub fn unresolved_type_mut(&mut self) -> &mut T {
        &mut self.typ
    }

    pub fn is_implicit(&self) -> bool {
        self.is_implicit
    }
}

impl<Id, T> AliasData<Id, T>
where
    T: TypePtr<Id = Id>,
    Id: Clone,
{
    pub fn self_type(&self, context: &mut (impl TypeContext<Id, T> + ?Sized)) -> T {
        let f = context.ident(KindedIdent {
            name: self.name.clone(),
            typ: self.typ.kind(&Default::default()).into_owned(),
        });
        let args = self
            .params()
            .iter()
            .cloned()
            .map(|g| context.generic(g))
            .collect::<SmallVec<[_; 5]>>();
        let args = context.intern_types(args);
        context.app(f, args)
    }
}

impl<Id, T> AliasData<Id, T>
where
    T: TypePtr<Id = Id>,
{
    pub fn new(name: Id, args: T::Generics, typ: T) -> AliasData<Id, T> {
        AliasData {
            name,
            args,
            typ,
            is_implicit: false,
        }
    }
}

impl<Id, T> AliasData<Id, T>
where
    T: TypePtr<Id = Id>,
{
    pub fn params(&self) -> &[Generic<Id>] {
        &self.args
    }

    pub fn params_mut(&mut self) -> &mut [Generic<Id>]
    where
        T::Generics: DerefMut<Target = [Generic<Id>]>,
    {
        &mut self.args
    }

    pub fn aliased_type(&self) -> &T {
        &self.typ
    }

    pub fn kind<'k>(&'k self, cache: &'k KindCache) -> Cow<'k, ArcKind> {
        let result_type = self.unresolved_type().kind(cache);
        self.params().iter().rev().fold(result_type, |acc, param| {
            Cow::Owned(Kind::function(param.kind.clone(), acc.into_owned()))
        })
    }
}

impl<Id, T> Deref for AliasRef<Id, T>
where
    T: TypePtr<Id = Id>,
{
    type Target = AliasData<Id, T>;

    fn deref(&self) -> &Self::Target {
        &self.group[self.index]
    }
}

#[derive(Clone, Hash, Eq, PartialEq, Debug, AstClone)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive",
    serde(deserialize_state = "Seed<FieldId, U>")
)]
#[cfg_attr(feature = "serde_derive", serde(de_parameters = "U"))]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(deserialize = "
           FieldId: DeserializeState<'de, Seed<FieldId, U>> + Clone + ::std::any::Any,
           T: DeserializeState<'de, Seed<FieldId, U>>
                             "))
)]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "SeSeed"))]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(serialize = "T: SerializeState<SeSeed>, FieldId: SerializeState<SeSeed>"))
)]
pub struct Field<FieldId, T = ArcType<FieldId>> {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub name: FieldId,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub typ: T,
}

/// `SmallVec` used in the `Type::App` constructor to avoid allocating a `Vec` for every applied
/// type. If `Type` is changed in a way that changes its size it is likely a good idea to change
/// the number of elements in the `SmallVec` so that it fills out the entire `Type` enum while not
/// increasing the size of `Type`.
pub type AppVec<T> = SmallVec<[T; 2]>;

impl<SpId, T> Field<SpId, T> {
    pub fn new(name: SpId, typ: T) -> Self {
        Field { name, typ }
    }

    pub fn ctor_with<J, Id>(
        context: &mut (impl TypeContext<Id, T> + ?Sized),
        enum_type: KindedIdent<Id>,
        ctor_name: SpId,
        elems: J,
    ) -> Self
    where
        J: IntoIterator<Item = T>,
        J::IntoIter: DoubleEndedIterator,
        T: TypePtr<Id = Id>,
    {
        let enum_type = context.ident(enum_type);
        let typ = context.function_type(ArgType::Constructor, elems, enum_type);
        Field {
            name: ctor_name,
            typ,
        }
    }

    pub fn ctor<J, Id>(enum_type: KindedIdent<Id>, ctor_name: SpId, elems: J) -> Self
    where
        J: IntoIterator<Item = T>,
        J::IntoIter: DoubleEndedIterator,
        T: TypeExt<Id = Id> + From<Type<Id, T>>,
        T::Types: Default + Extend<T>,
    {
        let typ = Type::function_type(ArgType::Constructor, elems, Type::ident(enum_type));
        Field {
            name: ctor_name,
            typ,
        }
    }
}

#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum ArgType {
    Explicit,
    Implicit,
    Constructor,
}

impl Default for ArgType {
    fn default() -> Self {
        Self::Explicit
    }
}

/// The representation of gluon's types.
///
/// For efficiency this enum is not stored directly but instead a pointer wrapper which derefs to
/// `Type` is used to enable types to be shared. It is recommended to use the static functions on
/// `Type` such as `Type::app` and `Type::record` when constructing types as those will construct
/// the pointer wrapper directly.
#[derive(Clone, Debug, Eq, PartialEq, Hash, AstClone)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "Seed<Id, T>"))]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(
        deserialize = "
           T: Clone
                + TypePtr<Id = Id>
                + From<Type<Id, T>>
                + std::any::Any
                + DeserializeState<'de, Seed<Id, T>>,
           T::Types: Default + Extend<T>,
           T::Generics: Default + Extend<Generic<Id>> + Clone,
           T::Fields: DeserializeState<'de, Seed<Id, T>>,
           T::TypeFields: DeserializeState<'de, Seed<Id, T>>,
           Id: DeserializeState<'de, Seed<Id, T>>
                + Clone
                + std::any::Any,
            ",
        serialize = "
            T: TypePtr<Id = Id> + SerializeState<SeSeed>,
            Id: SerializeState<SeSeed>,
            T::Fields: SerializeState<SeSeed>,
            T::TypeFields: SerializeState<SeSeed>,
            "
    ))
)]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "SeSeed"))]
#[gluon(ast_clone_bounds = "T::Generics: AstClone<'ast, Id>,
                            T::Types: AstClone<'ast, Id>,
                            T::Fields: AstClone<'ast, Id>,
                            T::TypeFields: AstClone<'ast, Id>")]
pub enum Type<Id, T: TypePtr<Id = Id> = ArcType<Id>> {
    /// An unbound type `_`, awaiting ascription.
    Hole,
    /// An opaque type
    Opaque,
    /// A type used to mark type errors
    Error,
    /// A builtin type
    Builtin(BuiltinType),
    /// Universally quantified types
    Forall(
        #[cfg_attr(
            feature = "serde_derive",
            serde(state_with = "crate::serialization::seq")
        )]
        T::Generics,
        #[cfg_attr(feature = "serde_derive", serde(state))] T,
    ),
    /// A type application with multiple arguments. For example,
    /// `Map String Int` would be represented as `App(Map, [String, Int])`.
    App(
        #[cfg_attr(feature = "serde_derive", serde(state))] T,
        #[cfg_attr(
            feature = "serde_derive",
            serde(state_with = "crate::serialization::seq")
        )]
        T::Types,
    ),
    /// Function type which can have a explicit or implicit argument
    Function(
        ArgType,
        #[cfg_attr(feature = "serde_derive", serde(state))] T,
        #[cfg_attr(feature = "serde_derive", serde(state))] T,
    ),
    /// Record constructor, of kind `Row -> Type`
    Record(#[cfg_attr(feature = "serde_derive", serde(state))] T),
    /// Variant constructor, of kind `Row -> Type`
    Variant(#[cfg_attr(feature = "serde_derive", serde(state))] T),
    /// Effect constructor, of kind `Row -> Type -> Type`
    Effect(#[cfg_attr(feature = "serde_derive", serde(state))] T),
    /// The empty row, of kind `Row`
    EmptyRow,
    /// Row extension, of kind `... -> Row -> Row`
    ExtendRow {
        /// The fields of this record type
        #[cfg_attr(feature = "serde_derive", serde(state))]
        fields: T::Fields,
        /// The rest of the row
        #[cfg_attr(feature = "serde_derive", serde(state))]
        rest: T,
    },
    /// Row extension, of kind `... -> Row -> Row`
    ExtendTypeRow {
        /// The associated types of this record type
        #[cfg_attr(feature = "serde_derive", serde(state))]
        types: T::TypeFields,
        /// The rest of the row
        #[cfg_attr(feature = "serde_derive", serde(state))]
        rest: T,
    },
    /// An identifier type. These are created during parsing, but should all be
    /// resolved into `Type::Alias`es during type checking.
    ///
    /// Identifiers are also sometimes used inside aliased types to avoid cycles
    /// in reference counted pointers. This is a bit of a wart at the moment and
    /// _may_ cause spurious unification failures.
    Ident(#[cfg_attr(feature = "serde_derive", serde(state))] KindedIdent<Id>),
    Projection(
        #[cfg_attr(
            feature = "serde_derive",
            serde(state_with = "crate::serialization::seq")
        )]
        AppVec<Id>,
    ),
    /// An unbound type variable that may be unified with other types. These
    /// will eventually be converted into `Type::Generic`s during generalization.
    Variable(#[cfg_attr(feature = "serde_derive", serde(state))] TypeVariable),
    /// A variable that needs to be instantiated with a fresh type variable
    /// when the binding is referred to.
    Generic(#[cfg_attr(feature = "serde_derive", serde(state))] Generic<Id>),
    Alias(#[cfg_attr(feature = "serde_derive", serde(state))] AliasRef<Id, T>),
    Skolem(#[cfg_attr(feature = "serde_derive", serde(state))] Skolem<Id>),
}

impl<Id, T> Default for Type<Id, T>
where
    T: TypePtr<Id = Id>,
{
    fn default() -> Self {
        Type::Hole
    }
}

#[cfg(target_pointer_width = "64")]
// Safeguard against accidentally growing Type as it is a core type
const _: [(); 8 * 6] = [(); std::mem::size_of::<Type<Symbol, ArcType>>()];

impl<Id, T> Type<Id, T>
where
    T: TypePtr<Id = Id>,
{
    pub fn as_variable(&self) -> Option<&TypeVariable> {
        match *self {
            Type::Variable(ref var) => Some(var),
            _ => None,
        }
    }
}

impl<Id, T> Type<Id, T>
where
    T: From<Type<Id, T>> + TypeExt<Id = Id>,
    T::Types: Default + Extend<T>,
{
    pub fn hole() -> T {
        T::from(Type::Hole)
    }

    pub fn opaque() -> T {
        T::from(Type::Opaque)
    }

    pub fn error() -> T {
        T::from(Type::Error)
    }

    pub fn builtin(typ: BuiltinType) -> T {
        T::from(Type::Builtin(typ))
    }

    pub fn forall(params: Vec<Generic<Id>>, typ: T) -> T {
        if params.is_empty() {
            typ
        } else {
            T::from(Type::Forall(params, typ))
        }
    }

    pub fn array(typ: T) -> T {
        Type::app(Type::array_builtin(), collect![typ])
    }

    pub fn array_builtin() -> T {
        Type::builtin(BuiltinType::Array)
    }

    pub fn app(id: T, args: T::Types) -> T {
        if args.is_empty() {
            id
        } else {
            T::from(Type::App(id, args))
        }
    }

    pub fn variant(fields: Vec<Field<T::SpannedId, T>>) -> T {
        Type::poly_variant(fields, Type::empty_row())
    }

    pub fn poly_variant(fields: Vec<Field<T::SpannedId, T>>, rest: T) -> T {
        T::from(Type::Variant(Type::extend_row(fields, rest)))
    }

    pub fn effect(fields: Vec<Field<T::SpannedId, T>>) -> T {
        Type::poly_effect(fields, Type::empty_row())
    }

    pub fn poly_effect(fields: Vec<Field<T::SpannedId, T>>, rest: T) -> T {
        T::from(Type::Effect(Type::extend_row(fields, rest)))
    }

    pub fn tuple<S, I>(symbols: &mut S, elems: I) -> T
    where
        S: ?Sized + IdentEnv<Ident = Id>,
        T::SpannedId: From<(Id, Span<BytePos>)>,
        I: IntoIterator<Item = T>,
        T: From<(Type<Id, T>, Flags)> + HasSpan,
    {
        T::from(Type::tuple_(symbols, elems))
    }

    pub fn tuple_<S, I>(symbols: &mut S, elems: I) -> Type<Id, T>
    where
        S: ?Sized + IdentEnv<Ident = Id>,
        T::SpannedId: From<(Id, Span<BytePos>)>,
        I: IntoIterator<Item = T>,
        T: From<(Type<Id, T>, Flags)> + HasSpan,
    {
        NullInterner.tuple_(symbols, elems)
    }

    pub fn record(
        types: Vec<Field<T::SpannedId, Alias<Id, T>>>,
        fields: Vec<Field<T::SpannedId, T>>,
    ) -> T {
        Type::poly_record(types, fields, Type::empty_row())
    }

    pub fn poly_record(
        types: Vec<Field<T::SpannedId, Alias<Id, T>>>,
        fields: Vec<Field<T::SpannedId, T>>,
        rest: T,
    ) -> T {
        T::from(Type::Record(Type::extend_full_row(types, fields, rest)))
    }

    pub fn extend_full_row(
        types: Vec<Field<T::SpannedId, Alias<Id, T>>>,
        fields: Vec<Field<T::SpannedId, T>>,
        rest: T,
    ) -> T {
        Self::extend_type_row(types, Self::extend_row(fields, rest))
    }

    pub fn extend_row(fields: Vec<Field<T::SpannedId, T>>, rest: T) -> T {
        if fields.is_empty() {
            rest
        } else {
            T::from(Type::ExtendRow { fields, rest })
        }
    }

    pub fn extend_type_row(types: Vec<Field<T::SpannedId, Alias<Id, T>>>, rest: T) -> T {
        if types.is_empty() {
            rest
        } else {
            T::from(Type::ExtendTypeRow { types, rest })
        }
    }

    pub fn empty_row() -> T {
        T::from(Type::EmptyRow)
    }

    pub fn function<I>(args: I, ret: T) -> T
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: DoubleEndedIterator<Item = T>,
    {
        Self::function_type(ArgType::Explicit, args, ret)
    }

    pub fn function_implicit<I>(args: I, ret: T) -> T
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: DoubleEndedIterator<Item = T>,
    {
        Self::function_type(ArgType::Implicit, args, ret)
    }

    pub fn function_type<I>(arg_type: ArgType, args: I, ret: T) -> T
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: DoubleEndedIterator<Item = T>,
    {
        args.into_iter().rev().fold(ret, |body, arg| {
            T::from(Type::Function(arg_type, arg, body))
        })
    }

    pub fn generic(typ: Generic<Id>) -> T {
        T::from(Type::Generic(typ))
    }

    pub fn skolem(typ: Skolem<Id>) -> T {
        T::from(Type::Skolem(typ))
    }

    pub fn variable(typ: TypeVariable) -> T {
        T::from(Type::Variable(typ))
    }

    pub fn alias(name: Id, args: Vec<Generic<Id>>, typ: T) -> T {
        Self::alias_implicit(name, args, typ, false)
    }

    pub fn alias_implicit(name: Id, args: Vec<Generic<Id>>, typ: T, is_implicit: bool) -> T {
        T::from(Type::Alias(AliasRef {
            index: 0,
            group: Arc::from(vec![AliasData {
                name,
                args,
                typ,
                is_implicit,
            }]),
        }))
    }

    pub fn ident(id: KindedIdent<Id>) -> T {
        T::from(Type::Ident(id))
    }

    pub fn projection(id: AppVec<Id>) -> T {
        T::from(Type::Projection(id))
    }

    pub fn function_builtin() -> T {
        Type::builtin(BuiltinType::Function)
    }

    pub fn string() -> T {
        Type::builtin(BuiltinType::String)
    }

    pub fn char() -> T {
        Type::builtin(BuiltinType::Char)
    }

    pub fn byte() -> T {
        Type::builtin(BuiltinType::Byte)
    }

    pub fn int() -> T {
        Type::builtin(BuiltinType::Int)
    }

    pub fn float() -> T {
        Type::builtin(BuiltinType::Float)
    }

    pub fn unit() -> T {
        Type::record(vec![], vec![])
    }
}

impl<Id, T> Type<Id, T>
where
    T: TypePtr<Id = Id>,
{
    pub fn is_array(&self) -> bool {
        match self {
            Type::App(typ, _) => match &**typ {
                Type::Builtin(BuiltinType::Array) => true,
                _ => false,
            },
            _ => false,
        }
    }

    fn is_simple_constructor(&self) -> bool {
        let mut typ = self;
        while let Some((_, ret)) = typ.as_function() {
            typ = ret;
        }
        match typ {
            Type::Opaque => true,
            _ => false,
        }
    }

    pub fn as_function(&self) -> Option<(&T, &T)> {
        self.as_function_with_type().map(|t| (t.1, t.2))
    }

    pub fn as_explicit_function(&self) -> Option<(&T, &T)> {
        self.as_function_with_type().and_then(|t| {
            if t.0 == ArgType::Explicit {
                Some((t.1, t.2))
            } else {
                None
            }
        })
    }

    pub fn as_function_with_type(&self) -> Option<(ArgType, &T, &T)> {
        match *self {
            Type::Function(arg_type, ref arg, ref ret) => return Some((arg_type, arg, ret)),
            Type::App(ref app, ref args) => {
                if args.len() == 2 {
                    if let Type::Builtin(BuiltinType::Function) = **app {
                        return Some((ArgType::Explicit, &args[0], &args[1]));
                    }
                } else if args.len() == 1 {
                    if let Type::App(ref app, ref args2) = **app {
                        if let Type::Builtin(BuiltinType::Function) = **app {
                            return Some((ArgType::Explicit, &args2[0], &args[0]));
                        }
                    }
                }
            }
            _ => (),
        }
        None
    }

    pub fn unapplied_args(&self) -> Cow<[T]>
    where
        T: Clone,
    {
        match *self {
            Type::App(ref f, ref args) => {
                let mut f = f;
                let mut extra_args = Vec::new();
                while let Type::App(ref f2, ref args2) = **f {
                    f = f2;
                    extra_args.extend(args2.iter().rev().cloned());
                }
                if extra_args.is_empty() {
                    Cow::Borrowed(args)
                } else {
                    extra_args.reverse();
                    extra_args.extend(args.iter().cloned());
                    Cow::Owned(extra_args)
                }
            }
            _ => Cow::Borrowed(&[]),
        }
    }

    pub fn alias_ident(&self) -> Option<&Id> {
        match self {
            Type::App(id, _) => id.alias_ident(),
            Type::Ident(id) => Some(&id.name),
            Type::Alias(alias) => Some(&alias.name),
            _ => None,
        }
    }

    pub fn applied_alias(&self) -> Option<&AliasRef<Id, T>> {
        match *self {
            Type::Alias(ref alias) => Some(alias),
            Type::App(ref alias, _) => alias.applied_alias(),
            _ => None,
        }
    }

    pub fn is_non_polymorphic_record(&self) -> bool {
        match *self {
            Type::Record(ref row)
            | Type::ExtendRow { rest: ref row, .. }
            | Type::ExtendTypeRow { rest: ref row, .. } => row.is_non_polymorphic_record(),
            Type::EmptyRow => true,
            _ => false,
        }
    }

    pub fn params(&self) -> &[Generic<Id>] {
        match *self {
            Type::Alias(ref alias) => alias.typ.params(),
            _ => &[],
        }
    }

    pub fn kind<'k>(&'k self, cache: &'k KindCache) -> Cow<'k, ArcKind> {
        self.kind_(cache, 0)
    }

    fn kind_<'k>(&'k self, cache: &'k KindCache, applied_args: usize) -> Cow<'k, ArcKind> {
        let mut immediate_kind = match *self {
            Type::Function(_, _, _) => Cow::Borrowed(&cache.typ),
            Type::App(ref t, ref args) => t.kind_(cache, args.len()),
            Type::Error => Cow::Borrowed(&cache.error),
            Type::Hole => Cow::Borrowed(&cache.hole),
            Type::Opaque | Type::Builtin(_) | Type::Record(_) | Type::Variant(_) => {
                Cow::Owned(Kind::typ())
            }
            Type::EmptyRow | Type::ExtendRow { .. } | Type::ExtendTypeRow { .. } => {
                Cow::Owned(Kind::row())
            }
            Type::Effect(_) => {
                let t = Kind::typ();
                Cow::Owned(Kind::function(t.clone(), t))
            }
            Type::Forall(_, ref typ) => typ.kind_(cache, applied_args),
            Type::Variable(ref var) => Cow::Borrowed(&var.kind),
            Type::Skolem(ref skolem) => Cow::Borrowed(&skolem.kind),
            Type::Generic(ref gen) => Cow::Borrowed(&gen.kind),
            // FIXME can be another kind
            Type::Ident(_) | Type::Projection(_) => Cow::Owned(cache.typ()),
            Type::Alias(ref alias) => {
                return if alias.params().len() < applied_args {
                    alias.typ.kind_(cache, applied_args - alias.params().len())
                } else {
                    let mut kind = alias.typ.kind_(cache, 0).into_owned();
                    for arg in &alias.params()[applied_args..] {
                        kind = Kind::function(arg.kind.clone(), kind)
                    }
                    Cow::Owned(kind)
                };
            }
        };
        for _ in 0..applied_args {
            immediate_kind = match immediate_kind {
                Cow::Borrowed(k) => match **k {
                    Kind::Function(_, ref ret) => Cow::Borrowed(ret),
                    _ => return Cow::Borrowed(k),
                },
                Cow::Owned(k) => match *k {
                    Kind::Function(_, ref ret) => Cow::Owned(ret.clone()),
                    _ => return Cow::Owned(k.clone()),
                },
            };
        }
        immediate_kind
    }
}

impl<T> Type<Symbol, T>
where
    T: TypePtr<Id = Symbol>,
{
    /// Returns the name of `self`
    /// Example:
    /// Option a => Option
    /// Int => Int
    pub fn name(&self) -> Option<&SymbolRef> {
        if let Some(id) = self.alias_ident() {
            return Some(&**id);
        }

        match *self {
            Type::Function(..) => Some(BuiltinType::Function.symbol()),
            Type::App(ref id, _) => match **id {
                Type::Builtin(b) => Some(b.symbol()),
                _ => None,
            },
            Type::Builtin(b) => Some(b.symbol()),
            Type::Effect(_) => Some(SymbolRef::new("Effect")),
            _ => None,
        }
    }

    pub fn owned_name(&self) -> Option<SymbolKey> {
        if let Some(id) = self.alias_ident() {
            return Some(SymbolKey::Owned(id.clone()));
        }

        match *self {
            Type::Function(..) => Some(SymbolKey::Ref(BuiltinType::Function.symbol())),
            Type::App(ref id, _) => match **id {
                Type::Builtin(b) => Some(SymbolKey::Ref(b.symbol())),
                _ => None,
            },
            Type::Builtin(b) => Some(SymbolKey::Ref(b.symbol())),
            Type::Effect(_) => Some(SymbolKey::Ref(SymbolRef::new("Effect"))),
            _ => None,
        }
    }
}

#[derive(Eq, Clone)]
pub enum SymbolKey {
    Owned(Symbol),
    Ref(&'static SymbolRef),
}

impl fmt::Debug for SymbolKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", Borrow::<SymbolRef>::borrow(self))
    }
}

impl fmt::Display for SymbolKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", Borrow::<SymbolRef>::borrow(self))
    }
}

impl Hash for SymbolKey {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        Borrow::<SymbolRef>::borrow(self).hash(state)
    }
}

impl PartialEq for SymbolKey {
    fn eq(&self, other: &Self) -> bool {
        Borrow::<SymbolRef>::borrow(self) == Borrow::<SymbolRef>::borrow(other)
    }
}

impl PartialOrd for SymbolKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Borrow::<SymbolRef>::borrow(self).partial_cmp(Borrow::<SymbolRef>::borrow(other))
    }
}

impl Ord for SymbolKey {
    fn cmp(&self, other: &Self) -> Ordering {
        Borrow::<SymbolRef>::borrow(self).cmp(Borrow::<SymbolRef>::borrow(other))
    }
}

impl Deref for SymbolKey {
    type Target = SymbolRef;

    fn deref(&self) -> &Self::Target {
        match *self {
            SymbolKey::Owned(ref s) => s,
            SymbolKey::Ref(s) => s,
        }
    }
}

impl Borrow<SymbolRef> for SymbolKey {
    fn borrow(&self) -> &SymbolRef {
        self
    }
}

#[derive(Clone)]
struct ArcTypeInner<Id = Symbol> {
    typ: Type<Id, ArcType<Id>>,
    flags: Flags,
}

forward_eq_hash! { <Id> for ArcTypeInner<Id> { typ } }

/// A shared type which is atomically reference counted
#[derive(Eq, PartialEq, Hash)]
pub struct ArcType<Id = Symbol> {
    typ: Arc<ArcTypeInner<Id>>,
}

impl<Id> Default for ArcType<Id>
where
    Id: PartialEq,
{
    fn default() -> Self {
        Type::hole()
    }
}

#[cfg(feature = "serde")]
impl<'de, Id> DeserializeState<'de, Seed<Id, ArcType<Id>>> for ArcType<Id>
where
    Id: DeserializeState<'de, Seed<Id, ArcType<Id>>> + Clone + ::std::any::Any + PartialEq,
{
    fn deserialize_state<D>(
        seed: &mut Seed<Id, ArcType<Id>>,
        deserializer: D,
    ) -> Result<Self, D::Error>
    where
        D: crate::serde::de::Deserializer<'de>,
    {
        use crate::serialization::SharedSeed;
        let seed = SharedSeed::new(seed);
        crate::serde::de::DeserializeSeed::deserialize(seed, deserializer).map(ArcType::new)
    }
}

impl<Id> Clone for ArcType<Id> {
    fn clone(&self) -> ArcType<Id> {
        ArcType {
            typ: self.typ.clone(),
        }
    }
}

impl<Id: fmt::Debug> fmt::Debug for ArcType<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<Id: AsRef<str> + AsId<Id>> fmt::Display for ArcType<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", TypeFormatter::new(self))
    }
}

impl<Id> fmt::Pointer for ArcType<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:p}", &**self)
    }
}

impl<Id> Borrow<Type<Id, ArcType<Id>>> for ArcType<Id> {
    fn borrow(&self) -> &Type<Id, ArcType<Id>> {
        self
    }
}

impl<Id> Deref for ArcType<Id> {
    type Target = Type<Id, ArcType<Id>>;

    fn deref(&self) -> &Type<Id, ArcType<Id>> {
        &self.typ.typ
    }
}

impl<Id> HasSpan for ArcType<Id> {
    fn span(&self) -> Span<BytePos> {
        Span::new(0.into(), 0.into())
    }
}

impl<Id> HasMetadata for ArcType<Id> {
    fn metadata(&self) -> Option<&Metadata> {
        None
    }
}

pub fn row_iter<T>(typ: &T) -> RowIterator<T> {
    RowIterator { typ, current: 0 }
}

pub fn row_iter_mut<Id, T>(typ: &mut T) -> RowIteratorMut<Id, T> {
    RowIteratorMut {
        fields: [].iter_mut(),
        rest: Some(typ),
    }
}

pub fn type_field_iter<T>(typ: &T) -> TypeFieldIterator<T> {
    TypeFieldIterator { typ, current: 0 }
}

pub fn remove_forall<'a, Id, T>(typ: &'a T) -> &'a T
where
    T: TypePtr<Id = Id>,
    Id: 'a,
{
    match **typ {
        Type::Forall(_, ref typ) => remove_forall(typ),
        _ => typ,
    }
}

pub fn remove_forall_mut<'a, Id, T>(typ: &'a mut T) -> &'a mut T
where
    T: TypePtr<Id = Id> + DerefMut<Target = Type<Id, T>>,
    Id: 'a,
{
    if let Type::Forall(_, _) = **typ {
        match **typ {
            Type::Forall(_, ref mut typ) => remove_forall_mut(typ),
            _ => unreachable!(),
        }
    } else {
        typ
    }
}

pub trait TypeAlloc<T: TypePtr>: Sized {
    type Elem;

    fn alloc_extend(
        iter: impl IntoIterator<Item = Self::Elem>,
        context: &mut (impl ?Sized + TypeContext<T::Id, T>),
    ) -> Self;
}

macro_rules! type_alloc_impl {
    (T [$($where_: tt)*] $ty: ty, $elem: ty => $method: ident) => {
        impl<$($where_)*> TypeAlloc<T> for $ty
        where
            T: TypePtr,
        {
            type Elem = $elem;

            fn alloc_extend(
                iter: impl IntoIterator<Item = Self::Elem>,
                context: &mut (impl ?Sized + TypeContext<T::Id, T>),
            ) -> Self {
                context.$method(iter)
            }
        }
    }
}

type_alloc_impl! { T [T: TypePtr<Generics = Self>] Vec<Generic<<T as TypePtr>::Id>>, Generic<<T as TypePtr>::Id> => intern_generics }
type_alloc_impl! { T ['ast, T: TypePtr<Generics = Self>] &'ast mut [Generic<<T as TypePtr>::Id>], Generic<<T as TypePtr>::Id> => intern_generics }

type_alloc_impl! { T [T: TypePtr<Types = Self>] AppVec<T>, T => intern_types }
type_alloc_impl! { T ['ast, T: TypePtr<Types = Self>] &'ast mut [T], T => intern_types }

type_alloc_impl! { T [T: TypePtr<Fields = Self>] Vec<Field<<T as TypePtr>::SpannedId, T>>, Field<<T as TypePtr>::SpannedId, T> => intern_fields }
type_alloc_impl! { T ['ast, T: TypePtr<Fields = Self>] &'ast mut [Field<<T as TypePtr>::SpannedId, T>], Field<<T as TypePtr>::SpannedId, T> => intern_fields }

type_alloc_impl! { T [T: TypePtr<TypeFields = Self>] Vec<Field<<T as TypePtr>::SpannedId, Alias<<T as TypePtr>::Id, T>>>, Field<<T as TypePtr>::SpannedId, Alias<<T as TypePtr>::Id, T>> => intern_type_fields }
type_alloc_impl! { T ['ast, T: TypePtr<TypeFields = Self>] &'ast mut [Field<<T as TypePtr>::SpannedId, Alias<<T as TypePtr>::Id, T>>], Field<<T as TypePtr>::SpannedId, Alias<<T as TypePtr>::Id, T>> => intern_type_fields }

pub trait TypePtr: Deref<Target = Type<<Self as TypePtr>::Id, Self>> + Sized {
    type Id;
    type SpannedId;
    type Types: TypeAlloc<Self> + Deref<Target = [Self]> + Default;
    type Generics: TypeAlloc<Self> + Deref<Target = [Generic<Self::Id>]> + Default;
    type Fields: TypeAlloc<Self> + Deref<Target = [Field<Self::SpannedId, Self>]> + Default;
    type TypeFields: TypeAlloc<Self>
        + Deref<Target = [Field<Self::SpannedId, Alias<Self::Id, Self>>]>
        + Default;

    fn flags(&self) -> Flags {
        Flags::all()
    }

    fn spine(&self) -> &Self {
        match &**self {
            Type::App(ref id, _) => id.spine(),
            _ => self,
        }
    }

    fn display<A>(&self, width: usize) -> TypeFormatter<Self::Id, Self, A>
    where
        Self::Id: AsRef<str>,
        Self::SpannedId: AsRef<str>,
    {
        TypeFormatter::new(self).width(width)
    }
}

pub trait TypeExt:
    TypePtr<
        Types = AppVec<Self>,
        Generics = Vec<Generic<<Self as TypePtr>::Id>>,
        Fields = Vec<Field<<Self as TypePtr>::SpannedId, Self>>,
        TypeFields = Vec<Field<<Self as TypePtr>::SpannedId, Alias<<Self as TypePtr>::Id, Self>>>,
    > + Clone
    + Sized
{
    fn strong_count(typ: &Self) -> usize;

    /// Returns an iterator over all type fields in a record.
    /// `{ Test, Test2, x, y } => [Test, Test2]`
    fn type_field_iter(&self) -> TypeFieldIterator<Self> {
        type_field_iter(self)
    }

    fn arg_iter(&self) -> ArgIterator<Self> {
        arg_iter(self)
    }

    fn implicit_arg_iter(&self) -> ImplicitArgIterator<Self> {
        implicit_arg_iter(self)
    }

    /// Returns an iterator over all fields in a record.
    /// `{ Test, Test2, x, y } => [x, y]`
    fn row_iter(&self) -> RowIterator<Self> {
        row_iter(self)
    }

    fn remove_implicit_args<'a>(&'a self) -> &'a Self {
        match **self {
            Type::Function(ArgType::Implicit, _, ref typ) => typ.remove_implicit_args(),
            _ => self,
        }
    }

    fn remove_forall<'a>(&'a self) -> &'a Self {
        remove_forall(self)
    }

    fn remove_forall_and_implicit_args<'a>(&'a self) -> &'a Self {
        match **self {
            Type::Function(ArgType::Implicit, _, ref typ) => typ.remove_forall_and_implicit_args(),
            Type::Forall(_, ref typ) => typ.remove_forall_and_implicit_args(),
            _ => self,
        }
    }

    fn replace_generics(
        &self,
        interner: &mut impl TypeContext<Self::Id, Self>,
        named_variables: &mut FnvMap<Self::Id, Self>,
    ) -> Option<Self>
    where
        Self::Id: Clone + Eq + Hash,
        Self::SpannedId: Clone,
        Self: Clone,
        Self::Types: Clone,
        Self::Generics: Clone,
        Self::Fields: Clone,
    {
        if named_variables.is_empty() {
            None
        } else {
            self.replace_generics_(interner, named_variables)
        }
    }

    fn replace_generics_(
        &self,
        interner: &mut impl TypeContext<Self::Id, Self>,
        named_variables: &mut FnvMap<Self::Id, Self>,
    ) -> Option<Self>
    where
        Self::Id: Clone + Eq + Hash,
        Self::SpannedId: Clone,
        Self: Clone,
        Self::Types: Clone,
        Self::Generics: Clone,
        Self::Fields: Clone,
    {
        if !self.flags().intersects(Flags::HAS_GENERICS) {
            return None;
        }

        match &**self {
            Type::Generic(generic) => named_variables.get(&generic.id).cloned(),
            Type::Forall(params, typ) => {
                let removed: AppVec<_> = params
                    .iter()
                    .flat_map(|param| named_variables.remove_entry(&param.id))
                    .collect();

                let new_typ = typ.replace_generics(interner, named_variables);
                let new_typ = new_typ.map(|typ| interner.intern(Type::Forall(params.clone(), typ)));

                named_variables.extend(removed);

                new_typ
            }
            _ => walk_move_type_opt(
                self,
                &mut InternerVisitor::control(interner, |interner, typ: &Self| {
                    typ.replace_generics_(interner, named_variables)
                }),
            ),
        }
    }

    fn forall_scope_iter(&self) -> ForallScopeIter<Self> {
        ForallScopeIter {
            typ: self,
            offset: 0,
        }
    }

    fn pretty<'a, A>(&'a self, arena: &'a Arena<'a, A>) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        Self::Id: AsRef<str> + 'a,
        Self::SpannedId: AsRef<str> + AsId<Self::Id> + 'a,
        A: Clone,
        Self: HasMetadata + HasSpan,
    {
        top(self).pretty(&Printer::new(arena, &()))
    }

    /// Applies a list of arguments to a parameterised type, returning `Some`
    /// if the substitution was successful.
    ///
    /// Example:
    ///
    /// ```text
    /// self = forall e t . | Err e | Ok t
    /// args = [Error, Option a]
    /// result = | Err Error | Ok (Option a)
    /// ```
    fn apply_args<'a>(
        &self,
        params: &[Generic<Self::Id>],
        args: &'a [Self],
        interner: &mut impl TypeContext<Self::Id, Self>,
        named_variables: &mut FnvMap<Self::Id, Self>,
    ) -> Option<Self>
    where
        Self::Id: Clone + Eq + Hash,
        Self::SpannedId: Clone,
        Self: fmt::Display,
        Self::Id: fmt::Display,
        Self::Types: Clone + FromIterator<Self>,
        Self::Generics: Clone,
        Self::Fields: Clone,
    {
        let (non_replaced_type, unapplied_args) =
            self.arg_application(params, args, interner, named_variables)?;

        let non_replaced_type = non_replaced_type
            .replace_generics(interner, named_variables)
            .unwrap_or_else(|| non_replaced_type.clone());
        Some(interner.app(non_replaced_type, unapplied_args.iter().cloned().collect()))
    }

    fn arg_application<'a>(
        &self,
        params: &[Generic<Self::Id>],
        args: &'a [Self],
        interner: &mut impl TypeContext<Self::Id, Self>,
        named_variables: &mut FnvMap<Self::Id, Self>,
    ) -> Option<(Self, &'a [Self])>
    where
        Self::Id: Clone + Eq + Hash,
        Self: fmt::Display,
        Self::Id: fmt::Display,
        Self::Types: FromIterator<Self>,
        Self::Generics: Clone,
        Self::Fields: Clone,
    {
        // If the alias was just hiding an error then any application is also an error as we have
        // no way of knowing how many arguments it should take
        if let Type::Error = &**self {
            return Some((self.clone(), &[]));
        }

        let typ = if params.len() == args.len() {
            Cow::Borrowed(self)
        } else {
            // It is ok to take the type only if it is fully applied or if it
            // the missing argument only appears in order at the end, i.e:
            //
            // type Test a b c = Type (a Int) b c
            //
            // Test a b == Type (a Int) b
            // Test a == Type (a Int)
            // Test == ??? (Impossible to do a sane substitution)
            let (d, arg_types) = split_app(self);
            let allowed_missing_args = arg_types
                .iter()
                .rev()
                .zip(params.iter().rev())
                .take_while(|&(l, r)| match **l {
                    Type::Generic(ref g) => g == r,
                    _ => false,
                })
                .count();

            if params.len() > allowed_missing_args + args.len() {
                return None;
            }
            // Remove the args at the end of the aliased type
            let arg_types = arg_types
                .iter()
                .take(arg_types.len() + args.len() - params.len())
                .cloned()
                .collect();

            let d = d.cloned().unwrap_or_else(|| interner.function_builtin());
            Cow::Owned(interner.app(d, arg_types))
        };

        named_variables.extend(
            params
                .iter()
                .map(|g| g.id.clone())
                .zip(args.iter().cloned()),
        );

        Some((typ.into_owned(), &args[params.len().min(args.len())..]))
    }

    fn instantiate_generics(
        &self,
        interner: &mut impl Substitution<Self::Id, Self>,
        named_variables: &mut FnvMap<Self::Id, Self>,
    ) -> Self
    where
        Self::Id: Clone + Eq + Hash,
        Self::SpannedId: Clone,
        Self::Types: Clone,
        Self::Generics: Clone,
        Self::Fields: Clone,
    {
        let mut typ = self;
        while let Type::Forall(params, inner_type) = &**typ {
            named_variables.extend(
                params
                    .iter()
                    .map(|param| (param.id.clone(), interner.new_var())),
            );
            typ = inner_type;
        }
        if named_variables.is_empty() {
            typ.clone()
        } else {
            typ.replace_generics(interner, named_variables)
                .unwrap_or_else(|| typ.clone())
        }
    }

    fn skolemize(
        &self,
        interner: &mut impl Substitution<Self::Id, Self>,
        named_variables: &mut FnvMap<Self::Id, Self>,
    ) -> Self
    where
        Self::Id: Clone + Eq + Hash,
        Self::SpannedId: Clone,
        Self::Types: Clone,
        Self::Generics: Clone,
        Self::Fields: Clone,
    {
        let mut typ = self;
        while let Type::Forall(ref params, ref inner_type) = **typ {
            let iter = params.iter().map(|param| {
                (
                    param.id.clone(),
                    interner.new_skolem(param.id.clone(), param.kind.clone()),
                )
            });
            named_variables.extend(iter);
            typ = inner_type;
        }
        if named_variables.is_empty() {
            typ.clone()
        } else {
            typ.replace_generics(interner, named_variables)
                .unwrap_or_else(|| typ.clone())
        }
    }

    fn skolemize_in(
        &self,
        interner: &mut impl Substitution<Self::Id, Self>,
        named_variables: &mut FnvMap<Self::Id, Self>,
        f: impl FnOnce(Self) -> Self,
    ) -> Self
    where
        Self::Id: Clone + Eq + Hash,
        Self::SpannedId: Clone,
        Self::Types: Clone,
        Self::Generics: FromIterator<Generic<Self::Id>> + Clone,
        Self::Fields: Clone,
    {
        let skolemized = self.skolemize(interner, named_variables);
        let new_type = f(skolemized);
        interner.with_forall(new_type, self)
    }
}

pub fn forall_params<'a, T, Id>(mut typ: &'a T) -> impl Iterator<Item = &'a Generic<Id>>
where
    Id: 'a,
    T: TypePtr<Id = Id>,
{
    let mut i = 0;
    iter::repeat(()).scan((), move |_, _| {
        while let Type::Forall(ref params, ref inner_type) = **typ {
            if i < params.len() {
                i += 1;
                return Some(&params[i - 1]);
            } else {
                i = 0;
                typ = inner_type;
            }
        }
        None
    })
}

impl<Id> ArcType<Id>
where
    Id: PartialEq,
{
    pub fn new(typ: Type<Id, ArcType<Id>>) -> ArcType<Id> {
        let flags = Flags::from_type(&typ);
        Self::with_flags(typ, flags)
    }
}

impl<Id> TypePtr for ArcType<Id> {
    type Id = Id;
    type SpannedId = Id;
    type Types = AppVec<Self>;
    type Generics = Vec<Generic<Id>>;
    type Fields = Vec<Field<Id, Self>>;
    type TypeFields = Vec<Field<Id, Alias<Id, Self>>>;

    fn flags(&self) -> Flags {
        self.typ.flags
    }
}

impl<Id> TypeExt for ArcType<Id> {
    fn strong_count(typ: &ArcType<Id>) -> usize {
        Arc::strong_count(&typ.typ)
    }
}

pub struct ForallScopeIter<'a, T: 'a> {
    pub typ: &'a T,
    offset: usize,
}

impl<'a, T, Id: 'a> Iterator for ForallScopeIter<'a, T>
where
    T: TypePtr<Id = Id>,
{
    type Item = &'a Generic<Id>;

    fn next(&mut self) -> Option<Self::Item> {
        match **self.typ {
            Type::Forall(ref params, ref typ) => {
                let offset = self.offset;
                let item = params.get(offset).map(|param| {
                    self.offset += 1;
                    param
                });
                match item {
                    Some(_) => item,
                    None => {
                        self.typ = typ;
                        self.next()
                    }
                }
            }
            _ => None,
        }
    }
}

impl<Id> From<Type<Id, ArcType<Id>>> for ArcType<Id>
where
    Id: PartialEq,
{
    fn from(typ: Type<Id, ArcType<Id>>) -> ArcType<Id> {
        ArcType::new(typ)
    }
}

impl<Id> From<(Type<Id, ArcType<Id>>, Flags)> for ArcType<Id> {
    fn from((typ, flags): (Type<Id, ArcType<Id>>, Flags)) -> ArcType<Id> {
        ArcType::with_flags(typ, flags)
    }
}

#[derive(Clone)]
pub struct TypeFieldIterator<'a, T: 'a> {
    typ: &'a T,
    current: usize,
}

impl<'a, Id: 'a, T> Iterator for TypeFieldIterator<'a, T>
where
    T: TypePtr<Id = Id>,
{
    type Item = &'a Field<T::SpannedId, Alias<Id, T>>;

    fn next(&mut self) -> Option<&'a Field<T::SpannedId, Alias<Id, T>>> {
        match **self.typ {
            Type::ExtendRow { ref rest, .. } | Type::Record(ref rest) => {
                self.typ = rest;
                self.next()
            }
            Type::ExtendTypeRow {
                ref types,
                ref rest,
            } => {
                let current = self.current;
                self.current += 1;
                types.get(current).or_else(|| {
                    self.current = 0;
                    self.typ = rest;
                    self.next()
                })
            }
            _ => None,
        }
    }
}

#[derive(Clone)]
pub struct RowIterator<'a, T: 'a> {
    typ: &'a T,
    current: usize,
}

impl<'a, T> RowIterator<'a, T> {
    pub fn current_type(&self) -> &'a T {
        self.typ
    }
}

impl<'a, Id: 'a, T> Iterator for RowIterator<'a, T>
where
    T: TypePtr<Id = Id>,
{
    type Item = &'a Field<T::SpannedId, T>;

    fn next(&mut self) -> Option<&'a Field<T::SpannedId, T>> {
        match **self.typ {
            Type::Record(ref row) | Type::Variant(ref row) => {
                self.typ = row;
                self.next()
            }
            Type::ExtendRow {
                ref fields,
                ref rest,
                ..
            } => {
                let current = self.current;
                self.current += 1;
                fields.get(current).or_else(|| {
                    self.current = 0;
                    self.typ = rest;
                    self.next()
                })
            }
            Type::ExtendTypeRow { ref rest, .. } => {
                self.typ = rest;
                self.next()
            }
            _ => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<'a, Id: 'a, T> ExactSizeIterator for RowIterator<'a, T>
where
    T: TypePtr<Id = Id>,
{
    fn len(&self) -> usize {
        let mut typ = self.typ;
        let mut size = 0;
        loop {
            typ = match **typ {
                Type::Record(ref row) | Type::Variant(ref row) => row,
                Type::ExtendRow {
                    ref fields,
                    ref rest,
                    ..
                } => {
                    size += fields.len();
                    rest
                }
                Type::ExtendTypeRow { ref rest, .. } => rest,
                _ => break,
            };
        }
        size
    }
}

pub struct RowIteratorMut<'a, SpId: 'a, T: 'a> {
    fields: ::std::slice::IterMut<'a, Field<SpId, T>>,
    rest: Option<&'a mut T>,
}

impl<'a, SpId, T> RowIteratorMut<'a, SpId, T> {
    pub fn current_type(&mut self) -> &mut T {
        self.rest.as_mut().unwrap()
    }
}

impl<'a, SpId: 'a, Id: 'a, T: 'a> Iterator for RowIteratorMut<'a, SpId, T>
where
    T: DerefMut<Target = Type<Id, T>> + TypePtr<Id = Id, SpannedId = SpId>,
    T::Fields: DerefMut<Target = [Field<SpId, T>]>,
{
    type Item = &'a mut Field<SpId, T>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(x) = self.fields.next() {
                return Some(x);
            }
            match ***self.rest.as_ref()? {
                Type::Record(_)
                | Type::Variant(_)
                | Type::ExtendRow { .. }
                | Type::ExtendTypeRow { .. } => (),
                _ => return None,
            };

            let rest = mem::replace(&mut self.rest, None)?;
            self.rest = match **rest {
                Type::Record(ref mut row) | Type::Variant(ref mut row) => Some(row),
                Type::ExtendRow {
                    ref mut fields,
                    ref mut rest,
                    ..
                } => {
                    self.fields = fields.iter_mut();
                    Some(rest)
                }
                Type::ExtendTypeRow { ref mut rest, .. } => Some(rest),
                _ => unreachable!(),
            };
        }
    }
}

fn split_top<'a, Id, T>(self_: &'a T) -> Option<(Option<&'a T>, Cow<[T]>)>
where
    T: TypePtr<Id = Id> + Clone,
    Id: 'a,
{
    Some(match **self_ {
        Type::App(ref f, ref args) => (Some(f), Cow::Borrowed(args)),
        Type::Function(_, ref a, ref r) => (None, Cow::Owned(vec![a.clone(), r.clone()])),
        _ => return None,
    })
}

fn clone_cow<'a, T>(cow: Cow<'a, [T]>) -> impl DoubleEndedIterator<Item = T> + 'a
where
    T: ToOwned + Clone,
{
    use itertools::Either;

    match cow {
        Cow::Borrowed(ts) => Either::Left(ts.iter().cloned()),
        Cow::Owned(ts) => Either::Right(ts.into_iter()),
    }
}

pub fn split_app<'a, Id, T>(self_: &'a T) -> (Option<&'a T>, Cow<[T]>)
where
    T: TypePtr<Id = Id> + Clone,
    Id: 'a,
{
    match split_top(self_) {
        Some((f, args)) => {
            let mut f = f;
            let mut extra_args = Vec::new();
            while let Some((f2, args2)) = f.and_then(split_top) {
                f = f2;
                extra_args.extend(clone_cow(args2).rev());
            }
            if extra_args.is_empty() {
                (f, args)
            } else {
                extra_args.reverse();
                extra_args.extend(clone_cow(args));
                (f, Cow::Owned(extra_args))
            }
        }
        None => (Some(self_), Cow::Borrowed(&[][..])),
    }
}

pub fn ctor_args<Id, T>(typ: &T) -> ArgIterator<T>
where
    T: TypePtr<Id = Id>,
{
    ArgIterator { typ }
}

pub struct ArgIterator<'a, T: 'a> {
    /// The current type being iterated over. After `None` has been returned this is the return
    /// type.
    pub typ: &'a T,
}

/// Constructs an iterator over a functions arguments
pub fn arg_iter<Id, T>(typ: &T) -> ArgIterator<T>
where
    T: TypePtr<Id = Id>,
{
    ArgIterator { typ }
}

impl<'a, Id, T> Iterator for ArgIterator<'a, T>
where
    Id: 'a,
    T: TypePtr<Id = Id>,
{
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> {
        self.typ.as_function().map(|(arg, ret)| {
            self.typ = ret;
            arg
        })
    }
}

pub struct ImplicitArgIterator<'a, T: 'a> {
    /// The current type being iterated over. After `None` has been returned this is the return
    /// type.
    pub typ: &'a T,
}

/// Constructs an iterator over a functions arguments
pub fn implicit_arg_iter<Id, T>(typ: &T) -> ImplicitArgIterator<T>
where
    T: TypePtr<Id = Id>,
{
    ImplicitArgIterator { typ }
}

impl<'a, Id, T> Iterator for ImplicitArgIterator<'a, T>
where
    Id: 'a,
    T: TypePtr<Id = Id>,
{
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> {
        self.typ
            .as_function_with_type()
            .and_then(|(arg_type, arg, ret)| {
                if arg_type == ArgType::Implicit {
                    self.typ = ret;
                    Some(arg)
                } else {
                    None
                }
            })
    }
}

impl<Id> ArcType<Id> {
    fn with_flags(typ: Type<Id, ArcType<Id>>, flags: Flags) -> ArcType<Id> {
        let typ = Arc::new(ArcTypeInner { typ, flags });
        ArcType { typ }
    }

    pub fn set(into: &mut Self, typ: Type<Id, Self>)
    where
        Id: Clone + PartialEq,
    {
        let into = Arc::make_mut(&mut into.typ);
        into.flags = Flags::from_type(&typ);
        into.typ = typ;
    }

    /// Returns the lowest level which this type contains. The level informs from where type
    /// variables where created.
    pub fn level(&self) -> u32 {
        use std::cmp::min;
        fold_type(
            self,
            |typ, level| match **typ {
                Type::Variable(ref var) => min(var.id, level),
                _ => level,
            },
            u32::max_value(),
        )
    }

    pub fn needs_generalize(&self) -> bool
    where
        Id: PartialEq,
    {
        self.flags().intersects(Flags::NEEDS_GENERALIZE)
    }

    pub fn forall_params(&self) -> impl Iterator<Item = &Generic<Id>> {
        forall_params(self)
    }
}

impl TypeVariable {
    pub fn new(var: u32) -> TypeVariable {
        TypeVariable::with_kind(Kind::Type, var)
    }

    pub fn with_kind(kind: Kind, var: u32) -> TypeVariable {
        TypeVariable {
            kind: ArcKind::new(kind),
            id: var,
        }
    }
}

impl fmt::Display for TypeVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.id.fmt(f)
    }
}

impl<Id: fmt::Display> fmt::Display for Generic<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.id.fmt(f)
    }
}

impl fmt::Display for BuiltinType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.to_str().fmt(f)
    }
}

#[derive(PartialEq, Copy, Clone, PartialOrd)]
pub enum Prec {
    /// The type exists in the top context, no parentheses needed.
    Top,
    /// The type exists in a function argument `Type -> a`, parentheses are
    /// needed if the type is a function `(b -> c) -> a`.
    Function,
    /// The type exists in a constructor argument `Option Type`, parentheses
    /// are needed for functions or other constructors `Option (a -> b)`
    /// `Option (Result a b)`.
    Constructor,
}

impl Prec {
    pub fn enclose<'a, A>(
        &self,
        limit: Prec,
        arena: &'a Arena<'a, A>,
        doc: DocBuilder<'a, Arena<'a, A>, A>,
    ) -> DocBuilder<'a, Arena<'a, A>, A> {
        if *self >= limit {
            chain![arena, "(", doc, ")"]
        } else {
            doc
        }
    }
}

#[doc(hidden)]
pub fn dt<T>(prec: Prec, typ: &T) -> DisplayType<T> {
    DisplayType { prec, typ }
}

fn top<T>(typ: &T) -> DisplayType<T> {
    dt(Prec::Top, typ)
}

pub struct DisplayType<'a, T: 'a> {
    prec: Prec,
    typ: &'a T,
}

pub trait ToDoc<'a, A, B, E> {
    fn to_doc(&'a self, allocator: &'a A, env: E) -> DocBuilder<'a, A, B>
    where
        A: DocAllocator<'a, B>;
}

impl<'a, I, A> ToDoc<'a, Arena<'a, A>, A, ()> for ArcType<I>
where
    I: AsRef<str> + AsId<I>,
    A: Clone,
{
    fn to_doc(&'a self, arena: &'a Arena<'a, A>, _: ()) -> DocBuilder<'a, Arena<'a, A>, A> {
        self.to_doc(arena, &() as &dyn Source)
    }
}

impl<'a, I, A> ToDoc<'a, Arena<'a, A>, A, &'a dyn Source> for ArcType<I>
where
    I: AsRef<str> + AsId<I>,
    A: Clone,
{
    fn to_doc(
        &'a self,
        arena: &'a Arena<'a, A>,
        source: &'a dyn Source,
    ) -> DocBuilder<'a, Arena<'a, A>, A> {
        let printer = Printer::new(arena, source);
        dt(Prec::Top, self).pretty(&printer)
    }
}

fn is_tuple<T>(typ: &T) -> bool
where
    T: TypePtr,
    T::SpannedId: AsRef<str>,
{
    match **typ {
        Type::Record(_) => {
            type_field_iter(typ).next().is_none()
                && row_iter(typ).enumerate().all(|(i, field)| {
                    let name = field.name.as_ref();
                    name.starts_with('_') && name[1..].parse() == Ok(i)
                })
        }
        _ => false,
    }
}

const INDENT: isize = 4;

impl<'a, I, T> DisplayType<'a, T>
where
    T: TypePtr<Id = I> + HasSpan + HasMetadata + 'a,
    I: AsRef<str> + 'a,
    T::SpannedId: AsRef<str> + AsId<I> + 'a,
{
    pub fn pretty<A>(&self, printer: &Printer<'a, I, A>) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        A: Clone,
    {
        let typ = self.typ;

        let doc = self.pretty_(printer);
        match **typ {
            Type::ExtendRow { .. } | Type::Variant(..) => doc,
            _ => {
                let comment = printer.comments_before(typ.span().start());
                comment.append(doc)
            }
        }
    }

    fn pretty_<A>(&self, printer: &Printer<'a, I, A>) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        A: Clone,
    {
        let arena = printer.arena;

        let p = self.prec;
        let typ = self.typ;

        match **typ {
            Type::Hole => arena.text("_"),
            Type::Error => arena.text("!"),
            Type::Opaque => arena.text("<opaque>"),
            Type::Forall(ref args, ref typ) => {
                let doc = chain![
                    arena,
                    chain![
                        arena,
                        "forall ",
                        arena.concat(
                            args.iter()
                                .map(|arg| { arena.text(arg.id.as_ref()).append(arena.line()) })
                        ),
                        "."
                    ]
                    .group(),
                    chain![
                        arena,
                        printer.space_before(typ.span().start()),
                        top(typ).pretty_(printer)
                    ]
                    .nest(INDENT)
                ];
                p.enclose(Prec::Function, arena, doc).group()
            }
            Type::Variable(ref var) => arena.text(format!("{}", var.id)),
            Type::Skolem(ref skolem) => {
                chain![arena, skolem.name.as_ref(), "@", skolem.id.to_string()]
            }
            Type::Generic(ref gen) => arena.text(gen.id.as_ref()),
            Type::Function(..) => self.pretty_function(printer).nest(INDENT),
            Type::App(ref t, ref args) => match self.typ.as_function() {
                Some(_) => self.pretty_function(printer).nest(INDENT),
                None => {
                    let doc = dt(Prec::Top, t).pretty_(printer);
                    let arg_doc = arena.concat(args.iter().map(|arg| {
                        printer
                            .space_before(arg.span().start())
                            .append(dt(Prec::Constructor, arg).pretty_(printer))
                    }));
                    let doc = doc.append(arg_doc.nest(INDENT));
                    p.enclose(Prec::Constructor, arena, doc).group()
                }
            },
            Type::Variant(ref row) => {
                let mut first = true;

                let mut doc = arena.nil();
                let mut row = row;
                loop {
                    row = match **row {
                        Type::EmptyRow => break,
                        Type::ExtendRow {
                            ref fields,
                            ref rest,
                            ..
                        } => {
                            doc = doc.append(arena.concat(fields.iter().map(|field| {
                                chain![
                                    arena,
                                    if first {
                                        first = false;
                                        arena.nil()
                                    } else {
                                        arena.hardline()
                                    },
                                    chain![
                                        arena,
                                        "| ",
                                        field.name.as_ref() as &str,
                                        if field.typ.is_simple_constructor() {
                                            arena.concat(arg_iter(&field.typ).map(|arg| {
                                                chain![
                                                    arena,
                                                    " ",
                                                    dt(Prec::Constructor, arg).pretty(printer)
                                                ]
                                            }))
                                        } else {
                                            chain![
                                                arena,
                                                " :",
                                                arena.line(),
                                                top(&field.typ).pretty(printer),
                                            ]
                                            .nest(INDENT)
                                        }
                                    ]
                                    .group()
                                ]
                            })));
                            rest
                        }
                        _ => {
                            doc = chain![
                                arena,
                                doc,
                                if first { arena.nil() } else { arena.hardline() },
                                ".. ",
                                top(row).pretty(printer)
                            ];
                            break;
                        }
                    };
                }

                p.enclose(Prec::Constructor, arena, doc).group()
            }

            Type::Effect(ref row) => Self::pretty_record_like(
                row,
                printer,
                "[|",
                &mut |field: &'a Field<T::SpannedId, T>| {
                    chain![
                        arena,
                        pretty_print::doc_comment(arena, field.typ.comment()),
                        pretty_print::ident(arena, field.name.as_ref() as &str),
                        " : "
                    ]
                },
                "|]",
            ),

            Type::Builtin(ref t) => match *t {
                BuiltinType::Function => chain![arena, "(", t.to_str(), ")"],
                _ => arena.text(t.to_str()),
            },
            Type::Record(ref row) => {
                if is_tuple(typ) {
                    Self::pretty_record_like(row, printer, "(", &mut |_| arena.nil(), ")")
                } else {
                    let mut pretty_record_field = |field: &'a Field<T::SpannedId, T>| {
                        chain![
                            arena,
                            pretty_print::doc_comment(arena, field.typ.comment()),
                            pretty_print::ident(arena, field.name.as_ref() as &str),
                            " : "
                        ]
                    };
                    Self::pretty_record_like(row, printer, "{", &mut pretty_record_field, "}")
                }
            }
            Type::ExtendRow { .. } | Type::ExtendTypeRow { .. } => {
                self.pretty_row("{", printer, &mut |field| {
                    chain![
                        arena,
                        pretty_print::doc_comment(arena, field.typ.comment()),
                        pretty_print::ident(arena, field.name.as_ref() as &str),
                        " : "
                    ]
                })
            }
            // This should not be displayed normally as it should only exist in `ExtendRow`
            // which handles `EmptyRow` explicitly
            Type::EmptyRow => arena.text("EmptyRow"),
            Type::Ident(ref id) => {
                printer.symbol_with(&id.name, Name::new(id.as_ref()).name().as_str())
            }
            Type::Projection(ref ids) => arena.concat(
                ids.iter()
                    .map(|id| printer.symbol(id))
                    .intersperse(arena.text(".")),
            ),
            Type::Alias(ref alias) => printer.symbol(&alias.name),
        }
    }

    fn pretty_record_like<A>(
        row: &'a T,
        printer: &Printer<'a, I, A>,
        open: &'static str,
        pretty_field: &mut dyn FnMut(&'a Field<T::SpannedId, T>) -> DocBuilder<'a, Arena<'a, A>, A>,
        close: &'static str,
    ) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        A: Clone,
    {
        let arena = printer.arena;

        let forced_hardline = row_iter(row).any(|field| field.typ.comment().is_some());

        let hardline = if forced_hardline {
            arena.hardline()
        } else {
            arena.line()
        };

        let mut doc = arena.text(open);
        doc = match **row {
            Type::EmptyRow => doc,
            Type::ExtendRow { .. } | Type::ExtendTypeRow { .. } => doc
                .append(top(row).pretty_row(open, printer, pretty_field))
                .nest(INDENT),
            _ => doc
                .append(arena.line())
                .append("| ")
                .append(top(row).pretty(printer))
                .nest(INDENT),
        };
        if open != "(" {
            doc = doc.append(hardline);
        }

        doc.append(close).group()
    }

    fn pretty_row<A>(
        &self,
        open: &str,
        printer: &Printer<'a, I, A>,
        pretty_field: &mut dyn FnMut(&'a Field<T::SpannedId, T>) -> DocBuilder<'a, Arena<'a, A>, A>,
    ) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        A: Clone,
    {
        let arena = printer.arena;

        let mut doc = arena.nil();
        let mut typ = self.typ;

        let fields = {
            let mut typ = typ;
            loop {
                match **typ {
                    Type::ExtendRow { ref fields, .. } => break &fields[..],
                    Type::ExtendTypeRow { ref rest, .. } => typ = rest,
                    _ => break &[][..],
                }
            }
        };
        let forced_hardline = fields.iter().any(|field| field.typ.comment().is_some());

        let hardline = if forced_hardline {
            arena.hardline()
        } else {
            arena.line()
        };

        let print_any_field = fields
            .iter()
            .any(|field| printer.filter(field.name.as_id()) != Filter::Drop);

        let mut filtered = false;

        let types_len = type_field_iter(typ).count();
        for (i, field) in type_field_iter(typ).enumerate() {
            let filter = printer.filter(field.name.as_id());
            if filter == Filter::Drop {
                filtered = true;
                continue;
            }

            let f =
                chain![
                    arena,
                    chain![
                        arena,
                        field.name.as_ref() as &str,
                        arena.line(),
                        arena.concat(
                            field.typ.params().iter().map(|param| {
                                arena.text(param.id.as_ref()).append(arena.line())
                            })
                        )
                    ]
                    .group(),
                    arena.text("= "),
                    if filter == Filter::RetainKey {
                        arena.text("...")
                    } else {
                        top(&field.typ.typ).pretty(printer)
                    },
                    if i + 1 != types_len || print_any_field {
                        arena.text(",")
                    } else {
                        arena.nil()
                    }
                ]
                .group();
            doc = doc.append(hardline.clone()).append(f);
        }

        let mut row_iter = row_iter(typ);
        for (i, field) in row_iter.by_ref().enumerate() {
            let filter = printer.filter(field.name.as_id());
            if filter == Filter::Drop {
                filtered = true;
                continue;
            }

            let mut rhs = if filter == Filter::RetainKey {
                arena.text("...")
            } else {
                top(&field.typ).pretty(printer)
            };
            match *field.typ {
                // Records handle nesting on their own
                Type::Record(_) => (),
                _ => rhs = rhs.nest(INDENT),
            }
            let f = chain![
                arena,
                pretty_field(field),
                rhs.group(),
                if i + 1 != fields.len() {
                    arena.text(",")
                } else {
                    arena.nil()
                }
            ]
            .group();
            let space_before = if i == 0 && open == "(" {
                arena.nil()
            } else {
                hardline.clone()
            };
            doc = doc.append(space_before).append(f);
        }
        typ = row_iter.typ;

        let doc = if filtered {
            if let Doc::Nil = *doc.1 {
                chain![arena, hardline.clone(), "..."]
            } else {
                chain![
                    arena,
                    hardline.clone(),
                    "...,",
                    doc,
                    if forced_hardline {
                        arena.nil()
                    } else {
                        arena.text(",")
                    },
                    hardline.clone(),
                    "..."
                ]
            }
        } else {
            doc
        };
        match **typ {
            Type::EmptyRow => doc,
            _ => doc
                .append(arena.line())
                .append("| ")
                .append(top(typ).pretty(printer)),
        }
    }

    fn pretty_function<A>(&self, printer: &Printer<'a, I, A>) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        I: AsRef<str>,
        A: Clone,
    {
        let arena = printer.arena;
        let doc = self.pretty_function_(printer);
        self.prec.enclose(Prec::Function, arena, doc).group()
    }

    fn pretty_function_<A>(&self, printer: &Printer<'a, I, A>) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        I: AsRef<str>,
        A: Clone,
    {
        let arena = printer.arena;
        match self.typ.as_function_with_type() {
            Some((arg_type, arg, ret)) => chain![
                arena,
                chain![
                    arena,
                    if arg_type == ArgType::Implicit {
                        arena.text("[")
                    } else {
                        arena.nil()
                    },
                    dt(Prec::Function, arg).pretty_(printer),
                    if arg_type == ArgType::Implicit {
                        arena.text("]")
                    } else {
                        arena.nil()
                    },
                ]
                .group(),
                printer.space_after(arg.span().end()),
                "-> ",
                top(ret).pretty_function_(printer)
            ],
            None => self.pretty(printer),
        }
    }
}

pub fn pretty_print<'a, I, T, A>(
    printer: &Printer<'a, I, A>,
    typ: &'a T,
) -> DocBuilder<'a, Arena<'a, A>, A>
where
    I: AsRef<str> + 'a,
    T: TypePtr<Id = I> + HasSpan + HasMetadata,
    T::SpannedId: AsRef<str> + AsId<I> + 'a,
    A: Clone,
{
    dt(Prec::Top, typ).pretty(printer)
}

pub fn walk_type<'a, I, T, F>(typ: &'a T, mut f: F)
where
    F: Walker<'a, T>,
    T: TypePtr<Id = I> + 'a,
    I: 'a,
{
    f.walk(typ)
}

pub fn walk_type_<'a, I, T, F: ?Sized>(typ: &'a T, f: &mut F)
where
    F: Walker<'a, T>,
    T: TypePtr<Id = I> + 'a,
    I: 'a,
{
    match **typ {
        Type::Function(_, ref arg, ref ret) => {
            f.walk(arg);
            f.walk(ret);
        }
        Type::App(ref t, ref args) => {
            f.walk(t);
            for a in &**args {
                f.walk(a);
            }
        }
        Type::Forall(_, ref typ)
        | Type::Record(ref typ)
        | Type::Variant(ref typ)
        | Type::Effect(ref typ) => f.walk(typ),
        Type::ExtendRow {
            ref fields,
            ref rest,
        } => {
            for field in fields.iter() {
                f.walk(&field.typ);
            }
            f.walk(rest);
        }
        Type::ExtendTypeRow {
            ref types,
            ref rest,
        } => {
            for field in &**types {
                f.walk(&field.typ.typ);
            }
            f.walk(rest);
        }
        Type::Hole
        | Type::Opaque
        | Type::Error
        | Type::Builtin(_)
        | Type::Variable(_)
        | Type::Generic(_)
        | Type::Skolem(_)
        | Type::Ident(_)
        | Type::Projection(_)
        | Type::Alias(_)
        | Type::EmptyRow => (),
    }
}

pub fn walk_type_mut<Id, T, F: ?Sized>(typ: &mut T, f: &mut F)
where
    F: WalkerMut<T>,
    T: TypePtr<Id = Id> + DerefMut<Target = Type<Id, T>>,
    T::Types: DerefMut<Target = [T]>,
    T::Fields: DerefMut<Target = [Field<T::SpannedId, T>]>,
    T::TypeFields: DerefMut<Target = [Field<T::SpannedId, Alias<Id, T>>]>,
{
    match **typ {
        Type::Forall(_, ref mut typ) => f.walk_mut(typ),
        Type::Function(_, ref mut arg, ref mut ret) => {
            f.walk_mut(arg);
            f.walk_mut(ret);
        }
        Type::App(ref mut t, ref mut args) => {
            f.walk_mut(t);
            for a in args.iter_mut() {
                f.walk_mut(a);
            }
        }
        Type::Record(ref mut row) | Type::Variant(ref mut row) | Type::Effect(ref mut row) => {
            f.walk_mut(row)
        }
        Type::ExtendRow {
            ref mut fields,
            ref mut rest,
        } => {
            for field in &mut **fields {
                f.walk_mut(&mut field.typ);
            }
            f.walk_mut(rest);
        }
        Type::ExtendTypeRow {
            ref mut types,
            ref mut rest,
        } => {
            for field in &mut **types {
                if let Some(alias) = field.typ.try_get_alias_mut() {
                    let field_type = alias.unresolved_type_mut();
                    f.walk_mut(field_type);
                }
            }
            f.walk_mut(rest);
        }
        Type::Hole
        | Type::Opaque
        | Type::Error
        | Type::Builtin(_)
        | Type::Variable(_)
        | Type::Generic(_)
        | Type::Skolem(_)
        | Type::Ident(_)
        | Type::Projection(_)
        | Type::Alias(_)
        | Type::EmptyRow => (),
    }
}

pub fn fold_type<Id, T, F, A>(typ: &T, mut f: F, a: A) -> A
where
    F: FnMut(&T, A) -> A,
    T: TypePtr<Id = Id>,
{
    let mut a = Some(a);
    walk_type(typ, |t| {
        a = Some(f(t, a.take().expect("None in fold_type")));
    });
    a.expect("fold_type")
}

pub trait TypeVisitor<Id, T>
where
    T: TypePtr<Id = Id>,
    T::Types: Clone,
    T::Generics: Clone,
    T::Fields: Clone,
    T::TypeFields: Clone,
{
    type Context: TypeContext<Id, T>;

    fn context(&mut self) -> &mut Self::Context;

    fn make(&mut self, typ: Type<Id, T>) -> T {
        self.context().intern(typ)
    }

    fn make_types(&mut self, typ: impl IntoIterator<Item = T>) -> T::Types {
        self.context().intern_types(typ)
    }

    fn visit(&mut self, typ: &T) -> Option<T>
    where
        T: TypePtr<Id = Id> + Clone,
        Id: Clone,
        T::SpannedId: Clone,
    {
        walk_move_type_opt(typ, self)
    }

    fn forall(&mut self, params: T::Generics, typ: T) -> T {
        if params.is_empty() {
            typ
        } else {
            self.make(Type::Forall(params, typ))
        }
    }

    fn app(&mut self, id: T, args: T::Types) -> T {
        if args.is_empty() {
            id
        } else {
            self.make(Type::App(id, args))
        }
    }
}

pub trait Walker<'a, T> {
    fn walk(&mut self, typ: &'a T);
}

impl<Id, T, F> TypeVisitor<Id, T> for F
where
    F: ?Sized + FnMut(&T) -> Option<T>,
    Id: Clone,
    T::SpannedId: Clone,
    T: TypeExt<Id = Id> + From<(Type<Id, T>, Flags)> + From<Type<Id, T>>,
    T::Types: FromIterator<T> + Clone,
    T::Generics: FromIterator<Generic<Id>> + Clone,
    T::Fields: FromIterator<Field<T::SpannedId, T>> + Clone,
{
    type Context = NullInterner;

    fn context(&mut self) -> &mut Self::Context {
        NullInterner::new()
    }

    fn visit(&mut self, typ: &T) -> Option<T>
    where
        T: TypePtr<Id = Id> + From<Type<Id, T>> + Clone,
        Id: Clone,
    {
        let new_type = walk_move_type_opt(typ, self);
        let new_type2 = self(new_type.as_ref().map_or(typ, |t| t));
        new_type2.or(new_type)
    }
}

#[macro_export(local_inner_macros)]
macro_rules! expr {
    ($self: ident, $id: ident, $expr: expr) => {{
        let $id = $self;
        $expr
    }};
}

#[macro_export(local_inner_macros)]
macro_rules! forward_type_interner_methods_no_arg {
    ($typ: ty, [$($tokens: tt)+] $id: ident $($rest : ident)* ) => {
        fn $id(&mut self) -> $typ {
            $crate::expr!(self, $($tokens)+).$id()
        }
        $crate::forward_type_interner_methods_no_arg!($typ, [$($tokens)+] $($rest)*);
    };

    ($typ: ty, [$($tokens: tt)+]) => {
    }
}

#[macro_export]
macro_rules! forward_type_interner_methods {
    ($id: ty, $typ: ty, $($tokens: tt)+ ) => {
        fn intern(&mut self, typ: $crate::types::Type<$id, $typ>) -> $typ {
            $crate::expr!(self, $($tokens)+).intern(typ)
        }

        fn intern_types(&mut self, types: impl IntoIterator<Item = $typ>) -> <$typ as $crate::types::TypePtr>::Types {
            $crate::expr!(self, $($tokens)+).intern_types(types)
        }

        fn intern_generics(&mut self, types: impl IntoIterator<Item = $crate::types::Generic<$id>>) -> <$typ as $crate::types::TypePtr>::Generics {
            $crate::expr!(self, $($tokens)+).intern_generics(types)
        }

        fn intern_fields(&mut self, types: impl IntoIterator<Item = $crate::types::Field<<$typ as $crate::types::TypePtr>::SpannedId, $typ>>) -> <$typ as $crate::types::TypePtr>::Fields {
            $crate::expr!(self, $($tokens)+).intern_fields(types)
        }

        fn intern_type_fields(&mut self, types: impl IntoIterator<Item = $crate::types::Field<<$typ as $crate::types::TypePtr>::SpannedId, $crate::types::Alias<$id, $typ>>>) -> <$typ as $crate::types::TypePtr>::TypeFields {
            $crate::expr!(self, $($tokens)+).intern_type_fields(types)
        }

        fn intern_flags(&mut self, typ: $crate::types::Type<$id, $typ>, flags: $crate::types::Flags) -> $typ {
            $crate::expr!(self, $($tokens)+).intern_flags(typ, flags)
        }

        fn builtin(&mut self, typ: $crate::types::BuiltinType) -> $typ {
            $crate::expr!(self, $($tokens)+).builtin(typ)
        }

        fn forall(&mut self, params: <$typ as $crate::types::TypePtr>::Generics, typ: $typ) -> $typ {
            $crate::expr!(self, $($tokens)+).forall(params, typ)
        }

        fn with_forall(&mut self, typ: $typ, from: &$typ) -> $typ
        where
            $id: Clone + Eq + std::hash::Hash,
            $typ: $crate::types::TypeExt<Id = $id> + Clone,
            <$typ as $crate::types::TypePtr>::Generics: std::iter::FromIterator<$crate::types::Generic<$id>> + Clone,
        {
            $crate::expr!(self, $($tokens)+).with_forall(typ, from)
        }

        fn array(&mut self, typ: $typ) -> $typ {
            $crate::expr!(self, $($tokens)+).array(typ)
        }

        fn app(&mut self, id: $typ, args: <$typ as $crate::types::TypePtr>::Types) -> $typ {
            $crate::expr!(self, $($tokens)+).app(id, args)
        }

        fn variant(&mut self, fields: <$typ as $crate::types::TypePtr>::Fields) -> $typ {
            $crate::expr!(self, $($tokens)+).variant(fields)
        }

        fn poly_variant(&mut self, fields: <$typ as $crate::types::TypePtr>::Fields, rest: $typ) -> $typ {
            $crate::expr!(self, $($tokens)+).poly_variant(fields, rest)
        }

        fn effect(&mut self, fields: <$typ as $crate::types::TypePtr>::Fields) -> $typ {
            $crate::expr!(self, $($tokens)+).effect(fields)
        }

        fn poly_effect(&mut self, fields: <$typ as $crate::types::TypePtr>::Fields, rest: $typ) -> $typ {
            $crate::expr!(self, $($tokens)+).poly_effect(fields, rest)
        }

        fn record(
            &mut self,
            types: <$typ as $crate::types::TypePtr>::TypeFields,
            fields: <$typ as $crate::types::TypePtr>::Fields,
        ) -> $typ {
            $crate::expr!(self, $($tokens)+).record(types, fields)
        }

        fn poly_record(
            &mut self,
            types: <$typ as $crate::types::TypePtr>::TypeFields,
            fields: <$typ as $crate::types::TypePtr>::Fields,
            rest: $typ,
        ) -> $typ {
            $crate::expr!(self, $($tokens)+).poly_record(types, fields, rest)
        }

        fn extend_full_row(
            &mut self,
            types: <$typ as $crate::types::TypePtr>::TypeFields,
            fields: <$typ as $crate::types::TypePtr>::Fields,
            rest: $typ,
        ) -> $typ {
            $crate::expr!(self, $($tokens)+).extend_full_row(types, fields, rest)
        }

        fn extend_row(
            &mut self,
            fields: <$typ as $crate::types::TypePtr>::Fields,
            rest: $typ,
        ) -> $typ {
            $crate::expr!(self, $($tokens)+).extend_row(fields, rest)
        }

        fn extend_type_row(
            &mut self,
            types: <$typ as $crate::types::TypePtr>::TypeFields,
            rest: $typ,
        ) -> $typ {
            $crate::expr!(self, $($tokens)+).extend_type_row(types, rest)
        }

        fn generic(&mut self, typ: $crate::types::Generic<$id>) -> $typ {
            $crate::expr!(self, $($tokens)+).generic(typ)
        }

        fn skolem(&mut self, typ: $crate::types::Skolem<$id>) -> $typ {
            $crate::expr!(self, $($tokens)+).skolem(typ)
        }

        fn variable(&mut self, typ: $crate::types::TypeVariable) -> $typ {
            $crate::expr!(self, $($tokens)+).variable(typ)
        }

        fn alias(
            &mut self,
            name: $id,
            args: <$typ as $crate::types::TypePtr>::Generics,
            typ: $typ,
        ) -> $typ
        {
            $crate::expr!(self, $($tokens)+).alias(name, args, typ)
        }

        fn ident(&mut self, id: $crate::ast::KindedIdent<$id>) -> $typ {
            $crate::expr!(self, $($tokens)+).ident(id)
        }

        fn projection(&mut self, id: $crate::types::AppVec<$id>) -> $typ {
            $crate::expr!(self, $($tokens)+).projection(id)
        }

        fn builtin_type(&mut self, typ: $crate::types::BuiltinType) -> $typ {
            $crate::expr!(self, $($tokens)+).builtin_type(typ)
        }

        fn new_alias(&mut self, name: $id, args: <$typ as $crate::types::TypePtr>::Generics, typ: $typ) -> $crate::types::Alias<$id, $typ> {
            $crate::expr!(self, $($tokens)+).new_alias(name, args, typ)
        }

        fn new_data_alias(&mut self, data: $crate::types::AliasData<$id, $typ>) -> $crate::types::Alias<$id, $typ> {
            $crate::expr!(self, $($tokens)+).new_data_alias(data)
        }

        fn alias_group(
            &mut self,
            group: Vec<$crate::types::AliasData<$id, $typ>>,
            ) -> Vec<$crate::types::Alias<$id, $typ>>
        where
            $typ: $crate::types::TypeExt<Id = $id>,
            $id: PartialEq,
        {
            $crate::expr!(self, $($tokens)+).alias_group(group)
        }

        /*
           Avoid forwarding methods that take an iterator as they can cause panics when using `RefCell`

        fn tuple<S, I>(&mut self, symbols: &mut S, elems: I) -> $typ
        where
            S: ?Sized + $crate::ast::IdentEnv<Ident = $id>,
            I: IntoIterator<Item = $typ>,
        {
            $crate::expr!(self, $($tokens)+).tuple(symbols, elems)
        }

        fn tuple_<S, I>(&mut self, symbols: &mut S, elems: I) -> $crate::types::Type<$id, $typ>
        where
            S: ?Sized + $crate::ast::IdentEnv<Ident = $id>,
            I: IntoIterator<Item = $typ>,
        {
            $crate::expr!(self, $($tokens)+).tuple_(symbols, elems)
        }

        fn function<I>(&mut self, args: I, ret: $typ) -> $typ
        where
            $typ: Clone,
            I: IntoIterator<Item = $typ>,
            I::IntoIter: DoubleEndedIterator<Item = $typ>,
        {
            $crate::expr!(self, $($tokens)+).function( args, ret)
        }

        fn function_implicit<I>(&mut self, args: I, ret: $typ) -> $typ
        where
            I: IntoIterator<Item = $typ>,
            I::IntoIter: DoubleEndedIterator<Item = $typ>,
        {
            $crate::expr!(self, $($tokens)+).function_implicit(args, ret)
        }

        fn function_type<I>(&mut self, arg_type: $crate::types::ArgType, args: I, ret: $typ) -> $typ
        where
            I: IntoIterator<Item = $typ>,
            I::IntoIter: DoubleEndedIterator<Item = $typ>,
        {
            $crate::expr!(self, $($tokens)+).function_type(arg_type, args, ret)
        }
        */

        $crate::forward_type_interner_methods_no_arg!(
            $typ,
            [$($tokens)+]
            hole opaque error array_builtin empty_row function_builtin string char byte int float unit
        );
    }
}

pub struct InternerVisitor<'i, F, T> {
    interner: &'i mut T,
    visitor: F,
}

pub trait TypeContext<Id, T>
where
    T: TypePtr<Id = Id>,
{
    fn intern_flags(&mut self, typ: Type<Id, T>, flags: Flags) -> T;

    fn intern(&mut self, typ: Type<Id, T>) -> T;

    fn intern_types(&mut self, types: impl IntoIterator<Item = T>) -> T::Types;

    fn intern_generics(&mut self, types: impl IntoIterator<Item = Generic<Id>>) -> T::Generics;

    fn intern_fields(
        &mut self,
        types: impl IntoIterator<Item = Field<T::SpannedId, T>>,
    ) -> T::Fields;

    fn intern_type_fields(
        &mut self,
        types: impl IntoIterator<Item = Field<T::SpannedId, Alias<Id, T>>>,
    ) -> T::TypeFields;

    fn hole(&mut self) -> T {
        self.intern(Type::Hole)
    }

    fn opaque(&mut self) -> T {
        self.intern(Type::Opaque)
    }

    fn error(&mut self) -> T {
        self.intern(Type::Error)
    }

    fn builtin(&mut self, typ: BuiltinType) -> T {
        self.intern(Type::Builtin(typ))
    }

    fn forall(&mut self, params: T::Generics, typ: T) -> T {
        if params.is_empty() {
            typ
        } else {
            self.intern(Type::Forall(params, typ))
        }
    }

    fn with_forall(&mut self, typ: T, from: &T) -> T
    where
        Id: Clone + Eq + Hash,
        T: TypeExt<Id = Id> + Clone,
        T::Generics: FromIterator<Generic<Id>> + Clone,
    {
        let params = forall_params(from).cloned().collect();
        self.forall(params, typ)
    }

    fn array(&mut self, typ: T) -> T {
        let a = self.array_builtin();
        let typ = self.intern_types(Some(typ));
        self.app(a, typ)
    }

    fn array_builtin(&mut self) -> T {
        self.builtin(BuiltinType::Array)
    }

    fn app(&mut self, id: T, args: T::Types) -> T {
        if args.is_empty() {
            id
        } else {
            self.intern(Type::App(id, args))
        }
    }

    fn variant(&mut self, fields: T::Fields) -> T {
        let empty_row = self.empty_row();
        self.poly_variant(fields, empty_row)
    }

    fn poly_variant(&mut self, fields: T::Fields, rest: T) -> T {
        let row = self.extend_row(fields, rest);
        self.intern(Type::Variant(row))
    }

    fn effect(&mut self, fields: T::Fields) -> T {
        let empty_row = self.empty_row();
        self.poly_effect(fields, empty_row)
    }

    fn poly_effect(&mut self, fields: T::Fields, rest: T) -> T {
        let extend_row = self.extend_row(fields, rest);
        self.intern(Type::Effect(extend_row))
    }

    fn tuple<S, I>(&mut self, symbols: &mut S, elems: I) -> T
    where
        S: ?Sized + IdentEnv<Ident = Id>,
        T::SpannedId: From<(Id, Span<BytePos>)>,
        I: IntoIterator<Item = T>,
        T: HasSpan,
    {
        let t = self.tuple_(symbols, elems);
        self.intern(t)
    }

    fn tuple_<S, I>(&mut self, symbols: &mut S, elems: I) -> Type<Id, T>
    where
        S: ?Sized + IdentEnv<Ident = Id>,
        T::SpannedId: From<(Id, Span<BytePos>)>,
        T: HasSpan,
        I: IntoIterator<Item = T>,
    {
        let empty_row = self.empty_row();
        let elems = self.intern_fields(elems.into_iter().enumerate().map(|(i, typ)| Field {
            name: (symbols.from_str(&format!("_{}", i)), typ.span()).into(),
            typ,
        }));
        Type::Record(self.extend_row(elems, empty_row))
    }

    fn record(&mut self, types: T::TypeFields, fields: T::Fields) -> T {
        let empty_row = self.empty_row();
        self.poly_record(types, fields, empty_row)
    }

    fn poly_record(&mut self, types: T::TypeFields, fields: T::Fields, rest: T) -> T {
        let row = self.extend_full_row(types, fields, rest);
        self.intern(Type::Record(row))
    }

    fn extend_full_row(&mut self, types: T::TypeFields, fields: T::Fields, rest: T) -> T {
        let rest = self.extend_row(fields, rest);
        self.extend_type_row(types, rest)
    }

    fn extend_row(&mut self, fields: T::Fields, rest: T) -> T {
        if fields.is_empty() {
            rest
        } else {
            self.intern(Type::ExtendRow { fields, rest })
        }
    }

    fn extend_type_row(&mut self, types: T::TypeFields, rest: T) -> T {
        if types.is_empty() {
            rest
        } else {
            self.intern(Type::ExtendTypeRow { types, rest })
        }
    }

    fn empty_row(&mut self) -> T {
        self.intern(Type::EmptyRow)
    }

    fn function<I>(&mut self, args: I, ret: T) -> T
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: DoubleEndedIterator<Item = T>,
    {
        self.function_type(ArgType::Explicit, args, ret)
    }

    fn function_implicit<I>(&mut self, args: I, ret: T) -> T
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: DoubleEndedIterator<Item = T>,
    {
        self.function_type(ArgType::Implicit, args, ret)
    }

    fn function_type<I>(&mut self, arg_type: ArgType, args: I, ret: T) -> T
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: DoubleEndedIterator<Item = T>,
    {
        args.into_iter().rev().fold(ret, |body, arg| {
            self.intern(Type::Function(arg_type, arg, body))
        })
    }

    fn generic(&mut self, typ: Generic<Id>) -> T {
        self.intern(Type::Generic(typ))
    }

    fn skolem(&mut self, typ: Skolem<Id>) -> T {
        self.intern(Type::Skolem(typ))
    }

    fn variable(&mut self, typ: TypeVariable) -> T {
        self.intern(Type::Variable(typ))
    }

    fn alias(&mut self, name: Id, args: T::Generics, typ: T) -> T {
        self.intern(Type::Alias(AliasRef {
            index: 0,
            group: Arc::from(vec![AliasData {
                name,
                args,
                typ,
                is_implicit: false,
            }]),
        }))
    }

    fn ident(&mut self, id: KindedIdent<Id>) -> T {
        self.intern(Type::Ident(id))
    }

    fn projection(&mut self, id: AppVec<Id>) -> T {
        self.intern(Type::Projection(id))
    }

    fn function_builtin(&mut self) -> T {
        self.builtin(BuiltinType::Function)
    }

    fn string(&mut self) -> T {
        self.builtin(BuiltinType::String)
    }

    fn char(&mut self) -> T {
        self.builtin(BuiltinType::Char)
    }

    fn byte(&mut self) -> T {
        self.builtin(BuiltinType::Byte)
    }

    fn int(&mut self) -> T {
        self.builtin(BuiltinType::Int)
    }

    fn float(&mut self) -> T {
        self.builtin(BuiltinType::Float)
    }

    fn unit(&mut self) -> T {
        self.record(Default::default(), Default::default())
    }

    fn builtin_type(&mut self, typ: BuiltinType) -> T {
        match typ {
            BuiltinType::String => self.string(),
            BuiltinType::Byte => self.byte(),
            BuiltinType::Char => self.char(),
            BuiltinType::Int => self.int(),
            BuiltinType::Float => self.float(),
            BuiltinType::Array => self.array_builtin(),
            BuiltinType::Function => self.function_builtin(),
        }
    }

    fn new_alias(&mut self, name: Id, args: T::Generics, typ: T) -> Alias<Id, T> {
        Alias {
            _typ: self.alias(name, args, typ),
            _marker: PhantomData,
        }
    }

    fn new_data_alias(&mut self, data: AliasData<Id, T>) -> Alias<Id, T> {
        Alias {
            _typ: self.intern(Type::Alias(AliasRef {
                index: 0,
                group: Arc::from(vec![data]),
            })),
            _marker: PhantomData,
        }
    }

    fn alias_group(&mut self, group: Vec<AliasData<Id, T>>) -> Vec<Alias<Id, T>>
    where
        T: TypeExt<Id = Id>,
        Id: PartialEq,
    {
        let group = Arc::<[_]>::from(group);
        (0..group.len())
            .map(|index| {
                let typ = Type::Alias(AliasRef {
                    index,
                    group: group.clone(),
                });
                let flags = Flags::from_type(&typ)
                    | (if group[index].is_implicit {
                        Flags::HAS_IMPLICIT
                    } else {
                        Flags::empty()
                    });

                Alias {
                    _typ: self.intern_flags(typ, flags),
                    _marker: PhantomData,
                }
            })
            .collect()
    }
}

pub trait Substitution<Id, T>: TypeContext<Id, T>
where
    T: TypePtr<Id = Id>,
{
    fn new_var(&mut self) -> T;
    fn new_skolem(&mut self, name: Id, kind: ArcKind) -> T;
}

impl<'b, Id, T, V> TypeContext<Id, T> for &'b Rc<V>
where
    for<'a> &'a V: TypeContext<Id, T>,
    T: TypePtr<Id = Id>,
{
    forward_type_interner_methods!(Id, T, self_, &***self_);
}

impl<Id, T, V> TypeContext<Id, T> for Rc<V>
where
    for<'a> &'a V: TypeContext<Id, T>,
    T: TypePtr<Id = Id>,
{
    forward_type_interner_methods!(Id, T, self_, &**self_);
}

impl<'a, Id, T, V> TypeContext<Id, T> for &'a RefCell<V>
where
    V: TypeContext<Id, T>,
    T: TypePtr<Id = Id>,
{
    forward_type_interner_methods!(Id, T, self_, self_.borrow_mut());
}

pub type SharedInterner<Id, T> = TypeCache<Id, T>;

#[derive(Default)]
pub struct NullInterner;

impl NullInterner {
    pub fn new() -> &'static mut NullInterner {
        // SAFETY NullInterner is zero-sized
        unsafe { &mut *(&mut NullInterner as *mut _) }
    }
}

impl<Id, T> TypeContext<Id, T> for NullInterner
where
    T: TypePtr<Id = Id> + From<(Type<Id, T>, Flags)> + From<Type<Id, T>>,
    T::Types: FromIterator<T>,
    T::Generics: FromIterator<Generic<Id>>,
    T::Fields: FromIterator<Field<T::SpannedId, T>>,
    T::TypeFields: FromIterator<Field<T::SpannedId, Alias<Id, T>>>,
{
    fn intern(&mut self, typ: Type<Id, T>) -> T {
        T::from(typ)
    }

    fn intern_types(&mut self, types: impl IntoIterator<Item = T>) -> T::Types {
        types.into_iter().collect()
    }

    fn intern_generics(&mut self, types: impl IntoIterator<Item = Generic<Id>>) -> T::Generics {
        types.into_iter().collect()
    }

    fn intern_fields(
        &mut self,
        types: impl IntoIterator<Item = Field<T::SpannedId, T>>,
    ) -> T::Fields {
        types.into_iter().collect()
    }

    fn intern_type_fields(
        &mut self,
        types: impl IntoIterator<Item = Field<T::SpannedId, Alias<Id, T>>>,
    ) -> T::TypeFields {
        types.into_iter().collect()
    }

    fn intern_flags(&mut self, typ: Type<Id, T>, flags: Flags) -> T {
        T::from((typ, flags))
    }
}

macro_rules! forward_to_cache {
    ($($id: ident)*) => {
        $(
            fn $id(&mut self) -> T {
                TypeCache::$id(self)
            }
        )*
    }
}

impl<Id, T> TypeContext<Id, T> for TypeCache<Id, T>
where
    T: TypeExt<Id = Id> + From<(Type<Id, T>, Flags)> + From<Type<Id, T>> + Clone,
    T::Types: Default + Extend<T> + FromIterator<T>,
    T::Generics: FromIterator<Generic<Id>>,
    T::Fields: FromIterator<Field<T::SpannedId, T>>,
    T::TypeFields: FromIterator<Field<T::SpannedId, Alias<Id, T>>>,
{
    fn intern(&mut self, typ: Type<Id, T>) -> T {
        T::from(typ)
    }

    fn intern_types(&mut self, types: impl IntoIterator<Item = T>) -> T::Types {
        types.into_iter().collect()
    }

    fn intern_generics(&mut self, types: impl IntoIterator<Item = Generic<Id>>) -> T::Generics {
        types.into_iter().collect()
    }

    fn intern_fields(
        &mut self,
        types: impl IntoIterator<Item = Field<T::SpannedId, T>>,
    ) -> T::Fields {
        types.into_iter().collect()
    }

    fn intern_type_fields(
        &mut self,
        types: impl IntoIterator<Item = Field<T::SpannedId, Alias<Id, T>>>,
    ) -> T::TypeFields {
        types.into_iter().collect()
    }

    fn intern_flags(&mut self, typ: Type<Id, T>, flags: Flags) -> T {
        T::from((typ, flags))
    }

    forward_to_cache! {
        hole opaque error int byte float string char
        function_builtin array_builtin unit empty_row
    }
}

impl<'a, Id, T> TypeContext<Id, T> for &'a TypeCache<Id, T>
where
    T: TypeExt<Id = Id> + From<(Type<Id, T>, Flags)> + From<Type<Id, T>> + Clone,
    T::Types: Default + Extend<T> + FromIterator<T>,
    T::Generics: FromIterator<Generic<Id>>,
    T::Fields: FromIterator<Field<T::SpannedId, T>>,
    T::TypeFields: FromIterator<Field<T::SpannedId, Alias<Id, T>>>,
{
    fn intern(&mut self, typ: Type<Id, T>) -> T {
        T::from(typ)
    }

    fn intern_types(&mut self, types: impl IntoIterator<Item = T>) -> T::Types {
        types.into_iter().collect()
    }

    fn intern_generics(&mut self, types: impl IntoIterator<Item = Generic<Id>>) -> T::Generics {
        types.into_iter().collect()
    }

    fn intern_fields(
        &mut self,
        types: impl IntoIterator<Item = Field<T::SpannedId, T>>,
    ) -> T::Fields {
        types.into_iter().collect()
    }

    fn intern_type_fields(
        &mut self,
        types: impl IntoIterator<Item = Field<T::SpannedId, Alias<Id, T>>>,
    ) -> T::TypeFields {
        types.into_iter().collect()
    }

    fn intern_flags(&mut self, typ: Type<Id, T>, flags: Flags) -> T {
        T::from((typ, flags))
    }

    forward_to_cache! {
        hole opaque error int byte float string char
        function_builtin array_builtin unit empty_row
    }
}

use crate::ast::{ArenaRef, AstType};
impl<'ast, Id> TypeContext<Id, AstType<'ast, Id>> for ArenaRef<'_, 'ast, Id> {
    fn intern(&mut self, typ: Type<Id, AstType<'ast, Id>>) -> AstType<'ast, Id> {
        AstType::new_no_loc(*self, typ)
    }

    fn intern_types(
        &mut self,
        types: impl IntoIterator<Item = AstType<'ast, Id>>,
    ) -> &'ast mut [AstType<'ast, Id>] {
        self.alloc_extend(types)
    }

    fn intern_generics(
        &mut self,
        types: impl IntoIterator<Item = Generic<Id>>,
    ) -> &'ast mut [Generic<Id>] {
        self.alloc_extend(types)
    }

    fn intern_fields(
        &mut self,
        types: impl IntoIterator<Item = Field<Spanned<Id, BytePos>, AstType<'ast, Id>>>,
    ) -> &'ast mut [Field<Spanned<Id, BytePos>, AstType<'ast, Id>>] {
        self.alloc_extend(types)
    }

    fn intern_type_fields(
        &mut self,
        types: impl IntoIterator<Item = Field<Spanned<Id, BytePos>, Alias<Id, AstType<'ast, Id>>>>,
    ) -> &'ast mut [Field<Spanned<Id, BytePos>, Alias<Id, AstType<'ast, Id>>>] {
        self.alloc_extend(types)
    }

    fn intern_flags(
        &mut self,
        typ: Type<Id, AstType<'ast, Id>>,
        _flags: Flags,
    ) -> AstType<'ast, Id> {
        self.intern(typ)
    }
}

#[derive(Clone, Default)]
struct Interned<T>(T);

impl<T> Eq for Interned<T>
where
    T: Deref,
    T::Target: Eq,
{
}

impl<T> PartialEq for Interned<T>
where
    T: Deref,
    T::Target: PartialEq,
{
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        *self.0 == *other.0
    }
}

impl<T> std::hash::Hash for Interned<T>
where
    T: Deref,
    T::Target: std::hash::Hash,
{
    #[inline(always)]
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        (*self.0).hash(state)
    }
}

impl<Id, T> Borrow<Type<Id, T>> for Interned<T>
where
    T: TypePtr<Id = Id>,
{
    fn borrow(&self) -> &Type<Id, T> {
        &self.0
    }
}

pub trait TypeContextAlloc: TypePtr + Sized {
    fn alloc(into: &mut Self, typ: Type<Self::Id, Self>, flags: Flags);
}

impl TypeContextAlloc for ArcType {
    fn alloc(into: &mut Self, typ: Type<Symbol, Self>, flags: Flags) {
        match Arc::get_mut(&mut into.typ) {
            Some(into) => {
                into.flags = flags;
                into.typ = typ;
            }
            None => {
                *into = Self::with_flags(typ, flags);
            }
        }
    }
}

pub struct Interner<Id, T>
where
    T: TypeExt<Id = Id>,
    T::Types: Default + Extend<T> + FromIterator<T>,
{
    set: FnvMap<Interned<T>, ()>,
    scratch: Interned<T>,
    type_cache: TypeCache<Id, T>,
}

impl<Id, T> Default for Interner<Id, T>
where
    T: Default + TypeExt<Id = Id> + From<Type<Id, T>> + Clone,
    T::Target: Eq + Hash,
    T::Types: Default + Extend<T> + FromIterator<T>,
{
    fn default() -> Self {
        let mut interner = Interner {
            set: Default::default(),
            scratch: Default::default(),
            type_cache: Default::default(),
        };

        macro_rules! populate_builtins {
            ($($id: ident)*) => {
                $(
                    let x = interner.type_cache.$id();
                    interner.set.insert(Interned(x), ());
                )*
            }
        }

        populate_builtins! {
            hole opaque error int byte float string char
            function_builtin array_builtin unit empty_row
        }

        interner
    }
}

macro_rules! forward_to_intern_cache {
    ($($id: ident)*) => {
        $(
            fn $id(&mut self) -> T {
                self.type_cache.$id()
            }
        )*
    }
}

impl<Id, T> TypeContext<Id, T> for Interner<Id, T>
where
    T: TypeContextAlloc<Id = Id> + TypeExt<Id = Id> + Eq + Hash + Clone,
    T::Types: FromIterator<T>,
    T::Generics: FromIterator<Generic<Id>>,
    T::TypeFields: FromIterator<Field<T::SpannedId, Alias<Id, T>>>,
    T::SpannedId: Eq + Hash,
    Id: Eq + Hash,
{
    fn intern(&mut self, typ: Type<Id, T>) -> T {
        let flags = Flags::from_type(&typ);
        self.intern_flags(typ, flags)
    }

    fn intern_types(&mut self, types: impl IntoIterator<Item = T>) -> T::Types {
        types.into_iter().collect()
    }

    fn intern_generics(&mut self, types: impl IntoIterator<Item = Generic<Id>>) -> T::Generics {
        types.into_iter().collect()
    }

    fn intern_fields(
        &mut self,
        types: impl IntoIterator<Item = Field<T::SpannedId, T>>,
    ) -> T::Fields {
        types.into_iter().collect()
    }

    fn intern_type_fields(
        &mut self,
        types: impl IntoIterator<Item = Field<T::SpannedId, Alias<Id, T>>>,
    ) -> T::TypeFields {
        types.into_iter().collect()
    }

    fn intern_flags(&mut self, typ: Type<Id, T>, flags: Flags) -> T {
        use std::collections::hash_map::Entry;

        T::alloc(&mut self.scratch.0, typ, flags);
        match self.set.entry(self.scratch.clone()) {
            Entry::Occupied(entry) => return entry.key().0.clone(),
            Entry::Vacant(entry) => {
                entry.insert(());
                self.scratch.0.clone()
            }
        }
    }

    forward_to_intern_cache! {
        hole opaque error int byte float string char
        function_builtin array_builtin unit empty_row
    }
}

impl<'i, F, V> InternerVisitor<'i, F, V> {
    pub fn new<Id, T>(interner: &'i mut V, visitor: F) -> Self
    where
        F: FnMut(&mut V, &T) -> Option<T>,
        T: TypeExt<Id = Id>,
        V: TypeContext<Id, T>,
    {
        InternerVisitor { interner, visitor }
    }

    pub fn control<Id, T>(
        interner: &'i mut V,
        visitor: F,
    ) -> InternerVisitor<'i, ControlVisitation<F>, V>
    where
        F: FnMut(&mut V, &T) -> Option<T>,
        T: TypeExt<Id = Id>,
        V: TypeContext<Id, T>,
    {
        InternerVisitor {
            interner,
            visitor: ControlVisitation(visitor),
        }
    }
}

impl<'i, F, V, Id, T> TypeVisitor<Id, T> for InternerVisitor<'i, F, V>
where
    F: FnMut(&mut V, &T) -> Option<T>,
    Id: Clone,
    T::SpannedId: Clone,
    T: TypeExt<Id = Id, Types = AppVec<T>>,
    V: TypeContext<Id, T>,
    T::Generics: FromIterator<Generic<Id>> + Clone,
    T::Fields: FromIterator<Field<T::SpannedId, T>> + Clone,
{
    type Context = V;

    fn context(&mut self) -> &mut Self::Context {
        &mut self.interner
    }

    fn visit(&mut self, typ: &T) -> Option<T>
    where
        T: TypePtr<Id = Id> + Clone,
        Id: Clone,
    {
        let new_type = walk_move_type_opt(typ, self);
        let new_type2 = (self.visitor)(self.interner, new_type.as_ref().map_or(typ, |t| t));
        new_type2.or(new_type)
    }
}

impl<'i, F, V, Id, T> TypeVisitor<Id, T> for InternerVisitor<'i, ControlVisitation<F>, V>
where
    F: FnMut(&mut V, &T) -> Option<T>,
    Id: Clone,
    T::SpannedId: Clone,
    T: TypeExt<Id = Id>,
    V: TypeContext<Id, T>,
    T::Types: Clone,
    T::Generics: Clone,
    T::Fields: Clone,
{
    type Context = V;

    fn context(&mut self) -> &mut Self::Context {
        &mut self.interner
    }

    fn visit(&mut self, typ: &T) -> Option<T>
    where
        T: TypePtr<Id = Id> + Clone,
        Id: Clone,
    {
        (self.visitor.0)(self.interner, typ)
    }
}

/// Wrapper type which allows functions to control how to traverse the members of the type
pub struct ControlVisitation<F: ?Sized>(pub F);

impl<F, Id, T> TypeVisitor<Id, T> for ControlVisitation<F>
where
    F: FnMut(&T) -> Option<T>,
    Id: Clone,
    T::SpannedId: Clone,
    T: TypeExt<Id = Id> + From<(Type<Id, T>, Flags)> + From<Type<Id, T>>,
    T::Types: FromIterator<T> + Clone,
    T::Generics: FromIterator<Generic<Id>> + Clone,
    T::Fields: FromIterator<Field<T::SpannedId, T>> + Clone,
{
    type Context = NullInterner;

    fn context(&mut self) -> &mut Self::Context {
        NullInterner::new()
    }

    fn visit(&mut self, typ: &T) -> Option<T>
    where
        T: TypePtr<Id = Id> + From<Type<Id, T>> + Clone,
        Id: Clone,
    {
        (self.0)(typ)
    }
}

impl<'a, F, T> Walker<'a, T> for ControlVisitation<F>
where
    F: ?Sized + FnMut(&'a T),
    T: 'a,
{
    fn walk(&mut self, typ: &'a T) {
        (self.0)(typ)
    }
}

pub struct FlagsVisitor<F: ?Sized>(pub Flags, pub F);

impl<F, Id, T> TypeVisitor<Id, T> for FlagsVisitor<F>
where
    F: FnMut(&T) -> Option<T>,
    Id: Clone,
    T::SpannedId: Clone,
    T: TypeExt<Id = Id> + From<(Type<Id, T>, Flags)> + From<Type<Id, T>>,
    T::Types: FromIterator<T> + Clone,
    T::Generics: FromIterator<Generic<Id>> + Clone,
    T::Fields: FromIterator<Field<T::SpannedId, T>> + Clone,
{
    type Context = NullInterner;

    fn context(&mut self) -> &mut Self::Context {
        NullInterner::new()
    }

    fn visit(&mut self, typ: &T) -> Option<T>
    where
        T: TypePtr<Id = Id> + From<Type<Id, T>> + Clone,
        Id: Clone,
    {
        if self.0.intersects(typ.flags()) {
            let new_type = walk_move_type_opt(typ, self);
            let new_type2 = (self.1)(new_type.as_ref().map_or(typ, |t| t));
            new_type2.or(new_type)
        } else {
            None
        }
    }
}

impl<'a, T, F> Walker<'a, T> for FlagsVisitor<F>
where
    F: ?Sized + FnMut(&'a T),
    T: TypeExt + 'a,
{
    fn walk(&mut self, typ: &'a T) {
        if self.0.intersects(typ.flags()) {
            (self.1)(typ);
            walk_type_(typ, self);
        }
    }
}

impl<'a, I, T, F> Walker<'a, T> for F
where
    F: ?Sized + FnMut(&'a T),
    T: TypePtr<Id = I> + 'a,
    I: 'a,
{
    fn walk(&mut self, typ: &'a T) {
        self(typ);
        walk_type_(typ, self)
    }
}

pub trait WalkerMut<T> {
    fn walk_mut(&mut self, typ: &mut T);
}

impl<Id, T, F: ?Sized> WalkerMut<T> for F
where
    F: FnMut(&mut T),
    T: TypePtr<Id = Id> + DerefMut<Target = Type<Id, T>>,
    T::Types: DerefMut<Target = [T]>,
    T::Fields: DerefMut<Target = [Field<T::SpannedId, T>]>,
    T::TypeFields: DerefMut<Target = [Field<T::SpannedId, Alias<Id, T>>]>,
{
    fn walk_mut(&mut self, typ: &mut T) {
        self(typ);
        walk_type_mut(typ, self)
    }
}

/// Walks through a type calling `f` on each inner type. If `f` return `Some` the type is replaced.
pub fn walk_move_type<F: ?Sized, I, T>(typ: T, f: &mut F) -> T
where
    F: TypeVisitor<I, T>,
    T: TypePtr<Id = I> + Clone,
    T::Types: Clone,
    T::Generics: Clone,
    T::Fields: Clone,
    T::TypeFields: Clone,
    T::SpannedId: Clone,
    I: Clone,
{
    f.visit(&typ).unwrap_or(typ)
}

pub fn visit_type_opt<F: ?Sized, I, T>(typ: &T, f: &mut F) -> Option<T>
where
    F: TypeVisitor<I, T>,
    T: TypePtr<Id = I> + Clone,
    T::Types: Clone,
    T::Generics: Clone,
    T::Fields: Clone,
    T::TypeFields: Clone,
    T::SpannedId: Clone,
    I: Clone,
{
    f.visit(typ)
}

pub fn walk_move_type_opt<F: ?Sized, I, T>(typ: &Type<I, T>, f: &mut F) -> Option<T>
where
    F: TypeVisitor<I, T>,
    T: TypePtr<Id = I> + Clone,
    T::Types: Clone,
    T::Generics: Clone,
    T::Fields: Clone,
    T::TypeFields: Clone,
    T::SpannedId: Clone,
    I: Clone,
{
    match *typ {
        Type::Forall(ref args, ref typ) => f.visit(typ).map(|typ| f.forall(args.clone(), typ)),

        Type::Function(arg_type, ref arg, ref ret) => {
            let new_arg = f.visit(arg);
            let new_ret = f.visit(ret);
            merge(arg, new_arg, ret, new_ret, |arg, ret| {
                f.make(Type::Function(arg_type, arg, ret))
            })
        }
        Type::App(ref id, ref args) => {
            // TODO Avoid Vec allocation
            let new_args = walk_move_types(f, args.iter(), |f, t| f.visit(t))
                .map(|args: Vec<_>| f.make_types(args));
            merge(id, f.visit(id), args, new_args, |x, y| f.app(x, y))
        }
        Type::Record(ref row) => f.visit(row).map(|row| f.make(Type::Record(row))),
        Type::Variant(ref row) => f.visit(row).map(|row| f.make(Type::Variant(row))),
        Type::Effect(ref row) => f.visit(row).map(|row| f.make(Type::Effect(row))),
        Type::ExtendRow {
            ref fields,
            ref rest,
        } => {
            let new_fields = walk_move_types(f, fields.iter(), |f, field| {
                f.visit(&field.typ)
                    .map(|typ| Field::new(field.name.clone(), typ))
            })
            .map(|args: Vec<_>| f.context().intern_fields(args));
            let new_rest = f.visit(rest);
            merge(fields, new_fields, rest, new_rest, |fields, rest| {
                f.make(Type::ExtendRow { fields, rest })
            })
        }
        Type::ExtendTypeRow {
            ref types,
            ref rest,
        } => {
            let new_rest = f.visit(rest);
            new_rest.map(|rest| {
                f.make(Type::ExtendTypeRow {
                    types: types.clone(),
                    rest,
                })
            })
        }
        Type::Hole
        | Type::Opaque
        | Type::Error
        | Type::Builtin(_)
        | Type::Variable(_)
        | Type::Skolem(_)
        | Type::Generic(_)
        | Type::Ident(_)
        | Type::Projection(_)
        | Type::Alias(_)
        | Type::EmptyRow => None,
    }
}

pub fn walk_move_types<'a, I, F, T, S, R>(state: &mut S, types: I, f: F) -> Option<R>
where
    S: ?Sized,
    I: IntoIterator<Item = &'a T>,
    I::IntoIter: FusedIterator + Clone,
    F: FnMut(&mut S, &'a T) -> Option<T>,
    T: Clone + 'a,
    R: FromIterator<T>,
{
    merge_collect(state, types, f, |_, e| e.clone())
}

pub fn translate_alias<Id, T, U, F, I>(
    interner: &mut I,
    alias: &AliasData<Id, T>,
    mut translate: F,
) -> AliasData<Id, U>
where
    T: TypePtr<Id = Id>,
    U: TypePtr<Id = Id>,
    Id: Clone,
    T::SpannedId: Clone,
    F: FnMut(&mut I, &T) -> U,
    I: TypeContext<Id, U>,
{
    AliasData {
        name: alias.name.clone(),
        args: interner.intern_generics(alias.args.iter().cloned()),
        typ: translate(interner, &alias.typ),
        is_implicit: alias.is_implicit,
    }
}

pub fn translate_type<Id, T, U>(interner: &mut impl TypeContext<Id, U>, arc_type: &T) -> U
where
    T: TypePtr<Id = Id>,
    U: TypePtr<Id = Id>,
    Id: Clone,
    T::SpannedId: Into<U::SpannedId>,
    T::SpannedId: Clone,
{
    translate_type_with(interner, arc_type, |interner, typ| {
        translate_type(interner, typ)
    })
}

pub fn translate_type_with<Id, T, U, I, F>(
    interner: &mut I,
    typ: &Type<Id, T>,
    mut translate: F,
) -> U
where
    T: TypePtr<Id = Id>,
    U: TypePtr<Id = Id>,
    Id: Clone,
    T::SpannedId: Into<U::SpannedId>,
    T::SpannedId: Clone,
    F: FnMut(&mut I, &T) -> U,
    I: TypeContext<Id, U>,
{
    macro_rules! intern {
        ($e: expr) => {{
            let t = $e;
            interner.intern(t)
        }};
    }
    match *typ {
        Type::Function(arg_type, ref arg, ref ret) => {
            let t = Type::Function(arg_type, translate(interner, arg), translate(interner, ret));
            interner.intern(t)
        }
        Type::App(ref f, ref args) => {
            let f = translate(interner, f);
            let args = args
                .iter()
                .map(|typ| translate(interner, typ))
                .collect::<SmallVec<[_; 5]>>();
            let t = Type::App(f, interner.intern_types(args));
            interner.intern(t)
        }
        Type::Record(ref row) => intern!(Type::Record(translate(interner, row))),
        Type::Variant(ref row) => intern!(Type::Variant(translate(interner, row))),
        Type::Effect(ref row) => intern!(Type::Effect(translate(interner, row))),
        Type::Forall(ref params, ref typ) => {
            let t = Type::Forall(
                interner.intern_generics(params.iter().cloned()),
                translate(interner, typ),
            );
            interner.intern(t)
        }
        Type::Skolem(ref skolem) => interner.intern(Type::Skolem(Skolem {
            name: skolem.name.clone(),
            id: skolem.id.clone(),
            kind: skolem.kind.clone(),
        })),
        Type::ExtendRow {
            ref fields,
            ref rest,
        } => {
            let fields = fields
                .iter()
                .map(|field| Field {
                    name: field.name.clone().into(),
                    typ: translate(interner, &field.typ),
                })
                .collect::<SmallVec<[_; 10]>>();
            let fields = interner.intern_fields(fields);

            let rest = translate(interner, rest);

            interner.extend_row(fields, rest)
        }
        Type::ExtendTypeRow {
            ref types,
            ref rest,
        } => {
            let types = types
                .iter()
                .map(|field| Field {
                    name: field.name.clone().into(),
                    typ: Alias {
                        _typ: translate(interner, &field.typ.as_type()),
                        _marker: PhantomData,
                    },
                })
                .collect::<SmallVec<[_; 10]>>();
            let types = interner.intern_type_fields(types);
            let rest = translate(interner, rest);

            interner.extend_type_row(types, rest)
        }
        Type::Hole => interner.hole(),
        Type::Opaque => interner.opaque(),
        Type::Error => interner.error(),
        Type::Builtin(ref builtin) => interner.builtin_type(builtin.clone()),
        Type::Variable(ref var) => interner.variable(var.clone()),
        Type::Generic(ref gen) => interner.generic(gen.clone()),
        Type::Ident(ref id) => interner.ident(id.clone()),
        Type::Projection(ref ids) => interner.projection(ids.clone()),
        Type::Alias(ref alias) => {
            let group: Vec<_> = alias
                .group
                .iter()
                .map(|alias_data| {
                    translate_alias(interner, alias_data, |interner, a| translate(interner, a))
                })
                .collect();

            interner.intern(Type::Alias(AliasRef {
                index: alias.index,
                group: Arc::from(group),
            }))
        }
        Type::EmptyRow => interner.empty_row(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn walk_move_types_test() {
        assert_eq!(
            walk_move_types(&mut (), [1, 2, 3].iter(), |_, i| if *i == 2 {
                Some(4)
            } else {
                None
            }),
            Some(vec![1, 4, 3])
        );
    }
}
