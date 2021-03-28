//! Rust type to gluon type conversion
//!
//! _This module requires Gluon to be built with the `serde` feature._

use crate::base::{
    ast::TypedIdent,
    symbol::{Symbol, Symbols},
    types::{ArcType, Field, Type, TypeCache, TypeExt},
};

use crate::api::VmType;
use crate::thread::Thread;
use crate::{Error as VmError, Result};

use crate::serde::de::{
    self, DeserializeOwned, DeserializeSeed, EnumAccess, Error, IntoDeserializer, MapAccess,
    SeqAccess, VariantAccess, Visitor,
};

/// Generates a Gluon expression for a type that is the Gluon equivalent to`T`.
///
/// ## Examples
///
/// For this `T`:
///
/// ```rust
/// struct Address {
///     street: String,
///     city: String,
/// }
/// ```
///
/// the following code will be generated:
///
/// ```gluon
/// type Address = { street: String, city: String }
/// { Address }
/// ```
pub fn make_source<T>(thread: &Thread) -> Result<String>
where
    T: DeserializeOwned,
{
    let (name, typ) = from_rust::<T>(thread)?;
    Ok(format!(
        r#"
type {0} = {1}
{{ {0} }}
"#,
        name,
        typ.pretty(&::pretty::Arena::<()>::new())
            .nest(4)
            .1
            .pretty(80)
    ))
}

/// Deserializes `T` from a gluon value assuming that `value` is of type `typ`.
pub fn from_rust<T>(thread: &Thread) -> Result<(Symbol, ArcType)>
where
    T: DeserializeOwned,
{
    let mut symbols = Symbols::new();
    from_rust_with_symbols::<T>(&mut symbols, thread)
}

pub fn from_rust_with_symbols<T>(
    symbols: &mut Symbols,
    thread: &Thread,
) -> Result<(Symbol, ArcType)>
where
    T: DeserializeOwned,
{
    let type_cache = thread.global_env().type_cache();
    let mut deserializer = Deserializer::from_value(&type_cache, thread, symbols);
    T::deserialize(&mut deserializer)?;
    let mut variants = Vec::new();
    while let Some(variant) = deserializer.variant.take() {
        variants.push(variant);
        deserializer.variant_index += 1;
        match T::deserialize(&mut deserializer) {
            Ok(_) => (),
            Err(VmError::Message(ref msg)) if msg == "" => break,
            Err(err) => return Err(err),
        }
    }
    let typ = if variants.is_empty() {
        deserializer.typ.expect("typ")
    } else {
        type_cache.variant(variants)
    };
    Ok((
        deserializer.state.symbols.simple_symbol(deserializer.name),
        typ,
    ))
}

struct State<'de> {
    cache: &'de TypeCache<Symbol, ArcType<Symbol>>,
    thread: &'de Thread,
    symbols: &'de mut Symbols,
}

struct Deserializer<'de> {
    state: State<'de>,
    typ: Option<ArcType>,
    variant: Option<Field<Symbol, ArcType>>,
    variant_index: usize,
    name: &'static str,
}

impl<'de> Deserializer<'de> {
    fn from_value(
        cache: &'de TypeCache<Symbol, ArcType<Symbol>>,
        thread: &'de Thread,
        symbols: &'de mut Symbols,
    ) -> Self {
        Deserializer {
            state: State {
                cache,
                thread,
                symbols,
            },
            typ: None,
            variant: None,
            variant_index: 0,
            name: "",
        }
    }
}

impl<'de, 't, 'a> de::Deserializer<'de> for &'a mut Deserializer<'de> {
    type Error = VmError;

    fn deserialize_any<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(VmError::Message("Cant deserialize any".to_string()))
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.typ = Some(bool::make_type(self.state.thread));
        visitor.visit_bool(false)
    }

    // The `parse_signed` function is generic over the integer type `T` so here
    // it is invoked with `T=i8`. The next 8 methods are similar.
    fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.typ = Some(self.state.cache.byte());
        visitor.visit_i8(0)
    }

    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.typ = Some(self.state.cache.int());
        visitor.visit_i16(0)
    }

    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.typ = Some(self.state.cache.int());
        visitor.visit_i32(0)
    }

    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.typ = Some(self.state.cache.int());
        visitor.visit_i64(0)
    }

    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.typ = Some(self.state.cache.byte());
        visitor.visit_i8(0)
    }

    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.typ = Some(self.state.cache.int());
        visitor.visit_u16(0)
    }

    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.typ = Some(self.state.cache.int());
        visitor.visit_u32(0)
    }

    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.typ = Some(self.state.cache.int());
        visitor.visit_u64(0)
    }

    fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.typ = Some(self.state.cache.float());
        visitor.visit_f32(0.)
    }

    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.typ = Some(self.state.cache.float());
        visitor.visit_f64(0.)
    }

    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.typ = Some(self.state.cache.char());
        visitor.visit_char('\0')
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.typ = Some(self.state.cache.string());
        visitor.visit_str("")
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_str(visitor)
    }

    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.typ = Some(Type::array(self.state.cache.byte()));
        visitor.visit_bytes(b"")
    }

    fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_bytes(visitor)
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let value = visitor.visit_some(&mut *self)?;
        let option_alias = self
            .state
            .thread
            .find_type_info("std.types.Option")
            .unwrap()
            .clone()
            .into_type();
        self.typ = Some(Type::app(
            option_alias,
            collect![self.typ.take().expect("typ")],
        ));
        Ok(value)
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.typ = Some(self.state.cache.unit());
        visitor.visit_unit()
    }

    fn deserialize_unit_struct<V>(self, name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.name = name;
        self.deserialize_unit(visitor)
    }

    fn deserialize_newtype_struct<V>(self, name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.name = name;
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let (value, typ) = {
            let mut seq_deserializer = SeqDeserializer::new(&mut *self, 1);
            let value = visitor.visit_seq(&mut seq_deserializer)?;
            assert!(seq_deserializer.types.len() == 1);
            (value, seq_deserializer.types.pop().unwrap())
        };
        self.typ = Some(Type::array(typ));
        Ok(value)
    }

    fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let (value, types) = {
            let mut seq_deserializer = SeqDeserializer::new(&mut *self, len);
            (
                visitor.visit_seq(&mut seq_deserializer)?,
                seq_deserializer.types,
            )
        };
        self.typ = Some(self.state.cache.tuple(self.state.symbols, types));
        Ok(value)
    }

    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_seq(visitor)
    }

    fn deserialize_map<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(VmError::Message(
            "Maps cannot be mapped to gluon types yet".to_string(),
        ))
    }

    fn deserialize_struct<V>(
        self,
        name: &'static str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.name = name;
        let (value, types) = {
            let mut map_deserializer = MapDeserializer::new(&mut *self, fields.iter().cloned());
            (
                visitor.visit_map(&mut map_deserializer)?,
                map_deserializer.types,
            )
        };
        self.typ = Some(self.state.cache.record(vec![], types));
        Ok(value)
    }

    fn deserialize_enum<V>(
        self,
        name: &'static str,
        variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.name = name;
        match variants.get(self.variant_index) {
            Some(variant) => visitor.visit_enum(Enum::new(self, variant)),
            None => Err(VmError::Message("".to_string())),
        }
    }

    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_str(visitor)
    }

    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_any(visitor)
    }
}

struct SeqDeserializer<'de: 't, 't> {
    deserializer: &'t mut Deserializer<'de>,
    types: Vec<ArcType>,
    len: usize,
}

impl<'de, 't> SeqDeserializer<'de, 't> {
    fn new(deserializer: &'t mut Deserializer<'de>, len: usize) -> Self {
        SeqDeserializer {
            deserializer,
            len,
            types: Vec::new(),
        }
    }
}

impl<'de, 'a, 't> SeqAccess<'de> for &'a mut SeqDeserializer<'de, 't> {
    type Error = VmError;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>>
    where
        T: DeserializeSeed<'de>,
    {
        if self.len == 0 {
            Ok(None)
        } else {
            self.len -= 1;
            let value = seed.deserialize(&mut *self.deserializer)?;
            self.types.push(self.deserializer.typ.take().expect("typ"));
            Ok(Some(value))
        }
    }
}

struct MapDeserializer<'de: 't, 't, I> {
    deserializer: &'t mut Deserializer<'de>,
    iter: I,
    types: Vec<Field<Symbol, ArcType>>,
}

impl<'de, 't, I> MapDeserializer<'de, 't, I> {
    fn new(deserializer: &'t mut Deserializer<'de>, iter: I) -> Self {
        MapDeserializer {
            deserializer,
            iter,
            types: Vec::new(),
        }
    }
}

impl<'de, 't, I> MapAccess<'de> for MapDeserializer<'de, 't, I>
where
    I: Iterator<Item = &'static str> + Clone,
{
    type Error = VmError;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>>
    where
        K: DeserializeSeed<'de>,
    {
        match self.iter.clone().next() {
            Some(field) => seed.deserialize(field.into_deserializer()).map(Some),
            None => Ok(None),
        }
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value>
    where
        V: DeserializeSeed<'de>,
    {
        match self.iter.next() {
            Some(field) => {
                let value = seed.deserialize(&mut *self.deserializer)?;
                self.types.push(Field::new(
                    self.deserializer.state.symbols.simple_symbol(field),
                    self.deserializer.typ.take().expect("typ"),
                ));
                Ok(value)
            }
            None => Err(Self::Error::custom("Unable to deserialize value")),
        }
    }
}

struct Enum<'a, 'de: 'a> {
    de: &'a mut Deserializer<'de>,
    variant: &'static str,
}

impl<'a, 'de> Enum<'a, 'de> {
    fn new(de: &'a mut Deserializer<'de>, variant: &'static str) -> Self {
        Enum { de, variant }
    }
}

impl<'a, 'de> EnumAccess<'de> for Enum<'a, 'de> {
    type Error = VmError;
    type Variant = Self;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self::Variant)>
    where
        V: DeserializeSeed<'de>,
    {
        seed.deserialize(self.variant.into_deserializer())
            .map(|value| (value, self))
    }
}

impl<'de, 'a> VariantAccess<'de> for Enum<'a, 'de> {
    type Error = VmError;

    fn unit_variant(self) -> Result<()> {
        self.de.variant = Some(Field::ctor(
            TypedIdent {
                name: self.de.state.symbols.simple_symbol(self.de.name),
                typ: self.de.state.cache.kind_cache.typ(),
            },
            self.de.state.symbols.simple_symbol(self.variant),
            vec![],
        ));
        Ok(())
    }

    fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value>
    where
        T: DeserializeSeed<'de>,
    {
        let value = seed.deserialize(&mut *self.de)?;
        self.de.variant = Some(Field::ctor(
            TypedIdent {
                name: self.de.state.symbols.simple_symbol(self.de.name),
                typ: self.de.state.cache.kind_cache.typ(),
            },
            self.de.state.symbols.simple_symbol(self.variant),
            vec![self.de.typ.take().expect("typ")],
        ));
        Ok(value)
    }

    fn tuple_variant<V>(self, len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let (value, types) = {
            let mut seq_deserializer = SeqDeserializer::new(&mut *self.de, len);
            (
                visitor.visit_seq(&mut seq_deserializer)?,
                seq_deserializer.types,
            )
        };
        self.de.variant = Some(Field::ctor(
            TypedIdent {
                name: self.de.state.symbols.simple_symbol(self.de.name),
                typ: self.de.state.cache.kind_cache.typ(),
            },
            self.de.state.symbols.simple_symbol(self.variant),
            types,
        ));
        Ok(value)
    }

    fn struct_variant<V>(self, fields: &'static [&'static str], visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let (value, types) = {
            let mut map_deserializer = MapDeserializer::new(&mut *self.de, fields.iter().cloned());
            (
                visitor.visit_map(&mut map_deserializer)?,
                map_deserializer.types,
            )
        };
        self.de.variant = Some(Field::ctor(
            TypedIdent {
                name: self.de.state.symbols.simple_symbol(self.de.name),
                typ: self.de.state.cache.kind_cache.typ(),
            },
            self.de.state.symbols.simple_symbol(self.variant),
            vec![self.de.state.cache.record(vec![], types)],
        ));
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::from_rust_with_symbols;
    use super::*;
    use crate::thread::RootedThread;

    use base::kind::Kind;

    #[allow(dead_code)]
    #[derive(Deserialize)]
    struct Test {
        x: i32,
        name: String,
    }

    #[test]
    fn struct_type() {
        let mut symbols = Symbols::new();
        let (name, typ) =
            from_rust_with_symbols::<Test>(&mut symbols, &RootedThread::new()).unwrap();
        assert_eq!(name.declared_name(), "Test");
        assert_eq!(
            typ,
            Type::record(
                vec![],
                vec![
                    Field::new(symbols.simple_symbol("x"), Type::int()),
                    Field::new(symbols.simple_symbol("name"), Type::string()),
                ]
            )
        );
    }

    #[allow(dead_code)]
    #[derive(Deserialize)]
    enum Enum {
        A,
        B(i32),
        C(String, f64),
        D { foo: i32 },
    }

    #[test]
    fn enum_type() {
        let mut symbols = Symbols::new();
        let (name, typ) =
            from_rust_with_symbols::<Enum>(&mut symbols, &RootedThread::new()).unwrap();
        assert_eq!(name.declared_name(), "Enum");
        let enum_ident = TypedIdent {
            name: symbols.simple_symbol("Enum"),
            typ: Kind::typ(),
        };
        assert_eq!(
            typ,
            Type::variant(vec![
                Field::ctor(enum_ident.clone(), symbols.simple_symbol("A"), vec![]),
                Field::ctor(
                    enum_ident.clone(),
                    symbols.simple_symbol("B"),
                    vec![Type::int()]
                ),
                Field::ctor(
                    enum_ident.clone(),
                    symbols.simple_symbol("C"),
                    vec![Type::string(), Type::float()],
                ),
                Field::ctor(
                    enum_ident,
                    symbols.simple_symbol("D"),
                    vec![Type::record(
                        vec![],
                        vec![Field::new(symbols.simple_symbol("foo"), Type::int())]
                    )]
                ),
            ])
        );
    }

    #[derive(Deserialize)]
    struct MyArray(Vec<f64>);

    #[test]
    fn vec_type() {
        let mut symbols = Symbols::new();
        let (name, typ) =
            from_rust_with_symbols::<MyArray>(&mut symbols, &RootedThread::new()).unwrap();
        assert_eq!(name.declared_name(), "MyArray");
        assert_eq!(typ, Type::array(Type::float()));
    }
}
