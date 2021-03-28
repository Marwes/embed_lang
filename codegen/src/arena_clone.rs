use proc_macro2::{Ident, Span, TokenStream};
use syn::{self, Data, DeriveInput, Fields, GenericParam, Generics};

use crate::{
    attr::{Container, CrateName},
    shared::{map_type_params, split_for_impl},
};

pub fn derive(input: TokenStream) -> TokenStream {
    let derive_input = syn::parse2(input).expect("Input is checked by rustc");

    let container = Container::from_ast(&derive_input);

    let DeriveInput {
        ident,
        data,
        generics,
        ..
    } = derive_input;

    let tokens = match data {
        Data::Struct(_) | Data::Enum(_) => gen_impl(&container, ident, generics, &data),
        Data::Union(_) => panic!("Unions are not supported"),
    };

    tokens.into()
}

fn gen_impl(container: &Container, ident: Ident, generics: Generics, data: &Data) -> TokenStream {
    let trait_bounds = &map_type_params(&generics, |ty| {
        quote! { #ty: _gluon_api::VmType, #ty::Type: Sized }
    });

    let (impl_generics, ty_generics, where_clause) = split_for_impl(&generics, &[]);

    let make_type_impl = match *data {
        Data::Struct(ref struct_) => match struct_.fields {
            Fields::Named(ref fields) => {
                let fields = fields.named.iter().map(|field| {
                    let ident = field.ident.as_ref().unwrap().to_string();
                    let typ = &field.ty;
                    quote! {
                        _gluon_base::types::Field {
                            name: _gluon_base::symbol::Symbol::from(#ident),
                            typ: <#typ as _gluon_api::VmType>::make_type(vm),
                        }
                    }
                });
                quote! {
                    _gluon_base::types::Type::record(
                        vec![],
                        vec![#(#fields),*],
                    )
                }
            }
            Fields::Unnamed(ref fields) => {
                if fields.unnamed.len() == 1 {
                    let typ = &fields.unnamed[0].ty;
                    quote! {
                        <#typ as _gluon_api::VmType>::make_type(vm)
                    }
                } else {
                    let fields = fields.unnamed.iter().map(|field| &field.ty);
                    quote! {
                        _gluon_base::types::Type::tuple(vec![#(
                            <#fields as _gluon_api::VmType>::make_type(vm)
                        ),*])
                    }
                }
            }
            Fields::Unit => quote!(_gluon_base::types::Type::unit()),
        },
        Data::Enum(ref enum_) => {
            let variants = enum_.variants.iter().map(|variant| {
                let variant_ident = variant.ident.to_string();
                match variant.fields {
                    Fields::Named(ref fields) => {
                        let fields = fields.named.iter().map(|field| {
                            let variant_ident = field.variant_ident.as_ref().unwrap().to_string();
                            let typ = &field.ty;
                            quote! {
                                _gluon_base::types::Field {
                                    name: _gluon_base::symbol::Symbol::from(#variant_ident),
                                    typ: <#typ as _gluon_api::VmType>::make_type(vm),
                                }
                            }
                        });
                        quote! {{
                            let ctor_name = _gluon_base::symbol::Symbol::from(#variant_ident);
                            let typ = _gluon_base::types::Type::record(
                                vec![],
                                vec![#(#fields),*],
                            );
                            _gluon_base::types::Field::ctor(
                                ctor_name,
                                vec![typ],
                            )
                        }}
                    }
                    Fields::Unnamed(ref fields) => {
                        let args = fields.unnamed.iter().map(|field| {
                            let typ = &field.ty;
                            quote! {
                                <#typ as _gluon_api::VmType>::make_type(vm)
                            }
                        });
                        quote! {{
                            let ctor_name = _gluon_base::symbol::Symbol::from(#variant_ident);
                            _gluon_base::types::Field::ctor(
                                ctor_name,
                                vec![#(#args),*],
                            )
                        }}
                    }
                    Fields::Unit => quote! {{
                        let ctor_name = _gluon_base::symbol::Symbol::from(#variant_ident);
                        _gluon_base::types::Field::ctor(
                            _gluon_base::ast::TypedIdent {
                                name: _gluon_base::symbol::Symbol::from(#ident),
                                typ: vm.global_env().type_cache().kind_cache.typ(),
                            },
                            ctor_name,
                            vec![],
                        )
                    }},
                }
                //----------------------------------------------------

                //----------------------------------------------------
            });
            quote! {
                _gluon_base::types::Type::variant(
                    vec![#(#variants),*]
                )
            }
        }
        _ => panic!("Only structs and enums can derive `ArenaClone`"),
    };

    let dummy_const = Ident::new(
        &format!("_IMPL_ARENA_CLONE_FOR_{}", ident),
        Span::call_site(),
    );

    quote! {
        #[allow(non_upper_case_globals)]
        const #dummy_const: () = {

            #[automatically_derived]
            #[allow(unused_attributes, unused_variables)]
            impl #impl_generics #ident #ty_generics
                #where_clause #(#trait_bounds,)*
            {
                pub fn clone(&self, arena: &Arena<Symbol>) -> Self {
                    #make_type_impl
                }
            }
        };
    }
}
