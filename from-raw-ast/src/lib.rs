use darling::{FromDeriveInput, FromField, FromMeta, FromVariant};
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[derive(Debug, Default, FromMeta)]
#[darling(default)]
struct Lorem {
    #[darling(rename = "sit")]
    ipsum: bool,
    dolor: Option<String>,
}

#[derive(Debug, FromDeriveInput)]
#[darling(attributes(from_raw_ast))]
struct MyTraitOpts {
    ident: syn::Ident,
    // attrs: Vec<syn::Attribute>,
    // a: syn::Path,
    // raw: syn::Path,
    data: darling::ast::Data<MyVariant, MyField>,
}

#[derive(Debug, FromVariant)]
// #[darling(attributes(lorem))]
struct MyVariant {
    ident: syn::Ident,
    fields: darling::ast::Fields<MyField>,
}
#[derive(Debug, FromField)]
#[darling(attributes(spanner))]
struct MyField {
    ident: Option<syn::Ident>,
    // #[darling(default)]
    // span: bool,
}

// fn do_fields(fields: darling::ast::Fields<MyField>) -> proc_macro2::TokenStream {
//     if fields.is_tuple() {
//         let initializers: proc_macro2::TokenStream = fields
//             .into_iter()
//             .enumerate()
//             .map(|(idx, _f)| {
//                 let idx = syn::Index::from(idx);
//                 quote! {
//                     FromRawAst::from_raw_ast(ctx, r.#idx),
//                 }
//             })
//             .collect();

//         quote! {
//             (#initializers)
//         }
//     } else {
//         let initializers: proc_macro2::TokenStream = fields
//             .into_iter()
//             .find(|f| f.)
//             .map(|f| {
//                 let name = f.ident.unwrap();
//                 quote! {
//                     #name: FromRawAst::from_raw_ast(ctx, r.#name),
//                 }
//             })
//             .collect();

//         quote! {
//             {#initializers}
//         }
//     }
// }

#[proc_macro_derive(Spanner, attributes(spanner))]
pub fn derive_answer_fn(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let MyTraitOpts {
        ident, //raw,
        data,
    } = MyTraitOpts::from_derive_input(&input).unwrap();

    let implementation: proc_macro2::TokenStream = match data {
        darling::ast::Data::Enum(variants) => {
            let variants: proc_macro2::TokenStream = variants
                .into_iter()
                .map(|v| {
                    let name = v.ident;

                    if v.fields.is_newtype() {
                        quote! {
                            Self::#name(r) => Spanner::pest_span(r),
                        }
                    } else {
                        todo!()
                    }
                })
                .collect();
            quote! {
                match self {
                    #variants
                }
            }
        }
        darling::ast::Data::Struct(fields) => {
            if fields.is_newtype() {
                quote! {
                    self.0
                }
            } else {
                let field = fields.into_iter().next().unwrap();
                let name = field.ident;
                quote! {
                    self.#name
                }
            }
        }
    };

    quote! {
        impl <'t> Spanner<'t> for #ident<'t> {
            fn pest_span(&self) -> pest::Span<'t> {
                #implementation
            }
        }
    }
    .into()
}
