use std::ops;

use logos::Logos;
use smallvec::SmallVec;

use super::*;

#[derive(Debug, PartialEq, Eq)]
pub struct Impl {
    impl_for: ObjectType,
    kind: ImplKind,
    generics: Vec<IdentName>,
}

/// Object type. Used for function arguments, return types.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ObjectType {
    /// Concrete type with optional generics.
    Concrete {
        /// Name of the type.
        name: ItemPath,

        /// Generics of the type. Can be empty.
        generics: Vec<IdentName>,
    },

    /// Dynamic trait type with optional generics.
    Trait {
        /// Name of the trait.
        name: ItemPath,

        /// Generics of the trait. Can be empty.
        generics: Vec<IdentName>,
    },

    /// Function type with optional generics.
    Func {
        /// Generics of the function. Can be empty.
        generics: Vec<IdentName>,

        /// Argument types of the function.
        args: Vec<ObjectType>,

        /// Return type(s) of the function. Can be more than one if function returns a tuple.
        ret: Vec<ObjectType>,
    },

    /// Empty tuple type.
    /// ```yaml
    /// Fn() -> ()
    /// #       ^^
    /// ```
    Empty,
}

/// Implementation variant.
#[derive(Debug, PartialEq, Eq)]
pub enum ImplKind {
    /// Implement a new in-place defined extension for a type.
    /// ```yaml
    /// impl EmploymentRecord as EmploymentRecordExt:
    /// ```
    AsExt(IdentName),

    /// Implement a new trait for a type.
    /// ```yaml
    /// impl EmploymentRecordTrait for EmploymentRecord:
    /// ```
    Trait(ItemPath),

    /// Implement new functions for a type.
    /// ```yaml
    /// impl EmploymentRecord:
    /// ```
    Simple,
}

impl ImplKind {
    /// When parsing, there is two orders of identifiers, where one is the type being implemented
    /// and the other is the type being implemented for. Sometimes, the order is reversed.
    /// This function swaps the two identifiers when needed so that the first one is always the
    /// type being implemented and the second one is the type being implemented for.
    ///
    /// # Example
    /// ```yaml
    /// # Direct order: implemented for EmploymentRecord, implementing extension EmploymentRecordExt.
    /// impl EmploymentRecord as EmploymentRecordExt:
    /// ```
    ///
    /// ```yaml
    /// # Reversed order: implemented for EmploymentRecord, implementing trait EmploymentRecordTrait.
    /// impl EmploymentRecordTrait for EmploymentRecord:
    /// ```
    ///
    /// # Return
    /// Function returns the name of the type being implemented for.
    fn order_correction(&mut self, mut first_ident: IdentName) -> IdentName {
        use std::mem::swap;
        use ImplKind::*;

        match self {
            AsExt(_) => first_ident,
            Trait(ident) => {
                swap(ident, &mut first_ident);
                first_ident
            }
            Simple => first_ident,
        }
    }
}

/// Lexical element of "impl" line.
#[derive(Debug, Logos, PartialEq, Eq, Clone)]
#[logos(skip r"[ \t\n\f]+")]
pub enum ImplLex {
    #[token("as", priority = 100)]
    As,

    #[token("for", priority = 100)]
    For,

    #[token("impl", priority = 100)]
    Impl,

    #[token("dyn", priority = 100)]
    Dyn,

    #[token("const", priority = 100)]
    Const,

    #[regex("[a-zA-Z_][a-zA-Z0-9_]*", lex_to_ident_name)]
    Ident(IdentName),

    #[token("<")]
    OpenAngle,

    #[token(">")]
    CloseAngle,

    #[token("(")]
    OpenParen,

    #[token(")")]
    CloseParen,

    #[token(",")]
    Comma,

    #[token("->")]
    Arrow,

    #[token("::")]
    PathSeparator,
}

#[derive(Debug, thiserror::Error)]
pub enum ImplLexError {
    #[error("missing 'impl' keyword")]
    MissingImplKeyword,

    #[error("unknown token `{0}`")]
    UnknownToken(String),

    #[error("unexpected token. {0:#?}")]
    UnexpectedToken(ImplLex),

    #[error("unexpected end of input")]
    UnexpectedEnd,

    #[error("generics unclosed")]
    GenericsUnclosed,

    #[error("generics are missing comma between elements")]
    GenericsMissingComma,

    #[error("generics has double comma without element between them")]
    GenericsDoubleComma,
}

impl ImplLex {
    fn parse(string: &str) -> Result<Impl, ImplLexError> {
        use ImplLexError::*;

        let unknown_token = |span: ops::Range<usize>| Err(UnknownToken(string[span].to_owned()));

        // All lexemes except initial "impl".
        let lex = {
            let mut v: SmallVec<[(ImplLex, logos::Span); 64]> = Default::default();
            let mut lex = ImplLex::lexer(string).spanned();

            // All impl blocks start with "impl" keyword.
            let expect_impl_keywork = lex.next().ok_or(MissingImplKeyword)?;
            if let Ok(expect_impl_keywork) = expect_impl_keywork.0 {
                if expect_impl_keywork != ImplLex::Impl {
                    return Err(MissingImplKeyword);
                }
            } else {
                return unknown_token(expect_impl_keywork.1);
            }

            for (lex, span) in lex {
                if let Ok(lex) = lex {
                    v.push((lex, span));
                } else {
                    return Err(UnknownToken(string[span].to_owned()));
                }
            }
            v
        };

        // Parsing iterator over lexemes.
        let mut iter = lex.into_iter().map(|v| v.0).peekable();

        macro_rules! expect(
            (Ident) => {
                match iter.next() {
                    Some(ImplLex::Ident(ident)) => ident,
                    Some(t) => return Err(UnexpectedToken(t)),
                    None => return Err(UnexpectedEnd),
                }
            };
            ($token:ident) => {
                match iter.next() {
                    Some(ImplLex::$token) => (),
                    Some(t) => return Err(UnexpectedToken(t)),
                    None => return Err(UnexpectedEnd),
                }
            };
        );

        // Parse optional generics.
        let generics = {
            let mut generics: SmallVec<[IdentName; 4]> = Default::default();
            if let Some(ImplLex::OpenAngle) = iter.peek() {
                iter.next();

                let mut was_comma = false; // Whether last lexem was comma.
                loop {
                    match iter.next() {
                        Some(ImplLex::Ident(ident)) => {
                            if generics.is_empty() || was_comma {
                                generics.push(ident);
                                was_comma = false;
                            } else {
                                return Err(GenericsMissingComma);
                            }
                        }
                        Some(ImplLex::Comma) => {
                            if was_comma {
                                return Err(GenericsDoubleComma);
                            }
                            was_comma = true;
                        }
                        Some(ImplLex::CloseAngle) => {
                            break;
                            // Trailing comma is allowed.
                        }
                        Some(_) => return Err(GenericsUnclosed),
                        None => return Err(UnexpectedEnd),
                    }
                }
            }
            generics
        };

        // Parse first identifier. It is either the trait being implemented or the type being
        // implemented for. Order is corrected later.
        let first_ident = expect!(Ident);

        let kind = match iter.peek() {
            Some(ImplLex::As) => {
                iter.next();

                let ext_name = expect!(Ident);
                ImplKind::AsExt(ext_name)
            }
            Some(ImplLex::For) => {
                iter.next();

                // TODO support for something else than direct trait name.
                // For example Fn() -> T, or traits with generics.
                let impl_for = expect!(Ident);
                ImplKind::Trait(impl_for)
            }
            Some(_) => ImplKind::Simple,
            None => ImplKind::Simple,
        };

        if let Some(next) = iter.next() {
            // Expected end of input.
            Err(UnexpectedToken(next))
        } else {
            let mut kind = kind;
            let impl_for = kind.order_correction(first_ident);
            Ok(Impl {
                impl_for: ObjectType::Concrete {
                    name: impl_for,
                    generics: vec![], // TODO support for generics.
                },
                kind,
                generics: generics.to_vec(),
            })
        }
    }
}

/// Convert lexical token to identifier name.
///
/// # Safety
/// Should be called carefully on correct tokens to perform conversion into `IdentName`.
/// In debug mode, it will panic on invalid string inputs.
fn lex_to_ident_name(lex: &mut logos::Lexer<ImplLex>) -> IdentName {
    let s = lex.slice().to_string();
    if cfg!(debug_assertions) {
        IdentName::try_from(s).expect("regex validated this")
    } else {
        IdentName(s)
    }
}

/// Declaration of a generic. The one that comes after `impl` keyword, among other places.
/// 
/// # Example
/// ```yaml
/// impl<T> EmploymentRecordTrait<T> for EmploymentRecord
/// #   ^^^                      ^^^
pub struct DeclGeneric {
    name: IdentName,
    spec: DeclGenericSpec,
}

pub enum DeclGenericSpec {
    /// Constant generic.
    Const {
        /// Type of the constant.
        ty: ObjectType,
    },

    /// Just a simple identifier without any specification.
    Simple,
}

impl DeclGeneric {
    fn parse() -> Result<DeclGeneric, ()> {
        unimplemented!()
    }
}

/// Definition of a generic. The one that is used to define generic's exact types.
/// 
/// # Example
/// ```yaml
/// calling_my_fn::<Count = 2, String>::(arg1, arg2)
/// #              ^^^^^^^^^^^^^^^^^^^
/// 
/// type: FixedPoint<Precision = 1>
/// #               ^^^^^^^^^^^^^^^
/// ```
pub enum DefGeneric {
    /// Assigning value to a constant-generic.
    AssignConst {
        /// Name of the generic parameter.
        name: IdentName,

        /// Value of the generic parameter assigned.
        value: String, // TODO parse this too
    },

    /// An item path. Possibly just one identifier, but can be more.
    /// This should then be resolved to a type, via name resolution mechanics.
    Path {
        /// Name of the generic parameter.
        name: ItemPath,
    },
}

impl DefGeneric {
    fn parse() -> Result<DefGeneric, ()> {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn impl_lex() {
        let s = "impl EmploymentRecord as EmploymentRecordExt";
        let impl_for = {
            let ident = IdentName::try_from("EmploymentRecord").unwrap();
            ObjectType::Concrete {
                name: ident,
                generics: vec![],
            }
        };
        let impl_ = ImplLex::parse(s).unwrap();
        assert_eq!(
            impl_,
            Impl {
                impl_for: impl_for.clone(),
                kind: ImplKind::AsExt(IdentName::try_from("EmploymentRecordExt").unwrap()),
                generics: vec![]
            }
        );

        let s = "impl EmploymentRecordTrait for EmploymentRecord";
        let impl_ = ImplLex::parse(s).unwrap();
        assert_eq!(
            impl_,
            Impl {
                impl_for: impl_for.clone(),
                kind: ImplKind::Trait(IdentName::try_from("EmploymentRecordTrait").unwrap()),
                generics: vec![]
            }
        );

        let s = "impl EmploymentRecord";
        let impl_ = ImplLex::parse(s).unwrap();
        assert_eq!(
            impl_,
            Impl {
                impl_for: impl_for.clone(),
                kind: ImplKind::Simple,
                generics: vec![]
            }
        );

        let s = "impl<T> EmploymentRecordTrait for EmploymentRecord";
        let impl_ = ImplLex::parse(s).unwrap();
        assert_eq!(
            impl_,
            Impl {
                impl_for: impl_for.clone(),
                kind: ImplKind::Trait(IdentName::try_from("EmploymentRecordTrait").unwrap()),
                generics: vec![IdentName::try_from("T").unwrap()]
            }
        );

        let s = "impl<T, U> EmploymentRecordTrait for EmploymentRecord";
        let impl_ = ImplLex::parse(s).unwrap();
        assert_eq!(
            impl_,
            Impl {
                impl_for: impl_for.clone(),
                kind: ImplKind::Trait(IdentName::try_from("EmploymentRecordTrait").unwrap()),
                generics: vec![
                    IdentName::try_from("T").unwrap(),
                    IdentName::try_from("U").unwrap()
                ]
            }
        );
    }
}
