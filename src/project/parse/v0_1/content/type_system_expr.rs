use std::ops;

use logos::Logos;
use smallvec::SmallVec;

use super::*;

/// Iterator over lexical elements.
type LexIter<'a> = logos::SpannedIter<'a, HeadLex>;

/// Check if parser could not start parsing from the very beginning of the input, as
/// first token is not valid for the parser.
/// 
/// This allows to understand whether the parsing itself failed mid-way or the input
/// was not valid for the parser to begin with. Allowing to decide on whether to
/// try another course or to terminate current execution with underlying sub-parser's error to
/// be propagated.
trait IsWrongStart {
    fn is_wrong_start(&self) -> bool;
}

/// Create a guarded context for running a parser to restore the original state if parsing fails.
trait Guard<'lex> {
    fn guard<T, E>(&mut self, f: impl FnOnce(&mut Self) -> Result<T, E>) -> Result<T, E>;
}

impl<'lex, 'context> Guard<'lex> for LexIter<'lex> {
    fn guard<T, E>(&mut self, f: impl FnOnce(&mut Self) -> Result<T, E>) -> Result<T, E> {
        let original = self.clone();
        match f(self) {
            Ok(v) => Ok(v),
            Err(e) => {
                *self = original;
                Err(e)
            },
        }
    }
}

/// "Impl" block header. like
/// ```yaml
///     impl EmploymentRecord as EmploymentRecordExt:
/// ```
#[derive(Debug, PartialEq, Eq)]
pub struct Impl {
    /// An object for which this implementation is defined.
    impl_for: ObjectType,

    /// Kind of implementation header.
    kind: ImplKind,

    /// Generics of the implementation. These are related to the "impl" keyword itself,
    /// not any of the following types.
    ///
    /// ```yaml
    ///     impl<T, U> EmploymentRecordTrait<T, U> for EmploymentRecord:
    /// #       ^^^^^^
    /// ```
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

pub enum ObjectTypeError {
    InvalidStart(HeadLex),

    /// Generic type has an unparseable token.
    UnknownToken(String),

    UnexpectedEnd,
}

impl IsWrongStart for ObjectTypeError {
    fn is_wrong_start(&self) -> bool {
        matches!(self, ObjectTypeError::InvalidStart(_))
    }
}

impl ObjectType {
    fn parse(tokens: &mut LexIter) -> Result<ObjectType, ObjectTypeError> {
        unimplemented!()
    }
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
    /// Direct order: implemented for EmploymentRecord, implementing extension EmploymentRecordExt.
    /// ```yaml
    /// impl EmploymentRecord as EmploymentRecordExt:
    /// ```
    ///
    /// Reversed order: implemented for EmploymentRecord, implementing trait EmploymentRecordTrait.
    /// ```yaml
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

/// Lexical element of `impl` or `fn` headers.
#[derive(Debug, Logos, PartialEq, Eq, Clone)]
#[logos(skip r"[ \t\n\f]+")]
pub enum HeadLex {
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

    #[token("fn", priority = 100)]
    Fn,

    #[regex("[a-zA-Z_][a-zA-Z0-9_]*", lex_to_ident_name)]
    Ident(IdentName),

    #[regex(r#"[-]{0,1}[0-9]+"#, lex_construct_number)]
    NumLit(Number),

    #[regex(r#""([^\\"]|\\")*""#, lex_to_str_lit)]
    StrLit(String),

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

    #[token("=")]
    Assign,
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Number {
    neg: bool,
    int: u64,
}

/// Convert lexical token to number literal.
///
/// # Safety
/// Should be called carefully on correct tokens to perform conversion into `Number`.
/// Otherwise, it will panic on invalid string inputs.
fn lex_construct_number(lex: &mut logos::Lexer<HeadLex>) -> Number {
    let s = lex.slice();
    let neg = s.starts_with('-');
    let s = if neg { &s[1..] } else { s };

    let int: u64 = s.parse().expect("regex validated this");

    Number { neg, int }
}

/// Convert lexical token to identifier name.
///
/// # Safety
/// Should be called carefully on correct tokens to perform conversion into `IdentName`.
/// In debug mode, it will panic on invalid string inputs.
fn lex_to_ident_name(lex: &mut logos::Lexer<HeadLex>) -> IdentName {
    let s = lex.slice().to_string();
    if cfg!(debug_assertions) {
        IdentName::try_from(s).expect("regex validated this")
    } else {
        IdentName(s)
    }
}

fn lex_to_str_lit(lex: &mut logos::Lexer<HeadLex>) -> String {
    let slice = lex.slice();

    if cfg!(debug_assertions) {
        // Check start and end to be quotes.
        assert_eq!(slice.chars().next(), Some('"'));
        assert_eq!(slice.chars().last(), Some('"'));
    }

    let unquoted = &slice[1..slice.len() - 1];

    // Apply escape sequences.
    unquoted.replace("\\\"", "\"")
}

impl HeadLex {
    /// Expect next token to be the same as this one.
    fn expect<E: From<HeadError>>(&self, iter: &mut LexIter, err: E) -> Result<(), E> {
        use HeadError::*;

        if let Some(next) = iter.next() {
            if let Ok(next) = next.0 {
                if next == *self {
                    Ok(())
                } else {
                    Err(err)
                }
            } else {
                Err(UnknownToken(iter.slice().to_owned()).into())
            }
        } else {
            Err(UnexpectedEnd.into())
        }
    }

    /// Check if next token is the same as this one. If so, advance the iterator and return true.
    fn probe(&self, iter: &mut LexIter) -> bool {
        let backup = iter.clone();

        if let Some(next) = iter.next() {
            if let Ok(next) = next.0 {
                return next == *self;
            }
        }

        *iter = backup;
        false
    }

    /// Expect next token to be an identifier.
    fn expect_ident<E: From<HeadError>>(iter: &mut LexIter, err: E) -> Result<IdentName, E> {
        use HeadError::*;

        if let Some(next) = iter.next() {
            if let Ok(HeadLex::Ident(ident)) = next.0 {
                Ok(ident)
            } else {
                Err(err)
            }
        } else {
            Err(UnexpectedEnd.into())
        }
    }

    /// Expect next token to be a string literal.
    fn expect_str_lit<E: From<HeadError>>(iter: &mut LexIter, err: E) -> Result<HeadLex, E> {
        use HeadError::*;

        if let Some(next) = iter.next() {
            if let Ok(HeadLex::StrLit(s)) = next.0 {
                Ok(HeadLex::StrLit(s))
            } else {
                Err(err)
            }
        } else {
            Err(UnexpectedEnd.into())
        }
    }

    /// Expect next token to be a number literal.
    fn expect_num_lit<E: From<HeadError>>(iter: &mut LexIter, err: E) -> Result<HeadLex, E> {
        use HeadError::*;

        if let Some(next) = iter.next() {
            if let Ok(HeadLex::NumLit(n)) = next.0 {
                Ok(HeadLex::NumLit(n))
            } else {
                Err(err)
            }
        } else {
            Err(UnexpectedEnd.into())
        }
    }

    /// Expect next token to be a literal.
    fn expect_lit<E: From<HeadError>>(iter: &mut LexIter, err: E) -> Result<HeadLex, E> {
        use HeadError::*;

        if let Some(next) = iter.next() {
            if let Ok(next) = next.0 {
                match next {
                    HeadLex::StrLit(_) | HeadLex::NumLit(_) => Ok(next),
                    _ => Err(err),
                }
            } else {
                Err(UnknownToken(iter.slice().to_owned()).into())
            }
        } else {
            Err(UnexpectedEnd.into())
        }
    }
}

/// Generic error for header parsing, that can occur in any specialized parser.
pub enum HeadError {
    /// Generic error for unexpected end of input.
    UnexpectedEnd,

    /// Token cannot be parsed from this string.
    UnknownToken(String),
}

#[derive(Debug, thiserror::Error)]
pub enum ImplLexError {
    #[error("missing 'impl' keyword")]
    MissingImplKeyword,

    #[error("unknown token `{0}`")]
    UnknownToken(String),

    #[error("unexpected token. {0:#?}")]
    UnexpectedToken(HeadLex),

    #[error("unexpected end of input")]
    UnexpectedEnd,

    #[error("generics unclosed")]
    GenericsUnclosed,

    #[error("generics are missing comma between elements")]
    GenericsMissingComma,

    #[error("generics has double comma without element between them")]
    GenericsDoubleComma,
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
    /// Assigning value to a named const generic.
    ///
    /// # Example
    /// FixedPrecision type has a named const generic `Precision`.
    /// ```yaml
    /// FixedPoint<Precision = 1>
    /// #         ^^^^^^^^^^^^^^^
    /// ```
    AssignConstNamed {
        /// Name of the generic parameter.
        name: IdentName,

        /// Value of the generic parameter assigned.
        value: Literal,
    },

    /// Assigning type to a named generic.
    ///
    /// Iterator in Permute has a named generic `Item`.
    /// ```yaml
    /// impl<T> Iterator<Item = T> for SomeIterType
    /// #               ^^^^^^^^^^
    /// ```
    ///
    AssignTypeNamed {
        /// Name of the generic parameter.
        name: IdentName,

        /// Type of the generic parameter assigned.
        ty: ObjectType,
    },

    /// An item path. Possibly just one identifier, but can be more.
    /// This should then be resolved to a type, via name resolution mechanics.
    Path {
        /// Name of the generic parameter.
        name: ItemPath,
    },
}

/// Literal value.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Literal {
    Str(String),
    Num(Number),
}

impl From<Literal> for HeadLex {
    fn from(lit: Literal) -> HeadLex {
        match lit {
            Literal::Str(s) => HeadLex::StrLit(s),
            Literal::Num(n) => HeadLex::NumLit(n),
        }
    }
}

impl Literal {
    fn expect<E: From<HeadError>>(iter: &mut LexIter, err: E) -> Result<Literal, E> {
        use HeadError::*;

        if let Some(next) = iter.next() {
            if let Ok(next) = next.0 {
                match next {
                    HeadLex::StrLit(s) => Ok(Literal::Str(s)),
                    HeadLex::NumLit(n) => Ok(Literal::Num(n)),
                    _ => Err(err),
                }
            } else {
                Err(UnknownToken(iter.slice().to_owned()).into())
            }
        } else {
            Err(UnexpectedEnd.into())
        }
    }
}

pub enum DefGenericError {
    /// Generic definition is missing a name.
    MissingName,

    /// Generic definition is missing a value in opened assignment.
    MissingValue,

    /// Generic definition has an unparseable token.
    UnknownToken(String),

    /// Unexpected end of input.
    UnexpectedEnd,

    /// Generic definition has an invalid end.
    InvalidEnd,

    /// Generic type parsing has failed.
    ObjectTypeFailed(ObjectTypeError),
}

impl From<ObjectTypeError> for DefGenericError {
    fn from(err: ObjectTypeError) -> DefGenericError {
        DefGenericError::ObjectTypeFailed(err)
    }
}

impl From<HeadError> for DefGenericError {
    fn from(err: HeadError) -> DefGenericError {
        match err {
            HeadError::UnexpectedEnd => DefGenericError::UnexpectedEnd,
            HeadError::UnknownToken(s) => DefGenericError::UnknownToken(s),
        }
    }
}

impl DefGeneric {
    fn parse(tokens: &mut LexIter) -> Result<DefGeneric, DefGenericError> {
        use DefGenericError::*;
        use HeadLex::*;

        tokens.guard(|iter| {
            let name = HeadLex::expect_ident(&mut iter, MissingName)?;

            if Assign.probe(&mut iter) {
                // Either const or type assignment.

                // Try to parse const assignment.
                if let Ok(value) = Literal::expect(&mut iter, MissingValue) {
                    return Ok(DefGeneric::AssignConstNamed { name, value });
                }

                // Try to parse object type.
                match ObjectType::parse(&mut iter) {
                    Ok(ty) => return Ok(DefGeneric::AssignTypeNamed { name, ty }),
                    Err(e) => {
                        if !e.is_wrong_start() {
                            return Err(e.into());
                        }
                    }
                }

                return Err(InvalidEnd);
            }

            Ok(DefGeneric::Path { name })
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
