use logos::Logos;
use smallvec::{smallvec, SmallVec};

use super::*;

use crate::error_expl::{Span, Spanned};

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

/// Parse lexemes into a structure.
trait Parse: Sized {
    type Error;

    fn parse(tokens: &mut LexIter) -> Result<Self, Self::Error>;

    /// Parse with span.
    fn parse_span(tokens: &mut LexIter) -> Result<Spanned<Self>, Self::Error> {
        let start = tokens.span().start as _;
        let v = Self::parse(tokens);
        let end = tokens.span().end as _;
        let span = Span::new(start, end).expect("iterator above should give valid span");
        v.map(|v| span.with(v))
    }
}

/// Optional parsing. This can be used when some part of the input is optional, to not
/// fail the parsing if it is not present and instead return `Ok(None)`.
///
/// It is automatically implemented for all types that implement [Parse] trait and their
/// error type implements [IsWrongStart].
trait ParseOption: Parse {
    fn parse_option(tokens: &mut LexIter) -> Option<Result<Self, Self::Error>>;

    /// Parse with span.
    fn parse_option_span(tokens: &mut LexIter) -> Option<Result<Spanned<Self>, Self::Error>> {
        let start = tokens.span().start as _;
        let v = Self::parse_option(tokens);
        let end = tokens.span().end as _;
        let span = Span::new(start, end).expect("iterator above should give valid span");
        v.map(|v| v.map(|v| span.with(v)))
    }
}

impl<E, P> ParseOption for P
where
    E: IsWrongStart,
    P: Parse<Error = E>,
{
    fn parse_option(tokens: &mut LexIter) -> Option<Result<Self, Self::Error>> {
        match Self::parse(tokens) {
            Ok(v) => Some(Ok(v)),
            Err(e) => {
                if e.is_wrong_start() {
                    None
                } else {
                    Some(Err(e))
                }
            }
        }
    }
}

/// Default value for [Result] output from [ParseOption].
trait UnwrapOrDefaultParsed<T> {
    fn unwrap_or_default_parsed(self) -> T;
}

impl<P, E> UnwrapOrDefaultParsed<P> for Option<Result<P, E>>
where
    E: IsWrongStart,
    P: Parse<Error = E> + Default,
{
    fn unwrap_or_default_parsed(self) -> P {
        match self {
            Some(Ok(v)) => v,
            _ => P::default(),
        }
    }
}

impl<P, E> UnwrapOrDefaultParsed<Spanned<P>> for Option<Result<Spanned<P>, E>>
where
    E: IsWrongStart,
    P: Parse<Error = E> + Default,
{
    fn unwrap_or_default_parsed(self) -> Spanned<P> {
        match self {
            Some(Ok(v)) => v,
            _ => Spanned::default(),
        }
    }
}

trait MapInnerInto<P, U, E, EI> {
    fn map_inner_into(self, f: impl FnOnce(P) -> U, or_else: EI) -> Result<U, EI>;
}

impl<P, U, E, EI> MapInnerInto<P, U, E, EI> for Option<Result<P, E>>
where
    P: Parse<Error = E>,
    E: Into<EI>,
{
    fn map_inner_into(self, f: impl FnOnce(P) -> U, or_else: EI) -> Result<U, EI> {
        self.map(|v| v.map(f).map_err(Into::into))
            .unwrap_or(Err(or_else))
    }
}

trait WrongStart: From<HeadError> + IsWrongStart {
    fn wrong_start(wrong_token: HeadLex) -> Self;
}

/// Create a guarded context for running a parser to restore the original state if parsing fails.
trait Guard<'lex> {
    fn guard<T, E>(&mut self, f: impl FnOnce(&mut Self) -> Result<T, E>) -> Result<T, E>;
}

impl<'lex> Guard<'lex> for LexIter<'lex> {
    fn guard<T, E>(&mut self, f: impl FnOnce(&mut Self) -> Result<T, E>) -> Result<T, E> {
        let original = self.clone();
        match f(self) {
            Ok(v) => Ok(v),
            Err(e) => {
                *self = original;
                Err(e)
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ItemPathError {
    /// Item path is missing a name.
    MissingName,

    /// Item path has an unparseable token.
    UnknownToken(String),

    /// Unexpected end of input.
    UnexpectedEnd,

    /// Item path has an invalid end.
    InvalidEnd,
}

impl From<HeadError> for ItemPathError {
    fn from(err: HeadError) -> ItemPathError {
        match err {
            HeadError::UnexpectedEnd => ItemPathError::UnexpectedEnd,
            HeadError::UnknownToken(s) => ItemPathError::UnknownToken(s),
        }
    }
}

impl IsWrongStart for ItemPathError {
    fn is_wrong_start(&self) -> bool {
        matches!(self, ItemPathError::MissingName)
    }
}

impl Parse for ItemPath {
    type Error = ItemPathError;

    fn parse(tokens: &mut LexIter) -> Result<ItemPath, ItemPathError> {
        use HeadLex::*;
        use ItemPathError as E;

        tokens.guard(|iter| {
            let mut items = SmallVec::new();
            loop {
                let name = HeadLex::expect_ident(
                    iter,
                    if items.is_empty() {
                        E::MissingName
                    } else {
                        E::InvalidEnd
                    },
                )?;
                items.push(name);

                if !PathSeparator.probe(iter) {
                    break;
                }
            }

            Ok(ItemPath { items })
        })
    }
}

/// "Impl" block header. like
/// ```yaml
///     impl EmploymentRecord as EmploymentRecordExt:
/// ```
#[derive(Debug, PartialEq, Eq)]
pub struct Impl {
    /// Span of the `impl` token.
    impl_t: Span,

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
    generics: Spanned<Vec<DeclGeneric>>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ImplError {
    /// Generic declaration is missing a name.
    MissingName,

    /// Generic declaration has an unparseable token.
    UnknownToken(String),

    /// Unexpected end of input.
    UnexpectedEnd,

    /// Generics error.
    DeclGenerics(DeclGenericError),

    /// Object type parsing has failed.
    ObjectTypeFail(ObjectTypeError),

    /// Item path parsing has failed.
    ItemPathFail(ItemPathError),
}

impl From<DeclGenericError> for ImplError {
    fn from(err: DeclGenericError) -> ImplError {
        ImplError::DeclGenerics(err)
    }
}

impl From<ObjectTypeError> for ImplError {
    fn from(err: ObjectTypeError) -> ImplError {
        ImplError::ObjectTypeFail(err)
    }
}

impl From<ItemPathError> for ImplError {
    fn from(err: ItemPathError) -> ImplError {
        ImplError::ItemPathFail(err)
    }
}

impl IsWrongStart for ImplError {
    fn is_wrong_start(&self) -> bool {
        matches!(self, ImplError::MissingName)
    }
}

impl WrongStart for ImplError {
    fn wrong_start(_: HeadLex) -> Self {
        ImplError::MissingName
    }
}

impl From<HeadError> for ImplError {
    fn from(err: HeadError) -> ImplError {
        match err {
            HeadError::UnexpectedEnd => ImplError::UnexpectedEnd,
            HeadError::UnknownToken(s) => ImplError::UnknownToken(s),
        }
    }
}

impl Parse for Impl {
    type Error = ImplError;

    fn parse(tokens: &mut LexIter) -> Result<Impl, ImplError> {
        use HeadLex::*;
        use ImplError as E;

        tokens.guard(|iter| {
            // Parse keyword.
            let impl_t = Impl.expect_start::<E>(iter)?;

            // Parse declared generics.
            let generics = Vec::<DeclGeneric>::parse_option_span(iter).unwrap_or_default_parsed();

            // There are two possible orders of identifiers, where one is the type being implemented
            // and the other is the type being implemented for. Sometimes, the order is reversed.
            let first = ObjectType::parse(iter)?;

            // Parse the kind of implementation.
            let kind = if As.probe(iter) {
                // Implementing an extension.
                let ext = HeadLex::expect_ident(iter, E::MissingName)?;
                ImplKind::AsExt {
                    ext,
                    as_t: iter.span().into(),
                }
            } else if For.probe(iter) {
                // Implementing a trait.
                ImplKind::Trait {
                    name: ItemPath::parse(iter)?,
                    generics: Vec::<DeclGeneric>::parse_option_span(iter)
                        .unwrap_or_default_parsed(),
                    for_t: iter.span().into(),
                }
            } else {
                // Implementing new functions.
                ImplKind::Simple
            };

            let (kind, impl_for) = {
                let mut kind = kind;
                let impl_for = kind.order_correction(first);
                (kind, impl_for)
            };
            Ok(self::Impl {
                impl_t,
                impl_for,
                kind,
                generics,
            })
        })
    }
}

/// Object type. Used for function arguments, return types.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ObjectType {
    /// Concrete type with optional generics.
    Concrete {
        /// Name of the type.
        name: Spanned<ItemPath>,

        /// Generics of the type. Can be empty.
        generics: Spanned<Vec<DeclGeneric>>,
    },

    /// Dynamic trait type with optional generics.
    Trait {
        /// Name of the trait.
        name: ItemPath,

        /// Generics of the trait. Can be empty.
        generics: Spanned<Vec<DeclGeneric>>,
    },

    /// Function type with optional generics.
    Func {
        /// Span of the `fn` keyword.
        fn_t: Span,

        /// Generics of the function. Can be empty.
        generics: Spanned<Vec<DeclGeneric>>,

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

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ObjectTypeError {
    /// Generic type has an unparseable token.
    UnknownToken(String),

    UnexpectedEnd,

    ItemPathFailure(ItemPathError),
}

impl From<ItemPathError> for ObjectTypeError {
    fn from(err: ItemPathError) -> ObjectTypeError {
        ObjectTypeError::ItemPathFailure(err)
    }
}

impl IsWrongStart for ObjectTypeError {
    fn is_wrong_start(&self) -> bool {
        matches!(
            self,
            ObjectTypeError::ItemPathFailure(ItemPathError::MissingName)
        )
    }
}

impl WrongStart for ObjectTypeError {
    fn wrong_start(_: HeadLex) -> Self {
        ObjectTypeError::ItemPathFailure(ItemPathError::MissingName)
    }
}

impl From<HeadError> for ObjectTypeError {
    fn from(err: HeadError) -> ObjectTypeError {
        match err {
            HeadError::UnexpectedEnd => ObjectTypeError::UnexpectedEnd,
            HeadError::UnknownToken(s) => ObjectTypeError::UnknownToken(s),
        }
    }
}

impl Parse for ObjectType {
    type Error = ObjectTypeError;

    fn parse(tokens: &mut LexIter) -> Result<ObjectType, ObjectTypeError> {
        macro_rules! attempt {
            ($f:ident) => {
                match ObjectType::$f(tokens) {
                    Ok(t) => return Ok(t),
                    Err(e) => {
                        if !e.is_wrong_start() {
                            return Err(e);
                        }
                    }
                }
            };
        }

        // First try parse all variants that begin with a keyword.
        attempt!(parse_trait);
        attempt!(parse_func);

        // The only remaining option is a concrete type, which starts without a keyword.
        ObjectType::parse_concrete(tokens)
    }
}

impl ObjectType {
    fn parse_concrete(tokens: &mut LexIter) -> Result<ObjectType, ObjectTypeError> {
        tokens.guard(|iter| {
            let name = ItemPath::parse_span(iter)?;
            let generics = Vec::<DeclGeneric>::parse_option_span(iter).unwrap_or_default_parsed();

            Ok(ObjectType::Concrete { name, generics })
        })
    }

    fn parse_trait(tokens: &mut LexIter) -> Result<ObjectType, ObjectTypeError> {
        use HeadLex::*;
        use ObjectTypeError as E;

        tokens.guard(|iter| {
            // Trait type starts with `dyn` keyword.
            Dyn.expect_start::<E>(iter)?;

            let name = ItemPath::parse(iter)?;
            let generics = Vec::<DeclGeneric>::parse_option_span(iter).unwrap_or_default_parsed();

            Ok(ObjectType::Trait { name, generics })
        })
    }

    fn parse_func(tokens: &mut LexIter) -> Result<ObjectType, ObjectTypeError> {
        use HeadLex::*;
        use ObjectTypeError as E;

        tokens.guard(|iter| {
            // Function type starts with `fn` keyword.
            let fn_t = Fn.expect_start::<E>(iter)?;

            let generics = Vec::<DeclGeneric>::parse_option_span(iter).unwrap_or_default_parsed();

            // Parse arguments.
            OpenParen.expect(iter, E::UnexpectedEnd)?; // TODO normal errors here and below
            let args: SmallVec<[_; 8]> = HeadLex::comma_smallvec(iter, ObjectType::parse)?;
            CloseParen.expect(iter, E::UnexpectedEnd)?;

            // Parse optional return type.
            let ret: SmallVec<[_; 8]> = if Arrow.probe(iter) {
                // Either a tuple or a single type.
                if OpenParen.probe(iter) {
                    let v = HeadLex::comma_smallvec(iter, ObjectType::parse)?;
                    CloseParen.expect(iter, E::UnexpectedEnd)?;
                    v
                } else {
                    smallvec![ObjectType::parse(iter)?]
                }
            } else {
                smallvec![]
            };

            Ok(ObjectType::Func {
                fn_t,
                generics,
                args: args.into_vec(),
                ret: ret.into_vec(),
            })
        })
    }
}

/// Implementation variant.
#[derive(Debug, PartialEq, Eq)]
pub enum ImplKind {
    /// Implement a new in-place defined extension for a type.
    /// ```yaml
    /// impl EmploymentRecord as EmploymentRecordExt:
    /// ```
    AsExt {
        /// Name of the extension.
        ext: Spanned<IdentName>,

        /// Span of the `as` keyword.
        as_t: Span,
    },

    /// Implement a new trait for a type.
    /// ```yaml
    /// impl EmploymentRecordTrait for EmploymentRecord:
    /// ```
    Trait {
        /// Name of the trait. Path if specified.
        name: ItemPath,

        /// Generics of the trait. Can be empty.
        generics: Spanned<Vec<DeclGeneric>>,

        /// Span of the `for` keyword.
        for_t: Span,
    },

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
    fn order_correction(&mut self, mut first_ty: ObjectType) -> ObjectType {
        use std::mem::swap;
        use ImplKind::*;

        match self {
            AsExt { .. } => first_ty,
            Trait { name, generics, .. } => {
                match &mut first_ty {
                    ObjectType::Func { .. } => {
                        panic!("expected Concrete, got {first_ty:?}");
                    }
                    ObjectType::Concrete {
                        name: first_name,
                        generics: first_generics,
                    } => {
                        // This was mistake
                        swap(generics, first_generics);
                        swap(name, first_name);
                    }
                    ObjectType::Trait { .. } => {
                        panic!("unexpect 'dyn' for trait impl");
                        // Dyn is used for trait objects, not for trait implementations.
                    }
                    ObjectType::Empty => {}
                }

                first_ty
            }
            Simple => first_ty,
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
pub struct Number {
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
    fn expect<E: From<HeadError>>(&self, iter: &mut LexIter, err: E) -> Result<Span, E> {
        self.expect_peek(iter).map_err(|e| match e {
            Ok(_) => err,
            Err(e) => e.into(),
        })
    }

    /// Expect next token to be the same as this one.
    /// If not, return the next token that was instead. If there is no next token, return [HeadError].
    /// If next token is the same, advance the iterator.
    fn expect_peek(&self, iter: &mut LexIter) -> Result<Span, Result<Spanned<HeadLex>, HeadError>> {
        use HeadError::*;

        iter.guard(|iter| {
            if let Some((next, range)) = iter.next() {
                if let Ok(next) = next {
                    if next == *self {
                        Ok(range.into())
                    } else {
                        Err(Ok(Span::from(range).with(next)))
                    }
                } else {
                    Err(Err(UnknownToken(iter.slice().to_owned())))
                }
            } else {
                Err(Err(UnexpectedEnd))
            }
        })
    }

    /// Expect next token to be the same as this one. If not, return the next token that was instead.
    /// This function wraps the error into a [WrongStart] error. Which may be useful
    /// to reduce boilerplate in probing at the start of the parser.
    fn expect_start<E: WrongStart>(&self, iter: &mut LexIter) -> Result<Span, E> {
        self.expect_peek(iter).map_err(|e| match e {
            Ok(t) => WrongStart::wrong_start(t.into_inner()),
            Err(e) => e.into(),
        })
    }

    /// Check if next token is the same as this one. If so, advance the iterator and return true.
    fn probe(&self, iter: &mut LexIter) -> bool {
        self.spanprobe(iter).is_some()
    }

    /// Check if next token is the same as this one. If so, advance the iterator and return [Span].
    fn spanprobe(&self, iter: &mut LexIter) -> Option<Span> {
        let backup = iter.clone();

        if let Some((Ok(next), range)) = iter.next() {
            if next == *self {
                return Some(Span::from(range));
            }
        }

        *iter = backup;
        None
    }

    /// Expect next token to be an identifier.
    fn expect_ident<E: From<HeadError>>(
        iter: &mut LexIter,
        err: E,
    ) -> Result<Spanned<IdentName>, E> {
        use HeadError::*;

        if let Some((next, range)) = iter.next() {
            if let Ok(HeadLex::Ident(ident)) = next {
                Ok(Span::from(range).with(ident))
            } else {
                Err(err)
            }
        } else {
            Err(UnexpectedEnd.into())
        }
    }

    /// Parse a list of elements separated by commas into a small vector.
    /// Stop when a wrong start is encountered or next token is not a comma.
    fn comma_smallvec<const N: usize, T, E: From<HeadError> + IsWrongStart>(
        iter: &mut LexIter,
        mut f: impl FnMut(&mut LexIter) -> Result<T, E>,
    ) -> Result<SmallVec<[T; N]>, E> {
        let mut vec: SmallVec<[T; N]> = SmallVec::new();
        loop {
            match f(iter) {
                Ok(v) => vec.push(v),
                Err(e) => {
                    if e.is_wrong_start() {
                        break;
                    } else {
                        return Err(e);
                    }
                }
            }

            if HeadLex::Comma.probe(iter) {
                continue;
            } else {
                break;
            }
        }
        Ok(vec)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
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
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DeclGeneric {
    name: Spanned<IdentName>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum DeclGenericError {
    /// Generic declaration is missing a name.
    MissingName,

    /// Generic declaration has an unparseable token.
    UnknownToken(String),

    /// Unexpected end of input.
    UnexpectedEnd,
}

impl IsWrongStart for DeclGenericError {
    fn is_wrong_start(&self) -> bool {
        matches!(self, DeclGenericError::MissingName)
    }
}

impl WrongStart for DeclGenericError {
    fn wrong_start(_: HeadLex) -> Self {
        DeclGenericError::MissingName
    }
}

impl From<HeadError> for DeclGenericError {
    fn from(err: HeadError) -> DeclGenericError {
        match err {
            HeadError::UnexpectedEnd => DeclGenericError::UnexpectedEnd,
            HeadError::UnknownToken(s) => DeclGenericError::UnknownToken(s),
        }
    }
}

impl Parse for DeclGeneric {
    type Error = DeclGenericError;

    fn parse(tokens: &mut LexIter) -> Result<DeclGeneric, DeclGenericError> {
        use DeclGenericError::*;

        tokens.guard(|iter| {
            let name = HeadLex::expect_ident(iter, MissingName)?;

            Ok(DeclGeneric { name })
        })
    }
}

impl Parse for Vec<DeclGeneric> {
    type Error = DeclGenericError;

    /// Parse a list of generics. Consuming angle brackets too.
    fn parse(tokens: &mut LexIter) -> Result<Vec<DeclGeneric>, DeclGenericError> {
        use DeclGenericError as E;
        use HeadLex::*;

        // Parse generics split by commas.
        tokens.guard(|iter| {
            OpenAngle.expect_start::<E>(iter)?;
            let generics: SmallVec<[_; 8]> = HeadLex::comma_smallvec(iter, DeclGeneric::parse)?;
            CloseAngle.expect(iter, E::UnexpectedEnd)?;
            Ok(generics.into_vec())
        })
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
#[derive(Debug, PartialEq, Eq, Clone)]
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
        /// Span of the `=` token.
        assign_t: Span,

        /// Name of the generic parameter.
        name: Spanned<IdentName>,

        /// Value of the generic parameter assigned.
        value: Spanned<Literal>,
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
        /// Span of the `=` token.
        assign_t: Span,

        /// Name of the generic parameter.
        name: Spanned<IdentName>,

        /// Type of the generic parameter assigned.
        ty: ObjectType,
    },

    /// An item path. Possibly just one identifier, but can be more.
    /// This should then be resolved to a type, via name resolution mechanics.
    Path {
        /// Name of the generic parameter.
        path: ItemPath,
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
    fn expect<E: From<HeadError>>(iter: &mut LexIter, err: E) -> Result<Spanned<Literal>, E> {
        match Self::spanprobe(iter) {
            Some(Ok(v)) => Ok(v),
            Some(Err(e)) => Err(e),
            None => Err(err),
        }
    }

    fn spanprobe<E: From<HeadError>>(iter: &mut LexIter) -> Option<Result<Spanned<Literal>, E>> {
        use HeadError::*;
        use Literal::*;

        let backup = iter.clone();

        if let Some((next, range)) = iter.next() {
            let span = Span::from(range);
            if let Ok(next) = next {
                match next {
                    HeadLex::StrLit(s) => Some(Ok(span.with(Str(s)))),
                    HeadLex::NumLit(n) => Some(Ok(span.with(Num(n)))),
                    _ => {
                        *iter = backup;
                        None
                    }
                }
            } else {
                Some(Err(UnknownToken(iter.slice().to_owned()).into()))
            }
        } else {
            Some(Err(UnexpectedEnd.into()))
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum DefGenericError {
    /// Generic definition is missing a value in opened assignment.
    MissingValue,

    /// Generic definition has an unparseable token.
    UnknownToken(String),

    /// Unexpected end of input.
    UnexpectedEnd,

    /// Generic definition has an invalid end.
    InvalidEnd,

    /// Generic type parsing has failed.
    ObjectTypeFail(ObjectTypeError),

    ItemPathFail(ItemPathError),
}

impl From<ItemPathError> for DefGenericError {
    fn from(err: ItemPathError) -> DefGenericError {
        DefGenericError::ItemPathFail(err)
    }
}

impl IsWrongStart for DefGenericError {
    fn is_wrong_start(&self) -> bool {
        matches!(
            self,
            DefGenericError::ItemPathFail(ItemPathError::MissingName)
        )
    }
}

impl WrongStart for DefGenericError {
    fn wrong_start(_: HeadLex) -> Self {
        DefGenericError::ItemPathFail(ItemPathError::MissingName)
    }
}

impl From<ObjectTypeError> for DefGenericError {
    fn from(err: ObjectTypeError) -> DefGenericError {
        DefGenericError::ObjectTypeFail(err)
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

impl Parse for DefGeneric {
    type Error = DefGenericError;

    fn parse(tokens: &mut LexIter) -> Result<DefGeneric, DefGenericError> {
        use DefGenericError as E;
        use DefGenericError::*;
        use HeadLex::*;

        tokens.guard(|iter| {
            let path = ItemPath::parse(iter)?;

            match path.into_single_item() {
                Err(path) => Ok(DefGeneric::Path { path }),
                Ok(name) => {
                    if let Some(assign_t) = Assign.spanprobe(iter) {
                        // Either const or type assignment.

                        // Try to parse const assignment.
                        if let Some(value) = Literal::spanprobe::<E>(iter) {
                            Ok(DefGeneric::AssignConstNamed {
                                assign_t,
                                name,
                                value: value?,
                            })
                        } else {
                            // Try to parse type assignment.
                            ObjectType::parse_option(iter).map_inner_into(
                                |ty| DefGeneric::AssignTypeNamed { assign_t, name, ty },
                                InvalidEnd,
                            )
                        }
                    } else {
                        Ok(DefGeneric::Path {
                            path: ItemPath::single(name),
                        })
                    }
                }
            }
        })
    }
}

impl Parse for Vec<DefGeneric> {
    type Error = DefGenericError;

    fn parse(tokens: &mut LexIter) -> Result<Vec<DefGeneric>, DefGenericError> {
        use DefGenericError as E;
        use HeadLex::*;

        tokens.guard(|iter| {
            OpenAngle.expect_start::<E>(iter)?;
            let generics: SmallVec<[_; 8]> = HeadLex::comma_smallvec(iter, DefGeneric::parse)?;
            CloseAngle.expect(iter, E::UnexpectedEnd)?;
            Ok(generics.into_vec())
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn i(input: &str) -> IdentName {
        IdentName::try_from(input).unwrap()
    }

    #[test]
    fn test_parse_item_path_single() {
        let input = "MyType";
        let lex = HeadLex::lexer(input);
        let mut iter = lex.spanned();

        let path = ItemPath::parse(&mut iter).unwrap();
        assert_eq!(path.items.len(), 1);
        assert_eq!(*path.items[0], i("MyType"));

        assert!(path.into_single_item().is_ok());
    }

    #[test]
    fn test_parse_item_path_many() {
        let input = "MyType::Inner::Inner2";
        let lex = HeadLex::lexer(input);
        let mut iter = lex.spanned();

        let path = ItemPath::parse(&mut iter).unwrap();
        assert_eq!(path.items.len(), 3);
        assert_eq!(*path.items[0], i("MyType"));
        assert_eq!(*path.items[1], i("Inner"));
        assert_eq!(*path.items[2], i("Inner2"));
    }

    #[test]
    fn test_parse_item_path_error() {
        let input = "MyType::";
        let lex = HeadLex::lexer(input);
        let mut iter = lex.spanned();

        let path = ItemPath::parse(&mut iter);
        assert!(path.is_err());
    }

    #[test]
    fn test_parse_impl_simple() {
        let input = "impl MyType";
        let lex = HeadLex::lexer(input);
        let mut iter = lex.spanned();

        let imp = Impl::parse(&mut iter).unwrap();
        let ObjectType::Concrete { name, generics } = imp.impl_for else {
            panic!("expected ObjectType::Concrete, got {:?}", imp.impl_for);
        };
        assert_eq!(
            name.into_inner().into_single_item().unwrap().into_inner(),
            i("MyType")
        );
        assert!(generics.is_empty());
        assert_eq!(imp.kind, ImplKind::Simple);
    }

    #[test]
    fn test_parse_impl_trait() {
        let input = "impl MyTrait for MyType";
        let lex = HeadLex::lexer(input);
        let mut iter = lex.spanned();

        let imp = Impl::parse(&mut iter).unwrap();
        println!("{imp:#?}");

        let ObjectType::Concrete { name, generics } = imp.impl_for else {
            panic!("expected ObjectType::Concrete, got {:?}", imp.impl_for);
        };

        assert_eq!(
            name.into_inner().into_single_item().unwrap().into_inner(),
            i("MyType")
        );
        assert!(generics.is_empty());

        match imp.kind {
            ImplKind::Trait { name, generics, .. } => {
                assert_eq!(name.items.len(), 1);
                assert_eq!(*name.items[0], i("MyTrait"));
                assert!(generics.is_empty());
            }
            _ => panic!("expected ImplKind::Trait, got {:?}", imp.kind),
        }
    }

    #[test]
    fn test_parse_generics() {
        let input = "impl<T, U> MyTrait<T> for MyType<U>";
        let lex = HeadLex::lexer(input);
        let mut iter = lex.spanned();

        let imp = Impl::parse(&mut iter).unwrap();
        let ObjectType::Concrete { name, generics } = imp.impl_for else {
            panic!("expected ObjectType::Concrete, got {:?}", imp.impl_for);
        };

        assert_eq!(
            name.into_inner().into_single_item().unwrap().into_inner(),
            i("MyType")
        );
        assert_eq!(generics.len(), 1);
        assert_eq!(*generics[0].name, i("U"));

        match imp.kind {
            ImplKind::Trait { name, generics, .. } => {
                assert_eq!(name.items.len(), 1);
                assert_eq!(*name.items[0], i("MyTrait"));
                assert_eq!(generics.len(), 1);
                assert_eq!(*generics[0].name, i("T"));
            }
            _ => panic!("expected ImplKind::Trait, got {:?}", imp.kind),
        }

        let generics = imp.generics;
        assert_eq!(generics.len(), 2);
        assert_eq!(*generics[0].name, i("T"));
        assert_eq!(*generics[1].name, i("U"));
    }

    #[test]
    fn generics_parser() {
        let input = "<T, U>";
        let lex = HeadLex::lexer(input);
        let mut iter = lex.spanned();

        let generics = Vec::<DeclGeneric>::parse(&mut iter).unwrap();
        assert_eq!(generics.len(), 2);
        assert_eq!(*generics[0].name, i("T"));
        assert_eq!(*generics[1].name, i("U"));
    }

    #[test]
    fn generics_def_parser() {
        let input = "<T = 1, U = String, V = some::Item, W>";
        let lex = HeadLex::lexer(input);
        let mut iter = lex.spanned();

        let generics = Vec::<DefGeneric>::parse(&mut iter).unwrap();
        assert_eq!(generics.len(), 4);

        match &generics[0] {
            DefGeneric::AssignConstNamed { name, value, .. } => {
                assert_eq!(**name, i("T"));
                assert_eq!(**value, Literal::Num(Number { neg: false, int: 1 }));
            }
            _ => panic!(
                "expected DefGeneric::AssignConstNamed, got {:?}",
                generics[0]
            ),
        }

        match &generics[1] {
            DefGeneric::AssignTypeNamed { name, ty, .. } => {
                assert_eq!(**name, i("U"));
                assert_eq!(
                    ty,
                    &ObjectType::Concrete {
                        name: Span::NONE.with(ItemPath::single(Span::NONE.with(i("String")))),
                        generics: Span::NONE.with(vec![]),
                    }
                );
            }
            _ => panic!(
                "expected DefGeneric::AssignTypeNamed, got {:?}",
                generics[1]
            ),
        }

        match &generics[2] {
            DefGeneric::AssignTypeNamed { name, ty, .. } => {
                assert_eq!(**name, i("V"));
                assert_eq!(
                    ty,
                    &ObjectType::Concrete {
                        name: Span::NONE.with(ItemPath::from(
                            [Span::NONE.with(i("some")), Span::NONE.with(i("Item"))].as_ref()
                        )),
                        generics: Span::NONE.with(vec![]),
                    }
                );
            }
            _ => panic!(
                "expected DefGeneric::AssignTypeNamed, got {:?}",
                generics[2]
            ),
        }

        match &generics[3] {
            DefGeneric::Path { path } => {
                assert_eq!(path.items.len(), 1);
                assert_eq!(*path.items[0], i("W"));
            }
            _ => panic!("expected DefGeneric::Path, got {:?}", generics[3]),
        }
    }

    #[test]
    fn literal() {
        let input = "\"hello\"";
        let lex = HeadLex::lexer(input);
        let mut iter = lex.spanned();

        let lit = Literal::expect(&mut iter, HeadError::UnexpectedEnd).unwrap();
        assert_eq!(lit.into_inner(), Literal::Str("hello".to_string()));

        let input = "123";
        let lex = HeadLex::lexer(input);
        let mut iter = lex.spanned();

        let lit = Literal::expect(&mut iter, HeadError::UnexpectedEnd).unwrap();
        assert_eq!(
            lit.into_inner(),
            Literal::Num(Number {
                neg: false,
                int: 123
            })
        );
    }

    #[test]
    fn lit_num_negative() {
        let input = "-123";
        let lex = HeadLex::lexer(input);
        let mut iter = lex.spanned();

        let lit = Literal::expect(&mut iter, HeadError::UnexpectedEnd).unwrap();
        assert_eq!(
            lit.into_inner(),
            Literal::Num(Number {
                neg: true,
                int: 123
            })
        );
    }

    #[test]
    fn lit_str_escaped() {
        let input = r#""hello \"world\"""#;
        let lex = HeadLex::lexer(input);
        let mut iter = lex.spanned();

        let lit = Literal::expect(&mut iter, HeadError::UnexpectedEnd).unwrap();
        assert_eq!(
            lit.into_inner(),
            Literal::Str("hello \"world\"".to_string())
        );
    }

    #[test]
    fn parse_as_ext() {
        let input = "impl MyType as MyTypeExt";
        let lex = HeadLex::lexer(input);
        let mut iter = lex.spanned();

        let imp = Impl::parse(&mut iter).unwrap();
        let ObjectType::Concrete { name, generics } = imp.impl_for else {
            panic!("expected ObjectType::Concrete, got {:?}", imp.impl_for);
        };
        assert_eq!(
            name.into_inner().into_single_item().unwrap().into_inner(),
            i("MyType")
        );
        assert!(generics.is_empty());
        match imp.kind {
            ImplKind::AsExt { ext, .. } => {
                assert_eq!(ext.into_inner(), i("MyTypeExt"));
            }
            _ => panic!("expected ImplKind::AsExt, got {:?}", imp.kind),
        }
    }

    #[test]
    fn fn_trait() {
        let input = "fn<T>(arg1, arg2) -> T";
        let lex = HeadLex::lexer(input);
        let mut iter = lex.spanned();

        let ty = ObjectType::parse(&mut iter).unwrap();
        match ty {
            ObjectType::Func {
                generics,
                args,
                ret,
                ..
            } => {
                assert_eq!(generics.len(), 1);
                assert_eq!(*generics[0].name, i("T"));
                assert_eq!(args.len(), 2);
                assert_eq!(ret.len(), 1);
                assert_eq!(
                    ret[0],
                    ObjectType::Concrete {
                        name: Span::NONE.with(ItemPath::single(Span::NONE.with(i("T")))),
                        generics: Span::NONE.with(vec![]),
                    }
                );
            }
            _ => panic!("expected ObjectType::Func, got {:?}", ty),
        }
    }

    #[test]
    fn fn_trait_return_tuple() {
        let input = "fn() -> (T, U)";
        let lex = HeadLex::lexer(input);
        let mut iter = lex.spanned();

        let ty = ObjectType::parse(&mut iter).unwrap();
        match ty {
            ObjectType::Func {
                generics,
                args,
                ret,
                ..
            } => {
                assert!(generics.is_empty());
                assert!(args.is_empty());
                assert_eq!(ret.len(), 2);
                assert_eq!(
                    ret[0],
                    ObjectType::Concrete {
                        name: Span::NONE.with(ItemPath::single(Span::NONE.with(i("T")))),
                        generics: Span::NONE.with(vec![]),
                    }
                );
                assert_eq!(
                    ret[1],
                    ObjectType::Concrete {
                        name: Span::NONE.with(ItemPath::single(Span::NONE.with(i("U")))),
                        generics: Span::NONE.with(vec![]),
                    }
                );
            }
            _ => panic!("expected ObjectType::Func, got {:?}", ty),
        }
    }
}
