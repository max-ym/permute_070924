use lazy_regex::regex_is_match;
use thiserror::Error;

use crate::expr;

/// Domain is a struct that holds the information about all the registered
/// components in the system. It is the main struct that holds all the
/// information about the components, their types, formats, and other
/// properties.
///
/// This information is not loaded from the YAML files, but is defined
/// by the implementation that uses Permute framework.
/// The Domain struct is used to validate the correctness of the YAML
/// files, and to provide the information about the components to the
/// other parts of Permute framework.
#[derive(Default, Debug)]
pub struct Domain {
    sinks: Vec<Sink>,
    sources: Vec<Source>,
    types: Vec<CustomType>,
    fns: Vec<CustomFn>,
}

impl Domain {
    pub fn sink(&self, name: &str) -> Option<&Sink> {
        self.sinks.iter().find(|sink| sink.name == name)
    }

    pub fn source(&self, name: &str) -> Option<&Source> {
        self.sources.iter().find(|source| source.name == name)
    }

    pub fn custom_type(&self, name: &str) -> Option<&CustomType> {
        self.types.iter().find(|custom_type| custom_type.name == name)
    }

    pub fn custom_fn(&self, name: &str) -> Option<&CustomFn> {
        self.fns.iter().find(|custom_fn| custom_fn.name == name)
    }
}

#[derive(Debug)]
pub struct DomainBuilder {
    sinks: Vec<Sink>,
    sources: Vec<Source>,
    types: Vec<CustomType>,
    fns: Vec<CustomFn>,
}

impl DomainBuilder {
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            sinks: Vec::with_capacity(capacity),
            sources: Vec::with_capacity(capacity),
            types: Vec::with_capacity(capacity),
            fns: Vec::with_capacity(capacity),
        }
    }

    pub fn add_sink(&mut self, sink: Sink) {
        self.sinks.push(sink);
    }

    pub fn add_source(&mut self, source: Source) {
        self.sources.push(source);
    }

    pub fn add_type(&mut self, custom_type: CustomType) {
        self.types.push(custom_type);
    }

    pub fn add_fn(&mut self, custom_fn: CustomFn) {
        self.fns.push(custom_fn);
    }

    /// Validate all the items in the domain and build the Domain struct.
    /// This method will return the Domain struct if all the items are valid,
    /// or a list of errors if there are any issues with the items.
    pub fn build(self) -> Result<Domain, Vec<DomainBuilderError>> {
        todo!()
    }
}

#[derive(Debug, Error)]
pub enum DomainBuilderError {
    #[error(
        "Duplicated items found in the domain: {}",
        .0.iter().map(|item| item.name()).collect::<Vec<_>>().join(", ")
    )]
    DuplicatedItems(Vec<Item>),

    #[error(
        "Sink default expression `{default}` cannot be cast into the sink param type: {ty}",
        ty = .ty.name,
        default = .default.to_pretty_string(),
    )]
    SinkTypeDefaultMismatch { ty: DataType, default: expr::Expression },

    #[error(
        "Data type constant default `{default}` cannot be cast into the type: {ty}",
        ty = .ty.name,
        default = .default.to_pretty_string(),
    )]
    DataTypeConstDefaultMismatch { ty: DataType, default: expr::Expression },
}

#[derive(Debug)]
pub enum Item {
    Sink(Sink),
    Source(Source),
    Type(CustomType),
}

impl Item {
    pub fn name(&self) -> &str {
        match self {
            Item::Sink(sink) => &sink.name,
            Item::Source(source) => &source.name,
            Item::Type(custom_type) => &custom_type.name,
        }
    }
}

#[derive(Debug)]
pub struct Sink {
    pub name: ItemName,
    pub params: Vec<SinkParam>,
}

#[derive(Debug)]
pub struct SinkParam {
    pub name: ItemName,
    pub ty: ParamType,
    pub default: Option<expr::Expression>,
    pub required: bool,
}


impl SinkParam {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn ty(&self) -> &ParamType {
        &self.ty
    }

    pub fn default(&self) -> Option<&expr::Expression> {
        self.default.as_ref()
    }

    pub fn is_required(&self) -> bool {
        self.required
    }
}

#[derive(Debug, Error)]
#[error("Invalid item name: {0}")]
pub struct InvalidItemName(String);

#[derive(Clone, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ItemName(String);

impl ItemName {
    pub fn new(name: String) -> Result<Self, InvalidItemName> {
        if regex_is_match!(r"^[a-zA-Z_][a-zA-Z0-9_]{1,32}$", &name) {
            Ok(Self(name))
        } else {
            Err(InvalidItemName(name))
        }
    }
}

impl AsRef<str> for ItemName {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for ItemName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::fmt::Debug for ItemName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::str::FromStr for ItemName {
    type Err = InvalidItemName;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        ItemName::new(s.to_string())
    }
}

impl std::borrow::Borrow<str> for ItemName {
    fn borrow(&self) -> &str {
        &self.0
    }
}

impl std::ops::Deref for ItemName {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: AsRef<str>> std::cmp::PartialEq<T> for ItemName {
    fn eq(&self, other: &T) -> bool {
        self.0 == other.as_ref()
    }
}

#[derive(Debug)]
pub enum ParamType {
    /// A map of key-value pairs.
    Map(Vec<SinkParam>),

    /// List of expressions that can be evaluated to a value.
    ListExprs,

    /// A single expression that can be evaluated to a value.
    Value,
}

#[derive(Debug)]
pub struct Source {
    pub name: ItemName,
    pub filters: Vec<SourceFilter>,
    pub columns: Vec<SourceColumn>,
}

#[derive(Debug)]
pub struct SourceFilter {
    pub name: ItemName,
    pub ty: DataType,
}

#[derive(Debug)]
pub struct DataType {
    pub name: ItemName,
    pub generics: Vec<DataType>,
    pub consts: Vec<DataTypeConst>,
}

#[derive(Debug)]
pub struct DataTypeConst {
    pub name: ItemName,
    pub ty: DataType,
    pub default: Option<expr::Expression>,
}

#[derive(Debug)]
pub struct SourceColumn {
    pub name: ItemName,
    pub ty: DataType,
}

#[derive(Debug)]
pub struct CustomType {
    pub name: ItemName,
    pub fields: Vec<CustomTypeField>,
}

#[derive(Debug)]
pub struct CustomTypeField {
    pub name: ItemName,
    pub ty: DataType,
}

#[derive(Debug)]
pub struct CustomFn {
    pub name: ItemName,
    pub self_ty: Option<DataType>,
    pub args: Vec<DataType>,
    pub ret: DataType,
}
