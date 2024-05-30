use crate::{
    domain::{self, ItemName},
    expr::Expression,
};

#[derive(Debug)]
pub struct Ctx {
    pub sources: Vec<domain::Source>,
    pub sinks: Vec<Sink>,
    pub types: Vec<CustomType>,
    pub fns: Vec<CustomFn>,
}

#[derive(Debug)]
pub struct Sink {
    name: ItemName,
    params: Vec<SinkParam>,
}

#[derive(Debug)]
pub struct SinkParam {
    name: ItemName,
    ty: ParamType,
}

#[derive(Debug)]
pub enum ParamType {
    /// A map of key-value pairs.
    Map(Vec<SinkParam>),

    /// List of expressions that can be evaluated to a value.
    ListExprs(Vec<Expression>),

    /// A single expression that can be evaluated to a value.
    Value(Expression),
}

#[derive(Debug)]
pub struct CustomType {
    name: ItemName,
    inner: domain::CustomType,
}

#[derive(Debug)]
pub struct CustomFn {}
