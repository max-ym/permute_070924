use smallvec::SmallVec;

use crate::{
    domain::{self, ItemName},
    expr::Expression,
};

#[derive(Debug)]
pub struct Ctx {
    sources: Vec<domain::Source>,
    sinks: Vec<Sink>,
    types: Vec<CustomType>,
    fns: Vec<CustomFn>,
}

#[derive(Debug)]
pub struct Sink {
    path: Path,
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

    /// A function item.
    Function(FnItem),
}

#[derive(Debug)]
pub enum FnItem {
    /// Path to a function.
    Path(Path),

    /// Inline function.
    Inline(InlineFn),
}

#[derive(Debug)]
pub struct Path {
    path: SmallVec<[ItemName; 3]>,
}

#[derive(Debug)]
pub struct InlineFn {
    args: SmallVec<[FnArg; 1]>,
    output: DataTypePath,
    body: Expression,
}

#[derive(Debug)]
pub struct DataTypePath(Path);

#[derive(Debug)]
pub struct FnArg {
    name: ItemName,
    ty: DataTypePath,
}

#[derive(Debug)]
pub struct CustomType {
    name: Path,
    inner: domain::CustomType,
    checks: Vec<Expression>,
}

#[derive(Debug)]
pub struct CustomFn {
    name: ItemName,
    impl_on: Option<Path>,
    args: Vec<FnArg>,
    output: DataTypePath,
    body: Expression,
}
