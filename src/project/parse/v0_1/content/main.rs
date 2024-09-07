use std::collections::HashMap;

use super::*;

pub type BindName = IdentName;

#[derive(Debug)]
pub struct Main {
    /// The name of the project.
    name: Spanned<String>,

    /// Span of the key "name".
    name_t: Span,

    /// Configuration of the project.
    cfg: HashMap<Spanned<BindName>, Spanned<Binding>>,
}

/// A binding is a key-value pair.
/// In YAML file it is represented as a map with a string representing the key and then a value,
/// which can be a string, list, or map.
#[derive(Debug)]
pub struct Binding(HashMap<Spanned<BindName>, Spanned<BindingValue>>);

#[derive(Debug)]
pub enum BindingValue {
    /// Value is a string.
    String(String),

    /// Value is a map of binding values.
    Map(HashMap<Spanned<BindName>, Spanned<BindingValue>>),

    /// Value is a list of binding values.
    List(Vec<Spanned<BindingValue>>),
}

impl BindingValue {
    
}

#[cfg(test)]
mod tests {
    use super::*;
}
