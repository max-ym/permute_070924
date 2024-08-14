use std::collections::HashMap;

use super::*;

pub type BindName = IdentName;

#[derive(Debug, Deserialize)]
pub struct Main {
    pub name: String,
    pub cfg: HashMap<BindName, Binding>,
}

/// A binding is a key-value pair.
/// In YAML file it is represented as a map with a string representing the key and then a value,
/// which can be a string, list, or map.
#[derive(Debug, Deserialize)]
#[serde(transparent)]
pub struct Binding(HashMap<BindName, BindingValue>);

#[derive(Debug, Deserialize)]
#[serde(untagged)]
pub enum BindingValue {
    /// Value is a string.
    String(String),

    /// Value is a map of binding values.
    Map(HashMap<BindName, BindingValue>),

    /// Value is a list of binding values.
    List(Vec<BindingValue>),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample_file() {
        crate::init_log();

        let file = crate::Sample1::Main.into();
        let main: Main = serde_yml::from_str(file).unwrap();
        println!("{main:#?}");
    }
}
