use crate::span::*;

use super::{IdentName, ItemPath};

/// "Main" file type parsing.
pub mod main;

/// "Logic" file type parsing.
pub mod logic;


/// Type system expressions. This parses the lines defining implementations of the types,
/// traits, function headers, and other such expressions.
/// 
/// # Example
/// Examples of expressions being parsed here:
/// ```yaml
///    impl MyType:
/// ```
/// 
/// ```yaml
///     fn my_function():
/// ```
/// 
/// ```yaml
///    trait MyTrait:
/// ```
/// 
/// ```yaml
///   impl permute::EndlessIterator<Item = Integer> for RowSequence:
/// ```
pub mod type_system_expr;

/// Any YAML file representation. It later is used to locate specific fields 
/// expected in each file type.
pub struct ParsedYamlFile(Vec<(MarkSpan, yaml_rust2::Yaml)>);

mod yaml_loader;
