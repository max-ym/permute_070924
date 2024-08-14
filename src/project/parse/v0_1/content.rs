use serde::Deserialize;

use super::{IdentName, ItemPath};

/// "Main" file type parsing.
pub mod main;

/// "Transform" file type parsing.
pub mod transform;


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
