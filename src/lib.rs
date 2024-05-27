//! Permute is a framework and a DSL to describe data transformations.
//! It is designed to be used in a data processing pipeline, 
//! where data is transformed from one form to another.
//! Descriptory YAML files are used to describe the data, formats, transformations, validation
//! and other aspects of the data processing.
//! The decision to use YAML was made to make it possible to describe the data transformations
//! independently of the programming language used to implement the transformations, to
//! restrict the complexity of the transformations to a declarative form, to make a sandbox
//! that allows to use only specific sets of operations without access to any
//! restricted or sensitive resources. Basically, this allows to describe the data processing
//! on UI, without the need to write any code.

/// Module to register expected fields in the YAML file, and also describe the provided
/// types and formats, so that framework can validate correctness and compatibility.
pub mod domain;

/// Module to allow writing expressions in the YAML file, that can be used to
/// calculate values or transform the data.
pub mod expr;
