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
//! 
//! # YAML
//! ## File Kinds
//! There are several kinds of files that can be used in the framework:
//! - transform
//! - sink
//! - source
//! - feeder
//! - main
//! 
//! ### Main File
//! The main file is the entry point of the project. It describes the project, its name,
//! and defines the purpose of the program by creating a pipeline of data transformations.
//! Pipeline is complete when there is a source and a sink defined in the main file.
//! There can be several sources and sinks defined with complex flows of data.
//! 
//! ### Source File
//! Source file describes the data source. It can be a file, a database, a service, or any other
//! source of data. It describes the format of the data, and allows to define the schema
//! of the data, and also to validate the data. Source itself then is implemented externally
//! to the framework, and the framework only uses this definition as a contract (interface).
//! It does validate the data against the schema on runtime as to detect any errors in the
//! implementation.
//! 
//! ## Functions & Types
//! It is possible to define functions in the YAML file, that can be used to calculate values
//! or transform the data. File types where functions or types can be declared or defined:
//! - transform
//! - sink
//! - source
//! - feeder
//! 
//! ### Functional Code
//! #### Loops Nonexistent!
//! The language of function code is similar to Rust. However, it is not possible to
//! use any kind of loops directly. Though loop-like functionality can be defined
//! in external code. It was decided to avoid loops as to make the code more predictable
//! and linear by time complexity. Thus it is not possible to make an infinite loop
//! or a loop that will take a long time to execute in the language itself. Though it also
//! assumes that backend implementation of external functions is sane as not to allow to
//! do any harmful or infinite operations.
//! 
//! Recursion is also forbidden in the language as compiler will statically analyze the
//! execution paths and would reject the code if it detects a loop of function calls,
//! either direct from within the same function, or indirect through the chain
//! of function calls. It would not be able to detect a loop if it is defined in the
//! external code, so it is up to the developer to ensure that the code is safe on the
//! backend side.
//! 
//! #### External Code
//! Functions and types can be declared in the YAML file, but the actual implementation
//! can be delegated to the external code. This allows to use any kind of code, including
//! loops, recursion, and other constructs that are not allowed in the YAML file.
//! It also allows to use any library. It allows to write backend code that is
//! not possible to implement in YAML or otherwise is unwanted to be exposed to the
//! user.
//! 
//! #### Borrow & Copy Semantics
//! All values carried by the functions as arguments are borrowed Copy-on-Write. This means that
//! the value is copied only when modification on it is attempted.
//! By default, it is a reference,
//! though it is not directly specifiable in the code as there is no way to
//! define Rust-y references (or pointers). If the argument is declared as mutable,
//! then the value is modified in place and the caller would see the modified value after
//! the function's execution (aka mutable reference). All values passed to types (structures)
//! are copied and then the structure is the owner of the value with no connection to 
//! the original source value. It is not possible to make a structure to borrow the value.
//! 
//! If the function code creates a new binding to the argument of the function, then the
//! value is copied. It is copied in both cases, whether the argument is mutable or not.
//! Then the original value is still accessible (unless the name is shadowed). Unlike in Rust.
//! 
//! It was decided to use this approach to avoid the complexity of the ownership system as it
//! seemed unnecessary for the framework. We won't need to describe complex inter-object
//! references for the data processing and transformations.

// To suppress warnings during early development:
#![allow(dead_code)]

/// Module to register expected fields in the YAML file, and also describe the provided
/// types and formats, so that framework can validate correctness and compatibility.
pub mod domain;

/// Module that reads the YAML file and converts it to the internal representation
/// that can be used by the framework to perform analysis.
pub mod project;

/// Module to allow writing expressions in the YAML file, that can be used to
/// calculate values or transform the data.
pub mod expr;

/// Module that contains the contract, which is similar to [crate::domain::Domain] as it contains
/// all items, types, and other information
/// from YAML files. This is used to validate the configuration against
/// actual [crate::domain::Domain].
pub mod contract;

/// Module to aid user in understanding errors and providing hints on how to fix them.
pub mod error_expl;

#[cfg(test)]
pub fn init_log() {
    use log::*;

    flexi_logger::Logger::with(LevelFilter::Trace)
        .format(format)
        .start()
        .unwrap();

    fn format(
        write: &mut dyn std::io::Write,
        _: &mut flexi_logger::DeferredNow,
        record: &Record,
    ) -> std::io::Result<()> {
        write.write_all(
            format!(
                "[{} {}:{}] {} - {}",
                record.level(),
                record.file().unwrap_or_default(),
                record.line().unwrap_or_default(),
                record.module_path().unwrap_or_default(),
                record.args()
            )
            .as_bytes(),
        )
    }
}

/// Core Permute YAML file. This file is implicitly included into every project and describes
/// all base types in the framework for all programs. This file also can be referenced
/// in tests to validate the correctness of the framework. 
pub fn core_permute_yaml() -> &'static str {
    include_str!("core/permute.yaml")
}

/// Reference of test files from the sample1 example project.
#[cfg(test)]
pub enum Sample1 {
    Main,
    Csv,
    CsvFeed,
    CustomStruct,
    CustomStructUse,
    EmploymentRecord,
    Monetary,
    Transform,
}

#[cfg(test)]
impl Into<&'static str> for Sample1 {
    fn into(self) -> &'static str {
        use Sample1::*;
        match self {
            Main => include_str!("../examples/sample1/main.yaml"),
            Csv => include_str!("../examples/sample1/Csv.yaml"),
            CsvFeed => include_str!("../examples/sample1/CsvFeed.yaml"),
            CustomStruct => include_str!("../examples/sample1/custom_struct.yaml"),
            CustomStructUse => include_str!("../examples/sample1/custom_struct_use.yaml"),
            EmploymentRecord => include_str!("../examples/sample1/EmploymentRecord.yaml"),
            Monetary => include_str!("../examples/sample1/monetary.yaml"),
            Transform => include_str!("../examples/sample1/transform.yaml"),
        }
    }
}
