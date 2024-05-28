use thiserror::Error;

#[derive(Debug)]
pub struct Expression {}

impl TryFrom<&str> for Expression {
    type Error = Vec<TryFromStrError>;

    /// Tries to parse the expression from the provided string.
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        todo!()
    }
}

#[derive(Debug, Error)]
pub enum TryFromStrError {

}

impl Expression {
    /// Formats the expression as a human-readable string (code).
    pub fn to_pretty_string(&self) -> String {
        todo!("Implement to_pretty_string for Expression")
    }
}
