use log::trace;
use smallvec::SmallVec;

pub struct Pretty<'yaml> {
    yaml: &'yaml str,
}

impl<'yaml> Pretty<'yaml> {
    pub fn new(yaml: &'yaml str) -> Self {
        Self { yaml }
    }

    pub fn explain_builder(&self) -> ExplainBuilder<'yaml> {
        ExplainBuilder {
            yaml: self.yaml,
            error_context: None,
            explain_contexts: Default::default(),
        }
    }
}

pub struct ExplainBuilder<'yaml> {
    yaml: &'yaml str,
    error_context: Option<Context>,
    explain_contexts: SmallVec<[Context; 8]>,
}

impl<'yaml> ExplainBuilder<'yaml> {
    /// Add a context with the error message.
    pub fn push_context(&mut self, context: Context) -> &mut Self {
        self.explain_contexts.push(context);
        self
    }

    /// Add an error context to the error message.
    pub fn error(&mut self, context: Context) -> &mut Self {
        self.error_context = Some(context);
        self
    }

    /// Build pretty explanation from the provided contexts.
    pub fn build(self) -> Result<PrettyError, ExplainBuildError> {
        todo!("Implement building the explanation")
    }
}

#[derive(Debug, Clone)]
pub struct PrettyError(String);

impl std::fmt::Display for PrettyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::ops::Deref for PrettyError {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::convert::AsRef<str> for PrettyError {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ExplainBuildError {
    #[error("Error context is missing")]
    MissingErrorContext,
}

pub struct Context {
    important_start: Span,
    important_end: Span,

    additional_start: Span,
    additional_end: Span,

    message: String,
}

#[derive(Debug, Default)]
pub struct ContextBuilder {
    important_start: Option<Span>,
    important_end: Option<Span>,

    additional_start: Option<Span>,
    additional_end: Option<Span>,

    message: Option<String>,
}

impl ContextBuilder {
    pub fn new() -> Self {
        Self {
            important_start: None,
            important_end: None,
            additional_start: None,
            additional_end: None,
            message: None,
        }
    }

    pub fn important_start(&mut self, span: Span) -> &mut Self {
        self.important_start = Some(span);
        self
    }

    pub fn important_end(&mut self, span: Span) -> &mut Self {
        self.important_end = Some(span);
        self
    }

    pub fn additional_start(&mut self, span: Span) -> &mut Self {
        self.additional_start = Some(span);
        self
    }

    pub fn additional_end(&mut self, span: Span) -> &mut Self {
        self.additional_end = Some(span);
        self
    }

    pub fn message(&mut self, message: String) -> &mut Self {
        self.message = Some(message);
        self
    }

    pub fn build(self) -> Result<Context, ContextBuildError> {
        trace!("Building context");

        trace!("Check if important start and end are present");
        let important_start = self
            .important_start
            .ok_or(ContextBuildError::MissingImportantStart)?;
        let important_end = self
            .important_end
            .ok_or(ContextBuildError::MissingImportantEnd)?;

        trace!("Check order of important start and end");
        if important_start.start > important_end.start {
            return Err(ContextBuildError::ImportantStartAfterEnd);
        }

        let additional_start = self.additional_start.unwrap_or(important_start);
        let additional_end = self.additional_end.unwrap_or(important_end);

        trace!("Check order of additional start and end");
        if additional_start.start > additional_end.start {
            return Err(ContextBuildError::AdditionalStartAfterEnd);
        }

        trace!("Check additional and important spans overlaps");
        let important_combine = important_start.combine(&important_end);
        let additional_combine = additional_start.combine(&additional_end);
        if !important_combine.overlaps(&additional_combine) {
            return Err(ContextBuildError::AdditionalNotOverlapsImportant);
        }

        trace!("Check if message is present");
        if let Some(message) = self.message {
            trace!("Context is built successfully");
            Ok(Context {
                important_start,
                important_end,
                additional_start,
                additional_end,
                message,
            })
        } else {
            Err(ContextBuildError::MissingMessage)
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ContextBuildError {
    #[error("Missing important start")]
    MissingImportantStart,

    #[error("Missing important end")]
    MissingImportantEnd,

    #[error("Important start is after the end")]
    ImportantStartAfterEnd,

    #[error("Missing message")]
    MissingMessage,

    #[error("Additional start is after the end")]
    AdditionalStartAfterEnd,

    #[error("Additional context span does not overlap with important context span")]
    AdditionalNotOverlapsImportant,
}

/// Position in the source text. 32 bits should be enough for everyone.
type Pos = u32;

#[derive(Debug, Clone, Copy)]
pub struct Span {
    start: Pos,
    end: Pos,
}

#[derive(Debug, Clone, Copy, thiserror::Error)]
#[error("Start of the span is after the end")]
pub struct InvalidSpan;

impl Span {
    pub fn new(start: Pos, end: Pos) -> Result<Self, InvalidSpan> {
        if start > end {
            return Err(InvalidSpan);
        }
        Ok(Self { start, end })
    }

    /// Check if this span overlaps with another span in any part, either partially or fully.
    pub fn overlaps(&self, other: &Self) -> bool {
        self.start < other.end && self.end > other.start
            || other.start < self.end && other.end > self.start
    }

    /// Combine two spans into one, that covers both of them.
    /// Return `None` if the spans do not overlap.
    pub fn overlap(&self, other: &Self) -> Option<Self> {
        self.overlaps(other).then(|| {
            let start = self.start.min(other.start);
            let end = self.end.max(other.end);
            Self { start, end }
        })
    }

    /// Combine two spans into one, taking the smallest start and the largest end.
    pub fn combine(&self, other: &Self) -> Self {
        let start = self.start.min(other.start);
        let end = self.end.max(other.end);
        Self { start, end }
    }
}
