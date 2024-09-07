
/// Position in the source text. 32 bits should be enough for everyone.
type Pos = u32;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    start: Pos,
    end: Pos,
}

#[derive(Debug, Clone, Copy, thiserror::Error)]
#[error("Start of the span is after the end")]
pub struct InvalidSpan;

#[derive(Debug)]
pub struct Spanned<T> {
    value: T,
    span: Span,
}

impl<T> Spanned<T> {
    pub fn span(&self) -> Span {
        self.span
    }

    pub fn split(self) -> (T, Span) {
        (self.value, self.span)
    }

    pub fn into_inner(self) -> T {
        self.value
    }
}

impl<T> std::ops::Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> std::ops::DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl<T> std::cmp::PartialEq for Spanned<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<T> std::cmp::Eq for Spanned<T> where T: Eq {}

impl<T> Clone for Spanned<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            span: self.span,
        }
    }
}

impl<T> Default for Spanned<T>
where
    T: Default,
{
    fn default() -> Self {
        Self {
            value: Default::default(),
            span: Span { start: 0, end: 0 },
        }
    }
}

impl Span {
    pub const NONE: Self = Self { start: 0, end: 0 };

    pub fn new(start: Pos, end: Pos) -> Result<Self, InvalidSpan> {
        if start > end {
            return Err(InvalidSpan);
        }
        Ok(Self { start, end })
    }

    pub fn start(&self) -> Pos {
        self.start
    }

    pub fn end(&self) -> Pos {
        self.end
    }

    /// Check if this span overlaps with another span in any part, either partially or fully.
    pub fn overlaps(&self, other: &Self) -> bool {
        self.start < other.end && self.end > other.start
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

    pub fn with<T>(self, value: T) -> Spanned<T> {
        Spanned { value, span: self }
    }

    /// Check if the span does not point to anything.
    pub fn is_none(&self) -> bool {
        self.start == 0 && self.end == 0
    }
}

impl From<std::ops::Range<usize>> for Span {
    fn from(range: std::ops::Range<usize>) -> Self {
        Self {
            start: range.start as Pos,
            end: range.end as Pos,
        }
    }
}

/// A marker in the source text, containing the index, column, and line number.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Marker {
    idx: Pos,
    col: Pos,
    line: Pos,
}

impl Marker {
    pub fn new(idx: Pos, col: Pos, line: Pos) -> Self {
        Self { idx, col, line }
    }

    pub fn idx(&self) -> Pos {
        self.idx
    }

    pub fn col(&self) -> Pos {
        self.col
    }

    pub fn line(&self) -> Pos {
        self.line
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// A span between two markers.
pub struct MarkSpan {
    start: Marker,
    end: Marker,
}

impl MarkSpan {
    pub fn new(start: Marker, end: Marker) -> Self {
        Self { start, end }
    }

    pub fn start(&self) -> Marker {
        self.start
    }

    pub fn end(&self) -> Marker {
        self.end
    }
}

pub struct MarkSpanned<T> {
    value: T,
    span: MarkSpan,
}

impl<T> MarkSpanned<T> {
    pub fn span(&self) -> MarkSpan {
        self.span
    }

    pub fn split(self) -> (T, MarkSpan) {
        (self.value, self.span)
    }

    pub fn into_inner(self) -> T {
        self.value
    }
}

impl<T> std::ops::Deref for MarkSpanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> std::ops::DerefMut for MarkSpanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl<T> std::cmp::PartialEq for MarkSpanned<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<T> std::cmp::Eq for MarkSpanned<T> where T: Eq {}

impl<T> Clone for MarkSpanned<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            span: self.span,
        }
    }
}

impl<T> Default for MarkSpanned<T>
where
    T: Default,
{
    fn default() -> Self {
        Self {
            value: Default::default(),
            span: MarkSpan {
                start: Marker::new(0, 0, 0),
                end: Marker::new(0, 0, 0),
            },
        }
    }
}
