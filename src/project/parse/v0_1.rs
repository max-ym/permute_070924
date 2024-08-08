#[derive(Debug, Clone, serde::Deserialize)]
pub struct Header {
    pub version: Version,
    pub ty: FileType,
    pub uses: Vec<Use>,
}

#[derive(Debug, Clone)]
struct Version;

impl<'de> serde::Deserialize<'de> for Version {
    fn deserialize<D>(deserializer: D) -> Result<Version, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        // Please review, and improve handling of the new versions when they come.
        // This anyway won't compile without human review due to
        // exhaustive match check 😏

        let version = super::Version::deserialize(deserializer);
        match version {
            Ok(super::Version::Permute0_1) => Ok(Version),
            Err(e) => Err(e),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Use {
    pub item: ItemPath,
    pub use_as_or_wildcard: Option<UseAsOrWildcard>,
}

#[derive(Debug, Clone)]
pub enum UseAsOrWildcard {
    UseAs(ItemName),
    Wildcard,
}

#[derive(Debug, Clone)]
pub struct ItemPath {
    pub path: Vec<ItemName>,
}

/// Item name, which is a string that can be used to reference an item in the project.
/// The items are: modules, types, functions, variables, etc.
/// The item name is a string that can contain only alphanumeric characters and underscores.
/// The item name cannot be empty, and cannot be just an underscore.
#[derive(Debug, Clone)]
pub struct ItemName(String);

#[derive(Debug, Clone)]
pub enum InvalidItemName {
    Empty,
    Invalid(String),
}

impl Into<String> for ItemName {
    fn into(self) -> String {
        self.0
    }
}

impl std::fmt::Display for ItemName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl TryFrom<String> for ItemName {
    type Error = InvalidItemName;

    fn try_from(s: String) -> Result<Self, Self::Error> {
        if s.is_empty() {
            Err(InvalidItemName::Empty)
        } else if s == "_" {
            Err(InvalidItemName::Invalid(s))
        } else if s.chars().all(|c| c.is_alphanumeric() || c == '_') {
            Ok(ItemName(s))
        } else {
            Err(InvalidItemName::Invalid(s))
        }
    }
}

impl std::ops::Deref for ItemName {
    type Target = str;

    fn deref(&self) -> &str {
        &self.0
    }
}
