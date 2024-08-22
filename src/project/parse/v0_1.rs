use serde::{Deserialize, Deserializer};
use smallvec::{SmallVec, smallvec};

use crate::span::Spanned;

/// Parsing and basic validation of contents of the Permute YAML file, excluding the header.
pub mod content;

/// Header of the Permute YAML file.
/// Allows to check whether the file is a Permute file, and then
/// to extract version, type of the file, to further check if it is
/// supported.
#[derive(Debug, Clone, Deserialize)]
pub struct Header {
    /// Version "0.1" of the Permute YAML file.
    pub version: Version,

    /// Type of the file.
    #[serde(rename = "type")]
    pub ty: FileType,

    /// Optional use expressions in the file.
    #[serde(rename = "use", default)]
    pub uses: Vec<Use>,
}

/// Version of the Permute YAML file. This parser supports only version "0.1".
#[derive(Debug, Clone)]
pub struct Version;

impl<'de> Deserialize<'de> for Version {
    fn deserialize<D>(deserializer: D) -> Result<Version, D::Error>
    where
        D: Deserializer<'de>,
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

/// Use expression, e.g. `use std::io::Read;`. Without validation if it is actually correct.
/// This is parsed as plain string for further validation. And this type is just a marker
/// for the parser.
#[derive(Debug, Clone, Deserialize)]
pub struct Use(String);

impl std::borrow::Borrow<str> for Use {
    fn borrow(&self) -> &str {
        &self.0
    }
}

/// File type of Permute YAML.
///
/// # Deserialize
/// In YAML is it represented as string, e.g.
/// ```yaml
/// type: main
/// ```
/// Or it can be represented as custom type, e.g.
/// ```yaml
/// type:
///  custom: my_type
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FileType {
    Main,
    Transform,
    Feeder,
    Sink,
    Source,
    Struct,
    Custom(String),
}

impl FileType {
    pub fn name(&self) -> &'static str {
        use FileType::*;
        match self {
            Main => "main",
            Transform => "transform",
            Feeder => "feeder",
            Sink => "sink",
            Source => "source",
            Struct => "struct",
            Custom(_) => "custom",
        }
    }

    pub fn from_name(name: &str) -> Option<FileType> {
        use FileType::*;
        let variant = match name {
            "main" => Main,
            "transform" => Transform,
            "feeder" => Feeder,
            "sink" => Sink,
            "source" => Source,
            "struct" => Struct,
            "custom" => Custom(String::new()),
            _ => return None,
        };
        Some(variant)
    }
}

impl<'de> Deserialize<'de> for FileType {
    fn deserialize<D>(deserializer: D) -> Result<FileType, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Debug, Deserialize)]
        struct Custom {
            custom: String,
        }

        struct FileTypeVisitor;

        impl<'v> serde::de::Visitor<'v> for FileTypeVisitor {
            type Value = FileType;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("file type")
            }

            fn visit_str<E>(self, value: &str) -> Result<FileType, E>
            where
                E: serde::de::Error,
            {
                FileType::from_name(value).ok_or_else(|| E::custom("unknown file type"))
            }

            fn visit_map<A>(self, map: A) -> Result<FileType, A::Error>
            where
                A: serde::de::MapAccess<'v>,
            {
                let custom =
                    Custom::deserialize(serde::de::value::MapAccessDeserializer::new(map))?;
                Ok(FileType::Custom(custom.custom))
            }
        }

        deserializer.deserialize_any(FileTypeVisitor)
    }
}

/// Identifier name.
/// Alpha-numeric string, starting with a letter, can contain underscores.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Deserialize)]
#[serde(transparent)]
pub struct IdentName(String);

#[derive(Debug, PartialEq, Eq, Clone, thiserror::Error)]
pub enum IdentNameError {
    #[error("empty string")]
    Empty,

    #[error("must start with a letter")]
    StartWithLetter,

    #[error("can contain only alphanumeric characters and underscores")]
    InvalidChar,
}

impl TryFrom<String> for IdentName {
    type Error = IdentNameError;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        if let Some(first_char) = value.chars().next() {
            if !first_char.is_alphabetic() {
                return Err(IdentNameError::StartWithLetter);
            }
        } else {
            return Err(IdentNameError::Empty);
        }

        if !value.chars().all(|c| c.is_alphanumeric() || c == '_') {
            return Err(IdentNameError::InvalidChar);
        }

        Ok(IdentName(value))
    }
}

impl TryFrom<&str> for IdentName {
    type Error = IdentNameError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        IdentName::try_from(value.to_owned())
    }
}

/// Path to an item.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ItemPath {
    items: SmallVec<[Spanned<IdentName>; 1]>,
}

impl ItemPath {
    /// Whether the path is a single item.
    pub fn into_single_item(self) -> Result<Spanned<IdentName>, Self> {
        if self.items.len() == 1 {
            Ok(self.items.into_iter().next().unwrap())
        } else {
            Err(self)
        }
    }

    pub fn single(ident: Spanned<IdentName>) -> Self {
        Self {
            items: smallvec![ident],
        }
    }
}

impl From<&[Spanned<IdentName>]> for ItemPath {
    fn from(items: &[Spanned<IdentName>]) -> Self {
        Self {
            items: items.into(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deserialize_file_type() {
        use serde_yml::from_str;

        let yaml = r#"
            main
        "#;

        let v: FileType = from_str(yaml).unwrap();
        assert_eq!(v, FileType::Main);

        let yaml = r#"
            custom: my_type
        "#;

        let v: FileType = from_str(yaml).unwrap();
        assert_eq!(v, FileType::Custom("my_type".to_owned()));
    }

    #[test]
    fn deserialize_version() {
        use serde_yml::from_str;

        let yaml = r#"
            0.1
        "#;

        from_str::<Version>(yaml).unwrap();

        // Check if invalid version is not accepted
        let yaml = r#"
            0.2
        "#;

        let v: Result<Version, _> = from_str(yaml);
        assert!(v.is_err());
    }

    #[test]
    fn header_parse_main() {
        use serde_yml::from_str;

        let yaml = r#"
            version: 0.1
            type: main
            use:
              - std::io::Read
        "#;

        let v: Header = from_str(yaml).unwrap();
        assert_eq!(v.ty, FileType::Main);
        assert_eq!(v.uses.len(), 1);
        assert_eq!(v.uses[0].0, "std::io::Read");

        // YAML without use
        let yaml = r#"
            version: 0.1
            type: main
        "#;

        let v: Header = from_str(yaml).unwrap();
        assert_eq!(v.ty, FileType::Main);
        assert!(v.uses.is_empty());
    }

    #[test]
    fn header_parse_custom() {
        use serde_yml::from_str;

        let yaml = r#"
            version: 0.1
            type:
              custom: my_type
            use:
              - std::io::Read
        "#;

        let v: Header = from_str(yaml).unwrap();
        assert_eq!(v.ty, FileType::Custom("my_type".to_owned()));
        assert_eq!(v.uses.len(), 1);
        assert_eq!(v.uses[0].0, "std::io::Read");
    }
}
