use serde::Deserialize;
use log::trace;

/// Parsing YAML file into initial representation of the project files, almost without
/// validation or analysis, except for structural.
pub mod parse {
    use super::*;

    /// Version 0.1 of the project file format.
    pub mod v0_1;

    #[derive(Debug, thiserror::Error)]
    pub enum CheckVersionError {
        #[error(transparent)]
        UnknownVersion(#[from] UnknownVersionError),

        #[error("error deserializing header. {0}")]
        HeaderDeserialize(#[from] serde_yml::Error),
    }

    impl Version {
        pub fn extract_from(yaml: &str) -> Result<Version, CheckVersionError> {
            trace!("Extracting version from YAML");

            let header = Header::extract_from(yaml)?;
            let version = Version::try_from(header.version.as_str())?;
            Ok(version)
        }
    }

    #[derive(Debug, Clone, Deserialize)]
    pub struct Header {
        pub version: String,
    }

    impl Header {
        pub fn extract_from(yaml: &str) -> Result<Self, serde_yml::Error> {
            trace!("Extracting header from YAML");

            #[derive(Debug, Deserialize)]
            struct File {
                permute: Header,
            }

            let v: File = serde_yml::from_str(yaml)?;
            Ok(v.permute)
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Version {
    Permute0_1,
}

impl<'de> Deserialize<'de> for Version {
    fn deserialize<D>(deserializer: D) -> Result<Version, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::Error;
        let s = String::deserialize(deserializer)?;
        Version::try_from(s.as_str()).map_err(D::Error::custom)
    }
}

impl std::fmt::Display for Version {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Version::*;
        let v = match self {
            Permute0_1 => "0.1",
        };
        write!(f, "{}", v)
    }
}

#[derive(Debug, thiserror::Error)]
#[error("unsupported version: `{0}`")]
pub struct UnknownVersionError(String);

impl TryFrom<&str> for Version {
    type Error = UnknownVersionError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        use Version::*;
        let v = match value {
            "0.1" => Permute0_1,
            unknown => return Err(UnknownVersionError(unknown.to_owned())),
        };
        Ok(v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn version_display_eq_try_from() {
        crate::init_log();

        let v = Version::Permute0_1;
        assert_eq!(v.to_string(), "0.1");
        assert_eq!(Version::try_from("0.1").unwrap(), v);
    }

    #[test]
    fn extract_version() {
        crate::init_log();

        let yaml = include_str!("../examples/sample1/main.yaml");
        let version = Version::extract_from(yaml).unwrap();
        assert_eq!(version, Version::Permute0_1);
    }
}
