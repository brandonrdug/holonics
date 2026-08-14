//! The relative-path discipline.
//!
//! `CLAUDE.md` §0: *"No absolute frame in a lineage. Ten C++ card adapters folded the filesystem
//! path into the rest integrity, and one deed asserted that dependence as its own success
//! condition."*
//!
//! A deposit that recorded where it was checked out would drift the moment the tree moved, and the
//! drift would be indistinguishable from corruption. So every path this tool records is relative to
//! a declared root, and the refusal is structural rather than advisory: an absolute path, a `..`
//! component, a `.` component, a backslash, or whitespace never enters a manifest.
//!
//! The closure hash likewise folds *content* digests only, never a path. Two checkouts at different
//! absolute locations produce byte-identical manifests.

use std::fmt;
use std::path::{Component, Path, PathBuf};

/// A path that has been checked against the frame discipline. The invariant is on construction.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct RelPath(String);

impl RelPath {
    /// The single reserved word. A manifest row is read as a founding declaration when its first
    /// field is `founding`, so no deposit may occupy that field.
    pub const RESERVED: &'static str = "founding";

    pub fn parse(raw: &str) -> Result<Self, FrameRefusal> {
        if raw.is_empty() {
            return Err(FrameRefusal::Empty);
        }
        if raw.chars().any(char::is_whitespace) {
            return Err(FrameRefusal::Whitespace(raw.to_string()));
        }
        if raw.contains('\\') {
            return Err(FrameRefusal::Backslash(raw.to_string()));
        }
        if raw == Self::RESERVED {
            return Err(FrameRefusal::Reserved(raw.to_string()));
        }
        let path = Path::new(raw);
        for component in path.components() {
            match component {
                Component::Normal(_) => {}
                Component::CurDir => return Err(FrameRefusal::CurDir(raw.to_string())),
                Component::ParentDir => return Err(FrameRefusal::ParentDir(raw.to_string())),
                Component::RootDir | Component::Prefix(_) => {
                    return Err(FrameRefusal::Absolute(raw.to_string()))
                }
            }
        }
        Ok(Self(raw.to_string()))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn under(&self, root: &Path) -> PathBuf {
        root.join(&self.0)
    }
}

impl fmt::Display for RelPath {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

/// A founding's name. Same discipline, minus the path structure.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct FoundingName(String);

impl FoundingName {
    pub fn parse(raw: &str) -> Result<Self, FrameRefusal> {
        if raw.is_empty() {
            return Err(FrameRefusal::Empty);
        }
        if raw.chars().any(char::is_whitespace) {
            return Err(FrameRefusal::Whitespace(raw.to_string()));
        }
        Ok(Self(raw.to_string()))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for FoundingName {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum FrameRefusal {
    Empty,
    Whitespace(String),
    Backslash(String),
    Absolute(String),
    ParentDir(String),
    CurDir(String),
    Reserved(String),
}

impl fmt::Display for FrameRefusal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => write!(formatter, "the empty path carries no frame"),
            Self::Whitespace(raw) => write!(
                formatter,
                "`{raw}` carries whitespace; a manifest row is whitespace-separated"
            ),
            Self::Backslash(raw) => write!(formatter, "`{raw}` carries a backslash separator"),
            Self::Absolute(raw) => write!(
                formatter,
                "`{raw}` is absolute; a deposit may not fold a checkout location into its lineage"
            ),
            Self::ParentDir(raw) => write!(
                formatter,
                "`{raw}` climbs above the declared root with `..`"
            ),
            Self::CurDir(raw) => write!(
                formatter,
                "`{raw}` carries a `.` component; two spellings of one path are two rows"
            ),
            Self::Reserved(raw) => write!(
                formatter,
                "`{raw}` is the reserved manifest row tag and cannot be a deposited path"
            ),
        }
    }
}

impl std::error::Error for FrameRefusal {}

#[cfg(test)]
mod tests {
    use super::{FrameRefusal, RelPath};

    #[test]
    fn the_frame_refusals_are_structural() {
        assert!(
            RelPath::parse("output/lean-proof-production/carrier-transport-00000.lean").is_ok()
        );
        assert_eq!(
            RelPath::parse("/home/b/Workspaces/holonics/x.lean"),
            Err(FrameRefusal::Absolute(
                "/home/b/Workspaces/holonics/x.lean".into()
            ))
        );
        assert_eq!(
            RelPath::parse("../laboratory/x.lean"),
            Err(FrameRefusal::ParentDir("../laboratory/x.lean".into()))
        );
        assert_eq!(
            RelPath::parse("./x.lean"),
            Err(FrameRefusal::CurDir("./x.lean".into()))
        );
        assert_eq!(
            RelPath::parse("a b.lean"),
            Err(FrameRefusal::Whitespace("a b.lean".into()))
        );
        assert_eq!(
            RelPath::parse("founding"),
            Err(FrameRefusal::Reserved("founding".into()))
        );
        assert_eq!(RelPath::parse(""), Err(FrameRefusal::Empty));
    }
}
