//! `MANIFEST.txt` — the two-hash binding, and the reader the archived body never had for its own.
//!
//! Shape, deliberately line-oriented and greppable:
//!
//! ```text
//! truth_status=established-bounded
//! ...
//! columns=path content_sha256 closure_sha256 founding
//! founding <name> <closure_sha256> <material-path>...
//! <path> <content_sha256> <closure_sha256> <founding>
//! ```
//!
//! The deposit row is **byte-compatible with the archived C++ manifest**
//! (`archive/cpp-engine/standing/MANIFEST.txt`, written by `HolonicDeposit.cmake:109`), which is
//! why this reader consumes that file natively — 123 rows whose content hashes CMake computed. That
//! is the independent-implementation cross-check `CLAUDE.md` §8 asks for, on real deposited octets
//! rather than a fixture.
//!
//! The `founding` row is the thing the C++ manifest lacked, and its absence is why the C++ verifier
//! could not recompute a closure. `HolonicRegistry.cmake:64-72` substituted a proxy: it compared the
//! *current build tree's* output against the recorded content hash. That proxy is blind in both
//! directions — a founding whose material moved but whose output is unchanged reads as held, and a
//! founding whose output is nondeterministic reads as drifted with its material untouched. Recording
//! the material lets the closure be recomputed from what it actually is.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::Path;

use crate::frame::{FoundingName, RelPath};
use crate::sha256::is_hex64;

pub const MANIFEST_NAME: &str = "MANIFEST.txt";

pub const LAW: &str =
    "a deposited return names the founding that produced it and the material that founding mounted";
pub const CLOSURE_LAW: &str = "sha256 of the concatenated lowercase hex content digests of the executable then each mount, in declared order";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FoundingRow {
    pub name: FoundingName,
    pub closure: String,
    pub material: Vec<RelPath>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DepositRow {
    pub path: RelPath,
    pub content: String,
    pub closure: String,
    pub founding: FoundingName,
}

#[derive(Debug, Clone, Default)]
pub struct Manifest {
    pub headers: BTreeMap<String, String>,
    pub foundings: Vec<FoundingRow>,
    pub deposits: Vec<DepositRow>,
}

impl Manifest {
    pub fn render(&self) -> String {
        let octets: u64 = self
            .headers
            .get("deposited_octets")
            .and_then(|value| value.parse().ok())
            .unwrap_or(0);
        let derived: usize = self
            .headers
            .get("derived_returns_not_deposited")
            .and_then(|value| value.parse().ok())
            .unwrap_or(0);

        let mut out = String::new();
        let _ = writeln!(out, "truth_status=established-bounded");
        let _ = writeln!(out, "evidence=computational-witness");
        let _ = writeln!(out, "law={LAW}");
        let _ = writeln!(out, "closure={CLOSURE_LAW}");
        let _ = writeln!(out, "columns=path content_sha256 closure_sha256 founding");
        let _ = writeln!(out, "foundings={}", self.foundings.len());
        let _ = writeln!(out, "deposited_returns={}", self.deposits.len());
        let _ = writeln!(out, "deposited_octets={octets}");
        let _ = writeln!(out, "derived_returns_not_deposited={derived}");
        for founding in &self.foundings {
            let _ = write!(out, "founding {} {}", founding.name, founding.closure);
            for material in &founding.material {
                let _ = write!(out, " {material}");
            }
            out.push('\n');
        }
        for deposit in &self.deposits {
            let _ = writeln!(
                out,
                "{} {} {} {}",
                deposit.path, deposit.content, deposit.closure, deposit.founding
            );
        }
        out
    }

    /// Reads both this manifest shape and the archived C++ one. A line that is neither a header, a
    /// founding row, nor a four-column deposit row is skipped, matching the archived reader's
    /// regex-guarded loop (`HolonicRegistry.cmake:40-42`).
    ///
    /// **A row that is SHAPED like a deposit but carries a corrupt hash refuses rather than
    /// skipping.** Skipping it was a fail-open: a single character flipped in a recorded digest made
    /// `is_hex64` false, the row fell out of `deposits`, and `verify_manifest` — which iterates only
    /// the rows that survived parsing — reported `HELD` on a deposit it had never looked at. The
    /// superseded machinery failed CLOSED here: `HolonicRegistry.cmake:41`'s looser `([0-9a-f]+)`
    /// matched the corrupt row and refused it on the hash comparison. Failing open where the
    /// machinery one replaces failed closed is the `CLAUDE.md` §13 rule-3 defect, so the shape test
    /// is width-only (two adjacent 64-character fields) and the hex test is the refusal.
    ///
    /// The width test cannot fire on prose: two adjacent 64-character words in a four-word line is
    /// not a sentence. Corruption that CHANGES a digest's width escapes it, which is what the
    /// header cross-check below is for — `deposited_returns` and `foundings` are compared against
    /// the rows actually read, so a row lost by any mechanism at all is caught by count.
    pub fn parse(text: &str) -> Result<Self, ManifestRefusal> {
        let mut manifest = Self::default();
        for (index, raw) in text.lines().enumerate() {
            let line = index + 1;
            let trimmed = raw.trim_end();
            if trimmed.is_empty() {
                continue;
            }
            if let Some((key, value)) = header_of(trimmed) {
                manifest.headers.insert(key.to_string(), value.to_string());
                continue;
            }
            let fields: Vec<&str> = trimmed.split_whitespace().collect();
            if fields.first() == Some(&RelPath::RESERVED) {
                if fields.len() < 3 || !is_hex64(fields[2]) {
                    return Err(ManifestRefusal::MalformedFounding(line));
                }
                let name = FoundingName::parse(fields[1])
                    .map_err(|_| ManifestRefusal::MalformedFounding(line))?;
                let mut material = Vec::with_capacity(fields.len() - 3);
                for raw_material in &fields[3..] {
                    material.push(
                        RelPath::parse(raw_material)
                            .map_err(|_| ManifestRefusal::MalformedFounding(line))?,
                    );
                }
                manifest.foundings.push(FoundingRow {
                    name,
                    closure: fields[2].to_string(),
                    material,
                });
                continue;
            }
            if fields.len() == 4 && fields[1].len() == 64 && fields[2].len() == 64 {
                if !is_hex64(fields[1]) || !is_hex64(fields[2]) {
                    return Err(ManifestRefusal::CorruptDigest(line));
                }
                let path = RelPath::parse(fields[0])
                    .map_err(|_| ManifestRefusal::MalformedDeposit(line))?;
                let founding = FoundingName::parse(fields[3])
                    .map_err(|_| ManifestRefusal::MalformedDeposit(line))?;
                manifest.deposits.push(DepositRow {
                    path,
                    content: fields[1].to_string(),
                    closure: fields[2].to_string(),
                    founding,
                });
            }
        }
        if manifest.headers.is_empty() && manifest.deposits.is_empty() {
            return Err(ManifestRefusal::Empty);
        }
        manifest.check_count("deposited_returns", manifest.deposits.len())?;
        manifest.check_count("foundings", manifest.foundings.len())?;
        Ok(manifest)
    }

    /// A declared count that disagrees with the rows actually read means a row was lost between the
    /// writing and the reading, whatever the mechanism. This is the check the archived reader never
    /// had — `HolonicRegistry.cmake` parsed `deposited_returns` and never compared it to anything.
    fn check_count(&self, header: &'static str, read: usize) -> Result<(), ManifestRefusal> {
        match self.headers.get(header).map(|value| value.parse::<usize>()) {
            Some(Ok(recorded)) if recorded != read => Err(ManifestRefusal::CountDisagrees {
                header,
                recorded,
                read,
            }),
            _ => Ok(()),
        }
    }

    pub fn read(path: &Path) -> Result<Self, ManifestRefusal> {
        let text = std::fs::read_to_string(path)
            .map_err(|error| ManifestRefusal::Unreadable(error.to_string()))?;
        Self::parse(&text)
    }

    pub fn founding(&self, name: &FoundingName) -> Option<&FoundingRow> {
        self.foundings.iter().find(|row| &row.name == name)
    }
}

fn header_of(line: &str) -> Option<(&str, &str)> {
    let (key, value) = line.split_once('=')?;
    if key.is_empty() || key.chars().any(char::is_whitespace) {
        return None;
    }
    Some((key, value))
}

#[derive(Debug)]
pub enum ManifestRefusal {
    Unreadable(String),
    Empty,
    MalformedFounding(usize),
    MalformedDeposit(usize),
    CorruptDigest(usize),
    CountDisagrees {
        header: &'static str,
        recorded: usize,
        read: usize,
    },
}

impl std::fmt::Display for ManifestRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unreadable(why) => write!(formatter, "manifest unreadable ({why})"),
            Self::Empty => write!(formatter, "manifest carries neither header nor deposit"),
            Self::MalformedFounding(line) => {
                write!(formatter, "manifest line {line}: malformed founding row")
            }
            Self::MalformedDeposit(line) => {
                write!(formatter, "manifest line {line}: malformed deposit row")
            }
            Self::CorruptDigest(line) => write!(
                formatter,
                "manifest line {line}: a deposit row carries a 64-character field that is not a \
                 hex digest; a row that cannot be read is a deposit removed from the gate, so it \
                 refuses here rather than falling out of the manifest silently"
            ),
            Self::CountDisagrees {
                header,
                recorded,
                read,
            } => write!(
                formatter,
                "manifest declares {header}={recorded} and carries {read}; a row was lost between \
                 the writing and the reading"
            ),
        }
    }
}

impl std::error::Error for ManifestRefusal {}

#[cfg(test)]
mod tests {
    use super::Manifest;

    #[test]
    fn the_archived_cpp_row_shape_reads_natively() {
        let archived = "truth_status=established-bounded\n\
             columns=path content_sha256 closure_sha256 founding\n\
             deposited_returns=1\n\
             receipts/R1_EXACT_DEED.txt \
             556c5bab75d77c4ec75f68e4084d07acab531ea1c402524066f5e3199ff05571 \
             2977c7ef54c16271e5a5b48704cd48d6fdf4ca50a7e7bb1eb69e522277aacf78 \
             r1.exact_device_deed\n";
        let manifest = Manifest::parse(archived).expect("archived shape parses");
        assert_eq!(manifest.deposits.len(), 1);
        assert!(
            manifest.foundings.is_empty(),
            "the archived manifest recorded no founding material, which is the gap"
        );
        assert_eq!(
            manifest.deposits[0].path.as_str(),
            "receipts/R1_EXACT_DEED.txt"
        );
        assert_eq!(
            manifest.deposits[0].founding.as_str(),
            "r1.exact_device_deed"
        );
    }

    #[test]
    fn render_then_parse_is_the_identity_on_rows() {
        let text = "truth_status=established-bounded\n\
             deposited_octets=7\n\
             derived_returns_not_deposited=3\n\
             founding f 2977c7ef54c16271e5a5b48704cd48d6fdf4ca50a7e7bb1eb69e522277aacf78 a.rs b.rs\n\
             out/x.lean \
             556c5bab75d77c4ec75f68e4084d07acab531ea1c402524066f5e3199ff05571 \
             2977c7ef54c16271e5a5b48704cd48d6fdf4ca50a7e7bb1eb69e522277aacf78 f\n";
        let first = Manifest::parse(text).expect("parses");
        let second = Manifest::parse(&first.render()).expect("re-parses");
        assert_eq!(first.foundings, second.foundings);
        assert_eq!(first.deposits, second.deposits);
        assert_eq!(second.render(), first.render());
        assert_eq!(
            second.headers.get("deposited_octets").map(String::as_str),
            Some("7")
        );
        assert_eq!(
            second
                .headers
                .get("derived_returns_not_deposited")
                .map(String::as_str),
            Some("3")
        );
    }
}
