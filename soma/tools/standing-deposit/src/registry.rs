//! The depositor and the verifier, and the one distinction the whole tool exists for.
//!
//! ```text
//!   CONTENT drift  — a deposited file no longer matches its recorded hash.
//!                    The deposit is corrupt. REFUSE.
//!   ABSENT         — a deposited file is gone. That is the tiger-figure loss itself. REFUSE.
//!   UNMANIFESTED   — a file stands inside the standing that no row binds. REFUSE.
//!   CLOSURE drift  — the founding's material has moved since the deposit.
//!                    The machine has advanced past what it rested. REPORT, never refuse:
//!                    a standing that could not fall behind the current would not be standing.
//! ```
//!
//! The first, second and fourth are verbatim from
//! `archive/cpp-engine/cmake/HolonicRegistry.cmake:10-18`, which is where the distinction was first
//! written and where it caught the path-fold contamination.
//!
//! UNMANIFESTED is the species neither body had. Both verifiers walked the manifest and asked the
//! tree about each row; neither walked the tree and asked the manifest. The manifest could
//! therefore drift away from the standing in the one direction that leaves every row passing — an
//! unbound file, which is exactly the condition the tiger figures and
//! `semantics_invariant_under_exact_chart` were lost in. It refuses rather than reports because a
//! standing whose contents exceed its manifest cannot be cited as an evidence set: "the standing"
//! would name something the manifest does not describe.
//!
//! Its territory is not the whole directory. It is the set of first path components the rows
//! themselves occupy — `output/` here, `artifacts/` and `receipts/` in the archived standing — so
//! `MANIFEST.txt`, `PLAN.txt` and `README.md` sit outside it by construction rather than by a
//! name-exclusion list that would rot.

use std::fs::{self, File};
use std::io::{Read, Write};
use std::path::Path;

use crate::frame::{FoundingName, RelPath};
use crate::manifest::{DepositRow, FoundingRow, Manifest, ManifestRefusal, MANIFEST_NAME};
use crate::plan::Plan;
use crate::sha256::{file_digest_hex, Sha256};

// ---------------------------------------------------------------------------------------------
// depositing

#[derive(Debug)]
pub enum DepositRefusal {
    MaterialAbsent {
        founding: FoundingName,
        path: RelPath,
    },
    ReturnAbsent {
        founding: FoundingName,
        path: RelPath,
    },
    Io {
        path: String,
        why: String,
    },
}

impl std::fmt::Display for DepositRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MaterialAbsent { founding, path } => write!(
                formatter,
                "founding `{founding}` declares closure material `{path}` that is not a file; \
                 a closure computed over material that is not there is not a closure"
            ),
            Self::ReturnAbsent { founding, path } => write!(
                formatter,
                "founding `{founding}` declares return `{path}` that is not a file"
            ),
            Self::Io { path, why } => write!(formatter, "`{path}`: {why}"),
        }
    }
}

impl std::error::Error for DepositRefusal {}

/// Fold a founding's material into a closure hash.
///
/// The construction is the archived one (`HolonicDeposit.cmake:57-69`): each material file's
/// lowercase hex content digest is concatenated in declared order, and that string's octets are
/// hashed. Content only — no path enters the fold, so two checkouts at different absolute locations
/// produce the same closure.
///
/// `missing` collects material that is not currently a file. At deposit time that is a refusal; at
/// verify time it is a legitimate observation that the machine moved.
pub fn fold_closure(root: &Path, material: &[RelPath]) -> (String, Vec<RelPath>) {
    let mut hasher = Sha256::new();
    let mut missing = Vec::new();
    for item in material {
        let path = item.under(root);
        match file_digest_hex(&path) {
            Ok((digest, _)) => hasher.update(digest.as_bytes()),
            Err(_) => missing.push(item.clone()),
        }
    }
    (hasher.finish_hex(), missing)
}

/// Copy one file into the standing while hashing it, in a single pass over the octets.
fn copy_hashing(from: &Path, to: &Path) -> std::io::Result<(String, u64)> {
    if let Some(parent) = to.parent() {
        fs::create_dir_all(parent)?;
    }
    let mut source = File::open(from)?;
    let mut sink = File::create(to)?;
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 65536];
    let mut octets = 0u64;
    loop {
        let read = source.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
        sink.write_all(&buffer[..read])?;
        octets += read as u64;
    }
    sink.flush()?;
    Ok((hasher.finish_hex(), octets))
}

/// Execute a plan: fold each founding's closure, copy its returns into the standing, write the
/// manifest. Returns the manifest it wrote.
pub fn deposit(root: &Path, plan: &Plan, standing: &Path) -> Result<Manifest, DepositRefusal> {
    let mut manifest = Manifest::default();
    let mut octets_total: u64 = 0;
    let mut derived_total: usize = 0;

    for founding in &plan.foundings {
        let material = founding.material();
        let (closure, missing) = fold_closure(root, &material);
        if let Some(path) = missing.into_iter().next() {
            return Err(DepositRefusal::MaterialAbsent {
                founding: founding.name.clone(),
                path,
            });
        }
        manifest.foundings.push(FoundingRow {
            name: founding.name.clone(),
            closure: closure.clone(),
            material,
        });

        // Sorted, so that a plan emitted by a directory walk deposits identically whatever order
        // the walk returned.
        let mut returns = founding.returns.clone();
        returns.sort();
        for returned in returns {
            let source = returned.under(root);
            if !source.is_file() {
                return Err(DepositRefusal::ReturnAbsent {
                    founding: founding.name.clone(),
                    path: returned,
                });
            }
            let target = returned.under(standing);
            let (content, octets) =
                copy_hashing(&source, &target).map_err(|error| DepositRefusal::Io {
                    path: returned.to_string(),
                    why: error.to_string(),
                })?;
            octets_total += octets;
            manifest.deposits.push(DepositRow {
                path: returned,
                content,
                closure: closure.clone(),
                founding: founding.name.clone(),
            });
        }
        derived_total += founding.derived.len();
    }

    manifest
        .headers
        .insert("deposited_octets".into(), octets_total.to_string());
    manifest
        .headers
        .insert("derived_returns_not_deposited".into(), derived_total.to_string());

    fs::create_dir_all(standing).map_err(|error| DepositRefusal::Io {
        path: standing.display().to_string(),
        why: error.to_string(),
    })?;

    // A return dropped from the plan is a superseded return, and superseded machinery fails closed
    // (`CLAUDE.md` §13 rule 3): it is removed, not left lying in the standing to be re-cited. Without
    // this, `deposit` would emit a standing that its own `verify` refuses as UNMANIFESTED. The
    // deletion is bounded twice over — only under the roots the NEW manifest's rows occupy, and only
    // when there is at least one such row, so a plan that founded nothing can never empty a standing.
    if !manifest.deposits.is_empty() {
        for stray in unmanifested_returns(&manifest, standing) {
            let path = standing.join(&stray);
            fs::remove_file(&path).map_err(|error| DepositRefusal::Io {
                path: stray,
                why: error.to_string(),
            })?;
        }
    }

    let manifest_path = standing.join(MANIFEST_NAME);
    fs::write(&manifest_path, manifest.render()).map_err(|error| DepositRefusal::Io {
        path: manifest_path.display().to_string(),
        why: error.to_string(),
    })?;
    Ok(manifest)
}

// ---------------------------------------------------------------------------------------------
// verifying

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClosureStatus {
    Held,
    Drifted {
        recorded: String,
        recomputed: String,
        missing: Vec<RelPath>,
    },
}

#[derive(Debug, Default)]
pub struct Verdict {
    pub checked: usize,
    pub content_drift: usize,
    pub absent: usize,
    pub unmanifested: usize,
    pub closure_held: usize,
    pub closure_drift: usize,
    pub closure_unrecomputable: usize,
    pub foundings_checked: usize,
    pub foundings_drifted: usize,
    pub lines: Vec<String>,
}

impl Verdict {
    /// The whole point, in one predicate. Closure drift is not in it.
    pub fn refuses(&self) -> bool {
        self.content_drift > 0 || self.absent > 0 || self.unmanifested > 0
    }

    pub fn render(&self) -> String {
        use std::fmt::Write as _;
        let mut out = String::new();
        let _ = writeln!(out, "truth_status=established-bounded");
        let _ = writeln!(out, "evidence=computational-witness");
        let _ = writeln!(
            out,
            "law=a deposit is evidence only where its content hash still holds"
        );
        let _ = writeln!(
            out,
            "closure_law=a standing that could not fall behind the current would not be standing"
        );
        let _ = writeln!(out, "checked={}", self.checked);
        let _ = writeln!(out, "content_drift={}", self.content_drift);
        let _ = writeln!(out, "absent={}", self.absent);
        let _ = writeln!(out, "unmanifested={}", self.unmanifested);
        let _ = writeln!(out, "closure_held={}", self.closure_held);
        let _ = writeln!(out, "closure_drift={}", self.closure_drift);
        let _ = writeln!(
            out,
            "closure_unrecomputable={}",
            self.closure_unrecomputable
        );
        let _ = writeln!(out, "foundings_checked={}", self.foundings_checked);
        let _ = writeln!(out, "foundings_drifted={}", self.foundings_drifted);
        let _ = writeln!(
            out,
            "verdict={}",
            if self.refuses() { "REFUSED" } else { "HELD" }
        );
        for line in &self.lines {
            let _ = writeln!(out, "{line}");
        }
        out
    }
}

/// Verify a standing against the material currently in `root`.
///
/// `root` may be `None` when the founding material is not present in this tree at all — for the
/// archived C++ standing, for instance, whose deed binaries are gone. Every founding then reads
/// `Unrecorded`/drifted and nothing is refused on that account.
pub fn verify(root: &Path, standing: &Path) -> Result<Verdict, ManifestRefusal> {
    let manifest = Manifest::read(&standing.join(MANIFEST_NAME))?;
    Ok(verify_manifest(&manifest, root, standing))
}

pub fn verify_manifest(manifest: &Manifest, root: &Path, standing: &Path) -> Verdict {
    let mut verdict = Verdict::default();

    // One fold per founding, not one per deposit: the closure is a property of the founding.
    let mut statuses: Vec<(FoundingName, ClosureStatus)> = Vec::new();
    for founding in &manifest.foundings {
        verdict.foundings_checked += 1;
        let (recomputed, missing) = fold_closure(root, &founding.material);
        let status = if missing.is_empty() && recomputed == founding.closure {
            ClosureStatus::Held
        } else {
            verdict.foundings_drifted += 1;
            for gone in &missing {
                verdict
                    .lines
                    .push(format!("closure_material_absent {} {gone}", founding.name));
            }
            verdict.lines.push(format!(
                "closure_drift {} recorded={} recomputed={}",
                founding.name, founding.closure, recomputed
            ));
            ClosureStatus::Drifted {
                recorded: founding.closure.clone(),
                recomputed,
                missing,
            }
        };
        statuses.push((founding.name.clone(), status));
    }

    for deposit in &manifest.deposits {
        verdict.checked += 1;
        let deposited = deposit.path.under(standing);
        if !deposited.is_file() {
            verdict.absent += 1;
            verdict
                .lines
                .push(format!("absent {} {}", deposit.path, deposit.founding));
            continue;
        }
        match file_digest_hex(&deposited) {
            Ok((holds, _)) if holds == deposit.content => {}
            Ok((holds, _)) => {
                verdict.content_drift += 1;
                verdict.lines.push(format!(
                    "content_drift {} {} recorded={} holds={holds}",
                    deposit.path, deposit.founding, deposit.content
                ));
                continue;
            }
            Err(error) => {
                verdict.absent += 1;
                verdict.lines.push(format!(
                    "absent {} {} unreadable={error}",
                    deposit.path, deposit.founding
                ));
                continue;
            }
        }

        match statuses
            .iter()
            .find(|(name, _)| name == &deposit.founding)
            .map(|(_, status)| status)
        {
            Some(ClosureStatus::Held) => verdict.closure_held += 1,
            Some(ClosureStatus::Drifted { .. }) => verdict.closure_drift += 1,
            // No founding row: the manifest recorded no material, so no closure can be
            // recomputed. This is the archived C++ manifest's condition for all 123 of its rows,
            // and it is reported, never refused.
            None => verdict.closure_unrecomputable += 1,
        }
    }

    for stray in unmanifested_returns(manifest, standing) {
        verdict.unmanifested += 1;
        verdict.lines.push(format!("unmanifested {stray}"));
    }

    verdict
}

/// Walk the manifest's own territory and report what no row binds.
///
/// The territory is the set of first path components the rows occupy, so a standing whose rows all
/// live under `output/` is never asked about `MANIFEST.txt`. A manifest with no rows claims no
/// territory and this returns nothing — an empty standing cannot be accused of holding a stray.
fn unmanifested_returns(manifest: &Manifest, standing: &Path) -> Vec<String> {
    use std::collections::BTreeSet;

    let bound: BTreeSet<&str> = manifest
        .deposits
        .iter()
        .map(|deposit| deposit.path.as_str())
        .collect();
    let roots: BTreeSet<&str> = manifest
        .deposits
        .iter()
        .filter_map(|deposit| deposit.path.as_str().split('/').next())
        .collect();

    let mut stray = Vec::new();
    for root in roots {
        let mut pending = vec![standing.join(root)];
        while let Some(directory) = pending.pop() {
            let Ok(entries) = fs::read_dir(&directory) else {
                continue;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    pending.push(path);
                    continue;
                }
                let Ok(relative) = path.strip_prefix(standing) else {
                    continue;
                };
                let name = relative.to_string_lossy().replace('\\', "/");
                if !bound.contains(name.as_str()) {
                    stray.push(name);
                }
            }
        }
    }
    stray.sort();
    stray
}

#[cfg(test)]
mod tests {
    use super::fold_closure;
    use std::path::Path;

    #[test]
    fn a_closure_over_no_material_is_the_empty_digest() {
        let (closure, missing) = fold_closure(Path::new("/nonexistent"), &[]);
        assert!(missing.is_empty());
        assert_eq!(
            closure,
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }
}
