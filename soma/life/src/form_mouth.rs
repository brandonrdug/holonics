//! The near side of the plate mouth: where a driver's sealed octets land on disk.
//!
//! ```text
//!   a driver  ──seal──▶  octets  ──▶  output/<driver>/<name>-<sha256>.form  ──▶  holon-plate deposit
//!                          │                          ▲
//!                          └──────▶  sha256 ───────────┘   the receipt's hash IS the artifact's
//!                                    into the JSON receipt  address; one string, two places
//! ```
//!
//! # Why this owner exists and why it lives in `life`
//!
//! `blueprint/THE_ASSEMBLY.md` fact **F1**: `holon-plate` depends on `life`, so a `life` example can
//! never call `holon_plate::deposit`. That is a Cargo cycle, and it is the whole reason the plate's
//! mouth has been unfed while roughly two dozen drivers were already producing exactly the octets it
//! wants. The seam is closed by **adding no dependency at all**: the driver writes the octets to a
//! declared path, and `holon-plate` — which is above `life` and may name it — reads the file.
//!
//! Every driver here already computed `sha256` over those octets and then dropped them. A hash is a
//! claim *about* octets that are gone; it cannot be mounted, cannot be re-lit, and cannot be
//! refused. `THE_ASSEMBLY.md` loop **(d)**: *the signal is the octets.* This owner is the one line
//! that stops dropping them.
//!
//! # The address is the content, and that resolves a gap in the design
//!
//! `THE_ASSEMBLY.md:72` gives the shape `output/<driver>/<name>.form`; `THE_ASSEMBLY.md:108`
//! requires content addressing *"so nothing is written twice"*. **The design does not say which
//! governs, and the two disagree the moment a deposit site runs more than once.** They disagreed
//! badly: `eros_text_training` seals a rest inside a per-candidate loop, its own receipt carried
//! **511 distinct rest hashes**, and the fixed name `machine-rest.form` left **one** file on disk.
//! Five hundred and ten returned forms were overwritten, and the survivor carried nothing saying
//! which rest it was. A receipt with 511 hashes beside one nameless artifact is `CLAUDE.md` §9
//! inverted — *counts are supporting receipts and never substitutes* — and it is the loss the
//! repository's own `.gitignore` note describes happening to the laboratory's figures.
//!
//! **The resolution taken here: content addressing governs, and `:72`'s shape is the special case
//! of a site that runs once.** A form's address is
//!
//! ```text
//!   output/<driver>/<name>-<sha256 of the octets>.form
//!         └ who     └ which site sealed it   └ which form it is
//! ```
//!
//! `<name>` says *where in the driver* the seal happened; the digest says *which form*. Neither is
//! redundant: without the name a reader cannot tell a rest from a checkpoint, and without the digest
//! two rests from one site collide. Three consequences, and each of them is a law rather than a
//! convenience:
//!
//! - **Nothing correct is ever overwritten.** Two different forms take two addresses. A site called
//!   511 times deposits as many files as it returned distinct forms.
//! - **Depositing the same form twice is idempotent.** Identical octets compose the identical path
//!   and the second write is byte-for-byte the first. That is `:108`'s *"nothing is written twice"*
//!   read as a statement about content, which is the only reading under which it is achievable
//!   without a lock — and `:108` says exactly that: *concurrency is solved by content addressing,
//!   not locking.*
//! - **The receipt and the artifact are bound by one string.** Every driver here reports
//!   `sha256(octets)` in its JSON. That hash is now the artifact's file name, so a reader goes from
//!   a receipt line to the form on disk with no index, and a receipt whose hash names no file is
//!   visibly a receipt with nothing under it.
//!
//! The digest is lowercase hex, which is inside the name law's own alphabet — so content addressing
//! does not have to escape the name law, and `the_content_address_is_itself_a_declared_name` holds
//! that.
//!
//! # What this owner is not
//!
//! It is **not a codec**. It does not know what a form is, does not parse one, and holds no schema.
//! The schema is named at the mouth on the far side (`holon-plate deposit --from ERST:…`), by a
//! reader that holds it. A guess here about which body a file carries is precisely the failure the
//! plate container exists to make impossible, so nothing here guesses.
//!
//! It carries **no count, ratio, score or figure** that could be read as a competence number. What
//! it returns is an address — a [`DepositedForm`] naming the path, the content address, and the
//! octets that went to it — because `THE_ASSEMBLY.md`'s reviewable rule is that no adapter may
//! reduce a returned structure to a boolean or a scalar on its way to the next organ. A `bool` here
//! would be exactly that, and so is a caller that binds the return to `_`.
//!
//! # The two laws, and why each is a law rather than a convenience
//!
//! **The name law.** A driver name and a form name are `[a-z0-9]([a-z0-9_-])*`. This is not
//! cosmetic: it is what makes `..`, `/`, `\`, a leading `-`, a drive letter, and an absolute path
//! unrepresentable *by the character law itself* rather than by a list of special cases someone has
//! to remember to extend. A path traversal is refused here for the same reason `9` is: it is not a
//! declared name.
//!
//! **The read-back law.** After writing, the octets are read back and required to be byte-identical.
//! This mirrors `holon_plate::registry::deposit`, which re-takes the form from the mounted body
//! before sealing anything. A short write on a full disk produces a truncated `.form` whose driver
//! still prints a perfectly correct `sha256` of the octets it *held* — the receipt and the artifact
//! disagreeing with nobody looking, which is the exact shape of the defect `CLAUDE.md` §8 convicts.
//! Reading back is one syscall and it makes that disagreement impossible to reach.
//!
//! An **empty** form is refused, before any address is composed. Zero octets are not a small form;
//! they are the absence of one, and a zero-length `.form` beside a confident hash would be a law
//! that returned nothing while looking like it returned something.

use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

/// The suffix every deposited form carries. `holon-plate` names its own container suffix
/// (`.holon`); this is the *unwrapped* form the container is sealed around, so it is a different
/// suffix on purpose.
pub const FORM_SUFFIX: &str = "form";

/// The declared root a driver deposits under, relative to the invocation directory. This is the
/// same `/output/` the repository's `.gitignore` already declares as the place a driver writes its
/// returns — and, by that file's own note, the place a return does *not* acquire standing. Standing
/// is `/standing/`; this is the mouth, not the deposit ledger.
pub const DEPOSIT_ROOT: &str = "output";

/// What a deposit returned: the address, the content address it was composed from, and the octets
/// that reached it.
///
/// Deliberately not a `bool` and not a byte count. The next organ is
/// `holon-plate deposit --from SCHEMA:<path>`, so the path *is* the return; the octets travel with
/// it so a caller that wants to go on inspecting them never has to read the file back, and
/// [`DepositedForm::address`] travels with it so a caller can print the one string that binds its
/// own receipt to the file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DepositedForm {
    /// Where the octets were written, exactly as the name law and the content address composed it.
    pub path: PathBuf,
    /// The lowercase SHA-256 hex of the octets — the discriminating half of the file name, and the
    /// same string a driver reports as this form's hash.
    pub address: String,
    /// The octets that were written, read back off the disk. Equal to what was handed in, or this
    /// would have refused.
    pub octets: Vec<u8>,
}

/// Why a deposit was refused. Every variant names the part that failed and the value that failed
/// it, because a refusal that says only "invalid" cannot be acted on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FormMouthRefusal {
    /// A name part was empty. An empty driver name would collapse two levels of the path into one;
    /// an empty form name would produce a file whose whole name is its content address, with
    /// nothing left saying which site sealed it.
    NameEmpty { part: &'static str },
    /// A name part carries an octet the name law does not declare. `octet` is the first one, in
    /// source order, so the report names a cause rather than a symptom.
    NameUndeclared {
        part: &'static str,
        name: String,
        octet: u8,
    },
    /// A name part starts with `_` or `-`. Separators join declared runs; a name that opens with
    /// one has nothing to join, and a leading `-` is read as a flag by every shell tool that would
    /// later carry this path.
    NameOpensOnSeparator { part: &'static str, name: String },
    /// Zero octets were handed in. Not a small form: the absence of one. No address is composed,
    /// because there is no content to address; the refusal names the directory it would have been
    /// founded under and the site that offered it.
    FormEmpty { under: PathBuf, name: String },
    /// The directory could not be founded, or the write itself failed.
    WriteRefused { path: PathBuf, detail: String },
    /// The read-back law fired: what came off the disk is not what went to it.
    NotReadBackIdentical {
        path: PathBuf,
        written: usize,
        read_back: usize,
    },
}

impl core::fmt::Display for FormMouthRefusal {
    fn fmt(&self, out: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NameEmpty { part } => write!(
                out,
                "REFUSED: the {part} name is empty; a declared path has no empty component"
            ),
            Self::NameUndeclared { part, name, octet } => write!(
                out,
                "REFUSED: the {part} name `{name}` carries the octet {:?}, which the name law does \
                 not declare.\n         A name is [a-z0-9]([a-z0-9_-])*; `..`, `/` and an absolute \
                 path are refused by that law rather than by a special case.",
                *octet as char
            ),
            Self::NameOpensOnSeparator { part, name } => write!(
                out,
                "REFUSED: the {part} name `{name}` opens on a separator; a separator joins declared \
                 runs and has nothing to join at the start of a name"
            ),
            Self::FormEmpty { under, name } => write!(
                out,
                "REFUSED: the {name} site offered zero octets under {}. Zero octets are not a small \
                 form, they are the absence of one; there is no content to address and a hash \
                 reported beside an empty artifact is a receipt with nothing under it.",
                under.display()
            ),
            Self::WriteRefused { path, detail } => {
                write!(out, "REFUSED: cannot deposit {}: {detail}", path.display())
            }
            Self::NotReadBackIdentical {
                path,
                written,
                read_back,
            } => write!(
                out,
                "REFUSED: {written} octets were written to {} and {read_back} came back.\n         \
                 The driver's hash would still be correct about the octets it held; the artifact \
                 beside it would not be those octets.",
                path.display()
            ),
        }
    }
}

impl std::error::Error for FormMouthRefusal {}

/// The content address of one form: lowercase SHA-256 hex over its octets.
///
/// Lowercase hex and not base64, base32 or uppercase, because `[0-9a-f]` is inside the name law's
/// own alphabet — the composed file stem is therefore itself a declared name and content addressing
/// needs no escape hatch through the law it is composed under.
pub fn content_address(octets: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut address = String::with_capacity(64);
    for octet in Sha256::digest(octets) {
        address.push(HEX[usize::from(octet >> 4)] as char);
        address.push(HEX[usize::from(octet & 0x0f)] as char);
    }
    address
}

/// The name law, applied to one part.
///
/// `[a-z0-9]([a-z0-9_-])*`. Everything a path could use to leave its declared subtree — `.`, `/`,
/// `\`, `:`, a NUL — is outside the declared alphabet, so `..` and `/etc/passwd` are refused by the
/// same clause that refuses `Driver`.
fn declare_name(part: &'static str, name: &str) -> Result<(), FormMouthRefusal> {
    let octets = name.as_bytes();
    let Some(&first) = octets.first() else {
        return Err(FormMouthRefusal::NameEmpty { part });
    };
    if let Some(&octet) = octets
        .iter()
        .find(|octet| !matches!(octet, b'a'..=b'z' | b'0'..=b'9' | b'_' | b'-'))
    {
        return Err(FormMouthRefusal::NameUndeclared {
            part,
            name: name.to_owned(),
            octet,
        });
    }
    if matches!(first, b'_' | b'-') {
        return Err(FormMouthRefusal::NameOpensOnSeparator {
            part,
            name: name.to_owned(),
        });
    }
    Ok(())
}

/// Compose the declared, content-addressed path for one form, under an explicit root.
///
/// The root is a parameter rather than baked in so the law can be exercised from two frames — a
/// path law tested under exactly one root cannot distinguish *joining* the root from *ignoring* it.
/// The default frame, the one every driver uses, is [`declared_path`], and it is exercised too.
pub fn declared_path_under(
    root: &Path,
    driver: &str,
    name: &str,
    octets: &[u8],
) -> Result<PathBuf, FormMouthRefusal> {
    declare_name("driver", driver)?;
    declare_name("form", name)?;
    let under = root.join(driver);
    if octets.is_empty() {
        return Err(FormMouthRefusal::FormEmpty {
            under,
            name: name.to_owned(),
        });
    }
    let address = content_address(octets);
    Ok(under.join(format!("{name}-{address}.{FORM_SUFFIX}")))
}

/// Compose the declared, content-addressed path for one form, under [`DEPOSIT_ROOT`].
pub fn declared_path(driver: &str, name: &str, octets: &[u8]) -> Result<PathBuf, FormMouthRefusal> {
    declared_path_under(Path::new(DEPOSIT_ROOT), driver, name, octets)
}

/// Write one form's octets to its declared path under an explicit root, founding the directory.
pub fn deposit_form_under(
    root: &Path,
    driver: &str,
    name: &str,
    octets: &[u8],
) -> Result<DepositedForm, FormMouthRefusal> {
    let path = declared_path_under(root, driver, name, octets)?;
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).map_err(|error| FormMouthRefusal::WriteRefused {
            path: path.clone(),
            detail: error.to_string(),
        })?;
    }
    std::fs::write(&path, octets).map_err(|error| FormMouthRefusal::WriteRefused {
        path: path.clone(),
        detail: error.to_string(),
    })?;
    let read_back = std::fs::read(&path).map_err(|error| FormMouthRefusal::WriteRefused {
        path: path.clone(),
        detail: error.to_string(),
    })?;
    if read_back != octets {
        return Err(FormMouthRefusal::NotReadBackIdentical {
            path,
            written: octets.len(),
            read_back: read_back.len(),
        });
    }
    Ok(DepositedForm {
        address: content_address(&read_back),
        path,
        octets: read_back,
    })
}

/// Write one form's octets to its declared path under [`DEPOSIT_ROOT`], founding the directory.
///
/// This is what a driver calls. It is one call beside the driver's existing hash and it changes
/// nothing the driver reports — except that the driver now has an address to report beside it.
pub fn deposit_form(
    driver: &str,
    name: &str,
    octets: &[u8],
) -> Result<DepositedForm, FormMouthRefusal> {
    deposit_form_under(Path::new(DEPOSIT_ROOT), driver, name, octets)
}

/// The `String`-error spelling, for the many drivers whose helpers return `Result<_, String>`.
/// Same law, same refusal text; only the carrier differs.
pub fn deposit_form_or_message(
    driver: &str,
    name: &str,
    octets: &[u8],
) -> Result<DepositedForm, String> {
    deposit_form(driver, name, octets).map_err(|refusal| refusal.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// SHA-256 of `b"abc"`, from FIPS 180-4's own published example. It is here so the address law
    /// is checked against an outside frame rather than against another call to the same digest —
    /// `address == content_address(octets)` is a tautology and proves nothing about the address.
    const ABC_ADDRESS: &str = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";

    /// A scratch root per test, so two tests writing at once cannot see each other's octets and no
    /// test writes into the repository's real `output/`.
    ///
    /// The *driver* name is carried per test too, by [`scratch_driver`]. That is not decoration: it
    /// is what makes these tests hermetic against a mutation that drops the root. Under such a
    /// mutation every test used to write to one relative `./driver/` path and they raced, so the
    /// mutation killed four tests in one run and six in the next. A mutation table row that is not
    /// reproducible is not evidence, and the cause was the fixture, not the mutation.
    fn scratch(tag: &str) -> PathBuf {
        let root = std::env::temp_dir().join(format!("holonics-form-mouth-{tag}"));
        let _ = std::fs::remove_dir_all(&root);
        root
    }

    /// A driver name unique to one test, so no two tests in this module can ever compose one path
    /// even if the root is removed from the composition entirely.
    fn scratch_driver(tag: &str) -> String {
        format!("form_mouth_{}", tag.replace('-', "_"))
    }

    // -----------------------------------------------------------------------------------------
    // the name law

    #[test]
    fn the_declared_path_is_root_then_driver_then_name_dash_address_dot_form() {
        let path = declared_path_under(
            Path::new("output"),
            "eros_text_training",
            "machine-rest",
            b"abc",
        )
        .expect("both names are declared");
        assert_eq!(
            path,
            PathBuf::from("output")
                .join("eros_text_training")
                .join(format!("machine-rest-{ABC_ADDRESS}.form"))
        );
    }

    /// The second frame for the path law. Under one root a composition that dropped the root, or
    /// that swapped the driver and the name, can still look right; under two roots and two
    /// driver/name pairs it cannot.
    #[test]
    fn the_path_law_carries_its_root_and_keeps_driver_and_name_in_order() {
        let under_output =
            declared_path_under(Path::new("output"), "alpha", "beta", b"abc").expect("names");
        let under_other =
            declared_path_under(Path::new("elsewhere"), "alpha", "beta", b"abc").expect("names");
        assert_ne!(under_output, under_other);
        assert!(under_output.starts_with("output"));
        assert!(under_other.starts_with("elsewhere"));

        // driver and name are not interchangeable
        let forward =
            declared_path_under(Path::new("output"), "alpha", "beta", b"abc").expect("names");
        let reversed =
            declared_path_under(Path::new("output"), "beta", "alpha", b"abc").expect("names");
        assert_ne!(forward, reversed);
        assert_eq!(
            forward,
            PathBuf::from(format!("output/alpha/beta-{ABC_ADDRESS}.form"))
        );
    }

    /// The positive control for every refusal below. A law that refused *everything* would pass all
    /// the refusal tests and be worthless; this is the case that must be accepted.
    #[test]
    fn a_declared_name_is_accepted() {
        for name in [
            "a",
            "z9",
            "eros_text_training",
            "machine-rest",
            "0",
            "a_b-c9",
        ] {
            assert!(
                declare_name("driver", name).is_ok(),
                "`{name}` is inside the declared alphabet"
            );
        }
    }

    #[test]
    fn a_traversal_is_refused_by_the_alphabet_not_by_a_special_case() {
        for name in ["..", ".", "a/b", "a\\b", "/etc", "C:", "a.b"] {
            match declare_name("driver", name) {
                Err(FormMouthRefusal::NameUndeclared { .. }) => {}
                other => panic!("`{name}` must be refused as an undeclared octet, got {other:?}"),
            }
        }
    }

    #[test]
    fn an_uppercase_or_space_bearing_name_is_refused() {
        for name in ["Driver", "two words", "café"] {
            assert!(matches!(
                declare_name("form", name),
                Err(FormMouthRefusal::NameUndeclared { .. })
            ));
        }
    }

    #[test]
    fn an_empty_name_is_refused_and_says_which_part() {
        assert_eq!(
            declared_path_under(Path::new("output"), "", "rest", b"octets"),
            Err(FormMouthRefusal::NameEmpty { part: "driver" })
        );
        assert_eq!(
            declared_path_under(Path::new("output"), "driver", "", b"octets"),
            Err(FormMouthRefusal::NameEmpty { part: "form" })
        );
    }

    #[test]
    fn a_name_opening_on_a_separator_is_refused() {
        for name in ["-rest", "_rest"] {
            match declare_name("form", name) {
                Err(FormMouthRefusal::NameOpensOnSeparator { .. }) => {}
                other => panic!("`{name}` opens on a separator, got {other:?}"),
            }
        }
        // and a separator anywhere else is fine — otherwise this test would be indistinguishable
        // from a blanket ban on separators
        assert!(declare_name("form", "r-e_s-t").is_ok());
    }

    // -----------------------------------------------------------------------------------------
    // the content address

    /// The address is the digest of the content, checked against FIPS 180-4's published value for
    /// `"abc"` — a frame outside this module. Without the published vector, every assertion about
    /// the address would be this module comparing the digest to itself.
    #[test]
    fn the_content_address_is_the_published_digest_of_the_content() {
        assert_eq!(content_address(b"abc"), ABC_ADDRESS);
        assert_eq!(content_address(b"abc").len(), 64);
        assert!(
            content_address(b"abc")
                .bytes()
                .all(|octet| matches!(octet, b'0'..=b'9' | b'a'..=b'f')),
            "the address is lowercase hex"
        );
    }

    /// The address depends on the *content*, not on its length and not on the site name. Two octet
    /// populations of equal length differing in one bit must take two addresses; an address derived
    /// from `octets.len()`, or a constant, dies here.
    #[test]
    fn the_address_moves_when_one_octet_moves_and_the_length_does_not() {
        let left = content_address(b"the same length");
        let right = content_address(b"the same lengti");
        assert_ne!(left, right);
        assert_eq!(b"the same length".len(), b"the same lengti".len());
        // and it does not depend on the site name: the same octets under two names take one address
        assert_eq!(content_address(b"identical"), content_address(b"identical"));
    }

    /// Content addressing must not need an escape hatch through the law it composes under. The
    /// whole file stem `<name>-<address>` is itself a declared name, so a reader of the alphabet
    /// law can read a deposited file name and a driver name by the same clause. A digest encoded in
    /// base64 or uppercase hex fails this.
    #[test]
    fn the_content_address_is_itself_a_declared_name() {
        let path = declared_path_under(Path::new("output"), "some_driver", "a-rest", b"octets")
            .expect("a path");
        let stem = path
            .file_stem()
            .and_then(|stem| stem.to_str())
            .expect("a stem");
        assert_eq!(stem, format!("a-rest-{}", content_address(b"octets")));
        assert!(
            declare_name("form", stem).is_ok(),
            "the composed stem `{stem}` must itself be a declared name"
        );
    }

    // -----------------------------------------------------------------------------------------
    // the write

    #[test]
    fn the_octets_reach_the_declared_path_and_come_back_identical() {
        let root = scratch("reaches");
        let driver = scratch_driver("reaches");
        let octets: Vec<u8> = (0..=255u8).collect();
        let deposited =
            deposit_form_under(&root, &driver, "a-rest", &octets).expect("the octets deposit");
        assert_eq!(
            deposited.path,
            root.join(&driver)
                .join(format!("a-rest-{}.form", content_address(&octets)))
        );
        assert_eq!(deposited.address, content_address(&octets));
        assert_eq!(deposited.octets, octets);
        assert_eq!(std::fs::read(&deposited.path).expect("the file"), octets);
        // the nonzero control: the artifact on disk is provably not empty, and it is exactly as
        // long as what was handed in
        assert_eq!(
            std::fs::metadata(&deposited.path).expect("metadata").len(),
            256
        );
        std::fs::remove_dir_all(&root).ok();
    }

    /// Two different octet populations under **one site name** must land in two different files.
    ///
    /// This is the whole of the 511-forms-into-one-file loss, as a test. A mouth that composed its
    /// path from `<name>` alone passes every other test in this module and fails here.
    #[test]
    fn two_forms_from_one_site_take_two_addresses_and_both_survive() {
        let root = scratch("one-site");
        let driver = scratch_driver("one-site");
        let first = deposit_form_under(&root, &driver, "machine-rest", b"the-longer-earlier-form")
            .expect("first");
        let second = deposit_form_under(&root, &driver, "machine-rest", b"short").expect("second");
        assert_ne!(first.path, second.path);
        assert_eq!(
            std::fs::read(&first.path).expect("the first form survived the second"),
            b"the-longer-earlier-form"
        );
        assert_eq!(std::fs::read(&second.path).expect("second"), b"short");
        let deposited: Vec<_> = std::fs::read_dir(root.join(&driver))
            .expect("the driver directory")
            .map(|entry| entry.expect("an entry").file_name())
            .collect();
        assert_eq!(
            deposited.len(),
            2,
            "one site sealed two distinct forms and the directory holds {deposited:?}"
        );
        std::fs::remove_dir_all(&root).ok();
    }

    /// The same form deposited twice from one site takes one address, and the file is unchanged.
    /// `THE_ASSEMBLY.md:108`'s *"nothing is written twice"* read as a statement about content —
    /// which is the only reading achievable without a lock, and the one `:108` names.
    #[test]
    fn the_same_form_deposited_twice_takes_one_address() {
        let root = scratch("idempotent");
        let driver = scratch_driver("idempotent");
        let first = deposit_form_under(&root, &driver, "machine-rest", b"one form").expect("first");
        let again = deposit_form_under(&root, &driver, "machine-rest", b"one form").expect("again");
        assert_eq!(first.path, again.path);
        assert_eq!(first.address, again.address);
        let deposited: Vec<_> = std::fs::read_dir(root.join(&driver))
            .expect("the driver directory")
            .map(|entry| entry.expect("an entry").file_name())
            .collect();
        assert_eq!(deposited.len(), 1, "{deposited:?}");
        std::fs::remove_dir_all(&root).ok();
    }

    /// Two different sites under one driver stay apart even when they seal identical octets — the
    /// site name is not redundant with the address.
    #[test]
    fn two_sites_sealing_identical_octets_stay_apart() {
        let root = scratch("two-sites");
        let driver = scratch_driver("two-sites");
        let rest = deposit_form_under(&root, &driver, "machine-rest", b"same").expect("rest");
        let checkpoint =
            deposit_form_under(&root, &driver, "checkpoint", b"same").expect("checkpoint");
        assert_ne!(rest.path, checkpoint.path);
        assert_eq!(rest.address, checkpoint.address);
        std::fs::remove_dir_all(&root).ok();
    }

    #[test]
    fn an_empty_form_is_refused_and_no_file_is_founded() {
        let root = scratch("empty");
        let driver = scratch_driver("empty");
        let refusal = deposit_form_under(&root, &driver, "rest", b"")
            .expect_err("zero octets are not a form");
        match refusal {
            FormMouthRefusal::FormEmpty { under, name } => {
                assert_eq!(under, root.join(&driver));
                assert_eq!(name, "rest");
            }
            other => panic!("the empty-form law must fire here, got {other:?}"),
        }
        assert!(!root.exists(), "a refused deposit founds nothing at all");
    }

    #[test]
    fn a_refused_name_founds_no_directory() {
        let root = scratch("no-dir");
        assert!(deposit_form_under(&root, "..", "rest", b"octets").is_err());
        assert!(!root.exists(), "a refused name founds no directory at all");
    }

    /// The read-back law, fired. A directory standing where the file should go makes the write
    /// itself fail; this is the reachable half of that law and it proves the refusal is wired to
    /// the write rather than decorative.
    #[test]
    fn a_write_that_cannot_land_is_refused_by_name() {
        let root = scratch("blocked");
        let driver = scratch_driver("blocked");
        let blocked = declared_path_under(&root, &driver, "rest", b"octets").expect("a path");
        std::fs::create_dir_all(&blocked).expect("a blocking dir");
        let refusal =
            deposit_form_under(&root, &driver, "rest", b"octets").expect_err("cannot land");
        assert!(
            matches!(refusal, FormMouthRefusal::WriteRefused { .. }),
            "got {refusal:?}"
        );
        std::fs::remove_dir_all(&root).ok();
    }

    /// The read-back law, fired on a write that **succeeds** and still does not hold the octets.
    ///
    /// A symlink to `/dev/null` is the honest induction: the write returns `Ok` and reports every
    /// octet taken, and the read returns nothing. That is precisely the shape of the defect this law
    /// exists for — the driver's `sha256` is a perfectly correct hash of octets that are not in the
    /// file beside it — and without this case the read-back comparison would be a branch no test
    /// ever enters, which is `CLAUDE.md` §8's *a law that returns zero proves nothing about itself*
    /// applied to the law's own coverage.
    #[cfg(unix)]
    #[test]
    fn a_write_that_succeeds_without_holding_the_octets_is_refused() {
        let root = scratch("devnull");
        let driver = scratch_driver("devnull");
        let path = declared_path_under(&root, &driver, "rest", b"octets").expect("a path");
        std::fs::create_dir_all(path.parent().expect("a parent")).expect("the driver directory");
        std::os::unix::fs::symlink("/dev/null", &path).expect("a symlink to /dev/null");
        let refusal =
            deposit_form_under(&root, &driver, "rest", b"octets").expect_err("nothing landed");
        match refusal {
            FormMouthRefusal::NotReadBackIdentical {
                written, read_back, ..
            } => {
                assert_eq!(written, 6);
                assert_eq!(read_back, 0);
            }
            other => panic!("the read-back law must fire here, got {other:?}"),
        }
        std::fs::remove_dir_all(&root).ok();
    }

    // -----------------------------------------------------------------------------------------
    // the default frame — the one every driver uses
    //
    // `deposit_form` and `deposit_form_or_message` are what the ~39 driver sites call, and until
    // these two tests existed neither was executed by anything: the root could be replaced with
    // `MUTANT_WRONG_ROOT` and the suite stayed green. Both refusals below compose the full path
    // under `DEPOSIT_ROOT` and touch no filesystem, so the default frame is exercised without any
    // test ever writing inside the repository. The default frame's *write* is driven end to end in
    // `soma/tools/holon-plate/tests/plate_mouth.rs`, from a working directory it owns.

    #[test]
    fn the_production_entry_point_composes_under_the_deposit_root() {
        let refusal = deposit_form("eros_text_training", "machine-rest", b"")
            .expect_err("zero octets are not a form");
        match refusal {
            FormMouthRefusal::FormEmpty { under, name } => {
                assert_eq!(
                    under,
                    PathBuf::from(DEPOSIT_ROOT).join("eros_text_training")
                );
                assert_eq!(under, PathBuf::from("output/eros_text_training"));
                assert_eq!(name, "machine-rest");
            }
            other => panic!("the default frame must refuse an empty form, got {other:?}"),
        }
        // and the composing half, on the same frame: the path a driver's octets take
        assert_eq!(
            declared_path("eros_text_training", "machine-rest", b"abc").expect("a path"),
            PathBuf::from(format!(
                "output/eros_text_training/machine-rest-{ABC_ADDRESS}.form"
            ))
        );
    }

    /// The `String`-carrier spelling is what 38 of the 39 driver sites call. It must carry the same
    /// law, refuse the same inputs, and render the default-rooted path in its message — a delegate
    /// that fabricated an `Ok` for anything dies here.
    #[test]
    fn the_message_carrying_entry_point_refuses_what_the_law_refuses() {
        let message = deposit_form_or_message("eros_text_training", "machine-rest", b"")
            .expect_err("zero octets are not a form");
        assert!(
            message.contains("output/eros_text_training"),
            "the refusal names the default-rooted directory: {message}"
        );
        assert_eq!(
            message,
            deposit_form("eros_text_training", "machine-rest", b"")
                .expect_err("the same refusal")
                .to_string(),
            "the two carriers must render one law"
        );
        // the name law reaches the production entry point too, and refuses before any directory is
        // founded — `..` here would otherwise compose `output/../rest-<address>.form`
        match deposit_form_or_message("..", "rest", b"octets") {
            Err(message) => assert!(message.contains("REFUSED"), "{message}"),
            Ok(deposited) => panic!("`..` deposited to {}", deposited.path.display()),
        }
    }

    // -----------------------------------------------------------------------------------------
    // the refusals render their own cause

    /// Two refusals differing **only** in the offending octet must render differently.
    ///
    /// The previous shape of this test asserted `rendered.contains('/')`, which the format-string
    /// literal and the `{name}` interpolation both satisfy on their own: deleting `*octet as char`
    /// from the `Display` impl entirely left the test green. Holding `name` fixed and moving only
    /// `octet` is the only comparison in which the octet is the variable.
    #[test]
    fn a_refusal_renders_the_octet_that_caused_it() {
        let rendered = |octet: u8| {
            FormMouthRefusal::NameUndeclared {
                part: "driver",
                name: "a-b".to_owned(),
                octet,
            }
            .to_string()
        };
        let slash = rendered(b'/');
        let colon = rendered(b':');
        assert_ne!(
            slash, colon,
            "two refusals differing only in the offending octet render identically, so the octet \
             is not rendered"
        );
        assert!(slash.contains("'/'"), "{slash}");
        assert!(colon.contains("':'"), "{colon}");
        // and the name is rendered too, which is a different claim from the octet being rendered
        assert!(slash.contains("a-b"), "{slash}");
    }

    #[test]
    fn a_read_back_refusal_renders_both_lengths_and_its_path() {
        let rendered = FormMouthRefusal::NotReadBackIdentical {
            path: PathBuf::from("output/d/r-0123.form"),
            written: 900,
            read_back: 128,
        }
        .to_string();
        assert!(rendered.contains("900"), "{rendered}");
        assert!(rendered.contains("128"), "{rendered}");
        assert!(rendered.contains("output/d/r-0123.form"), "{rendered}");
        // 900 and 128 are not interchangeable: the message says which is which
        let written_at = rendered.find("900").expect("the written count");
        let read_back_at = rendered.find("128").expect("the read-back count");
        assert!(written_at < read_back_at, "{rendered}");
    }

    #[test]
    fn an_empty_form_refusal_renders_the_site_and_the_directory() {
        let rendered = FormMouthRefusal::FormEmpty {
            under: PathBuf::from("output/eros_text_training"),
            name: "machine-rest".to_owned(),
        }
        .to_string();
        assert!(rendered.contains("output/eros_text_training"), "{rendered}");
        assert!(rendered.contains("machine-rest"), "{rendered}");
    }
}
