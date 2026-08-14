//! The falsifier, executed.
//!
//! > *Corrupt one deposited octet and confirm **refusal**. Advance the machine one step past its
//! > rest and confirm a **report**, not a refusal. If both produce the same response, the
//! > distinction that caught the path-fold contamination has not been ported.*
//! > — `blueprint/THE_ROADMAP.md`, "Deposit and closure drift cross to Rust"
//!
//! Both cases are exercised, and a third that runs them together: a verifier that has only ever
//! seen clean input returns zero and proves nothing about itself (`CLAUDE.md` §8, a law that
//! returns zero proves nothing about itself).

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU32, Ordering};

use crate::manifest::{Manifest, ManifestRefusal, MANIFEST_NAME};
use crate::plan::Plan;
use crate::registry::{deposit, fold_closure, verify, Verdict};
use crate::sha256::file_digest_hex;
use crate::RelPath;

// ---------------------------------------------------------------------------------------------
// a scratch ecology, no dev-dependencies

static NEXT: AtomicU32 = AtomicU32::new(0);

struct Scratch(PathBuf);

impl Scratch {
    fn new(label: &str) -> Self {
        let unique = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "soma-standing-deposit-{}-{label}-{unique}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).expect("scratch root");
        Self(path)
    }

    fn root(&self) -> PathBuf {
        self.0.join("tree")
    }

    fn standing(&self) -> PathBuf {
        self.0.join("standing")
    }

    fn write(&self, relative: &str, contents: &str) {
        let path = self.root().join(relative);
        fs::create_dir_all(path.parent().expect("parent")).expect("parent");
        fs::write(path, contents).expect("write");
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

const PLAN: &str = "\
# two foundings so that drift in one is visibly not drift in the other
founding proof.production
executable bin/driver
mount corpus/one.lean
mount corpus/two.lean
return out/theorem-a.lean
return out/theorem-b.lean
derived out/STDOUT.txt

founding phase.atlas
mount corpus/one.lean
return out/tiger.ppm
";

/// A standing, freshly rested. Returns the scratch so the caller keeps it alive.
fn rest() -> Scratch {
    let scratch = Scratch::new("rest");
    scratch.write(
        "bin/driver",
        "the deed binary, standing in for a build artifact\n",
    );
    scratch.write("corpus/one.lean", "theorem one : True := trivial\n");
    scratch.write("corpus/two.lean", "theorem two : True := trivial\n");
    scratch.write("out/theorem-a.lean", "theorem a : 1 + 1 = 2 := rfl\n");
    scratch.write("out/theorem-b.lean", "theorem b : 2 + 2 = 4 := rfl\n");
    scratch.write("out/tiger.ppm", "P3 1 1 255 200 120 40\n");
    scratch.write("plan.txt", PLAN);

    let plan = Plan::read(&scratch.root().join("plan.txt")).expect("plan reads");
    let manifest = deposit(&scratch.root(), &plan, &scratch.standing()).expect("deposit");
    assert_eq!(manifest.deposits.len(), 3);
    assert_eq!(manifest.foundings.len(), 2);
    assert_eq!(
        manifest
            .headers
            .get("derived_returns_not_deposited")
            .map(String::as_str),
        Some("1"),
        "the one declared-and-refused derived return is counted, not silently dropped"
    );
    scratch
}

fn verdict_of(scratch: &Scratch) -> Verdict {
    verify(&scratch.root(), &scratch.standing()).expect("manifest reads")
}

// ---------------------------------------------------------------------------------------------
// the control: a clean standing

#[test]
fn a_freshly_rested_standing_holds_with_every_closure_current() {
    let scratch = rest();
    let verdict = verdict_of(&scratch);
    assert!(!verdict.refuses(), "{}", verdict.render());
    assert_eq!(verdict.checked, 3);
    assert_eq!(verdict.content_drift, 0);
    assert_eq!(verdict.absent, 0);
    assert_eq!(verdict.closure_held, 3);
    assert_eq!(verdict.closure_drift, 0);
    assert_eq!(verdict.foundings_drifted, 0);
}

// ---------------------------------------------------------------------------------------------
// falsifier, first half: corrupt one deposited octet

#[test]
fn one_corrupted_deposited_octet_refuses() {
    let scratch = rest();
    let deposited = scratch.standing().join("out/theorem-a.lean");
    let mut octets = fs::read(&deposited).expect("read deposit");
    let before = octets.clone();
    octets[9] ^= 0x01; // exactly one octet, exactly one bit
    assert_eq!(octets.len(), before.len(), "length is unchanged");
    assert_eq!(
        octets.iter().zip(&before).filter(|(a, b)| a != b).count(),
        1,
        "exactly one octet differs"
    );
    fs::write(&deposited, &octets).expect("corrupt deposit");

    let verdict = verdict_of(&scratch);
    assert!(verdict.refuses(), "one corrupt octet must refuse");
    assert_eq!(verdict.content_drift, 1);
    assert_eq!(verdict.absent, 0);
    assert_eq!(
        verdict.closure_drift, 0,
        "nothing in the machine moved; this is corruption, not advance"
    );
    assert!(verdict.render().contains("verdict=REFUSED"));
    assert!(verdict
        .lines
        .iter()
        .any(|line| line.starts_with("content_drift out/theorem-a.lean proof.production")));
}

#[test]
fn an_absent_deposit_refuses_because_that_is_the_loss_itself() {
    let scratch = rest();
    fs::remove_file(scratch.standing().join("out/tiger.ppm")).expect("remove deposit");
    let verdict = verdict_of(&scratch);
    assert!(verdict.refuses());
    assert_eq!(verdict.absent, 1);
    assert_eq!(verdict.content_drift, 0);
    assert!(verdict
        .lines
        .iter()
        .any(|line| line == "absent out/tiger.ppm phase.atlas"));
}

// ---------------------------------------------------------------------------------------------
// falsifier, second half: advance the machine one step past its rest

#[test]
fn advancing_the_machine_one_step_reports_and_does_not_refuse() {
    let scratch = rest();
    // One step: a mounted input gains an octet. `corpus/two.lean` is material for
    // `proof.production` only, so `phase.atlas` must be untouched.
    scratch.write(
        "corpus/two.lean",
        "theorem two : True := trivial\ntheorem three : True := trivial\n",
    );

    let verdict = verdict_of(&scratch);
    assert!(
        !verdict.refuses(),
        "an advance is not a corruption:\n{}",
        verdict.render()
    );
    assert_eq!(verdict.content_drift, 0);
    assert_eq!(verdict.absent, 0);
    assert_eq!(verdict.closure_drift, 2, "both of that founding's deposits");
    assert_eq!(verdict.closure_held, 1, "the untouched founding is current");
    assert_eq!(verdict.foundings_drifted, 1);
    assert!(verdict.render().contains("verdict=HELD"));
    assert!(verdict
        .lines
        .iter()
        .any(|line| line.starts_with("closure_drift proof.production recorded=")));
}

#[test]
fn a_removed_mount_is_closure_drift_and_still_does_not_refuse() {
    let scratch = rest();
    fs::remove_file(scratch.root().join("corpus/one.lean")).expect("remove a mount");
    let verdict = verdict_of(&scratch);
    assert!(!verdict.refuses(), "{}", verdict.render());
    assert_eq!(verdict.closure_drift, 3, "both foundings mount it");
    assert_eq!(verdict.foundings_drifted, 2);
    assert!(verdict
        .lines
        .iter()
        .any(|line| line == "closure_material_absent proof.production corpus/one.lean"));
}

// ---------------------------------------------------------------------------------------------
// the two species are separable, which is the whole claim

#[test]
fn the_two_species_are_separable_in_one_run() {
    let scratch = rest();
    // corruption in one founding
    let deposited = scratch.standing().join("out/tiger.ppm");
    let mut octets = fs::read(&deposited).expect("read");
    octets[3] ^= 0x20;
    fs::write(&deposited, &octets).expect("corrupt");
    // advance in the other
    scratch.write("bin/driver", "the deed binary, rebuilt\n");

    let verdict = verdict_of(&scratch);
    assert!(verdict.refuses(), "the corruption refuses");
    assert_eq!(verdict.content_drift, 1, "and only the corrupt one refuses");
    assert_eq!(
        verdict.closure_drift, 2,
        "the advance is reported on the other founding's two deposits"
    );
    assert_eq!(
        verdict.foundings_drifted, 1,
        "the executable is material for proof.production only"
    );
    // The refusal names the corrupt deposit; the report names the advanced founding. Two
    // different lines, two different verbs.
    assert!(verdict
        .lines
        .iter()
        .any(|line| line.starts_with("content_drift out/tiger.ppm")));
    assert!(verdict
        .lines
        .iter()
        .any(|line| line.starts_with("closure_drift proof.production")));
}

// ---------------------------------------------------------------------------------------------
// the closure's own laws

#[test]
fn the_closure_folds_material_in_declared_order() {
    let scratch = Scratch::new("order");
    scratch.write("a", "alpha\n");
    scratch.write("b", "beta\n");
    let a = RelPath::parse("a").unwrap();
    let b = RelPath::parse("b").unwrap();
    let (forward, _) = fold_closure(&scratch.root(), &[a.clone(), b.clone()]);
    let (backward, _) = fold_closure(&scratch.root(), &[b, a]);
    assert_ne!(
        forward, backward,
        "a founding that mounts in a different order is a different founding"
    );
}

#[test]
fn the_closure_does_not_fold_an_absolute_frame() {
    // The same tree at two different absolute locations must deposit identically. `CLAUDE.md` §0:
    // ten C++ card adapters folded the filesystem path into the rest integrity.
    let here = rest();
    let there = Scratch::new("elsewhere");
    fs::create_dir_all(there.root()).expect("root");
    copy_tree(&here.root(), &there.root());
    let plan = Plan::read(&there.root().join("plan.txt")).expect("plan");
    let elsewhere = deposit(&there.root(), &plan, &there.standing()).expect("deposit");
    let original = Manifest::read(&here.standing().join(MANIFEST_NAME)).expect("manifest");
    assert_ne!(
        here.root(),
        there.root(),
        "the two checkouts are at different absolute paths"
    );
    assert_eq!(
        original.render(),
        elsewhere.render(),
        "two checkouts, one manifest, octet for octet"
    );
}

fn copy_tree(from: &Path, to: &Path) {
    for entry in fs::read_dir(from).expect("read_dir") {
        let entry = entry.expect("entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("file_type").is_dir() {
            fs::create_dir_all(&target).expect("mkdir");
            copy_tree(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), &target).expect("copy");
        }
    }
}

// ---------------------------------------------------------------------------------------------
// the independent-implementation cross-check
//
// `CLAUDE.md` §8: where an independent implementation exists, use it. CMake's `file(SHA256)` wrote
// 123 content hashes into `archive/cpp-engine/standing/MANIFEST.txt` and the deposited octets are
// still there. This verifier reads that manifest natively and rehashes every one of them. If the
// SHA-256 written out in `sha256.rs` were wrong, all 123 would drift.

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(3)
        .expect("repository root")
        .to_path_buf()
}

#[test]
fn the_archived_cpp_standing_verifies_against_this_sha256() {
    let root = repository_root();
    let standing = root.join("archive/cpp-engine/standing");
    if !standing.join(MANIFEST_NAME).is_file() {
        return; // the archive is not present in this checkout
    }
    let verdict = verify(&root, &standing).expect("archived manifest reads");
    assert_eq!(
        verdict.checked, 123,
        "the archived manifest declares deposited_returns=123"
    );
    assert!(
        !verdict.refuses(),
        "CMake's 123 content hashes must reproduce under this SHA-256:\n{}",
        verdict.render()
    );
    assert_eq!(verdict.content_drift, 0);
    assert_eq!(verdict.absent, 0);
    assert_eq!(
        verdict.closure_unrecomputable, 123,
        "the archived manifest recorded closure hashes but not the material behind them, \
         so no closure there can be recomputed — that is the gap this port closes"
    );
    assert_eq!(verdict.foundings_checked, 0);
}

#[test]
fn the_archived_manifest_declares_what_the_roadmap_reads_from_it() {
    let manifest_path = repository_root().join("archive/cpp-engine/standing/MANIFEST.txt");
    if !manifest_path.is_file() {
        return;
    }
    let manifest = Manifest::read(&manifest_path).expect("reads");
    assert_eq!(
        manifest
            .headers
            .get("deposited_returns")
            .map(String::as_str),
        Some("123")
    );
    assert_eq!(
        manifest.headers.get("deposited_octets").map(String::as_str),
        Some("802855")
    );
    // The roadmap reads this field as a backlog of standing owed a deposit. It is not: the C++
    // depositor counted here the returns it deliberately REFUSED as reproducible derived bulk
    // (`HolonicDeposit.cmake:12-19, 100-103`). They lived in a build tree that no longer exists.
    assert_eq!(
        manifest
            .headers
            .get("derived_returns_not_deposited")
            .map(String::as_str),
        Some("126")
    );
}

#[test]
fn hashing_a_real_deposited_file_agrees_with_the_manifest_row() {
    let root = repository_root();
    let standing = root.join("archive/cpp-engine/standing");
    let manifest_path = standing.join(MANIFEST_NAME);
    if !manifest_path.is_file() {
        return;
    }
    let manifest = Manifest::read(&manifest_path).expect("reads");
    let row = manifest
        .deposits
        .iter()
        .find(|row| row.path.as_str() == "receipts/R1_EXACT_DEED.txt")
        .expect("R1 receipt row");
    assert_eq!(
        row.content, "556c5bab75d77c4ec75f68e4084d07acab531ea1c402524066f5e3199ff05571",
        "the row is the one CMake wrote"
    );
    let (holds, _) = file_digest_hex(&row.path.under(&standing)).expect("hash");
    assert_eq!(holds, row.content);
}

// ---------------------------------------------------------------------------------------------
// the three fail-open closures
//
// Each of these was found by an adversarial reader after the tool was reported complete, and each
// is a way for the gate to say HELD about a deposit it never looked at. The first two are the
// `CLAUDE.md` §13 rule-3 defect exactly — the superseded CMake machinery failed CLOSED on both,
// because its looser `([0-9a-f]+)` row regex matched a corrupt digest and refused it on comparison.

/// Corrupting a recorded digest used to drop the row out of `deposits` — `is_hex64` returned false,
/// the row fell through the parser's `if`, and `verify_manifest` iterates only surviving rows. The
/// deposit left the gate and the gate said HELD.
#[test]
fn a_corrupted_recorded_digest_refuses_instead_of_dropping_the_row() {
    let scratch = rest();
    let manifest_path = scratch.standing().join(MANIFEST_NAME);
    let text = fs::read_to_string(&manifest_path).expect("read manifest");

    let row = text
        .lines()
        .find(|line| line.contains("out/theorem-a.lean"))
        .expect("the row is there");
    let fields: Vec<&str> = row.split_whitespace().collect();
    // One character, inside the recorded content digest, to a non-hex character of the same width.
    let corrupt_digest = format!("z{}", &fields[1][1..]);
    let corrupted = text.replace(fields[1], &corrupt_digest);
    assert_ne!(corrupted, text, "the corruption landed");
    assert_eq!(
        corrupted.len(),
        text.len(),
        "width unchanged, so only hex-ness moved"
    );
    fs::write(&manifest_path, &corrupted).expect("write");

    match verify(&scratch.root(), &scratch.standing()) {
        Err(ManifestRefusal::CorruptDigest(_)) => {}
        Err(other) => panic!("refused for the wrong reason: {other}"),
        Ok(verdict) => panic!(
            "a corrupt digest was READ as a manifest and the gate returned a verdict:\n{}",
            verdict.render()
        ),
    }
}

/// Corruption that changes a digest's WIDTH escapes the shape test above, so the declared count is
/// the second, independent closure. It catches a row lost by any mechanism at all, including one
/// deleted outright.
#[test]
fn a_row_deleted_outright_refuses_on_the_declared_count() {
    let scratch = rest();
    let manifest_path = scratch.standing().join(MANIFEST_NAME);
    let text = fs::read_to_string(&manifest_path).expect("read manifest");
    let kept: Vec<&str> = text
        .lines()
        .filter(|line| !line.contains("out/theorem-a.lean"))
        .collect();
    fs::write(&manifest_path, format!("{}\n", kept.join("\n"))).expect("write");

    match verify(&scratch.root(), &scratch.standing()) {
        Err(ManifestRefusal::CountDisagrees {
            header,
            recorded,
            read,
        }) => {
            assert_eq!(header, "deposited_returns");
            assert_eq!((recorded, read), (3, 2));
        }
        Err(other) => panic!("refused for the wrong reason: {other}"),
        Ok(verdict) => panic!(
            "a deleted row left the manifest self-consistent:\n{}",
            verdict.render()
        ),
    }
}

/// Both verifiers walked the manifest and asked the tree about each row. Neither walked the tree
/// and asked the manifest, so the standing could hold a file no row binds and every row still pass.
#[test]
fn a_file_no_row_binds_refuses_even_though_every_row_holds() {
    let scratch = rest();
    let stray = scratch.standing().join("out/unbound.lean");
    fs::write(&stray, "theorem nobody_deposited_me : True := trivial\n").expect("plant");

    let verdict = verdict_of(&scratch);
    assert_eq!(verdict.content_drift, 0, "every row still holds");
    assert_eq!(verdict.absent, 0, "nothing is missing");
    assert_eq!(verdict.closure_held, 3, "the closures are current");
    assert_eq!(verdict.unmanifested, 1);
    assert!(
        verdict
            .lines
            .iter()
            .any(|line| line == "unmanifested out/unbound.lean"),
        "the stray is named, not just counted: {:?}",
        verdict.lines
    );
    assert!(verdict.refuses(), "{}", verdict.render());
}

/// The territory is the roots the rows occupy, so the manifest and the plan beside it are not
/// strays. A name-exclusion list would have rotted the first time a bookkeeping file was added.
#[test]
fn the_manifest_and_the_plan_are_not_strays_in_their_own_standing() {
    let scratch = rest();
    fs::write(scratch.standing().join("README.md"), "what rests here\n").expect("write");
    let verdict = verdict_of(&scratch);
    assert_eq!(verdict.unmanifested, 0, "{}", verdict.render());
    assert!(!verdict.refuses());
}

/// Dropping a return from the plan must REMOVE it, not leave it behind — otherwise `deposit` emits
/// a standing that its own `verify` refuses.
#[test]
fn a_return_dropped_from_the_plan_is_removed_from_the_standing() {
    let scratch = rest();
    let dropped = scratch.standing().join("out/theorem-b.lean");
    assert!(dropped.is_file(), "it was deposited by the first rest");

    let reduced = PLAN.replace("return out/theorem-b.lean\n", "");
    assert_ne!(reduced, PLAN, "the plan really shrank");
    scratch.write("plan.txt", &reduced);
    let plan = Plan::read(&scratch.root().join("plan.txt")).expect("plan reads");
    let manifest = deposit(&scratch.root(), &plan, &scratch.standing()).expect("re-deposit");

    assert_eq!(manifest.deposits.len(), 2);
    assert!(
        !dropped.exists(),
        "a superseded return fails closed: it is removed, not left to be re-cited"
    );
    let verdict = verdict_of(&scratch);
    assert!(!verdict.refuses(), "{}", verdict.render());
    assert_eq!(verdict.unmanifested, 0);
}

/// A plan that founded nothing may not empty a standing. The prune is bounded by the new
/// manifest's own rows, and with no rows there is no territory to prune.
#[test]
fn a_plan_that_founds_nothing_cannot_empty_a_standing() {
    let scratch = rest();
    scratch.write("plan.txt", "# nothing at all\n");
    let plan = Plan::read(&scratch.root().join("plan.txt")).expect("plan reads");
    let manifest = deposit(&scratch.root(), &plan, &scratch.standing()).expect("deposit");
    assert!(manifest.deposits.is_empty());
    assert!(
        scratch.standing().join("out/theorem-a.lean").is_file(),
        "an empty plan is not an instruction to destroy the standing"
    );
}
