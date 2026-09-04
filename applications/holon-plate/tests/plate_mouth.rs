//! The plate mouth, executed end to end across the dependency edge that forbids the obvious wiring.
//!
//! ```text
//!   a life driver          the disk                        a holon-plate reader
//!   ─────────────          ────────                        ────────────────────
//!   encode_native_bytes ─▶ .local/artifacts/<driver>/<name>-<sha>.form ─▶ deposit ─▶ .holon ─▶ resume ─▶ a body
//!          │                                                                                   │
//!          └── sha256 into its JSON receipt — the same string as <sha>            present a deed ┘
//! ```
//!
//! `archive/plans/THE_ASSEMBLY.md` fact **F1**: `holon-plate` depends on `life`, so a `life` example can
//! never call `holon_plate::deposit`. The seam is closed by a file and no new dependency. This test
//! stands on the far side of that edge — it may name `life`, and does — and drives the whole path
//! the shell drives, so the seam is checked by `cargo test` rather than only by someone remembering
//! to run two commands.
//!
//! # What each test here can be wrong about
//!
//! The mouth is the easiest thing in this repository to make vacuously green. A test that wrote
//! octets, read them back and stopped would pass forever while `resume` refused every real form. So
//! every test below crosses at least one frame boundary:
//!
//! - the **round trip** goes octets → file → `deposit` → `resume`, and `resume` re-takes the form
//!   from a body it mounted rather than comparing the octets it was handed;
//! - the **refusal control** proves the path can say no — a form deposited under the wrong tag is
//!   refused, so a passing round trip is evidence rather than the only reachable outcome;
//! - the **zero-return control** requires the re-lit body to move a census field under a deed,
//!   which is `CLAUDE.md` §8 pointed at this seam: *a law that returns zero proves nothing about
//!   itself*;
//! - the **nonzero control** requires the census the body reports to carry a field that is provably
//!   not zero, so "every field is 0 and they agree" cannot be what the round trip established;
//! - the **production frame** drives `life::form_mouth::deposit_form_or_message` — the entry point
//!   all ~39 driver sites actually call, under its own default root — from a working directory this
//!   test owns. Without it the default root could be replaced with `MUTANT_WRONG_ROOT`, or the
//!   whole production entry point replaced with a fabricated `Ok` that writes nothing, and this
//!   suite stayed green.
//!
//! # What the fixtures here are, exactly
//!
//! Two form species reach this mouth. `ERST` is produced below by the same three calls
//! `eros_text_training.rs:930` makes (`rest_image` → `encode_native_bytes`), on this file's own
//! material. `HTEC` is produced by the same call `eros_holonic_training_ecology.rs:144` makes
//! (`TrainingEcology::encode_native_bytes`), also on this file's own material — **and that driver
//! cannot be run from this repository at all**: it takes a `SOURCE.json` that is not tracked here,
//! so no real `HTEC` form exists on disk to test against. What is established below is that the
//! mouth carries a form of each species through deposit, resume and a deed. What is **not**
//! established is that either driver's own material produces a canonical form — only running the
//! driver shows that, and `eros_text_training` is the one of the two that can be run.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, MutexGuard};

use body::num::Cog;
use holon_plate::registry::{deposit, resume};
use holon_plate::schema::{present_and_require_change, ResumeRefusal};
use holon_plate::schemas::conditioned::{ConditionedDeed, CONDITIONED_TAG};
use holon_plate::schemas::current::{CurrentDeed, CURRENT_TAG};
use holon_plate::schemas::training::{TrainingDeed, TRAINING_TAG};
use holon_plate::SchemaTag;
use holonic_engine::conditioned_derivation::{expose, ConditionedBody, DerivationQuery};
use life::conditioned_rest::ConditionedRest;
use life::form_mouth::{
    content_address, declared_path, deposit_form, deposit_form_or_message, deposit_form_under,
    DepositedForm, FormMouthRefusal, DEPOSIT_ROOT,
};
use life::holonic_training::{FaceAddress, SourceFace, TrainingEcology};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, CurrentEvent, CurrentGeometry, LiveCurrentMachine, SparseStandingSurface,
};

// ---------------------------------------------------------------------------------------------
// the two form species that reach this mouth, produced by the calls the drivers make

/// A scratch root **and** a driver name per test.
///
/// Both, not just the root. Under a mutation that drops the root from the path composition, tests
/// sharing one driver name write into one relative directory and race: that is why the previous
/// root-drop row killed four tests in one run and six in the next, and a mutation table row that is
/// not reproducible is not evidence. The cause was the fixture, not the mutation.
/// This file runs one test at a time.
///
/// `the_production_entry_point_writes_under_output_and_the_form_resumes` moves the process working
/// directory, because the default deposit root is relative to it and that is the frame every driver
/// runs in. A working directory is process-global, so any test running beside it resolves relative
/// paths somewhere it did not choose. In the unmutated mouth nothing else here uses a relative path
/// -- but "it happens not to matter" is exactly what made the earlier root-drop mutation kill four
/// tests in one run and six in the next. One lock makes the mutation table reproducible by
/// construction instead of by luck, and the whole file finishes in well under a second either way.
static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());

fn alone() -> MutexGuard<'static, ()> {
    // A test that fails poisons the lock; the next test still needs to run, and it is the failure
    // that is the report, not the poisoning.
    ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

fn scratch(tag: &str) -> (PathBuf, String) {
    let root = std::env::temp_dir().join(format!("holonics-plate-mouth-{tag}"));
    let _ = std::fs::remove_dir_all(&root);
    (root, format!("plate_mouth_{}", tag.replace('-', "_")))
}

fn face(axis: &str, ordinal: u64, value: &str) -> SourceFace {
    SourceFace::new(FaceAddress::new(axis, ordinal), value.as_bytes().to_vec())
}

fn parameters(receiver: &str) -> BTreeMap<String, String> {
    BTreeMap::from([("receiver".to_owned(), receiver.to_owned())])
}

/// An `HTEC` form, through `TrainingEcology::encode_native_bytes` — the call
/// `eros_holonic_training_ecology.rs:144` makes. The material is this file's, not that driver's;
/// see the module note.
fn training_octets() -> Vec<u8> {
    let mut ecology = TrainingEcology::new(2, 8).expect("a training ecology");
    for ordinal in 0..4u64 {
        ecology
            .cultivate(
                &[
                    face("left", ordinal, "seven"),
                    face("right", ordinal, "eight"),
                ],
                &parameters("alpha"),
                b"fifty-six",
            )
            .expect("a cultivation");
    }
    ecology.encode_native_bytes().expect("a training form")
}

/// An `ERST` form, through `machine.rest_image()?.encode_native_bytes()?` — the call nineteen of
/// the wired drivers make, `eros_text_training.rs:931` among them.
fn current_octets() -> Vec<u8> {
    current_octets_from(&[13i64, 29, 17])
}

/// The same producer over declared material, so a second `ERST` form can be made that is genuinely
/// a different form rather than a copy of the first.
fn current_octets_from(relations: &[i64]) -> Vec<u8> {
    let action = ActionCurrent::new(Cog::lit(1)).expect("a resolving action");
    let relation = |value: i64| RelationAtom::new(Cog::lit(value)).expect("a live relation");
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).expect("rank"));
    let lineages = [
        machine
            .attach(CurrentGeometry::Cell(relation(13)))
            .expect("an ingress"),
        machine
            .attach(CurrentGeometry::Cell(relation(13)))
            .expect("an ingress"),
    ];
    for value in relations.iter().copied() {
        let currents = [
            CurrentEvent::continuing(lineages[0], CurrentGeometry::Cell(relation(value)), action),
            CurrentEvent::continuing(lineages[1], CurrentGeometry::Cell(relation(value)), action),
        ];
        machine
            .receive(ContemporaryEvent::unrelated(&currents))
            .expect("a contemporary event");
    }
    machine
        .rest_image()
        .expect("a receiving-edge rest")
        .encode_native_bytes()
        .expect("a current form")
}

/// A `CDER` form, through `ConditionedRest::seal(&body)?.encode_native_bytes()?` — the two calls
/// `eros_mathematics_instance_rest.rs` makes at its seal. The material is this file's, not that
/// driver's: the driver reads fourteen declared documents and a 103-artifact deposit off disk, and a
/// test that needed those paths would be a test of the repository's contents.
fn conditioned_octets() -> Vec<u8> {
    conditioned_octets_from("the exact carrier carries a formal kernel through a transport")
}

/// The same producer over declared material, so a second `CDER` form can be made that is genuinely
/// a different form rather than a copy of the first.
fn conditioned_octets_from(surface: &str) -> Vec<u8> {
    let mut body = ConditionedBody::mount([
        (
            "alpha.lean".to_owned(),
            "namespace Soma\ntheorem carrier_alpha (h : P) : exactCarrier P := by\n  \
             have bridged := exactCarry h\nend Soma\n"
                .to_owned(),
        ),
        (
            "beta.lean".to_owned(),
            "namespace Soma\ntheorem carrier_beta (h : P) : exactCarrier P := by\n  \
             have bridged := formalKernel h\nend Soma\n"
                .to_owned(),
        ),
    ])
    .expect("the deposit mounts");
    body.condition(&[
        expose("document:one", surface),
        expose(
            "document:two",
            "an exact transport of the formal carrier meets the kernel",
        ),
    ]);
    ConditionedRest::seal(&body)
        .expect("the body seals")
        .encode_native_bytes()
        .expect("a conditioned rest form")
}

fn conditioned_deed() -> Vec<u8> {
    ConditionedDeed {
        whole: "document:three".to_owned(),
        text: "a novel receiver meets the exact carrier".to_owned(),
    }
    .encode()
}

fn training_deed() -> Vec<u8> {
    TrainingDeed {
        faces: vec![face("left", 9, "nine"), face("right", 9, "six")],
        parameters: parameters("beta"),
        consequence: b"fifty-four".to_vec(),
    }
    .encode()
}

fn current_deed() -> Vec<u8> {
    CurrentDeed {
        relation: 71,
        action: 1,
    }
    .encode()
}

/// Every (site, schema, octets, deed) species this mouth carries today. The first field is the
/// **site name** the form is sealed under, not a claim about which driver ran.
fn wired() -> Vec<(&'static str, SchemaTag, Vec<u8>, Vec<u8>)> {
    vec![
        (
            "training-ecology-rest",
            TRAINING_TAG,
            training_octets(),
            training_deed(),
        ),
        (
            "machine-rest",
            CURRENT_TAG,
            current_octets(),
            current_deed(),
        ),
        (
            "conditioned-rest",
            CONDITIONED_TAG,
            conditioned_octets(),
            conditioned_deed(),
        ),
    ]
}

/// The driver half of the seam: write the octets exactly as a wired driver does.
fn at_the_mouth(root: &Path, driver: &str, site: &str, octets: &[u8]) -> DepositedForm {
    deposit_form_under(root, driver, site, octets).expect("the mouth takes the octets")
}

// ---------------------------------------------------------------------------------------------
// the round trip

/// octets → file → `deposit` → `.holon` → `resume` → a body whose form is the same octets.
///
/// This is the whole of `THE_ASSEMBLY.md` loop **(d)**, in process. `resume` re-takes the form from
/// the body it mounted; it never compares the octets it was handed to themselves, so a codec whose
/// output is not canonical for its own schema fails here rather than passing on a hash.
#[test]
fn a_driver_form_written_to_the_mouth_deposits_and_resumes() {
    let _alone = alone();
    let (root, driver) = scratch("round-trip");
    for (site, tag, octets, _) in wired() {
        let deposited = at_the_mouth(&root, &driver, site, &octets);

        // a second process would read the file; this reads the file
        let from_disk = std::fs::read(&deposited.path).expect("the deposited form");
        assert_eq!(from_disk, octets, "{site}: the mouth carried the octets");

        let plate = deposit(tag, &from_disk).unwrap_or_else(|refusal| {
            panic!("{site}: {tag} refused its own driver's form:\n{refusal}")
        });
        assert_eq!(plate.form_octets, octets.len());

        let relit = resume(&plate.plate)
            .unwrap_or_else(|refusal| panic!("{site}: resume refused:\n{refusal}"));
        assert_eq!(relit.tag, tag);
        assert_eq!(
            relit.body.form().expect("the re-lit body's form"),
            octets,
            "{site}: the body that came out carries the octets that went in"
        );
    }
    std::fs::remove_dir_all(&root).ok();
}

/// The nonzero control. A census whose every field is `0` would agree with itself across both
/// frames and establish nothing, so at least one field must be provably nonzero — and it must be a
/// field of the *body*, recomputed on the far side, not a field copied out of the plate.
///
/// There is no `!census.is_empty()` assertion here any more. Both schemas build their census with a
/// fixed `Census::found([...])` literal — seven names for `ERST`, five for `HTEC` — so a non-empty
/// census is a theorem about the carrier and could not have come out otherwise. `CLAUDE.md` §8:
/// a receipt that could not have come out otherwise carries no evidence.
#[test]
fn the_resumed_census_is_not_all_zero() {
    let _alone = alone();
    let (root, driver) = scratch("nonzero");
    for (site, tag, octets, _) in wired() {
        let deposited = at_the_mouth(&root, &driver, site, &octets);
        let from_disk = std::fs::read(&deposited.path).expect("the deposited form");
        let plate = deposit(tag, &from_disk).expect("a deposit");
        let relit = resume(&plate.plate).expect("a resume");
        let census = relit.relit.rows();
        let nonzero: Vec<_> = census
            .iter()
            .filter(|(_, value)| *value != 0)
            .map(|(field, value)| format!("{field}={value}"))
            .collect();
        assert!(
            !nonzero.is_empty(),
            "{site}: every census field is zero, so the two frames agreeing proves nothing:\n{:?}",
            census
        );
        // and the census must not be one value wearing several names. A `census()` that returned a
        // constant would agree with itself across both frames forever and satisfy the check above.
        let distinct: std::collections::BTreeSet<u64> =
            census.iter().map(|(_, value)| *value).collect();
        assert!(
            distinct.len() > 1,
            "{site}: every census field carries the same value {:?}; a constant agrees with \
             itself across both frames and establishes nothing",
            census
        );
    }
    std::fs::remove_dir_all(&root).ok();
}

/// The zero-return control, at this seam. A body that resumed off the mouth and could not be moved
/// would satisfy every digest in the container and be inert. `CLAUDE.md` §8.
#[test]
fn a_body_resumed_off_the_mouth_takes_a_deed_and_moves() {
    let _alone = alone();
    let (root, driver) = scratch("deed");
    for (site, tag, octets, deed) in wired() {
        let deposited = at_the_mouth(&root, &driver, site, &octets);
        let from_disk = std::fs::read(&deposited.path).expect("the deposited form");
        let plate = deposit(tag, &from_disk).expect("a deposit");
        let mut relit = resume(&plate.plate).expect("a resume");
        let (before, after) = present_and_require_change(relit.body.as_mut(), &deed)
            .unwrap_or_else(|refusal| panic!("{site}: the deed was refused:\n{refusal}"));
        let moved: Vec<_> = before
            .rows()
            .iter()
            .filter(|(field, was)| after.value(field) != Some(*was))
            .map(|(field, _)| field.clone())
            .collect();
        assert!(
            !moved.is_empty(),
            "{site}: the form changed but no census field moved, so nothing the census can see \
             received anything"
        );
    }
    std::fs::remove_dir_all(&root).ok();
}

// ---------------------------------------------------------------------------------------------
// the refusal controls — without these, a green round trip is the only reachable outcome

/// A form deposited under the wrong held tag must be refused. This is the negative control for the
/// round trip: it proves the path is capable of saying no about real octets, so the round trip
/// passing is evidence and not a property of the mechanism.
#[test]
fn a_driver_form_under_the_wrong_held_tag_is_refused() {
    let _alone = alone();
    let (root, driver) = scratch("wrong-tag");
    let crossed = [
        ("training-ecology-rest", CURRENT_TAG, training_octets()),
        ("machine-rest", TRAINING_TAG, current_octets()),
        ("conditioned-rest", TRAINING_TAG, conditioned_octets()),
        ("training-ecology-rest", CONDITIONED_TAG, training_octets()),
    ];
    for (site, wrong_tag, octets) in crossed {
        let deposited = at_the_mouth(&root, &driver, site, &octets);
        let from_disk = std::fs::read(&deposited.path).expect("the deposited form");
        match deposit(wrong_tag, &from_disk) {
            Err(ResumeRefusal::FormRefused { .. })
            | Err(ResumeRefusal::FormNotCanonical { .. }) => {}
            Err(other) => panic!("{site} under {wrong_tag}: unexpected refusal {other:?}"),
            Ok(_) => panic!(
                "{site}'s form was accepted as {wrong_tag}. The mouth cannot tell two schemas \
                 apart, so nothing it accepts is evidence."
            ),
        }
    }
    std::fs::remove_dir_all(&root).ok();
}

/// A tag no reader holds is refused by name rather than guessed at, and the refusal says what *is*
/// held. The shell path (`--from XXXX:file`) reaches exactly this.
#[test]
fn an_unheld_tag_is_refused_by_name() {
    let _alone = alone();
    let unheld = SchemaTag::parse("ZZZZ").expect("four octets of [A-Z0-9]");
    match deposit(unheld, &current_octets()) {
        Err(ResumeRefusal::SchemaUnheld { tag, held, .. }) => {
            assert_eq!(tag, unheld);
            assert!(
                held.iter().any(|name| name.starts_with("ERST/")),
                "the refusal names what is held: {held:?}"
            );
        }
        other => panic!("an unheld tag must refuse by name, got {other:?}"),
    }
}

/// A truncated form must not deposit. The driver's own `sha256` would still be a perfectly correct
/// hash of the octets it *held*; only mounting can tell that what reached the disk is not a form.
#[test]
fn a_truncated_driver_form_does_not_deposit() {
    let _alone = alone();
    let octets = current_octets();
    assert!(octets.len() > 16, "the fixture form is long enough to cut");
    let truncated = &octets[..octets.len() - 8];
    assert!(
        deposit(CURRENT_TAG, truncated).is_err(),
        "a form cut short mounted anyway"
    );
    // and the control for that control: the uncut form does deposit, so the assertion above is
    // about the cut and not about the fixture
    assert!(deposit(CURRENT_TAG, &octets).is_ok());
}

/// The mouth refuses a form of zero octets, and refuses before founding anything. A driver whose
/// codec emitted nothing would otherwise leave an empty `.form` beside a confident hash.
#[test]
fn the_mouth_refuses_an_empty_form() {
    let _alone = alone();
    let (root, driver) = scratch("empty");
    let refusal = deposit_form_under(&root, &driver, "machine-rest", b"")
        .expect_err("zero octets are not a form");
    match refusal {
        FormMouthRefusal::FormEmpty { under, name } => {
            assert_eq!(under, root.join(&driver));
            assert_eq!(name, "machine-rest");
        }
        other => panic!("the empty-form law must fire here, got {other:?}"),
    }
    assert!(!root.exists(), "a refused deposit founds nothing at all");
}

/// A body resumed off the mouth **derives**; it does not replay.
///
/// The `CDER` form has no field for a query and none for a derived passage, and this drives that
/// claim rather than restating it: the body is resumed from octets alone, asked a statement, and
/// every artifact it returns is checked to be absent from the octets it was resumed from. A schema
/// that had quietly sealed its last answer beside the body would fail here and pass every other
/// test in this file.
#[test]
fn a_conditioned_body_resumed_off_the_mouth_derives_what_the_octets_do_not_carry() {
    let _alone = alone();
    let (root, driver) = scratch("conditioned-derives");
    let octets = conditioned_octets();
    let deposited = at_the_mouth(&root, &driver, "conditioned-rest", &octets);
    let from_disk = std::fs::read(&deposited.path).expect("the deposited form");
    let plate = deposit(CONDITIONED_TAG, &from_disk).expect("a deposit");
    let relit = resume(&plate.plate).expect("a resume");

    // the body is re-mounted from the resumed form's octets and asked
    let rest = ConditionedRest::decode_native_bytes(&relit.body.form().expect("the form"))
        .expect("the form reopens");
    let body = rest.mount().expect("the rest mounts");
    let derived = body
        .derive(&DerivationQuery::reaching("(h : P) : exactCarrier P"))
        .expect("derives");
    assert!(
        !derived.is_empty(),
        "the resumed body derived nothing, so nothing below is evidence"
    );
    for passage in &derived {
        assert!(
            !from_disk
                .windows(passage.name.len())
                .any(|window| window == passage.name.as_bytes()),
            "the sealed octets carry the artifact name {:?}, so this is a replay",
            passage.name
        );
    }
    std::fs::remove_dir_all(&root).ok();
}

/// Two conditioned rests from one site — the shape a driver produces when it seals once per run —
/// take two addresses and both resume as bodies.
#[test]
fn two_conditioned_rests_from_one_site_both_reach_the_far_side() {
    let _alone = alone();
    let (root, driver) = scratch("two-conditioned");
    let earlier = conditioned_octets_from("the exact carrier carries a formal kernel");
    let later = conditioned_octets_from("the exact carrier carries a formal kernel and a receiver");
    assert_ne!(earlier, later, "the two fixtures must be two forms");

    let first = at_the_mouth(&root, &driver, "conditioned-rest", &earlier);
    let second = at_the_mouth(&root, &driver, "conditioned-rest", &later);
    assert_ne!(first.path, second.path);
    for deposited in [&first, &second] {
        let from_disk = std::fs::read(&deposited.path).expect("both forms are still on disk");
        let plate = deposit(CONDITIONED_TAG, &from_disk).expect("a deposit");
        let relit = resume(&plate.plate).expect("a resume");
        assert_eq!(relit.body.form().expect("the form"), deposited.octets);
    }
    std::fs::remove_dir_all(&root).ok();
}

// ---------------------------------------------------------------------------------------------
// the content address — the half of the mouth that decides whether a return survives

/// Two different forms sealed at **one site** must both survive, at two addresses.
///
/// This is the loss the content address exists to close, driven through the whole seam rather than
/// only through the mouth: `eros_text_training` seals a rest inside a per-candidate loop, its own
/// receipt carried 511 distinct rest hashes, and a fixed `machine-rest.form` left one file behind.
/// Both forms below must reach `deposit` and `resume` as two bodies.
#[test]
fn two_forms_from_one_site_both_reach_the_far_side() {
    let _alone = alone();
    let (root, driver) = scratch("two-forms");
    let first = current_octets_from(&[13i64, 29, 17]);
    let second = current_octets_from(&[13i64, 29, 17, 41]);
    assert_ne!(first, second, "the two fixtures must be two forms");

    let earlier = at_the_mouth(&root, &driver, "machine-rest", &first);
    let later = at_the_mouth(&root, &driver, "machine-rest", &second);
    assert_ne!(earlier.path, later.path);

    for deposited in [&earlier, &later] {
        let from_disk = std::fs::read(&deposited.path).expect("both forms are still on disk");
        let plate = deposit(CURRENT_TAG, &from_disk).expect("a deposit");
        let relit = resume(&plate.plate).expect("a resume");
        assert_eq!(
            relit.body.form().expect("the re-lit body's form"),
            deposited.octets
        );
    }

    // the earlier form was not overwritten by the later one
    assert_eq!(
        std::fs::read(&earlier.path).expect("the earlier form"),
        first
    );
    let held: Vec<_> = std::fs::read_dir(root.join(&driver))
        .expect("the driver directory")
        .map(|entry| entry.expect("an entry").file_name())
        .collect();
    assert_eq!(held.len(), 2, "{held:?}");
    std::fs::remove_dir_all(&root).ok();
}

/// The path a driver writes is the path the shell command names, and the address in it is the same
/// string the driver reports as that form's hash. If this drifts, every documented
/// `holon-plate deposit --from ERST:.local/artifacts/<driver>/<name>-<sha256>.form` stops resolving and
/// nothing else in the suite would notice.
#[test]
fn the_declared_path_is_the_one_the_shell_names() {
    let _alone = alone();
    let octets = current_octets();
    let address = content_address(&octets);
    assert_eq!(
        declared_path("eros_text_training", "machine-rest", &octets).expect("a path"),
        PathBuf::from(format!(
            "{DEPOSIT_ROOT}/eros_text_training/machine-rest-{address}.form"
        ))
    );
    assert_eq!(DEPOSIT_ROOT, ".local/artifacts");
}

// ---------------------------------------------------------------------------------------------
// the production frame

/// `deposit_form_or_message` under its own default root, driven end to end.
///
/// Every one of the ~39 driver sites calls `deposit_form_or_message` or `deposit_form`, and neither
/// was executed by any test in this repository: every other test here and in `life` goes through
/// `deposit_form_under` with an explicit root. Under that gap the default root could be replaced
/// with `Path::new("MUTANT_WRONG_ROOT")`, or the whole production entry point replaced with a
/// fabricated `Ok(DepositedForm { .. })` that writes nothing, and both suites stayed green.
///
/// The default root is relative to the invocation directory, so this test **owns a working
/// directory** under the system temp root for the duration. Nothing is written inside the
/// repository, and nothing races: every other test in this binary addresses its files absolutely,
/// and `holon_plate::registry::{deposit, resume}` touch no filesystem at all. The observations are
/// carried out of the working directory and asserted after it is restored, so a failure cannot
/// leave the process pointing somewhere else.
#[test]
fn the_production_entry_point_writes_under_output_and_the_form_resumes() {
    let _alone = alone();
    struct Observed {
        message_carrier: PathBuf,
        refusal_carrier: PathBuf,
        from_disk: Vec<u8>,
        held: Vec<std::ffi::OsString>,
        resumed: Vec<u8>,
        moved: Vec<String>,
    }

    let (root, driver) = scratch("production-frame");
    std::fs::create_dir_all(&root).expect("a working directory of this test's own");
    let previously = std::env::current_dir().expect("the invocation directory");
    std::env::set_current_dir(&root).expect("enter the working directory");

    let htec_driver = format!("{driver}_htec");
    let octets = current_octets();
    let training = training_octets();
    let observed = (|| -> Result<Observed, String> {
        // the exact call 38 of the 39 driver sites make
        let deposited = deposit_form_or_message(&driver, "machine-rest", &octets)?;
        // and the exact call the 39th makes, with the other carrier, under its own driver name so
        // the directory listing below is about one site
        let by_refusal = deposit_form(&htec_driver, "training-ecology-rest", &training)
            .map_err(|refusal| refusal.to_string())?;

        let from_disk = std::fs::read(&deposited.path)
            .map_err(|error| format!("{} reads: {error}", deposited.path.display()))?;
        let mut held: Vec<_> = std::fs::read_dir(Path::new(DEPOSIT_ROOT).join(&driver))
            .map_err(|error| format!("the driver directory reads: {error}"))?
            .map(|entry| entry.expect("an entry").file_name())
            .collect();
        held.sort();

        let plate = deposit(CURRENT_TAG, &from_disk).map_err(|refusal| refusal.to_string())?;
        let mut relit = resume(&plate.plate).map_err(|refusal| refusal.to_string())?;
        let resumed = relit.body.form()?;
        let (before, after) = present_and_require_change(relit.body.as_mut(), &current_deed())
            .map_err(|refusal| refusal.to_string())?;
        let moved = before
            .rows()
            .iter()
            .filter(|(field, was)| after.value(field) != Some(*was))
            .map(|(field, _)| field.clone())
            .collect();

        Ok(Observed {
            message_carrier: deposited.path,
            refusal_carrier: by_refusal.path,
            from_disk,
            held,
            resumed,
            moved,
        })
    })();

    std::env::set_current_dir(&previously).expect("restore the invocation directory");
    let observed = observed.expect("the production entry point deposits, resumes and moves");

    // the default root, joined rather than ignored, with the site name and the content address
    assert_eq!(
        observed.message_carrier,
        PathBuf::from(format!(
            ".local/artifacts/{driver}/machine-rest-{}.form",
            content_address(&octets)
        ))
    );
    assert_eq!(
        observed.refusal_carrier,
        PathBuf::from(format!(
            ".local/artifacts/{htec_driver}/training-ecology-rest-{}.form",
            content_address(&training)
        ))
    );
    // the file the production entry point wrote is under the working directory it was invoked in
    assert!(root.join(&observed.message_carrier).is_file());
    assert!(root.join(&observed.refusal_carrier).is_file());
    assert_eq!(observed.from_disk, octets);
    assert_eq!(
        observed.held,
        vec![std::ffi::OsString::from(format!(
            "machine-rest-{}.form",
            content_address(&octets)
        ))]
    );
    // and the far side re-lit a body off it and moved
    assert_eq!(observed.resumed, octets);
    assert!(
        !observed.moved.is_empty(),
        "the deed moved no census field on a body resumed from the production frame"
    );

    std::fs::remove_dir_all(&root).ok();
}
