//! The three verbs, driven through the actual binary.
//!
//! The library tests prove the mechanism; these prove the mouth. In particular they assert the
//! **wording**, because the wording is load-bearing: a `resume` that reported a restore would be
//! lying about the mechanism even with every digest holding, and no unit test on the format would
//! catch it.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU32, Ordering};

use holon_plate::schemas::current::CurrentDeed;
use holon_plate::schemas::training::TrainingDeed;

static NEXT: AtomicU32 = AtomicU32::new(0);

struct Scratch(PathBuf);

impl Scratch {
    fn new(label: &str) -> Self {
        let unique = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "holon-plate-{}-{label}-{unique}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).expect("a scratch root");
        Self(path)
    }

    fn at(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn holon_plate(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_holon-plate"))
        .args(args)
        .output()
        .expect("the holon-plate binary runs")
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn text(path: &Path) -> String {
    path.to_string_lossy().into_owned()
}

/// A training-ecology form, written by its own codec through the library surface.
fn training_form(scratch: &Scratch) -> PathBuf {
    use std::collections::BTreeMap;
    use life::holonic_training::{FaceAddress, SourceFace, TrainingEcology};

    let mut ecology = TrainingEcology::new(2, 8).expect("an ecology");
    let parameters = BTreeMap::from([("receiver".to_owned(), "alpha".to_owned())]);
    for ordinal in 0..4u64 {
        let faces = vec![
            SourceFace::new(FaceAddress::new("left", ordinal), b"seven".to_vec()),
            SourceFace::new(FaceAddress::new("right", ordinal), b"eight".to_vec()),
        ];
        ecology
            .cultivate(&faces, &parameters, b"fifty-six")
            .expect("a cultivation");
    }
    let path = scratch.at("body.form");
    fs::write(&path, ecology.encode_native_bytes().expect("a form")).expect("write");
    path
}

fn training_deed(scratch: &Scratch) -> PathBuf {
    use std::collections::BTreeMap;
    use life::holonic_training::{FaceAddress, SourceFace};

    let deed = TrainingDeed {
        faces: vec![
            SourceFace::new(FaceAddress::new("left", 9), b"nine".to_vec()),
            SourceFace::new(FaceAddress::new("right", 9), b"six".to_vec()),
        ],
        parameters: BTreeMap::from([("receiver".to_owned(), "beta".to_owned())]),
        consequence: b"fifty-four".to_vec(),
    };
    let path = scratch.at("further.deed");
    fs::write(&path, deed.encode()).expect("write");
    path
}

#[test]
fn deposit_resume_redeposit_through_the_binary_is_byte_identical() {
    let scratch = Scratch::new("round-trip");
    let form = training_form(&scratch);
    let first = scratch.at("first.holon");
    let second = scratch.at("second.holon");

    let deposited = holon_plate(&[
        "deposit",
        "--from",
        &format!("HTEC:{}", text(&form)),
        "--to",
        &text(&first),
    ]);
    assert!(
        deposited.status.success(),
        "{}{}",
        stdout(&deposited),
        stderr(&deposited)
    );
    let report = stdout(&deposited);
    assert!(report.contains("DEPOSITED"), "{report}");
    assert!(report.contains("schema        HTEC/1"), "{report}");
    assert!(report.contains("A FORM was deposited"), "{report}");
    assert!(
        report.contains("were NOT deposited -- they died as they flowed"),
        "{report}"
    );

    let resumed = holon_plate(&[
        "resume",
        "--plate",
        &text(&first),
        "--to",
        &text(&second),
    ]);
    assert!(
        resumed.status.success(),
        "{}{}",
        stdout(&resumed),
        stderr(&resumed)
    );
    let report = stdout(&resumed);
    assert!(report.contains("RE-LIT"), "{report}");
    assert!(report.contains("A FRESH current was lit"), "{report}");
    assert!(
        report.contains("NOT the current that"),
        "the report must say the depositing current is gone: {report}"
    );
    assert!(
        report.contains("byte-identical to the plate it resumed: yes"),
        "{report}"
    );
    // no verb in this tool promises the old body back
    let lowered = report.to_lowercase();
    for banned in ["restore", "thaw", "unfreeze", "same body"] {
        assert!(!lowered.contains(banned), "`{banned}` appears in: {report}");
    }

    assert_eq!(
        fs::read(&first).expect("first plate"),
        fs::read(&second).expect("second plate"),
        "the re-deposited plate is not byte-identical to the plate it resumed"
    );
}

#[test]
fn a_corrupted_plate_refuses_through_the_binary_and_names_what_drifted() {
    let scratch = Scratch::new("corrupt");
    let form = training_form(&scratch);
    let plate = scratch.at("plate.holon");
    assert!(holon_plate(&[
        "deposit",
        "--from",
        &format!("HTEC:{}", text(&form)),
        "--to",
        &text(&plate),
    ])
    .status
    .success());

    let mut octets = fs::read(&plate).expect("a plate");
    let last_form_octet = octets.len() - 65;
    octets[last_form_octet] ^= 0x01;
    fs::write(&plate, &octets).expect("write");

    let refused = holon_plate(&["resume", "--plate", &text(&plate)]);
    assert_eq!(refused.status.code(), Some(1), "a corrupt plate must exit 1");
    let message = stderr(&refused);
    assert!(message.contains("REFUSED"), "{message}");
    assert!(message.contains("CONTENT drift"), "{message}");
    assert!(message.contains("form_sha256"), "{message}");
    assert!(message.contains("the FORM is what moved"), "{message}");
}

#[test]
fn the_binary_reports_an_unheld_schema_on_inspect_and_refuses_it_on_resume() {
    let scratch = Scratch::new("unheld");
    let form = training_form(&scratch);
    let plate = scratch.at("plate.holon");
    assert!(holon_plate(&[
        "deposit",
        "--from",
        &format!("HTEC:{}", text(&form)),
        "--to",
        &text(&plate),
    ])
    .status
    .success());

    // rewrite the head's schema tag and re-seal so both digests hold: only the schema is unheld
    let octets = fs::read(&plate).expect("a plate");
    let read = holon_plate::open(&octets).expect("a plate");
    let forged = holon_plate::seal(
        holon_plate::SchemaTag::parse("ZZZZ").expect("a tag"),
        1,
        &read.census,
        &read.form,
    );
    fs::write(&plate, &forged).expect("write");

    let inspected = holon_plate(&["inspect", "--plate", &text(&plate)]);
    assert!(inspected.status.success(), "{}", stderr(&inspected));
    let report = stdout(&inspected);
    assert!(report.contains("NOT HELD by this reader"), "{report}");
    assert!(report.contains("HTEC/1, ERST/2"), "{report}");
    assert!(report.contains("NO BODY WAS LIT"), "{report}");

    let refused = holon_plate(&["resume", "--plate", &text(&plate)]);
    assert_eq!(refused.status.code(), Some(1));
    let message = stderr(&refused);
    assert!(message.contains("ZZZZ/1"), "{message}");
    assert!(message.contains("not resumed by guessing"), "{message}");
}

#[test]
fn a_further_deed_through_the_binary_changes_the_body_and_the_plate() {
    let scratch = Scratch::new("deed");
    let form = training_form(&scratch);
    let deed = training_deed(&scratch);
    let first = scratch.at("first.holon");
    let second = scratch.at("second.holon");

    assert!(holon_plate(&[
        "deposit",
        "--from",
        &format!("HTEC:{}", text(&form)),
        "--to",
        &text(&first),
    ])
    .status
    .success());

    let resumed = holon_plate(&[
        "resume",
        "--plate",
        &text(&first),
        "--deed",
        &text(&deed),
        "--to",
        &text(&second),
    ]);
    assert!(
        resumed.status.success(),
        "{}{}",
        stdout(&resumed),
        stderr(&resumed)
    );
    let report = stdout(&resumed);
    assert!(
        report.contains("accepted it and CHANGED"),
        "the re-lit body must prove it resumed living: {report}"
    );
    assert!(report.contains("generation  4 -> 5"), "{report}");
    assert!(report.contains("fibers  1 -> 2"), "{report}");
    assert!(
        report.contains("byte-identical to the plate it resumed: no"),
        "{report}"
    );
    assert_ne!(
        fs::read(&first).expect("first"),
        fs::read(&second).expect("second")
    );

    // and the moved plate resumes in its own right
    let again = holon_plate(&["resume", "--plate", &text(&second)]);
    assert!(again.status.success(), "{}", stderr(&again));
    assert!(stdout(&again).contains("generation=5"), "{}", stdout(&again));
}

#[test]
fn a_deed_addressed_to_another_schema_refuses_through_the_binary() {
    let scratch = Scratch::new("misaddressed");
    let form = training_form(&scratch);
    let plate = scratch.at("plate.holon");
    let deed = scratch.at("wrong.deed");
    fs::write(
        &deed,
        CurrentDeed {
            relation: 71,
            action: 1,
        }
        .encode(),
    )
    .expect("write");

    assert!(holon_plate(&[
        "deposit",
        "--from",
        &format!("HTEC:{}", text(&form)),
        "--to",
        &text(&plate),
    ])
    .status
    .success());

    let refused = holon_plate(&["resume", "--plate", &text(&plate), "--deed", &text(&deed)]);
    assert_eq!(refused.status.code(), Some(1));
    let message = stderr(&refused);
    assert!(message.contains("addressed to schema ERST"), "{message}");
}

#[test]
fn the_help_states_what_the_plate_does_not_claim() {
    let helped = holon_plate(&["--help"]);
    assert!(helped.status.success());
    let report = stdout(&helped);
    assert!(report.contains("HTEC/1"), "{report}");
    assert!(report.contains("ERST/2"), "{report}");
    assert!(report.contains("REFUSED, never guessed at"), "{report}");
    assert!(
        report.contains("is not comprehension"),
        "the help must state the boundary: {report}"
    );
    assert!(
        report.contains("freezing is not understanding"),
        "{report}"
    );
    assert!(report.contains("applies no compression"), "{report}");
}

#[test]
fn an_unknown_flag_and_a_missing_file_are_invocation_faults_not_refusals() {
    assert_eq!(
        holon_plate(&["resume", "--plate", "/nonexistent/plate.holon"])
            .status
            .code(),
        Some(2)
    );
    assert_eq!(holon_plate(&["frobnicate"]).status.code(), Some(2));
    assert_eq!(
        holon_plate(&["deposit", "--from", "HTEC", "--to", "x.holon"])
            .status
            .code(),
        Some(2)
    );
}
