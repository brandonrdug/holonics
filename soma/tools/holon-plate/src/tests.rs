//! The plate's falsifiers, executed.
//!
//! Six things are asserted and each one can fail:
//!
//! 1. deposit -> resume -> re-deposit is **byte-identical**, and the round trip goes through a
//!    remount both ways rather than through byte equality alone;
//! 2. a corrupted plate **refuses**, and the refusal names which of the two species moved;
//! 3. the two species are **separable** — one corruption fires exactly one of them;
//! 4. an unheld schema and an unheld schema version **refuse rather than guess**;
//! 5. a plate whose declared census is not true of its form **refuses and names the field**, which
//!    a digest alone cannot catch;
//! 6. the zero-return control: a re-lit body must accept a further deed and **change**, and a body
//!    that does not change is refused. The control's own control is
//!    `an_inert_body_that_changes_nothing_is_refused`, without which (6) would be a law that has
//!    only ever seen input it passes on.

use std::collections::{BTreeMap, BTreeSet};

use body::num::Cog;
use holonic_engine::algebraic::{
    CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use holonic_engine::causal::EventId;
use holonic_engine::conditioned_derivation::{expose, ConditionedBody};
use holonic_engine::graded_complex_form::encode_native_bytes;
use life::conditioned_rest::ConditionedRest;
use life::holonic_training::{FaceAddress, SourceFace, TrainingEcology};
use num_bigint::BigInt;
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, CurrentEvent, CurrentGeometry, LiveCurrentMachine, SparseStandingSurface,
};

use crate::census::Census;
use crate::deed::DEED_HEAD_OCTETS;
use crate::plate::{self, PlateRefusal, SchemaTag, HEAD_OCTETS, SEAL_OCTETS};
use crate::registry::{deposit, inspect, redeposit, resume};
use crate::schema::{present_and_require_change, LitBody, PlateSchema, ResumeRefusal};
use crate::schemas::conditioned::{CONDITIONED_SCHEMA_VERSION, CONDITIONED_TAG};
use crate::schemas::current::{CurrentDeed, CURRENT_SCHEMA_VERSION, CURRENT_TAG};
use crate::schemas::rebase::{
    decode_euler, encode_euler, BoundaryTerm, RebaseBody, RebaseDeed, REBASE_SCHEMA_VERSION,
    REBASE_TAG,
};
use crate::schemas::training::{TrainingDeed, TRAINING_SCHEMA_VERSION, TRAINING_TAG};

// ---------------------------------------------------------------------------------------------
// two real bodies, driven by their own machines, no fixtures

fn face(axis: &str, ordinal: u64, value: &str) -> SourceFace {
    SourceFace::new(FaceAddress::new(axis, ordinal), value.as_bytes().to_vec())
}

fn parameters(receiver: &str) -> BTreeMap<String, String> {
    BTreeMap::from([("receiver".to_owned(), receiver.to_owned())])
}

/// A training ecology carried to a real recurrent population by four occurrences.
fn training_form() -> Vec<u8> {
    let mut ecology = TrainingEcology::new(2, 8).expect("a training ecology");
    for ordinal in 0..4u64 {
        let faces = vec![
            face("left", ordinal, "seven"),
            face("right", ordinal, "eight"),
        ];
        ecology
            .cultivate(&faces, &parameters("alpha"), b"fifty-six")
            .expect("a cultivation");
    }
    ecology.encode_native_bytes().expect("a training form")
}

/// A conditioned derivation body carried to a real founded morphology by exposure to two wholes,
/// mounted on two declared artifacts. Driven by `life`'s own owner; nothing here is a fixture blob.
fn conditioned_form() -> Vec<u8> {
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
        expose(
            "document:one",
            "the exact carrier carries a formal kernel through a transport",
        ),
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

fn relation(value: i64) -> RelationAtom {
    RelationAtom::new(Cog::lit(value)).expect("a live relation")
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("a resolving action")
}

/// A live current body with two settled lineages, each carried across three real events.
fn current_form() -> Vec<u8> {
    let first = relation(13);
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).expect("rank"));
    let lineages = [
        machine
            .attach(CurrentGeometry::Cell(first))
            .expect("an ingress"),
        machine
            .attach(CurrentGeometry::Cell(first))
            .expect("an ingress"),
    ];
    for value in [13i64, 29, 17] {
        let currents = [
            CurrentEvent::continuing(
                lineages[0],
                CurrentGeometry::Cell(relation(value)),
                action(),
            ),
            CurrentEvent::continuing(
                lineages[1],
                CurrentGeometry::Cell(relation(value)),
                action(),
            ),
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

// ---------------------------------------------------------------------------------------------
// the graded causal incidences, every one of them grown through `found_cell`

fn source() -> BTreeSet<EventId> {
    BTreeSet::from([EventId(1)])
}

fn vertex(complex: &mut GradedCausalComplex, name: &str) -> CausalCellId {
    complex
        .found_cell(name, source(), 0, CausalChain::default())
        .expect("a vertex")
}

fn edge(
    complex: &mut GradedCausalComplex,
    name: &str,
    from: CausalCellId,
    to: CausalCellId,
) -> CausalCellId {
    let mut boundary = CausalChain::default();
    boundary.add_term(to, ComparativeMultiplicity::positive(1u32));
    boundary.add_term(from, ComparativeMultiplicity::negative(1u32));
    complex
        .found_cell(name, source(), 1, boundary)
        .expect("an edge")
}

/// Three vertices, three edges, no filling. One piece, one loop, `chi = 0`.
fn hollow_triangle() -> GradedCausalComplex {
    let mut complex = GradedCausalComplex::default();
    let a = vertex(&mut complex, "a");
    let b = vertex(&mut complex, "b");
    let c = vertex(&mut complex, "c");
    edge(&mut complex, "ab", a, b);
    edge(&mut complex, "bc", b, c);
    edge(&mut complex, "ca", c, a);
    complex
}

/// The same triangle with its loop filled. `chi = +1`.
fn filled_triangle() -> GradedCausalComplex {
    let mut complex = hollow_triangle();
    let edges: Vec<CausalCellId> = complex
        .cells()
        .values()
        .filter(|cell| cell.grade == 1)
        .map(|cell| cell.id)
        .collect();
    let mut boundary = CausalChain::default();
    for edge in edges {
        boundary.add_term(edge, ComparativeMultiplicity::positive(1u32));
    }
    complex
        .found_cell("disc", source(), 2, boundary)
        .expect("a disc");
    complex
}

/// Two vertices joined by three edges. Two independent loops, `chi = -1`.
fn theta_graph() -> GradedCausalComplex {
    let mut complex = GradedCausalComplex::default();
    let a = vertex(&mut complex, "a");
    let b = vertex(&mut complex, "b");
    for name in ["first", "second", "third"] {
        edge(&mut complex, name, a, b);
    }
    complex
}

/// Three parallel edges between two vertices, and one face attached to them with **unequal
/// winding**: `4*e1 - 6*e2 + 2*e3`.
///
/// Every edge has the same boundary `b - a`, so the coefficients sum to zero and the attachment
/// closes at `found_cell`. The three magnitudes 4, 6 and 2 are what make this the one fixture in
/// the family that can gauge the pivot rule: `find_pivot` breaks ties with strict `<` and `>`, so
/// on the four simplicial bodies above — every nonzero entry at magnitude one — all three rules
/// select the first nonzero and the schema's three-rule cross-check compares one computation with
/// itself twice. Here `FirstNonzero` enters at row 0, `LargestMagnitude` at the `-6` in row 1, and
/// `SmallestMagnitude` at the `2` in row 2.
///
/// `gcd(4, 6, 2) = 2`, so it carries a `Z/2` at grade 1 as well: the agreement the three rules
/// reach is an agreement about a nontrivial reading, not about zero.
fn staggered_attachment() -> GradedCausalComplex {
    let mut complex = GradedCausalComplex::default();
    let a = vertex(&mut complex, "a");
    let b = vertex(&mut complex, "b");
    let edges: Vec<CausalCellId> = ["first", "second", "third"]
        .into_iter()
        .map(|name| edge(&mut complex, name, a, b))
        .collect();
    let mut face = CausalChain::default();
    face.add_term(edges[0], ComparativeMultiplicity::positive(4u32));
    face.add_term(edges[1], ComparativeMultiplicity::negative(6u32));
    face.add_term(edges[2], ComparativeMultiplicity::positive(2u32));
    complex
        .found_cell("staggered", source(), 2, face)
        .expect("a staggered attachment");
    complex
}

/// A face attached twice around a loop whose own boundary cancels. Carries torsion — a `Z/2` at
/// grade 1 — as `staggered_attachment` does; the three simplicial bodies above cannot.
fn doubled_attachment() -> GradedCausalComplex {
    let mut complex = GradedCausalComplex::default();
    let a = vertex(&mut complex, "a");
    let mut loop_boundary = CausalChain::default();
    loop_boundary.add_term(a, ComparativeMultiplicity::positive(1u32));
    loop_boundary.add_term(a, ComparativeMultiplicity::negative(1u32));
    let edge = complex
        .found_cell("loop", source(), 1, loop_boundary)
        .expect("a loop");
    let mut face = CausalChain::default();
    face.add_term(edge, ComparativeMultiplicity::positive(2u32));
    complex
        .found_cell("twice", source(), 2, face)
        .expect("a doubled attachment");
    complex
}

fn rebase_form(complex: &GradedCausalComplex) -> Vec<u8> {
    encode_native_bytes(complex).expect("a graded-complex form")
}

/// One further vertex: a cell whose boundary is empty, so it founds a generator and moves nothing
/// the boundary ranks can see.
fn rebase_deed() -> Vec<u8> {
    RebaseDeed {
        name: "d".to_owned(),
        grade: 0,
        source_events: vec![7],
        boundary: Vec::new(),
    }
    .encode()
}

/// One further edge between two named cells.
fn joining_deed(name: &str, from: u64, to: u64) -> Vec<u8> {
    RebaseDeed {
        name: name.to_owned(),
        grade: 1,
        source_events: vec![7],
        boundary: vec![
            BoundaryTerm {
                cell: to,
                positive: 1,
                negative: 0,
            },
            BoundaryTerm {
                cell: from,
                positive: 0,
                negative: 1,
            },
        ],
    }
    .encode()
}

fn bodies() -> [(SchemaTag, Vec<u8>, Vec<u8>); 3] {
    [
        (TRAINING_TAG, training_form(), training_deed()),
        (CURRENT_TAG, current_form(), current_deed()),
        (REBASE_TAG, rebase_form(&hollow_triangle()), rebase_deed()),
    ]
}

// ---------------------------------------------------------------------------------------------
// 1. the round trip

#[test]
fn deposit_resume_redeposit_is_byte_identical() {
    for (tag, form, _) in bodies() {
        let deposited = deposit(tag, &form).expect("a deposit");
        let relit = resume(&deposited.plate).expect("a re-light");
        let again = redeposit(relit.tag, relit.body.as_ref()).expect("a re-deposit");
        assert_eq!(
            deposited.plate, again.plate,
            "{tag}: the re-deposited plate is not byte-identical to the plate it resumed"
        );
        assert_eq!(deposited.form_sha256, again.form_sha256);
        assert_eq!(deposited.plate_sha256, again.plate_sha256);
        assert_eq!(deposited.census, again.census);
    }
}

#[test]
fn the_round_trip_passes_through_a_remount_and_not_a_copy() {
    // The deposited FORM is not the input octets moved across; it is what the mounted body
    // returned. If `deposit` ever copied instead of mounting, a form the codec would refuse would
    // still seal. It refuses -- both schemas carry their own magic in their leading octets and
    // neither codec will open a form whose magic has moved.
    for (tag, form, _) in bodies() {
        let mut broken = form.clone();
        broken[1] ^= 0xff;
        let refusal = deposit(tag, &broken).expect_err("a corrupt form must not seal");
        assert!(
            matches!(
                refusal,
                ResumeRefusal::FormRefused { .. } | ResumeRefusal::FormNotCanonical { .. }
            ),
            "{tag}: expected a mount refusal, got {refusal}"
        );
    }
}

#[test]
fn the_plate_head_is_exactly_thirty_two_octets_and_the_seal_sixty_four() {
    let form = training_form();
    let deposited = deposit(TRAINING_TAG, &form).expect("a deposit");
    let report = inspect(&deposited.plate).expect("an inspection");
    assert_eq!(
        report.plate_octets,
        HEAD_OCTETS + report.census_octets + report.form_octets + SEAL_OCTETS
    );
    assert_eq!(&deposited.plate[0..4], b"HLON".as_slice());
    assert_eq!(&deposited.plate[8..12], b"HTEC".as_slice());
    assert_eq!(report.form_octets, form.len());
    // the form goes to disk verbatim: no compression, nothing to mistake for a competence figure
    let form_start = HEAD_OCTETS + report.census_octets;
    assert_eq!(
        &deposited.plate[form_start..form_start + form.len()],
        &form[..]
    );
}

// ---------------------------------------------------------------------------------------------
// 2 and 3. corruption refuses, and the two species are separable

#[test]
fn a_corrupted_form_octet_refuses_and_names_the_form() {
    for (tag, form, _) in bodies() {
        let deposited = deposit(tag, &form).expect("a deposit");
        let census_octets = inspect(&deposited.plate)
            .expect("an inspection")
            .census_octets;
        let form_start = HEAD_OCTETS + census_octets;
        let mut corrupted = deposited.plate.clone();
        corrupted[form_start + form.len() / 2] ^= 0x01;

        let refusal = resume(&corrupted).expect_err("a corrupted plate must refuse");
        let ResumeRefusal::Plate(PlateRefusal::FormContentDrift {
            deposited: recorded,
            recomputed,
            form_octets,
        }) = &refusal
        else {
            panic!("{tag}: expected CONTENT drift, got {refusal}");
        };
        assert_ne!(recorded, recomputed);
        assert_eq!(*form_octets, form.len());
        let rendered = refusal.to_string();
        assert!(rendered.contains("CONTENT drift"), "{rendered}");
        assert!(rendered.contains(recorded), "{rendered}");
        assert!(rendered.contains(recomputed), "{rendered}");
        assert!(rendered.contains("the FORM is what moved"), "{rendered}");
    }
}

#[test]
fn a_corrupted_census_octet_refuses_and_names_the_binding() {
    for (tag, form, _) in bodies() {
        let deposited = deposit(tag, &form).expect("a deposit");
        // The last octet of the census is the high octet of the last field's value; flipping a low
        // bit there changes what the plate declares without touching the form.
        let census_octets = inspect(&deposited.plate)
            .expect("an inspection")
            .census_octets;
        let mut corrupted = deposited.plate.clone();
        corrupted[HEAD_OCTETS + census_octets - 8] ^= 0x01;

        let refusal = resume(&corrupted).expect_err("a corrupted declaration must refuse");
        let ResumeRefusal::Plate(PlateRefusal::PlateBindingDrift {
            deposited: recorded,
            recomputed,
        }) = &refusal
        else {
            panic!("{tag}: expected BINDING drift, got {refusal}");
        };
        assert_ne!(recorded, recomputed);
        let rendered = refusal.to_string();
        assert!(rendered.contains("BINDING drift"), "{rendered}");
        assert!(
            rendered.contains("the HEAD or CENSUS is what moved"),
            "{rendered}"
        );
    }
}

#[test]
fn the_two_species_are_separable_and_one_corruption_fires_exactly_one() {
    // A seal that folded the form into a single digest would move both digests on any corruption
    // and could not name the side that moved. This asserts the separation directly.
    let form = training_form();
    let deposited = deposit(TRAINING_TAG, &form).expect("a deposit");
    let census_octets = inspect(&deposited.plate)
        .expect("an inspection")
        .census_octets;
    let form_start = HEAD_OCTETS + census_octets;
    let seal_start = form_start + form.len();
    let recorded_form_digest = &deposited.plate[seal_start..seal_start + 32];

    // corrupt the form: the content digest moves, the binding digest is untouched
    let mut form_corrupted = deposited.plate.clone();
    form_corrupted[form_start] ^= 0x80;
    let mut binding = soma_standing_deposit::sha256::Sha256::new();
    binding.update(&form_corrupted[..form_start]);
    binding.update(recorded_form_digest);
    assert_eq!(
        binding.finish().to_vec(),
        deposited.plate[seal_start + 32..seal_start + 64].to_vec(),
        "corrupting the form must leave the binding digest standing"
    );

    // corrupt the census: the form digest is untouched
    let mut census_corrupted = deposited.plate.clone();
    census_corrupted[HEAD_OCTETS + 8] ^= 0x20;
    let mut content = soma_standing_deposit::sha256::Sha256::new();
    content.update(&census_corrupted[form_start..seal_start]);
    assert_eq!(
        content.finish().to_vec(),
        recorded_form_digest.to_vec(),
        "corrupting the census must leave the content digest standing"
    );

    assert!(matches!(
        resume(&form_corrupted),
        Err(ResumeRefusal::Plate(PlateRefusal::FormContentDrift { .. }))
    ));
    assert!(matches!(
        resume(&census_corrupted),
        Err(ResumeRefusal::Plate(PlateRefusal::PlateBindingDrift { .. }))
    ));
}

#[test]
fn a_corrupted_seal_does_not_accuse_the_form() {
    // The failure this catches: judging the content digest first reports "the FORM moved" for a
    // plate whose *recorded content digest* is what moved, with the form untouched.
    let form = training_form();
    let deposited = deposit(TRAINING_TAG, &form).expect("a deposit");
    let census_octets = inspect(&deposited.plate)
        .expect("an inspection")
        .census_octets;
    let seal_start = HEAD_OCTETS + census_octets + form.len();

    let mut corrupted = deposited.plate.clone();
    corrupted[seal_start + 5] ^= 0x40; // inside the recorded form_sha256
    assert_eq!(
        &corrupted[HEAD_OCTETS + census_octets..seal_start],
        &form[..],
        "the form itself must be untouched for this test to mean anything"
    );

    let refusal = resume(&corrupted).expect_err("a drifted seal must refuse");
    let ResumeRefusal::Plate(PlateRefusal::SealDrift { .. }) = &refusal else {
        panic!("expected SEAL drift, got {refusal}");
    };
    let rendered = refusal.to_string();
    assert!(rendered.contains("SEAL drift"), "{rendered}");
    assert!(
        rendered.contains("this refusal does not accuse it"),
        "{rendered}"
    );
    assert!(
        !rendered.contains("the FORM is what moved"),
        "an intact form must not be accused: {rendered}"
    );
}

#[test]
fn a_corrupted_head_extent_refuses_and_names_the_field() {
    let form = training_form();
    let deposited = deposit(TRAINING_TAG, &form).expect("a deposit");
    let mut corrupted = deposited.plate.clone();
    corrupted[24] = corrupted[24].wrapping_add(1); // form_octets, low octet
    let refusal = resume(&corrupted).expect_err("a drifted extent must refuse");
    let ResumeRefusal::Plate(PlateRefusal::ExtentOverruns { field, .. }) = &refusal else {
        panic!("expected an extent refusal, got {refusal}");
    };
    assert_eq!(*field, "form_octets");
    assert!(refusal.to_string().contains("form_octets"));
}

#[test]
fn a_truncated_plate_and_a_foreign_file_both_refuse() {
    let form = training_form();
    let deposited = deposit(TRAINING_TAG, &form).expect("a deposit");

    let truncated = &deposited.plate[..deposited.plate.len() - 1];
    assert!(matches!(
        resume(truncated),
        Err(ResumeRefusal::Plate(PlateRefusal::ExtentOverruns { .. }))
    ));

    let short = b"HLON";
    assert!(matches!(
        resume(short),
        Err(ResumeRefusal::Plate(PlateRefusal::ShortPlate { .. }))
    ));

    // a form file handed to the plate reader by mistake
    let refusal = resume(&form).expect_err("a bare form is not a plate");
    let ResumeRefusal::Plate(PlateRefusal::NotAPlate { found }) = &refusal else {
        panic!("expected NotAPlate, got {refusal}");
    };
    assert_eq!(found, b"HTEC");
    assert!(refusal.to_string().contains("HTEC"));
}

// ---------------------------------------------------------------------------------------------
// 4. an unheld schema refuses rather than guessing

#[test]
fn an_unheld_schema_refuses_rather_than_guessing() {
    let form = training_form();
    let census = Census::found([("generation", 4u64)]).expect("a census");
    let unheld = SchemaTag::parse("ZZZZ").expect("a tag");
    let plate = plate::seal(unheld, 1, &census, &form);

    // The container is perfectly well formed and both digests hold.
    let report = inspect(&plate).expect("an inspection reports an unheld schema");
    assert!(!report.held);
    assert_eq!(report.shape, None);

    // The form is a real, mountable HTEC form. A reader that guessed would succeed here, which is
    // exactly the failure being refused.
    assert!(crate::schemas::training::TrainingSchema
        .relight(&form)
        .is_ok());

    let refusal = resume(&plate).expect_err("an unheld schema must refuse");
    let ResumeRefusal::SchemaUnheld { tag, version, held } = &refusal else {
        panic!("expected SchemaUnheld, got {refusal}");
    };
    assert_eq!(tag.to_string(), "ZZZZ");
    assert_eq!(*version, Some(1));
    assert_eq!(
        held,
        &[
            "HTEC/2".to_owned(),
            "ERST/2".to_owned(),
            "RBIN/1".to_owned(),
            "CDER/1".to_owned()
        ]
    );
    let rendered = refusal.to_string();
    assert!(rendered.contains("ZZZZ/1"), "{rendered}");
    assert!(rendered.contains("HTEC/2"), "{rendered}");
    assert!(rendered.contains("not resumed by guessing"), "{rendered}");
}

#[test]
fn an_unheld_schema_version_refuses_rather_than_reading_it_as_the_held_one() {
    let form = training_form();
    let census = Census::found([("generation", 4u64)]).expect("a census");
    let plate = plate::seal(TRAINING_TAG, TRAINING_SCHEMA_VERSION + 40, &census, &form);
    let refusal = resume(&plate).expect_err("an unheld codec version must refuse");
    let ResumeRefusal::SchemaVersionUnheld { tag, found, held } = &refusal else {
        panic!("expected SchemaVersionUnheld, got {refusal}");
    };
    assert_eq!(*tag, TRAINING_TAG);
    assert_eq!(*found, TRAINING_SCHEMA_VERSION + 40);
    assert_eq!(*held, TRAINING_SCHEMA_VERSION);
    assert!(refusal.to_string().contains("would be a guess"));
}

#[test]
fn the_held_versions_are_taken_from_the_codecs_they_hold() {
    assert_eq!(
        CURRENT_SCHEMA_VERSION,
        soma_membrane::LIVE_CURRENT_REST_LAYOUT_VERSION
    );
    // HTEC's codec writes b"HTEC\0\0\0\x02"; the schema version is that trailing octet.
    let form = training_form();
    assert_eq!(&form[0..8], b"HTEC\0\0\0\x02".as_slice());
    assert_eq!(TRAINING_SCHEMA_VERSION, u32::from(form[7]));

    // RBIN's codec writes its magic and then its own layout version as a little-endian u32.
    // (`REBASE_SCHEMA_VERSION == GRADED_COMPLEX_FORM_LAYOUT_VERSION` is not asserted here: the
    // first is *defined* as the second at `schemas/rebase.rs`, so the comparison is a constant
    // against its own definition. What can fail is the octets the codec actually writes, below.)
    let form = rebase_form(&hollow_triangle());
    assert_eq!(&form[0..4], b"RBIN".as_slice());
    assert_eq!(
        u32::from_le_bytes(form[4..8].try_into().expect("four")),
        REBASE_SCHEMA_VERSION,
        "the held version must be the one the codec writes, not a literal beside it"
    );

    // CDER's codec writes b"CDER\0\0\0\x01"; the schema version is that trailing octet, and the
    // constant is derived from the prefix rather than restated beside it.
    let form = conditioned_form();
    assert_eq!(&form[0..8], b"CDER\0\0\0\x01".as_slice());
    assert_eq!(CONDITIONED_SCHEMA_VERSION, u32::from(form[7]));
    assert_eq!(CONDITIONED_TAG.to_string(), "CDER");
}

// ---------------------------------------------------------------------------------------------
// 5. the second frame

#[test]
fn a_declared_census_that_is_not_true_of_the_form_refuses_and_names_the_field() {
    let form = training_form();
    let honest = deposit(TRAINING_TAG, &form).expect("a deposit");
    let true_generation = honest.census.value("generation").expect("generation");

    let mut forged: Vec<(String, u64)> = honest
        .census
        .rows()
        .iter()
        .map(|(name, value)| (name.clone(), *value))
        .collect();
    for row in &mut forged {
        if row.0 == "generation" {
            row.1 = true_generation + 1;
        }
    }
    let forged = Census::found(forged).expect("a census");
    let plate = plate::seal(TRAINING_TAG, TRAINING_SCHEMA_VERSION, &forged, &form);

    // Both digests hold. A container that verified only hashes would accept this plate.
    inspect(&plate).expect("the container itself is intact");

    let refusal = resume(&plate).expect_err("a forged declaration must refuse");
    let ResumeRefusal::CensusDrift {
        field,
        declared,
        relit,
    } = &refusal
    else {
        panic!("expected CensusDrift, got {refusal}");
    };
    assert_eq!(field, "generation");
    assert_eq!(*declared, true_generation + 1);
    assert_eq!(*relit, true_generation);
    let rendered = refusal.to_string();
    assert!(rendered.contains("CENSUS drift"), "{rendered}");
    assert!(rendered.contains("generation"), "{rendered}");
    assert!(rendered.contains("the octets did not move"), "{rendered}");
}

#[test]
fn a_census_that_declares_less_than_the_body_holds_refuses() {
    let form = training_form();
    let honest = deposit(TRAINING_TAG, &form).expect("a deposit");
    // every declared field is true; one true field is simply left out
    let thin: Vec<(String, u64)> = honest
        .census
        .rows()
        .iter()
        .filter(|(name, _)| name != "fibers")
        .map(|(name, value)| (name.clone(), *value))
        .collect();
    let thin = Census::found(thin).expect("a census");
    let plate = plate::seal(TRAINING_TAG, TRAINING_SCHEMA_VERSION, &thin, &form);
    let refusal = resume(&plate).expect_err("an under-declared census must refuse");
    let ResumeRefusal::CensusFieldUndeclared { field } = &refusal else {
        panic!("expected CensusFieldUndeclared, got {refusal}");
    };
    assert_eq!(field, "fibers");
    assert!(refusal.to_string().contains("never declared"));
}

#[test]
fn the_census_wire_is_canonical_and_refuses_a_noncanonical_one() {
    let census = Census::found([("zulu", 1u64), ("alpha", 2), ("mike", 3)]).expect("a census");
    assert_eq!(
        census
            .rows()
            .iter()
            .map(|(name, _)| name.as_str())
            .collect::<Vec<_>>(),
        vec!["alpha", "mike", "zulu"],
        "a census is stored ascending so that two censuses of one body are byte-identical"
    );
    assert_eq!(Census::decode(&census.encode()).expect("a census"), census);
    assert!(Census::found([("alpha", 1u64), ("alpha", 2)]).is_err());
    assert!(Census::found([("Alpha", 1u64)]).is_err());
    assert!(Census::found([("", 1u64)]).is_err());

    // a hand-forged descending wire
    let mut wire = Vec::new();
    wire.extend_from_slice(&2u64.to_le_bytes());
    for (name, value) in [("zulu", 1u64), ("alpha", 2u64)] {
        wire.extend_from_slice(&(name.len() as u64).to_le_bytes());
        wire.extend_from_slice(name.as_bytes());
        wire.extend_from_slice(&value.to_le_bytes());
    }
    assert!(Census::decode(&wire).is_err());
}

// ---------------------------------------------------------------------------------------------
// 6. the zero-return control

#[test]
fn the_resumed_body_accepts_a_further_deed_and_changes() {
    for (tag, form, deed) in bodies() {
        let deposited = deposit(tag, &form).expect("a deposit");
        let mut relit = resume(&deposited.plate).expect("a re-light");

        let (before, after) =
            present_and_require_change(relit.body.as_mut(), &deed).expect("a further deed");
        assert_ne!(
            before, after,
            "{tag}: the re-lit body took a deed and its census did not move"
        );

        // and the change is durable: the moved body deposits to a DIFFERENT plate, which resumes
        let moved = redeposit(tag, relit.body.as_ref()).expect("a re-deposit after the deed");
        assert_ne!(
            moved.plate, deposited.plate,
            "{tag}: a body that received a deed must not re-deposit the plate it resumed"
        );
        let again = resume(&moved.plate).expect("the moved plate re-lights");
        assert_eq!(again.relit, after);
    }
}

#[test]
fn the_named_census_fields_that_move_are_the_structural_ones() {
    // HTEC: a new occurrence founds new transduction fibers -- a structural population, not a tally
    let form = training_form();
    let mut relit =
        resume(&deposit(TRAINING_TAG, &form).expect("a deposit").plate).expect("a re-light");
    let (before, after) =
        present_and_require_change(relit.body.as_mut(), &training_deed()).expect("a deed");
    assert!(
        after.value("fibers").expect("fibers") > before.value("fibers").expect("fibers"),
        "the deed must found new transduction fibers, not only advance a counter"
    );

    // ERST: a contemporary event advances every settled lineage's receiving edge
    let form = current_form();
    let mut relit =
        resume(&deposit(CURRENT_TAG, &form).expect("a deposit").plate).expect("a re-light");
    let (before, after) =
        present_and_require_change(relit.body.as_mut(), &current_deed()).expect("a deed");
    let lineages = before.value("lineages").expect("lineages");
    assert_eq!(
        after.value("carrier_cursors").expect("cursors"),
        before.value("carrier_cursors").expect("cursors") + lineages,
        "one contemporary event must advance every settled lineage's receiving edge by one"
    );
    assert_eq!(
        after.value("lineages"),
        before.value("lineages"),
        "continuing a lineage must not found one"
    );
    // THE CARRIER EXTENT MUST NOT MOVE, and this assertion earned its keep on 2026-08-15.
    //
    // A composing entry was wired into the live `Cell` branch that hour, which made the carrier
    // mount a further row on this deed — `720 -> 1272` — and **this line is what refused it.** The
    // wiring was wrong (an atom face routed into the word-grain climb) and was reverted; the
    // assertion was briefly inverted to accommodate it and is restored.
    //
    // Its reason is unchanged: a depth-one carrier holds its extent and advances within it, which
    // is exactly why an extent alone cannot witness that a body received anything. The structural
    // fields above carry the witness.
    assert_eq!(
        after.value("carrier_words"),
        before.value("carrier_words"),
        "a depth-one carrier holds its extent and advances within it -- which is exactly why an \
         extent alone cannot witness that a body received anything"
    );
}

/// The control's own control. Without this, `the_resumed_body_accepts_a_further_deed_and_changes`
/// would be a law that has only ever seen input it passes on.
#[test]
fn an_inert_body_that_changes_nothing_is_refused() {
    struct InertBody {
        form: Vec<u8>,
    }
    impl LitBody for InertBody {
        fn form(&self) -> Result<Vec<u8>, String> {
            Ok(self.form.clone())
        }
        fn census(&self) -> Result<Census, String> {
            Census::found([("generation", 1u64)]).map_err(|refusal| refusal.to_string())
        }
        fn present(&mut self, _deed: &[u8]) -> Result<(), String> {
            Ok(()) // it accepted the deed and did nothing, which is the failure being caught
        }
    }

    let mut inert = InertBody {
        form: b"a body that does not move".to_vec(),
    };
    let refusal = present_and_require_change(&mut inert, &training_deed())
        .expect_err("an inert body refuses");
    let ResumeRefusal::DeedChangedNothing {
        deed_octets,
        form_octets,
    } = &refusal
    else {
        panic!("expected DeedChangedNothing, got {refusal}");
    };
    assert_eq!(*deed_octets, training_deed().len());
    assert_eq!(*form_octets, inert.form.len());
    assert!(refusal
        .to_string()
        .contains("a law that returns zero proves nothing about itself"));
}

// ---------------------------------------------------------------------------------------------
// the deed mouth

#[test]
fn a_deed_addressed_to_another_schema_refuses() {
    let form = current_form();
    let mut relit =
        resume(&deposit(CURRENT_TAG, &form).expect("a deposit").plate).expect("a re-light");
    let refusal = present_and_require_change(relit.body.as_mut(), &training_deed())
        .expect_err("a deed addressed elsewhere must refuse");
    let ResumeRefusal::DeedRefused { detail } = &refusal else {
        panic!("expected DeedRefused, got {refusal}");
    };
    assert!(detail.contains("addressed to schema HTEC"), "{detail}");
    assert!(detail.contains("not re-addressed by guessing"), "{detail}");
}

#[test]
fn the_deed_wires_round_trip_and_refuse_trailing_octets() {
    let deed = TrainingDeed {
        faces: vec![face("left", 3, "three")],
        parameters: parameters("gamma"),
        consequence: b"nine".to_vec(),
    };
    assert_eq!(TrainingDeed::decode(&deed.encode()).expect("a deed"), deed);

    let deed = CurrentDeed {
        relation: -63_245,
        action: 1,
    };
    let encoded = deed.encode();
    assert_eq!(encoded.len(), DEED_HEAD_OCTETS + 16);
    assert_eq!(CurrentDeed::decode(&encoded).expect("a deed"), deed);

    let mut trailing = encoded.clone();
    trailing.push(0);
    assert!(CurrentDeed::decode(&trailing).is_err());
    assert!(CurrentDeed::decode(&encoded[..encoded.len() - 1]).is_err());
}

#[test]
fn a_deed_the_body_refuses_leaves_the_body_where_it_was() {
    let form = current_form();
    let deposited = deposit(CURRENT_TAG, &form).expect("a deposit");
    let mut relit = resume(&deposited.plate).expect("a re-light");
    // zero is the absence of an event action, not an action; the abi refuses it
    let refusal = present_and_require_change(
        relit.body.as_mut(),
        &CurrentDeed {
            relation: 71,
            action: 0,
        }
        .encode(),
    )
    .expect_err("a deed with no action current must refuse");
    let ResumeRefusal::DeedRefused { detail } = &refusal else {
        panic!("expected DeedRefused, got {refusal}");
    };
    assert!(detail.contains("absence of an event action"), "{detail}");
    let again = redeposit(CURRENT_TAG, relit.body.as_ref()).expect("a re-deposit");
    assert_eq!(
        again.plate, deposited.plate,
        "a refused deed must leave the body exactly where it was"
    );
}

// ---------------------------------------------------------------------------------------------
// RBIN: the reading, the declared bijection, and the field the hand-off moves

fn rebase_census(complex: &GradedCausalComplex) -> Census {
    RebaseBody::mount(&rebase_form(complex))
        .expect("a mounted incidence")
        .census()
        .expect("a reading")
}

fn field(census: &Census, name: &str) -> u64 {
    census
        .value(name)
        .unwrap_or_else(|| panic!("`{name}` is declared"))
}

/// The census is the reading, field for field, on four incidences whose readings genuinely differ.
///
/// Every number below is derivable by hand from `b_k = n_k - rank(d_k) - rank(d_{k+1})`, which is
/// why they are written out rather than recomputed from the same call that produced them: a test
/// that re-derived the census from the census could not fail.
#[test]
fn the_rbin_census_is_the_reading_taken_over_the_incidence() {
    let hollow = rebase_census(&hollow_triangle());
    assert_eq!(field(&hollow, "cells"), 6);
    assert_eq!(field(&hollow, "grades"), 2);
    assert_eq!(field(&hollow, "boundary_rank_total"), 2);
    assert_eq!(field(&hollow, "betti_total"), 2, "one piece, one loop");
    assert_eq!(field(&hollow, "torsion_factors"), 0);
    assert_eq!(field(&hollow, "euler_positive"), 0);
    assert_eq!(field(&hollow, "euler_negative"), 0);

    let filled = rebase_census(&filled_triangle());
    assert_eq!(field(&filled, "cells"), 7);
    assert_eq!(field(&filled, "grades"), 3);
    assert_eq!(field(&filled, "boundary_rank_total"), 3);
    assert_eq!(
        field(&filled, "betti_total"),
        1,
        "the filled loop is not a generator"
    );
    assert_eq!(field(&filled, "torsion_factors"), 0);

    let theta = rebase_census(&theta_graph());
    assert_eq!(field(&theta, "cells"), 5);
    assert_eq!(field(&theta, "boundary_rank_total"), 1);
    assert_eq!(field(&theta, "betti_total"), 3, "one piece, two loops");

    let doubled = rebase_census(&doubled_attachment());
    assert_eq!(field(&doubled, "cells"), 3);
    assert_eq!(field(&doubled, "grades"), 3);
    assert_eq!(field(&doubled, "boundary_rank_total"), 1);
    assert_eq!(field(&doubled, "betti_total"), 1);
}

/// **The nonzero control.** `torsion_factors` is the field this schema exists to carry, and a
/// census in which it is zero on every declared body would be a law that has never returned.
///
/// It is also the field a census cannot hold: the coefficients are `BigInt`s of varying arity. So
/// this asserts both halves — the count in the census is nonzero, and the coefficients themselves
/// come back whole from [`RebaseBody::reading`], which is what travels to a next organ.
#[test]
fn the_torsion_reading_is_provably_nonzero_and_comes_back_whole() {
    let body = RebaseBody::mount(&rebase_form(&doubled_attachment())).expect("a mount");
    let census = body.census().expect("a reading");
    assert_eq!(
        field(&census, "torsion_factors"),
        1,
        "the doubled attachment deposits a Z/2 and the census must count it"
    );

    let reading = body.reading().expect("the population itself").invariants;
    assert_eq!(
        reading.total_torsion(),
        vec![BigInt::from(2)],
        "the census counts the factors; the reading must return the factors themselves"
    );
    assert_eq!(reading.betti_vector(), vec![1, 0, 0]);
    assert_eq!(
        reading.grades[1].torsion,
        vec![BigInt::from(2)],
        "the winding sits at grade 1 and the reading says which grade"
    );

    // and the control's own control: an incidence with no doubled attachment returns none, so the
    // field above is reporting the material rather than the form.
    let flat = RebaseBody::mount(&rebase_form(&hollow_triangle())).expect("a mount");
    assert_eq!(
        field(&flat.census().expect("a reading"), "torsion_factors"),
        0
    );
    assert!(flat
        .reading()
        .expect("a reading")
        .invariants
        .total_torsion()
        .is_empty());
}

/// `i64 -> u64` is a declared bijection, never a cast.
#[test]
fn the_euler_pair_is_a_total_bijection_and_a_cast_would_not_be() {
    for characteristic in [i64::MIN, -1_000_000, -2, -1, 0, 1, 2, 1_000_000, i64::MAX] {
        let (positive, negative) = encode_euler(characteristic);
        assert!(
            positive == 0 || negative == 0,
            "{characteristic}: both halves of the pair are nonzero"
        );
        assert_eq!(
            decode_euler(positive, negative),
            Some(characteristic),
            "{characteristic} did not survive the pair"
        );
    }

    // the cast this refuses: `-1 as u64` is indistinguishable from an enormous positive count
    assert_eq!(encode_euler(-1), (0, 1));
    assert_ne!(encode_euler(-1).0, (-1i64) as u64);

    // outside the image, decoding returns None rather than guessing which half was meant
    assert_eq!(decode_euler(3, 4), None, "both nonzero is not in the image");
    assert_eq!(decode_euler(0, (i64::MAX as u64) + 2), None);
    assert_eq!(decode_euler((i64::MAX as u64) + 1, 0), None);
    assert_eq!(decode_euler(0, (i64::MAX as u64) + 1), Some(i64::MIN));
}

/// The pair must be exercised on **both** sides of zero and at it, or half the encoding is
/// declared and never run. Three incidences, three signs.
#[test]
fn three_incidences_place_the_euler_characteristic_on_both_sides_of_zero_and_at_it() {
    let filled = rebase_census(&filled_triangle());
    assert_eq!(
        (
            field(&filled, "euler_positive"),
            field(&filled, "euler_negative")
        ),
        (1, 0),
        "3 - 3 + 1 = +1"
    );

    let theta = rebase_census(&theta_graph());
    assert_eq!(
        (
            field(&theta, "euler_positive"),
            field(&theta, "euler_negative")
        ),
        (0, 1),
        "2 - 3 = -1, and a cast would have written 18446744073709551615 here"
    );

    let hollow = rebase_census(&hollow_triangle());
    assert_eq!(
        (
            field(&hollow, "euler_positive"),
            field(&hollow, "euler_negative")
        ),
        (0, 0),
        "3 - 3 = 0, the one value both halves share"
    );

    // and every declared pair is in the image, so a reader can recover the signed characteristic
    for (label, census, expected) in [
        ("filled", &filled, 1i64),
        ("theta", &theta, -1),
        ("hollow", &hollow, 0),
    ] {
        assert_eq!(
            decode_euler(
                field(census, "euler_positive"),
                field(census, "euler_negative")
            ),
            Some(expected),
            "{label}: the declared pair does not decode to the characteristic it encodes"
        );
    }
}

/// The claim the schema's doc comment makes, run on one body across two deeds.
///
/// The two deeds are **both at grade 1**, which is the whole point of the fixture: `cells` and the
/// Euler pair move identically under both, and only `betti_total` moves in the direction that says
/// what the deed did to the homology.
#[test]
fn the_deed_moves_betti_total_in_the_direction_that_says_what_it_did() {
    let mut disjoint = GradedCausalComplex::default();
    vertex(&mut disjoint, "a");
    vertex(&mut disjoint, "b");

    let deposited = deposit(REBASE_TAG, &rebase_form(&disjoint)).expect("a deposit");
    let mut relit = resume(&deposited.plate).expect("a re-light");

    // the first edge joins the two pieces: the new column is independent, so a generator DIES
    let (before, joined) =
        present_and_require_change(relit.body.as_mut(), &joining_deed("ab", 1, 2))
            .expect("a joining deed");
    assert_eq!(
        field(&before, "betti_total"),
        2,
        "two disjoint vertices, two generators"
    );
    assert_eq!(
        field(&joined, "betti_total"),
        1,
        "joining two pieces must KILL a generator"
    );

    // the second edge closes a loop: the new column is dependent, so a generator is FOUNDED
    let (_, looped) = present_and_require_change(relit.body.as_mut(), &joining_deed("ab2", 1, 2))
        .expect("a second joining deed");
    assert_eq!(
        field(&looped, "betti_total"),
        2,
        "a second edge on the same pair must FOUND a generator"
    );

    // and the five other fields cannot say that, which is why the schema names betti_total
    assert_eq!(
        (
            field(&before, "cells"),
            field(&joined, "cells"),
            field(&looped, "cells")
        ),
        (2, 3, 4),
        "`cells` moves by +1 under both deeds and so distinguishes neither"
    );
    assert_eq!(
        (
            field(&before, "euler_positive"),
            field(&joined, "euler_positive"),
            field(&looped, "euler_positive")
        ),
        (2, 1, 0),
        "the Euler pair moves by -1 under both deeds -- it records the grade, not the consequence"
    );
    assert_eq!(
        field(&joined, "boundary_rank_total"),
        field(&looped, "boundary_rank_total"),
        "`boundary_rank_total` does not move at all under the second deed"
    );
    assert_eq!(
        field(&joined, "grades"),
        field(&looped, "grades"),
        "`grades` does not move once the top grade is open"
    );
    assert_eq!(
        (
            field(&before, "torsion_factors"),
            field(&joined, "torsion_factors"),
            field(&looped, "torsion_factors")
        ),
        (0, 0, 0),
        "`torsion_factors` never moves here, which is why it cannot be the witness"
    );

    // the moved body is durable: it re-deposits to a different plate, and that plate re-lights
    let moved = redeposit(REBASE_TAG, relit.body.as_ref()).expect("a re-deposit");
    assert_ne!(moved.plate, deposited.plate);
    assert_eq!(resume(&moved.plate).expect("a re-light").relit, looped);
}

/// A deed the founder refuses must leave the incidence exactly where it was, and must be refused
/// by the mechanism rather than by a check the schema wrote beside it.
#[test]
fn a_deed_that_would_break_the_incidence_is_refused_and_the_body_stays_where_it_was() {
    let deposited = deposit(REBASE_TAG, &rebase_form(&hollow_triangle())).expect("a deposit");

    let refusals: [(Vec<u8>, &str); 4] = [
        // a grade-2 cell whose face is a vertex: the grades do not step by one
        (
            RebaseDeed {
                name: "misgraded".to_owned(),
                grade: 2,
                source_events: vec![7],
                boundary: vec![BoundaryTerm {
                    cell: 1,
                    positive: 1,
                    negative: 0,
                }],
            }
            .encode(),
            "boundary",
        ),
        // a vertex carrying a boundary
        (
            RebaseDeed {
                name: "heavy".to_owned(),
                grade: 0,
                source_events: vec![7],
                boundary: vec![BoundaryTerm {
                    cell: 1,
                    positive: 1,
                    negative: 0,
                }],
            }
            .encode(),
            "boundary",
        ),
        // an uncaused cell
        (
            RebaseDeed {
                name: "uncaused".to_owned(),
                grade: 0,
                source_events: Vec::new(),
                boundary: Vec::new(),
            }
            .encode(),
            "source occurrence",
        ),
        // a term declaring the same population on each hand: no incidence at all
        (
            RebaseDeed {
                name: "empty-term".to_owned(),
                grade: 1,
                source_events: vec![7],
                boundary: vec![BoundaryTerm {
                    cell: 1,
                    positive: 3,
                    negative: 3,
                }],
            }
            .encode(),
            "no incidence at all",
        ),
    ];

    for (deed, expected) in refusals {
        let mut relit = resume(&deposited.plate).expect("a re-light");
        let refusal = present_and_require_change(relit.body.as_mut(), &deed)
            .expect_err("a deed that breaks the incidence must refuse");
        let ResumeRefusal::DeedRefused { detail } = &refusal else {
            panic!("expected DeedRefused, got {refusal}");
        };
        assert!(
            detail.to_lowercase().contains(expected),
            "the refusal must name what it refused: {detail}"
        );
        let again = redeposit(REBASE_TAG, relit.body.as_ref()).expect("a re-deposit");
        assert_eq!(
            again.plate, deposited.plate,
            "a refused deed must leave the incidence exactly where it was"
        );
    }
}

/// A deed's source events arrive as a `Vec` and are mounted into a `BTreeSet`, so a repeat would
/// be silently absorbed and the deed would found a cell the depositor did not write.
///
/// The refusal is advertised in the schema's own `deed_shape()` and had no test; removing it killed
/// nothing. It is the deed-side twin of the form-side `NotAscending { field: "source events" }`,
/// and the distinction it enforces is the project's own: *an occurrence recurs, a source event does
/// not.*
#[test]
fn a_deed_repeating_a_source_occurrence_is_refused_rather_than_absorbed() {
    let deposited = deposit(REBASE_TAG, &rebase_form(&hollow_triangle())).expect("a deposit");
    let mut relit = resume(&deposited.plate).expect("a re-light");

    let repeated = RebaseDeed {
        name: "twice-caused".to_owned(),
        grade: 0,
        source_events: vec![7, 7],
        boundary: Vec::new(),
    }
    .encode();
    let refusal = present_and_require_change(relit.body.as_mut(), &repeated)
        .expect_err("a repeated source occurrence must refuse");
    let ResumeRefusal::DeedRefused { detail } = &refusal else {
        panic!("expected DeedRefused, got {refusal}");
    };
    assert!(
        detail.contains("repeats the source occurrence 7"),
        "the refusal must name the occurrence it refused: {detail}"
    );
    let again = redeposit(REBASE_TAG, relit.body.as_ref()).expect("a re-deposit");
    assert_eq!(
        again.plate, deposited.plate,
        "a refused deed must leave the incidence exactly where it was"
    );

    // the control: the same deed with the repeat removed is accepted, so the refusal is the
    // repeat and not the deed
    let honest = RebaseDeed {
        name: "twice-caused".to_owned(),
        grade: 0,
        source_events: vec![7, 9],
        boundary: Vec::new(),
    }
    .encode();
    let (before, after) = present_and_require_change(relit.body.as_mut(), &honest)
        .expect("two distinct occurrences must be accepted");
    assert_eq!(field(&before, "cells") + 1, field(&after, "cells"));
}

/// The second frame, on the field the schema names.
#[test]
fn a_forged_rbin_census_refuses_and_names_the_field() {
    let form = rebase_form(&doubled_attachment());
    let honest = deposit(REBASE_TAG, &form).expect("a deposit");
    let truth = honest
        .census
        .value("torsion_factors")
        .expect("torsion_factors");

    let forged: Vec<(String, u64)> = honest
        .census
        .rows()
        .iter()
        .map(|(name, value)| {
            if name == "torsion_factors" {
                (name.clone(), value + 4)
            } else {
                (name.clone(), *value)
            }
        })
        .collect();
    let forged = Census::found(forged).expect("a census");
    let plate = plate::seal(REBASE_TAG, REBASE_SCHEMA_VERSION, &forged, &form);

    // both digests hold, so nothing but a recomputation can catch this
    inspect(&plate).expect("the container itself is intact");
    let refusal = resume(&plate).expect_err("a forged declaration must refuse");
    let ResumeRefusal::CensusDrift {
        field,
        declared,
        relit,
    } = &refusal
    else {
        panic!("expected CensusDrift, got {refusal}");
    };
    assert_eq!(field, "torsion_factors");
    assert_eq!(*declared, truth + 4);
    assert_eq!(*relit, truth);
}

/// **The three-rule cross-check, gauged.**
///
/// `reading_of` recomputes the reading under every declared [`PivotRule`] and requires the three to
/// agree. That is only evidence if the three rules computed *differently*, and on every fixture
/// this project had until now they did not: a simplicial boundary matrix has every nonzero entry at
/// magnitude one, `find_pivot` breaks ties with strict `<` and `>`, so all three rules select the
/// first nonzero. Cutting `PivotRule::ALL` down to one rule killed no test in this file.
///
/// `staggered_attachment` is the material that fixes it, and this asserts both halves: three
/// schedules come back, they are pairwise different, and the invariants they agreed on carry a
/// `Z/2`. The four simplicial bodies are asserted to walk **one** sequence, so the aperture of the
/// gauge is declared rather than discovered.
#[test]
fn the_three_rule_cross_check_runs_over_three_genuinely_different_pivot_walks() {
    use holonic_engine::rebase_invariants::PivotRule;

    type Walk = Vec<(u32, Vec<(usize, usize)>)>;
    fn walks_of(complex: &GradedCausalComplex) -> (Vec<PivotRule>, BTreeSet<Walk>) {
        let reading = RebaseBody::mount(&rebase_form(complex))
            .expect("a mount")
            .reading()
            .expect("a reading");
        let rules = reading.schedules.iter().map(|walk| walk.rule).collect();
        let walks = reading
            .schedules
            .iter()
            .map(|schedule| {
                schedule
                    .per_grade
                    .iter()
                    .map(|(grade, walk)| (*grade, walk.selections.clone()))
                    .collect::<Walk>()
            })
            .collect();
        (rules, walks)
    }

    let (rules, walks) = walks_of(&staggered_attachment());
    assert_eq!(
        rules,
        PivotRule::ALL.to_vec(),
        "the cross-check must run every declared rule, in order, and say which walked which"
    );
    assert_eq!(
        walks.len(),
        3,
        "the three rules must take three different pivot walks or their agreement is one \
         computation compared with itself twice: {walks:?}"
    );

    let staggered = RebaseBody::mount(&rebase_form(&staggered_attachment()))
        .expect("a mount")
        .reading()
        .expect("a reading");
    assert_eq!(
        staggered.invariants.total_torsion(),
        vec![BigInt::from(2)],
        "the reading the three walks agreed on must be a nontrivial one"
    );
    let census = rebase_census(&staggered_attachment());
    assert_eq!(field(&census, "cells"), 6);
    assert_eq!(field(&census, "grades"), 3);
    assert_eq!(field(&census, "boundary_rank_total"), 2);
    assert_eq!(
        field(&census, "betti_total"),
        2,
        "one piece, one unfilled loop"
    );
    assert_eq!(field(&census, "torsion_factors"), 1);

    // the aperture of the gauge, declared: a simplicial body cannot gauge the rule at all
    for (label, complex) in [
        ("hollow_triangle", hollow_triangle()),
        ("filled_triangle", filled_triangle()),
        ("theta_graph", theta_graph()),
        ("doubled_attachment", doubled_attachment()),
    ] {
        let (_, walks) = walks_of(&complex);
        assert_eq!(
            walks.len(),
            1,
            "{label}: every nonzero entry is a unit here, so all three rules walk one sequence and \
             a three-rule agreement over this body is not evidence"
        );
    }
}

/// The pivot rule is a solver coordinate and the census is computed under all three. This asserts
/// the agreement independently rather than trusting the schema's own loop.
#[test]
fn the_pivot_rule_does_not_reach_the_rbin_census() {
    use holonic_engine::rebase_invariants::{invariants_agree, rebase_invariants, PivotRule};

    for complex in [
        hollow_triangle(),
        filled_triangle(),
        theta_graph(),
        doubled_attachment(),
        staggered_attachment(),
    ] {
        let census = rebase_census(&complex);
        let mut settled: Option<_> = None;
        for rule in PivotRule::ALL {
            let reading = rebase_invariants(&complex, rule).expect("a reading");
            let betti: u64 = reading.grades.iter().map(|grade| grade.betti as u64).sum();
            let torsion: u64 = reading
                .grades
                .iter()
                .map(|grade| grade.torsion.len() as u64)
                .sum();
            assert_eq!(field(&census, "betti_total"), betti, "under {rule:?}");
            assert_eq!(field(&census, "torsion_factors"), torsion, "under {rule:?}");
            match &settled {
                None => settled = Some(reading),
                Some(first) => assert!(
                    invariants_agree(first, &reading),
                    "{rule:?} moved the returned invariants"
                ),
            }
        }
    }
}

#[test]
fn the_rbin_deed_wire_round_trips_and_refuses_a_misaddressed_or_trailing_one() {
    let deed = RebaseDeed {
        name: "wide".to_owned(),
        grade: 2,
        source_events: vec![3, 5, 8],
        boundary: vec![
            BoundaryTerm {
                cell: 2,
                positive: 7,
                negative: 0,
            },
            BoundaryTerm {
                cell: 4,
                positive: 0,
                negative: 11,
            },
        ],
    };
    let encoded = deed.encode();
    assert_eq!(RebaseDeed::decode(&encoded).expect("a deed"), deed);

    let mut trailing = encoded.clone();
    trailing.push(0);
    assert!(RebaseDeed::decode(&trailing).is_err());
    assert!(RebaseDeed::decode(&encoded[..encoded.len() - 1]).is_err());
    assert!(
        RebaseDeed::decode(&training_deed()).is_err(),
        "a deed addressed to HTEC is not re-addressed by guessing"
    );

    // and at the plate's mouth, presented to the wrong body
    let mut relit = resume(
        &deposit(TRAINING_TAG, &training_form())
            .expect("a deposit")
            .plate,
    )
    .expect("a re-light");
    let refusal = present_and_require_change(relit.body.as_mut(), &encoded)
        .expect_err("a deed addressed to RBIN must refuse at an HTEC body");
    let ResumeRefusal::DeedRefused { detail } = &refusal else {
        panic!("expected DeedRefused, got {refusal}");
    };
    assert!(detail.contains("addressed to schema RBIN"), "{detail}");
}

// ---------------------------------------------------------------------------------------------
// inspect lights nothing

#[test]
fn inspect_verifies_the_container_and_does_not_mount_the_form() {
    // A plate whose head and census are honest but whose form is not a form of its schema: the
    // container is intact, so `inspect` reports it; `resume` mounts and refuses.
    let census = Census::found([
        ("active_templates", 0u64),
        ("fibers", 0),
        ("generation", 0),
        ("minimum_recurrence", 2),
        ("route_aperture", 8),
    ])
    .expect("a census");
    let plate = plate::seal(
        TRAINING_TAG,
        TRAINING_SCHEMA_VERSION,
        &census,
        b"not a form",
    );
    let report = inspect(&plate).expect("the container verifies");
    assert!(report.held);
    assert_eq!(report.form_octets, 10);
    let refusal = resume(&plate).expect_err("mounting must refuse");
    assert!(matches!(refusal, ResumeRefusal::FormRefused { .. }));
}
