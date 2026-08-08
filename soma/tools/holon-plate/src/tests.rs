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

use std::collections::BTreeMap;

use body::num::Cog;
use life::holonic_training::{FaceAddress, SourceFace, TrainingEcology};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, CurrentEvent, CurrentGeometry, LiveCurrentMachine, SparseStandingSurface,
};

use crate::census::Census;
use crate::deed::DEED_HEAD_OCTETS;
use crate::plate::{self, PlateRefusal, SchemaTag, HEAD_OCTETS, SEAL_OCTETS};
use crate::registry::{deposit, inspect, redeposit, resume};
use crate::schema::{present_and_require_change, LitBody, PlateSchema, ResumeRefusal};
use crate::schemas::current::{CurrentDeed, CURRENT_SCHEMA_VERSION, CURRENT_TAG};
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
            CurrentEvent::continuing(lineages[0], CurrentGeometry::Cell(relation(value)), action()),
            CurrentEvent::continuing(lineages[1], CurrentGeometry::Cell(relation(value)), action()),
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

fn bodies() -> [(SchemaTag, Vec<u8>, Vec<u8>); 2] {
    [
        (TRAINING_TAG, training_form(), training_deed()),
        (CURRENT_TAG, current_form(), current_deed()),
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
        let census_octets = inspect(&deposited.plate).expect("an inspection").census_octets;
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
        let census_octets = inspect(&deposited.plate).expect("an inspection").census_octets;
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
    let census_octets = inspect(&deposited.plate).expect("an inspection").census_octets;
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
    let census_octets = inspect(&deposited.plate).expect("an inspection").census_octets;
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
    assert!(crate::schemas::training::TrainingSchema.relight(&form).is_ok());

    let refusal = resume(&plate).expect_err("an unheld schema must refuse");
    let ResumeRefusal::SchemaUnheld { tag, version, held } = &refusal else {
        panic!("expected SchemaUnheld, got {refusal}");
    };
    assert_eq!(tag.to_string(), "ZZZZ");
    assert_eq!(*version, Some(1));
    assert_eq!(held, &["HTEC/1".to_owned(), "ERST/2".to_owned()]);
    let rendered = refusal.to_string();
    assert!(rendered.contains("ZZZZ/1"), "{rendered}");
    assert!(rendered.contains("HTEC/1"), "{rendered}");
    assert!(
        rendered.contains("not resumed by guessing"),
        "{rendered}"
    );
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
    // HTEC's codec writes b"HTEC\0\0\0\x01"; the schema version is that trailing octet.
    let form = training_form();
    assert_eq!(&form[0..8], b"HTEC\0\0\0\x01".as_slice());
    assert_eq!(TRAINING_SCHEMA_VERSION, u32::from(form[7]));
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
        census.rows().iter().map(|(name, _)| name.as_str()).collect::<Vec<_>>(),
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
    let mut relit = resume(&deposit(TRAINING_TAG, &form).expect("a deposit").plate).expect("a re-light");
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
    let refusal =
        present_and_require_change(&mut inert, &training_deed()).expect_err("an inert body refuses");
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
    let mut relit = resume(&deposit(CURRENT_TAG, &form).expect("a deposit").plate).expect("a re-light");
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
    let plate = plate::seal(TRAINING_TAG, TRAINING_SCHEMA_VERSION, &census, b"not a form");
    let report = inspect(&plate).expect("the container verifies");
    assert!(report.held);
    assert_eq!(report.form_octets, 10);
    let refusal = resume(&plate).expect_err("mounting must refuse");
    assert!(matches!(refusal, ResumeRefusal::FormRefused { .. }));
}
