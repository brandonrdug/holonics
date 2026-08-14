//! `cargo run -p holon-plate --example emit_form -- HTEC out.form`
//! `cargo run -p holon-plate --example emit_form -- ERST out.form`
//! `cargo run -p holon-plate --example emit_form -- RBIN out.form`
//! `cargo run -p holon-plate --example emit_form -- CDER out.form`
//! `cargo run -p holon-plate --example emit_form -- HTEC-DEED out.deed`
//! `cargo run -p holon-plate --example emit_form -- ERST-DEED out.deed`
//! `cargo run -p holon-plate --example emit_form -- RBIN-DEED out.deed`
//! `cargo run -p holon-plate --example emit_form -- CDER-DEED out.deed`
//!
//! A driver, so that the mouth can be fed.
//!
//! The plate deposits forms that other drivers produce, and there is a real seam here worth
//! naming: every `soma/life/examples/*` driver that reaches a rest **hashes** its form into a JSON
//! receipt and then drops the octets. `grep -n encode_native_bytes soma/life/examples/` returns
//! twenty-odd sites and not one of them writes the form where a second process could pick it up.
//! Until those drivers open their own mouths, this is where a form comes from.
//!
//! The bodies here are small and are grown by their own machines — four real cultivations, three
//! real contemporary events. They are a **demonstration seed**, not evidence of anything: no
//! capability claim rests on them and the census they carry is whatever those occurrences actually
//! produced.
//!
//! `CDER` is the one species that no longer has to come from here. Its production driver,
//! `soma/life/examples/eros_mathematics_instance_rest.rs`, opens its own mouth and writes a real
//! 989 KB conditioned rest — a morphology founded on fourteen declared documents over a
//! 103-artifact standing — to `output/eros_mathematics_instance_rest/`. The seed below exists so
//! that the `--deed` path is reachable from a shell without running that driver first, and it is
//! deliberately tiny beside it.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use body::num::Cog;
use holon_plate::schemas::conditioned::ConditionedDeed;
use holon_plate::schemas::current::CurrentDeed;
use holon_plate::schemas::rebase::{BoundaryTerm, RebaseDeed};
use holon_plate::schemas::training::TrainingDeed;
use holonic_engine::algebraic::{CausalChain, ComparativeMultiplicity, GradedCausalComplex};
use holonic_engine::causal::EventId;
use holonic_engine::conditioned_derivation::{expose, ConditionedBody};
use holonic_engine::graded_complex_form::encode_native_bytes;
use life::conditioned_rest::ConditionedRest;
use life::holonic_training::{FaceAddress, SourceFace, TrainingEcology};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, CurrentEvent, CurrentGeometry, LiveCurrentMachine, SparseStandingSurface,
};

const USAGE: &str =
    "usage: emit_form (HTEC|ERST|RBIN|CDER|HTEC-DEED|ERST-DEED|RBIN-DEED|CDER-DEED) OUT";

fn main() -> Result<(), String> {
    let mut arguments = std::env::args().skip(1);
    let what = arguments.next().ok_or_else(|| USAGE.to_owned())?;
    let out = PathBuf::from(arguments.next().ok_or_else(|| USAGE.to_owned())?);

    let octets = match what.as_str() {
        "HTEC" => training_form()?,
        "ERST" => current_form()?,
        "RBIN" => rebase_form()?,
        "CDER" => conditioned_form()?,
        "HTEC-DEED" => training_deed(),
        "ERST-DEED" => current_deed(),
        "RBIN-DEED" => rebase_deed(),
        "CDER-DEED" => conditioned_deed(),
        other => return Err(format!("`{other}` is not a held schema\n{USAGE}")),
    };
    std::fs::write(&out, &octets)
        .map_err(|error| format!("cannot write {}: {error}", out.display()))?;
    println!("{} octets -> {}", octets.len(), out.display());
    Ok(())
}

fn training_form() -> Result<Vec<u8>, String> {
    let mut ecology = TrainingEcology::new(2, 8)?;
    let parameters = BTreeMap::from([("receiver".to_owned(), "alpha".to_owned())]);
    for ordinal in 0..4u64 {
        let faces = vec![
            SourceFace::new(FaceAddress::new("left", ordinal), b"seven".to_vec()),
            SourceFace::new(FaceAddress::new("right", ordinal), b"eight".to_vec()),
        ];
        ecology.cultivate(&faces, &parameters, b"fifty-six")?;
    }
    ecology.encode_native_bytes()
}

fn training_deed() -> Vec<u8> {
    TrainingDeed {
        faces: vec![
            SourceFace::new(FaceAddress::new("left", 9), b"nine".to_vec()),
            SourceFace::new(FaceAddress::new("right", 9), b"six".to_vec()),
        ],
        parameters: BTreeMap::from([("receiver".to_owned(), "beta".to_owned())]),
        consequence: b"fifty-four".to_vec(),
    }
    .encode()
}

fn current_form() -> Result<Vec<u8>, String> {
    let relation = |value: i64| {
        RelationAtom::new(Cog::lit(value)).ok_or_else(|| "a canonical relation".to_owned())
    };
    let action = ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "a resolving action".to_owned())?;
    let first = relation(13)?;
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let lineages = [
        machine
            .attach(CurrentGeometry::Cell(first))
            .map_err(debug)?,
        machine
            .attach(CurrentGeometry::Cell(first))
            .map_err(debug)?,
    ];
    for value in [13i64, 29, 17] {
        let currents = [
            CurrentEvent::continuing(lineages[0], CurrentGeometry::Cell(relation(value)?), action),
            CurrentEvent::continuing(lineages[1], CurrentGeometry::Cell(relation(value)?), action),
        ];
        machine
            .receive(ContemporaryEvent::unrelated(&currents))
            .map_err(debug)?;
    }
    machine
        .rest_image()
        .map_err(debug)?
        .encode_native_bytes()
        .map_err(debug)
}

/// A conditioned derivation body over two declared artifacts, conditioned by exposure to two
/// wholes. The deed below presents a third whole, which founds stems the first two never witnessed.
fn conditioned_form() -> Result<Vec<u8>, String> {
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
    .map_err(debug)?;
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
        .map_err(|refusal| refusal.to_string())?
        .encode_native_bytes()
        .map_err(|refusal| refusal.to_string())
}

fn conditioned_deed() -> Vec<u8> {
    ConditionedDeed {
        whole: "document:three".to_owned(),
        text: "a novel receiver family meets the exact carrier".to_owned(),
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

/// Two vertices joined by one edge, grown through the incidence's own founder. The RBIN deed below
/// closes a loop on it, so the re-lit body's `betti_total` moves the other way from the way the
/// joining edge moved it.
fn rebase_form() -> Result<Vec<u8>, String> {
    let source = BTreeSet::from([EventId(1)]);
    let mut complex = GradedCausalComplex::default();
    let a = complex
        .found_cell("a", source.clone(), 0, CausalChain::default())
        .map_err(debug)?;
    let b = complex
        .found_cell("b", source.clone(), 0, CausalChain::default())
        .map_err(debug)?;
    let mut boundary = CausalChain::default();
    boundary.add_term(b, ComparativeMultiplicity::positive(1u32));
    boundary.add_term(a, ComparativeMultiplicity::negative(1u32));
    complex
        .found_cell("ab", source, 1, boundary)
        .map_err(debug)?;
    encode_native_bytes(&complex).map_err(debug)
}

fn rebase_deed() -> Vec<u8> {
    RebaseDeed {
        name: "ab2".to_owned(),
        grade: 1,
        source_events: vec![7],
        boundary: vec![
            BoundaryTerm {
                cell: 2,
                positive: 1,
                negative: 0,
            },
            BoundaryTerm {
                cell: 1,
                positive: 0,
                negative: 1,
            },
        ],
    }
    .encode()
}

fn debug(error: impl core::fmt::Debug) -> String {
    format!("{error:?}")
}
