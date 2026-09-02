//! WRD resident tests: the Lean declaration lattice mounts and conducts, and the kernel-face
//! junction derives the returned interaction that the session stages, commits, and withdraws.
//!
//! These tests bind the resident CUDA apparatus. They live in their own test binary because the
//! library suite's particle fixture measures the allocation grain against an exactly closing free
//! extent, and any concurrent resident allocation in the same process breaks that measurement.
//! Cargo runs test binaries one after another; inside this binary the tests serialize on one lock.

use std::collections::BTreeSet;
use std::sync::Mutex;

use holonic_engine::native_ecology::holonic_intelligence::{
    NativeInferenceAddress, NativeInferenceRequest,
};
use holonic_engine::receiver_exact_compression::ReceiverId;
use holonic_engine::{BoundaryId, EventId, ExactComplexWaveCurrent};
use life::lean_mathematics::{
    found_lean_lattice, generator_thread_address, LeanLatticeColdWitness, LeanMathematicsEcology,
    LeanSourceDocument, LEAN_LATTICE_SPOOL_ADDRESS,
};
use life::native_intelligence::route_return::{
    derive_world_return, KernelReturnFace, Termination, WorldReturnDisposition,
};
use life::native_intelligence::{
    ApparatusRealization, InferenceConfigurationAddress, MorphologyLineage,
    NativeCirculationBoundary, NativeCirculationConfiguration, NativeCirculationSession,
    NativeEcologyRest, NativeMorphologyPackage,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;

static RESIDENT: Mutex<()> = Mutex::new(());

const CORPUS: &str = "theorem alpha (n : Nat) : n + 0 = n := by\n  simp\n\n\
theorem beta (n : Nat) : 0 + n = n := by\n  rw [Nat.zero_add]\n\n\
theorem gamma (n : Nat) : n + 0 = 0 + n := by\n  rw [alpha, beta]\n\n\
theorem delta (n : Nat) : 0 + n = n + 0 := by\n  rw [gamma]\n";

const RECEIVER: ReceiverId = ReceiverId(7);
const FACE: BoundaryId = BoundaryId(0);

fn names(list: &[&str]) -> BTreeSet<String> {
    list.iter().map(|name| (*name).to_owned()).collect()
}

fn mounted() -> (NativeCirculationSession, LeanLatticeColdWitness, NativeCirculationBoundary) {
    let documents = vec![LeanSourceDocument::new("Test/Route.lean", CORPUS)];
    let ecology = LeanMathematicsEcology::condition(&documents).expect("conditions");
    let returned = found_lean_lattice(&ecology, RECEIVER).expect("lattice");
    let witness = returned.witness;
    let wire_before = returned.native.canonical_bytes().expect("wire");
    let rest = NativeEcologyRest::found(returned.native).expect("rest");
    let package = NativeMorphologyPackage::found(
        rest,
        MorphologyLineage::origin(),
        Vec::new(),
        vec![ApparatusRealization {
            apparatus_family: "lean-lattice-mouth".to_owned(),
            realization_version: "v1".to_owned(),
        }],
        Vec::new(),
    )
    .expect("package");
    assert_eq!(
        package.hot().native().canonical_bytes().expect("wire"),
        wire_before,
        "the witness departing leaves the scaffold identity unchanged"
    );
    let gamma = witness.generator_of("gamma").expect("gamma");
    let occurrence = witness.occurrence_of("alpha", "gamma").expect("occurrence");
    let configuration = NativeCirculationConfiguration::found(InferenceConfigurationAddress {
        ingress_aperture: "lean-declaration-lattice".to_owned(),
        occurrence,
        receiver: RECEIVER,
        continuation_receiver: "native-successor".to_owned(),
        world_return_law: "lean-kernel-junction".to_owned(),
        emission_codec: "route-organs".to_owned(),
        apparatus: "resident".to_owned(),
        stochastic_current: None,
    })
    .expect("configuration");
    let session = NativeCirculationSession::mount(package, configuration).expect("mount");
    let boundary = session
        .conduct(NativeInferenceRequest {
            address: NativeInferenceAddress {
                spool: LEAN_LATTICE_SPOOL_ADDRESS.to_owned(),
                thread: generator_thread_address(gamma),
                occurrence,
            },
            receiver: RECEIVER,
        })
        .expect("conduct");
    (session, witness, boundary)
}

#[test]
fn the_lattice_mounts_and_one_conduct_returns_plural_futures_and_actual_successors() {
    let _resident = RESIDENT.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    let (_session, _witness, boundary) = mounted();
    assert_eq!(boundary.futures.len(), 2, "both premises of gamma are futures");
    assert!(
        !boundary.actual_successors.is_empty(),
        "the later proof that carries gamma is an actual successor"
    );
}

#[test]
fn a_matched_return_deposits_with_storage_one_and_halts() {
    let _resident = RESIDENT.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    let (session, witness, boundary) = mounted();
    let faces = vec![KernelReturnFace {
        admitted: true,
        carried: names(&["alpha", "beta"]),
        diagnostic: String::new(),
    }];
    let disposition =
        derive_world_return(&boundary, &witness, &faces, EventId(100), FACE).expect("derive");
    assert_eq!(disposition.termination(), Termination::Halt);
    let WorldReturnDisposition::Matched {
        returned, junction, ..
    } = disposition
    else {
        panic!("a fully admitted route matches");
    };
    assert_eq!(junction.service_rounds, 1);
    assert_eq!(returned.storage, Rat::from_integer(BigInt::from(1)));
    assert_eq!(returned.exterior_current, ExactComplexWaveCurrent::one());
    for name in ["alpha", "beta", "gamma"] {
        assert!(returned
            .contact_support
            .contains(&witness.state_of(name).expect("state")));
    }
    let before = session.package().hot().native().canonical_bytes().expect("wire");
    let candidate = session.stage_return(&boundary, returned).expect("stage");
    let (session, commit) = session.commit(candidate).expect("commit");
    assert_eq!(session.generation(), 1);
    assert_eq!(commit.causal_cone.len(), 3, "the cone is the route");
    let (session, _) = session.withdraw_last_commit().expect("withdraw");
    assert_eq!(
        session.package().hot().native().canonical_bytes().expect("wire"),
        before,
        "withdrawal restores the predecessor exactly"
    );
}

#[test]
fn a_closer_admitted_without_organs_deposits_on_the_route_ends_alone() {
    let _resident = RESIDENT.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    let (_session, witness, boundary) = mounted();
    let faces = vec![
        KernelReturnFace {
            admitted: true,
            carried: BTreeSet::new(),
            diagnostic: String::new(),
        },
        KernelReturnFace {
            admitted: false,
            carried: names(&["alpha", "beta"]),
            diagnostic: String::new(),
        },
    ];
    let disposition =
        derive_world_return(&boundary, &witness, &faces, EventId(100), FACE).expect("derive");
    let WorldReturnDisposition::Reflected {
        returned, reflected, ..
    } = disposition
    else {
        panic!("one admitted emission of two reflects");
    };
    assert_eq!(reflected, names(&["alpha", "beta"]));
    assert_eq!(
        returned.contact_support,
        BTreeSet::from([
            witness.state_of("alpha").expect("from"),
            witness.state_of("gamma").expect("to"),
        ]),
        "the cone is the route's two ends when no admitted emission carried an organ"
    );
}

#[test]
fn a_partial_return_deposits_between_zero_and_one_and_reenters_or_opens() {
    let _resident = RESIDENT.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    let (_session, witness, boundary) = mounted();
    let faces = vec![
        KernelReturnFace {
            admitted: true,
            carried: names(&["alpha"]),
            diagnostic: String::new(),
        },
        KernelReturnFace {
            admitted: false,
            carried: names(&["beta"]),
            diagnostic: "error: unknown identifier 'beta'".to_owned(),
        },
    ];
    let disposition =
        derive_world_return(&boundary, &witness, &faces, EventId(100), FACE).expect("derive");
    let WorldReturnDisposition::Reflected {
        returned,
        junction,
        reflected,
        next_entering,
        ..
    } = disposition
    else {
        panic!("a partly admitted route reflects");
    };
    assert_eq!((junction.incident, junction.transmitted), (2, 1));
    assert_eq!(junction.service_rounds, 2);
    let zero = Rat::from_integer(BigInt::from(0));
    let one = Rat::from_integer(BigInt::from(1));
    assert!(returned.storage > zero && returned.storage < one);
    assert_eq!(returned.exterior_current.imaginary, junction.reflection_current());
    assert_eq!(reflected, names(&["beta"]));
    assert_eq!(next_entering, None, "beta carries no in-corpus premise to re-enter at");
}

#[test]
fn a_boundary_admitting_nothing_is_a_terminus_that_founds_the_next_entering_occurrence() {
    let _resident = RESIDENT.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    let (_session, witness, boundary) = mounted();
    let faces = vec![KernelReturnFace {
        admitted: false,
        carried: names(&["gamma"]),
        diagnostic: "error: gamma does not close the goal".to_owned(),
    }];
    let disposition =
        derive_world_return(&boundary, &witness, &faces, EventId(100), FACE).expect("derive");
    assert!(disposition.returned().is_none(), "a terminus deposits nothing");
    let expected = witness.occurrence_of("alpha", "gamma").expect("gamma's premise crossing");
    assert_eq!(disposition.termination(), Termination::Reenter(expected));
}
