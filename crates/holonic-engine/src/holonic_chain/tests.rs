//! **One chain, read at two consumers: a synthetic two-body hinge that always runs, and the
//! measured M5 RBX1 window when its authenticated release is present.**
//!
//! [definition] Every law this module owns is checked without any fixture by the synthetic tests
//! below. The measured reading is a measurement, not a law, and is `#[ignore]`d for that reason —
//! the same gating `causal_chord/tests.rs` already uses for the M5 presentation.
//!
//! [implemented-exact] No `f32` and no `f64` appears on any carrying or deciding path here. The
//! only floats in the file are the two wall-clock `as_secs_f64` calls inside the measured
//! readings' `eprintln!` receipts, which are printed and decide nothing.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::Rat;

use super::*;
use crate::causal_chord::PoleReading;
use crate::exact_linear::ExactRatMatrix;
use crate::holonic_interaction::{
    ApertureChart, Carrier, ContactFace, Coupling, HolonicInteraction, Medium, MediumContact,
    Perspective, ReceiverBody, SourceCurrent,
};
use crate::inertia::SymmetricForm;
use crate::neck::{ConstitutiveLink, NeckReading, WidthFace};
use crate::physical_constraint_complex::{ConstraintEdge, ConstraintVertexId};
use crate::physical_constraint_grading::EdgeProvenance;
use crate::rigidity_receiver::{ExactConfiguration, RigidityJacobian, rigidity_reading};

fn int(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn rat(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn matrix(rows: usize, columns: usize, entries: &[i64]) -> ExactRatMatrix {
    ExactRatMatrix::shaped(
        rows,
        columns,
        entries
            .chunks(columns)
            .map(|row| row.iter().copied().map(int).collect())
            .collect(),
    )
    .expect("a declared matrix")
}

fn form(extent: usize, entries: &[i64]) -> SymmetricForm {
    SymmetricForm::from_rows(
        entries
            .chunks(extent)
            .map(|row| row.iter().copied().map(int).collect())
            .collect(),
    )
    .expect("a declared symmetric form")
}

fn identity(extent: usize) -> SymmetricForm {
    let mut entries = vec![0i64; extent * extent];
    for at in 0..extent {
        entries[at * extent + at] = 1;
    }
    form(extent, &entries)
}

fn places(coordinates: &[i64]) -> Vec<Rat> {
    coordinates.iter().copied().map(int).collect()
}

// =============================================================================================
// the abstract chain: one storage medium, one pinhole, one three-mode medium
// =============================================================================================

/// `|source⟩ → medium(1 mode) → skew neck → medium(3 modes) → ⟨perspective|` with the aperture
/// reading the declared downstream coordinate. `Ω_down` is the nearest-neighbour skew chain, so
/// what the perspective sees depends on how deep inside the downstream medium it reads.
fn skew_chain(aperture: &[i64]) -> HolonicChain {
    let upstream = Medium::declared("test|upstream", identity(1), matrix(1, 1, &[0]), Vec::new())
        .expect("the upstream medium stands");
    let downstream = Medium::declared(
        "test|downstream",
        identity(3),
        matrix(3, 3, &[0, 1, 0, -1, 0, 1, 0, -1, 0]),
        Vec::new(),
    )
    .expect("the downstream medium stands");
    let coupling = Coupling::declared(
        "test|neck",
        Carrier::Medium(0),
        Carrier::Medium(1),
        matrix(3, 1, &[1, 0, 0]),
    )
    .expect("the coupling stands");
    let source = SourceCurrent::declared(
        "test|source",
        Carrier::Medium(0),
        matrix(1, 1, &[1]),
        vec!["drive".to_owned()],
    )
    .expect("the source stands");
    let perspective = Perspective::standing(
        "test|perspective",
        Carrier::Medium(1),
        matrix(1, 3, aperture),
        vec!["read".to_owned()],
    )
    .expect("the perspective stands");
    let interaction = HolonicInteraction::declared(
        "test|skew-chain",
        source,
        vec![upstream, downstream],
        Vec::new(),
        vec![coupling],
        None,
        perspective,
    )
    .expect("the interaction stands");
    HolonicChain::over("test|skew-chain", interaction).expect("the chain reads")
}

/// The same two media joined by a **dissipative** contact face instead of a skew coupling: the
/// relative slip between the upstream mode and the downstream medium's first mode.
fn dissipative_chain(aperture: &[i64]) -> HolonicChain {
    let upstream = Medium::declared("test|upstream", identity(1), matrix(1, 1, &[0]), Vec::new())
        .expect("the upstream medium stands");
    let downstream = Medium::declared(
        "test|downstream",
        identity(3),
        matrix(3, 3, &[0, 1, 0, -1, 0, 1, 0, -1, 0]),
        Vec::new(),
    )
    .expect("the downstream medium stands");
    let contact = MediumContact::declared(
        "test|neck-contact",
        Carrier::Medium(0),
        Carrier::Medium(1),
        ContactFace::declared(
            "test|neck-face",
            matrix(1, 4, &[1, -1, 0, 0]),
            identity(1),
            Rat::one(),
        )
        .expect("the face stands"),
    )
    .expect("the contact stands");
    let source = SourceCurrent::declared(
        "test|source",
        Carrier::Medium(0),
        matrix(1, 1, &[1]),
        vec!["drive".to_owned()],
    )
    .expect("the source stands");
    let perspective = Perspective::standing(
        "test|perspective",
        Carrier::Medium(1),
        matrix(1, 3, aperture),
        vec!["read".to_owned()],
    )
    .expect("the perspective stands");
    let interaction = HolonicInteraction::declared(
        "test|dissipative-chain",
        source,
        vec![upstream, downstream],
        vec![contact],
        Vec::new(),
        None,
        perspective,
    )
    .expect("the interaction stands");
    HolonicChain::over("test|dissipative-chain", interaction).expect("the chain reads")
}

/// The same two media with **no** coupling and **no** contact: a closed neck.
fn closed_chain() -> HolonicChain {
    let upstream = Medium::declared("test|upstream", identity(1), matrix(1, 1, &[0]), Vec::new())
        .expect("the upstream medium stands");
    let downstream = Medium::declared(
        "test|downstream",
        identity(3),
        matrix(3, 3, &[0, 1, 0, -1, 0, 1, 0, -1, 0]),
        Vec::new(),
    )
    .expect("the downstream medium stands");
    let source = SourceCurrent::declared(
        "test|source",
        Carrier::Medium(0),
        matrix(1, 1, &[1]),
        vec!["drive".to_owned()],
    )
    .expect("the source stands");
    let perspective = Perspective::standing(
        "test|perspective",
        Carrier::Medium(1),
        matrix(1, 3, &[1, 0, 0]),
        vec!["read".to_owned()],
    )
    .expect("the perspective stands");
    let interaction = HolonicInteraction::declared(
        "test|closed-chain",
        source,
        vec![upstream, downstream],
        Vec::new(),
        Vec::new(),
        None,
        perspective,
    )
    .expect("the interaction stands");
    HolonicChain::over("test|closed-chain", interaction).expect("the chain reads")
}

// =============================================================================================
// the chain is a reading contract, and it refuses what is not a chain
// =============================================================================================

/// A perspective that reads the medium the source excites is not downstream of any neck, so the
/// rank bound would be a statement about a different object. Refused by name.
#[test]
fn a_perspective_upstream_of_the_neck_is_refused() {
    let upstream = Medium::declared("test|upstream", identity(1), matrix(1, 1, &[0]), Vec::new())
        .expect("the upstream medium stands");
    let downstream = Medium::declared("test|downstream", identity(1), matrix(1, 1, &[0]), Vec::new())
        .expect("the downstream medium stands");
    let source = SourceCurrent::declared(
        "test|source",
        Carrier::Medium(0),
        matrix(1, 1, &[1]),
        vec!["drive".to_owned()],
    )
    .expect("the source stands");
    let perspective = Perspective::standing(
        "test|perspective",
        Carrier::Medium(0),
        matrix(1, 1, &[1]),
        vec!["read".to_owned()],
    )
    .expect("the perspective stands");
    let interaction = HolonicInteraction::declared(
        "test|not-a-chain",
        source,
        vec![upstream, downstream],
        Vec::new(),
        Vec::new(),
        None,
        perspective,
    )
    .expect("the interaction stands");
    let refusal = HolonicChain::over("test|not-a-chain", interaction)
        .expect_err("a perspective on the source's own medium is not downstream");
    assert!(
        matches!(refusal, ChainRefusal::PerspectiveIsNotDownstream { .. }),
        "the refusal names the perspective, not something else: {refusal}"
    );
}

/// A single medium is a unit, not a chain between consecutive media, and the refusal names the
/// object still owed.
#[test]
fn one_medium_is_not_a_chain_and_the_refusal_names_what_is_owed() {
    let only = Medium::declared("test|only", identity(2), matrix(2, 2, &[0, 0, 0, 0]), Vec::new())
        .expect("the medium stands");
    let source = SourceCurrent::declared(
        "test|source",
        Carrier::Medium(0),
        matrix(2, 1, &[1, 0]),
        vec!["drive".to_owned()],
    )
    .expect("the source stands");
    let perspective = Perspective::standing(
        "test|perspective",
        Carrier::Medium(0),
        matrix(1, 2, &[0, 1]),
        vec!["read".to_owned()],
    )
    .expect("the perspective stands");
    let interaction = HolonicInteraction::declared(
        "test|one-medium",
        source,
        vec![only],
        Vec::new(),
        Vec::new(),
        None,
        perspective,
    )
    .expect("the interaction stands");
    let refusal = HolonicChain::over("test|one-medium", interaction)
        .expect_err("one medium is not a chain");
    let message = refusal.to_string();
    assert!(
        message.contains("holonic_chain.rs::HolonicChain"),
        "the refusal names the owner the multi-neck chain would compose: {message}"
    );
    assert!(matches!(refusal, ChainRefusal::NotTwoMedia { declared: 1 }));
}

/// A coupling that jumps the neck straight from the source's medium to the receiver would make
/// the station accounting a partition of the wrong complex. Refused by name.
#[test]
fn a_coupling_that_jumps_the_neck_is_refused() {
    let upstream = Medium::declared("test|upstream", identity(1), matrix(1, 1, &[0]), Vec::new())
        .expect("the upstream medium stands");
    let downstream = Medium::declared("test|downstream", identity(1), matrix(1, 1, &[0]), Vec::new())
        .expect("the downstream medium stands");
    let body = ReceiverBody::declared("test|body", identity(1), matrix(1, 1, &[0]))
        .expect("the receiver's body stands");
    let source = SourceCurrent::declared(
        "test|source",
        Carrier::Medium(0),
        matrix(1, 1, &[1]),
        vec!["drive".to_owned()],
    )
    .expect("the source stands");
    let perspective = Perspective::participating(
        "test|perspective",
        matrix(1, 1, &[1]),
        vec!["read".to_owned()],
        body,
    )
    .expect("the perspective stands");
    let jumping = Coupling::declared(
        "test|jump",
        Carrier::Medium(0),
        Carrier::Perspective,
        matrix(1, 1, &[1]),
    )
    .expect("the coupling stands");
    let interaction = HolonicInteraction::declared(
        "test|jumped",
        source,
        vec![upstream, downstream],
        Vec::new(),
        vec![jumping],
        None,
        perspective,
    )
    .expect("the interaction stands");
    let refusal =
        HolonicChain::over("test|jumped", interaction).expect_err("a jumped neck is not a chain");
    assert!(matches!(refusal, ChainRefusal::ContactIsNotAStation { .. }));
}

// =============================================================================================
// 1. the neck is the rank of the coupling, and the transfer factors through it
// =============================================================================================

/// **The pinhole.** A rank-one coupling bounds the whole transfer at every probe off the poles,
/// and the exact rank factorization reconstructs the coupling.
#[test]
fn a_rank_one_coupling_is_a_pinhole_that_bounds_every_transfer() {
    let chain = skew_chain(&[1, 0, 0]);
    let coupling = chain.neck_coupling().expect("the coupling reads");
    assert_eq!(coupling.rank(), 1, "one channel at the interface's grain");
    assert!(coupling.is_pinhole());
    assert!(!coupling.is_dissipative(), "a skew coupling dissipates nothing");
    assert_eq!(
        coupling.left().multiply(coupling.right()).expect("the product returns"),
        *coupling.cross(),
        "the rank factorization reconstructs the neck exactly"
    );
    // The interconnection's own rank and the neck's rank agree here because `G₁ = I`; they are
    // kept in different accessors because in general they do not.
    assert_eq!(coupling.interconnection_rank(), 1);
    assert_eq!(coupling.upstream_storage_rank(), 1);

    let probes = vec![int(1), int(2), rat(1, 2), int(-3)];
    let reading = chain.rank_bound(&probes).expect("the rank bound reads");
    assert_eq!(reading.bound(), 1);
    assert!(reading.bound_is_attained(), "the bound is sharp at some probe");
    for (probe, rank) in reading.measured() {
        assert!(*rank <= 1, "the probe {probe} has rank {rank}, above the neck");
    }
}

/// **Closed.** With no coupling and no contact the two media do not communicate: the neck's rank
/// is zero, every Markov parameter is exactly the zero matrix, and the neck reading is `Closed`
/// with the flux through it forced to zero rather than assumed.
#[test]
fn a_closed_neck_transmits_nothing_and_says_so() {
    let chain = closed_chain();
    let coupling = chain.neck_coupling().expect("the coupling reads");
    assert!(coupling.is_closed());
    assert_eq!(coupling.rank(), 0);

    let parameters = chain.markov(6).expect("the Markov parameters read");
    for (step, parameter) in parameters.iter().enumerate() {
        assert!(
            parameter.entries().iter().all(Zero::is_zero),
            "step {step} of a closed chain carries something"
        );
    }
    let staircase = chain.markov_staircase(6, 0, 0).expect("the staircase reads");
    assert_eq!(
        staircase.relative_degree(),
        None,
        "a closed chain has no relative degree within any order, and the reading is bounded"
    );
    assert_eq!(staircase.read_to(), 6);

    let state = vec![int(1), int(1), int(1), int(1)];
    let stations = chain.power_stations(&state, &[int(1)]).expect("the stations read");
    let reading = chain
        .neck_reading(&stations, &int(1))
        .expect("the neck reading returns");
    match reading {
        NeckReading::Closed { station, flux } => {
            assert_eq!(station, 2, "the neck is the third station of the chain");
            assert!(flux.is_zero(), "a closed neck carries no flux: {flux}");
        }
        other => panic!("a zero-rank neck must read Closed, not {}", other.arm()),
    }
    let tube = chain.tube_profile(&stations).expect("the tube reads");
    assert!(
        tube.closed_station_discrepancy().is_empty(),
        "a closed station whose power current also vanishes leaves nothing behind"
    );
    // `speedup` is unavailable at a zero section and refuses by name rather than dividing.
    assert!(tube.profile().speedup().is_err());
}

/// The rank bound holds for a **dissipative** neck too, where the coupling lives in the contact
/// form rather than in the skew structure.
#[test]
fn a_dissipative_neck_obeys_the_same_rank_bound() {
    let chain = dissipative_chain(&[1, 0, 0]);
    let coupling = chain.neck_coupling().expect("the coupling reads");
    assert_eq!(coupling.rank(), 1);
    assert!(coupling.is_dissipative(), "the neck is a contact face");
    assert!(
        coupling.structure_cross().entries().iter().all(Zero::is_zero),
        "no skew interconnection was declared"
    );
    let reading = chain
        .rank_bound(&[int(1), int(3)])
        .expect("the rank bound reads");
    assert_eq!(reading.bound(), 1);
    assert!(reading.bound_is_attained());
}

// =============================================================================================
// 2. flux along the chain is the power current
// =============================================================================================

/// **The power balance closes exactly.** Injected port power equals the storage rate summed over
/// the blocks plus the dissipation summed over the faces, and the block route agrees with
/// `causal_chord::rate_form` to the last bit.
#[test]
fn the_power_balance_of_a_dissipative_chain_closes_with_a_zero_residual() {
    let chain = dissipative_chain(&[1, 0, 0]);
    let state = vec![int(2), int(-1), int(3), int(1)];
    let stations = chain
        .power_stations(&state, &[int(5)])
        .expect("the stations read");
    assert!(
        stations.transport_residual().is_zero(),
        "the block and face population is not a partition of the balance: {}",
        stations.transport_residual()
    );
    assert!(
        stations.rate_form_residual().is_zero(),
        "the block route and `rate_form` disagree by {}",
        stations.rate_form_residual()
    );
    assert!(stations.rate_form_agrees(), "AᵀG + GA = −2GMG entry by entry");
    assert!(
        stations.balances(),
        "some gap does not balance: fluxes {:?} against sources {:?}",
        stations.flux(),
        stations.source()
    );
    // The face population is returned whole, never only its sum.
    assert_eq!(stations.face_power().len(), 1);
    let (name, power) = &stations.face_power()[0];
    assert!(name.contains("neck-face"), "the face names itself: {name}");
    assert_eq!(*power, *stations.dissipated());
    // Every wall loss is nonnegative, and they sum to the dissipated power.
    let summed = stations
        .wall_loss()
        .iter()
        .fold(Rat::zero(), |sum, loss| sum + loss);
    assert_eq!(summed, *stations.dissipated());
}

/// **The power current is continuous across a lossless neck**, and its jump across a dissipative
/// one is exactly twice the cross dissipation. Both are computed from the generator's own blocks.
#[test]
fn the_power_current_is_continuous_across_a_lossless_neck() {
    let state = vec![int(2), int(-1), int(3), int(1)];

    let lossless = skew_chain(&[1, 0, 0]);
    let lossless_stations = lossless
        .power_stations(&state, &[int(5)])
        .expect("the stations read");
    assert!(lossless_stations.neck_is_lossless());
    assert_eq!(
        lossless_stations.flux()[1],
        lossless_stations.flux()[2],
        "a lossless neck passes the whole power current"
    );
    assert!(lossless_stations.dissipated().is_zero());

    let lossy = dissipative_chain(&[1, 0, 0]);
    let lossy_stations = lossy
        .power_stations(&state, &[int(5)])
        .expect("the stations read");
    assert!(!lossy_stations.neck_is_lossless());
    assert_eq!(
        &lossy_stations.flux()[2] - &lossy_stations.flux()[1],
        *lossy_stations.neck_jump(),
        "the jump is the station difference"
    );
    assert_eq!(
        *lossy_stations.neck_jump(),
        int(-2) * lossy_stations.cross_dissipation(),
        "and it is exactly twice the cross dissipation"
    );
}

/// **The tube's sections are computed, and the current density peaks at the neck.** With every gap
/// source vanishing the flux really is constant and `speedup` — B's own reading, available only on
/// a sourceless tube — returns the pinhole.
#[test]
fn a_steady_lossless_chain_speeds_up_into_its_neck() {
    // The conservative chain at a state whose every block storage rate vanishes: `Ω` is skew, so
    // `x` in the kernel of the flow's own pairing makes each gap source exactly zero.
    let chain = skew_chain(&[1, 0, 0]);
    let stations = chain
        .power_stations(&vec![Rat::zero(); 4], &[Rat::zero()])
        .expect("the stations read");
    assert!(stations.source().iter().all(Zero::is_zero));
    let tube = chain.tube_profile(&stations).expect("the tube reads");
    assert_eq!(
        tube.sections(),
        &[1, 1, 1, 3, 1],
        "rank B, rank G_up, rank A₂₁, rank G_down, rank C — all computed"
    );
    let profile = tube.profile();
    assert_eq!(
        tube.narrowest_station(),
        0,
        "a one-port source is itself a pinhole, so the tube's argmin is the source port"
    );
    assert!(
        !tube.neck_is_narrowest(),
        "the chain's neck is station 2; that the tube's argmin is elsewhere is a returned fact"
    );
    let speedup = profile.speedup().expect("a sourceless tube has a speed-up reading");
    assert!(speedup.flux_is_constant);

    // A chain whose media are wider than its neck puts the minimum at the neck station itself.
    let wide = wide_chain();
    let wide_stations = wide
        .power_stations(&vec![Rat::zero(); 7], &vec![Rat::zero(); 3])
        .expect("the stations read");
    let wide_tube = wide.tube_profile(&wide_stations).expect("the tube reads");
    assert_eq!(wide_tube.sections(), &[3, 3, 1, 4, 4]);
    assert_eq!(
        wide_tube.narrowest_station(),
        NECK_STATION,
        "the narrowest station of this tube is the neck"
    );
    assert!(wide_tube.neck_is_narrowest());
    let reading = wide_tube.profile().neck_reading(&int(1), &int(3));
    assert_eq!(reading.arm(), "pinhole");
}

/// A wider chain: three upstream modes, four downstream modes, one channel between them.
fn wide_chain() -> HolonicChain {
    let upstream = Medium::declared(
        "test|wide-upstream",
        identity(3),
        matrix(3, 3, &[0, 1, 0, -1, 0, 0, 0, 0, 0]),
        Vec::new(),
    )
    .expect("the upstream medium stands");
    let downstream = Medium::declared(
        "test|wide-downstream",
        identity(4),
        matrix(
            4,
            4,
            &[0, 1, 0, 0, -1, 0, 1, 0, 0, -1, 0, 1, 0, 0, -1, 0],
        ),
        Vec::new(),
    )
    .expect("the downstream medium stands");
    let coupling = Coupling::declared(
        "test|wide-neck",
        Carrier::Medium(0),
        Carrier::Medium(1),
        matrix(4, 3, &[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    )
    .expect("the coupling stands");
    let source = SourceCurrent::declared(
        "test|wide-source",
        Carrier::Medium(0),
        matrix(3, 3, &[1, 0, 0, 0, 1, 0, 0, 0, 1]),
        vec!["a".to_owned(), "b".to_owned(), "c".to_owned()],
    )
    .expect("the source stands");
    let perspective = Perspective::standing(
        "test|wide-perspective",
        Carrier::Medium(1),
        matrix(
            4,
            4,
            &[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
        ),
        vec!["w".to_owned(), "x".to_owned(), "y".to_owned(), "z".to_owned()],
    )
    .expect("the perspective stands");
    let interaction = HolonicInteraction::declared(
        "test|wide-chain",
        source,
        vec![upstream, downstream],
        Vec::new(),
        vec![coupling],
        None,
        perspective,
    )
    .expect("the interaction stands");
    HolonicChain::over("test|wide-chain", interaction).expect("the chain reads")
}

/// The station balance is computed by `neck.rs`, which computes it through `junction_law`, and
/// this owner re-implements neither.
#[test]
fn the_station_balance_is_the_junction_owner_s() {
    let chain = dissipative_chain(&[1, 0, 0]);
    let state = vec![int(2), int(-1), int(3), int(1)];
    let stations = chain
        .power_stations(&state, &[int(5)])
        .expect("the stations read");
    let tube = chain.tube_profile(&stations).expect("the tube reads");
    let balance = tube
        .profile()
        .station_balance()
        .expect("the station balance returns");
    assert_eq!(balance.gaps, 4);
    assert!(
        balance.is_balanced(),
        "the chain's own power stations do not balance its own tube: {:?}",
        balance.residual
    );
}

// =============================================================================================
// 3. the Markov staircase, and the relative degree per instance
// =============================================================================================

/// **No direct feedthrough across a neck**, and the relative degree is decided per instance by
/// where the perspective reads — not by whether the coupling stores or dissipates.
///
/// One source, one neck, one downstream medium: the relative degree is `1`, `2` and `3` as the
/// aperture moves one mode deeper. The same neck made dissipative instead of conservative leaves
/// the degree at `1`. **This owner therefore asserts no universal increment for inserting a
/// medium or a neck**, and this test is the evidence.
#[test]
fn the_relative_degree_is_computed_per_instance_and_has_no_universal_increment() {
    let mut degrees = Vec::new();
    for aperture in [[1, 0, 0], [0, 1, 0], [0, 0, 1]] {
        let chain = skew_chain(&aperture);
        let staircase = chain.markov_staircase(6, 0, 0).expect("the staircase reads");
        assert!(
            staircase.has_no_direct_feedthrough(),
            "C B must vanish when the ports sit on different media"
        );
        degrees.push(staircase.relative_degree().expect("a degree within the order"));
    }
    assert_eq!(
        degrees,
        vec![1, 2, 3],
        "one neck and one source, three relative degrees: the increment is not universal"
    );

    // A dissipative neck at the same station gives the same degree as the conservative one, so
    // the coupling's type does not set the increment either.
    let dissipative = dissipative_chain(&[1, 0, 0]);
    assert_eq!(
        dissipative
            .markov_staircase(6, 0, 0)
            .expect("the staircase reads")
            .relative_degree(),
        Some(1)
    );
    let conservative = skew_chain(&[1, 0, 0]);
    assert_eq!(
        conservative
            .markov_staircase(6, 0, 0)
            .expect("the staircase reads")
            .relative_degree(),
        Some(1)
    );
}

/// The jet of the impulse response is `C Aᵏ B / k!` in the unit chart, its vanishing order **is**
/// the relative degree, and `neck.rs`'s own `jet_order_at_neck` reads that order.
#[test]
fn the_impulse_response_jet_is_the_markov_staircase() {
    let chain = skew_chain(&[0, 1, 0]);
    let staircase = chain.markov_staircase(5, 0, 0).expect("the staircase reads");
    let parameters = staircase.parameters();
    assert_eq!(parameters.len(), 6);
    assert!(parameters[0].entries().iter().all(Zero::is_zero));
    assert!(parameters[1].entries().iter().all(Zero::is_zero));
    assert_eq!(*parameters[2].get(0, 0).expect("the entry"), int(-1));

    // `c_k = C Aᵏ B / k!`, so `c₂ = −1/2` and the jet's derivative value at order 2 is `−1`.
    assert_eq!(staircase.jet().coefficients()[2], rat(-1, 2));
    assert_eq!(staircase.jet().derivative_values()[2], int(-1));
    assert_eq!(staircase.jet().vanishing_order(), Some(2));
    assert_eq!(staircase.relative_degree(), Some(2));
    assert_eq!(staircase.neck_order().order, Some(2));
    assert_eq!(staircase.neck_order().read_to, 5);
    assert_eq!(staircase.ladder().top_order(), 5);
    assert!(staircase.ladder().restriction_is_projection());
}

/// The telescoping identity the Lean owner proves is computed here rather than asserted, so a
/// defect in the exact arithmetic would be a returned number.
#[test]
fn the_resolvent_telescope_closes_exactly() {
    let chain = dissipative_chain(&[1, 0, 0]);
    for order in 0..6 {
        let residual = chain
            .telescope_residual(&int(3), order)
            .expect("the telescope reads");
        assert!(
            residual.is_zero(),
            "at order {order} the telescope leaves {residual}"
        );
    }
}

/// A Markov order above the ceiling is refused before anything is sized by it.
#[test]
fn a_markov_order_above_the_ceiling_is_refused_before_it_is_sized() {
    let chain = skew_chain(&[1, 0, 0]);
    let refusal = chain
        .markov(MARKOV_ORDER_CEILING + 1)
        .expect_err("an order above the ceiling is refused");
    assert!(matches!(
        refusal,
        ChainRefusal::DeclarationAboveCeiling {
            ceiling: MARKOV_ORDER_CEILING,
            ..
        }
    ));
    let probes = vec![int(1); PROBE_CEILING + 1];
    assert!(matches!(
        chain.rank_bound(&probes).expect_err("too many probes"),
        ChainRefusal::DeclarationAboveCeiling { .. }
    ));
    assert!(matches!(
        chain.rank_bound(&[]).expect_err("no probes at all"),
        ChainRefusal::EmptyDeclaration { .. }
    ));
}

/// A probe on a pole is refused by name rather than inverted.
#[test]
fn a_probe_on_a_pole_is_refused() {
    let chain = closed_chain();
    // `A` has the eigenvalue `0` — the upstream mode is uncoupled and unforced.
    let refusal = chain
        .transfer_at(&Rat::zero())
        .expect_err("zero is a pole of this chain");
    assert!(matches!(refusal, ChainRefusal::ProbeOnAPole { .. }));
}

// =============================================================================================
// 4. the interface condition, the widths, and reversal
// =============================================================================================

/// The interface at the neck is read through A's `InterfaceReading`, which is
/// `junction_law::check_junction`, and its normal jump is the chain's own power-current jump.
#[test]
fn the_interface_at_the_neck_is_read_through_the_junction_owner() {
    let chain = dissipative_chain(&[1, 0, 0]);
    let state = vec![int(2), int(-1), int(3), int(1)];
    let stations = chain
        .power_stations(&state, &[int(5)])
        .expect("the stations read");
    let reading = chain.interface_reading(&stations).expect("the interface reads");
    assert_eq!(reading.left(), chain.upstream());
    assert_eq!(reading.right(), chain.downstream());
    assert!(
        reading.balances(),
        "the normal jump at the joint is not the source the neck injects"
    );
    assert!(reading.normal_remainder().is_some(), "the remainder is retained");
}

/// The three widths stay in three types and meet only through a declared constitutive link, whose
/// residual is returned. Above the declared extent the analytic width is **not decided within its
/// bound** and no value is invented for it.
#[test]
fn the_three_widths_meet_only_through_a_declared_link() {
    let chain = dissipative_chain(&[1, 0, 0]);
    let state = vec![int(2), int(-1), int(3), int(1)];
    let stations = chain
        .power_stations(&state, &[int(5)])
        .expect("the stations read");
    let link = ConstitutiveLink::declare(
        "test|link",
        "the declared receiving scope of this chain",
        WidthFace::Geometric,
        WidthFace::Analytic,
        Rat::one(),
    )
    .expect("the link stands");
    let widths = chain
        .chain_widths(&stations, None, link)
        .expect("the widths read");
    assert_eq!(widths.scope(), AnalyticScope::Taken);
    assert!(widths.analytic().is_some());
    assert!(widths.receiver().is_none());
    assert_eq!(widths.absent_faces(), Vec::new());
    let residual = widths.residual().expect("both faces are present");
    assert_eq!(
        residual.observed.clone() - &residual.predicted,
        residual.residual,
        "the residual is `observed − coefficient · from` and is returned, not rounded"
    );
    assert_eq!(residual.domain, "the declared receiving scope of this chain");

    // The receiver face is absent, so a link that needs it returns no reading and invents nothing.
    let receiver_link = ConstitutiveLink::declare(
        "test|receiver-link",
        "the declared receiving scope of this chain",
        WidthFace::Geometric,
        WidthFace::ReceiverUncertainty,
        Rat::one(),
    )
    .expect("the link stands");
    let absent = chain
        .chain_widths(&stations, None, receiver_link)
        .expect("the widths read");
    assert!(absent.residual().is_none());
    assert_eq!(absent.absent_faces(), vec![WidthFace::ReceiverUncertainty]);
}

/// Every neck invariant this chain did **not** read is named, with the owner it would compose.
#[test]
fn the_neck_invariants_name_what_they_did_not_read() {
    let chain = dissipative_chain(&[1, 0, 0]);
    let state = vec![int(2), int(-1), int(3), int(1)];
    let stations = chain
        .power_stations(&state, &[int(5)])
        .expect("the stations read");
    let link = ConstitutiveLink::declare(
        "test|link",
        "the declared receiving scope of this chain",
        WidthFace::Geometric,
        WidthFace::Analytic,
        Rat::one(),
    )
    .expect("the link stands");
    let widths = chain
        .chain_widths(&stations, None, link)
        .expect("the widths read");
    let staircase = chain.markov_staircase(5, 0, 0).expect("the staircase reads");
    let invariants = chain
        .neck_invariants(&stations, &widths, &staircase)
        .expect("the invariants read");
    let open: Vec<&'static str> = invariants
        .open_invariants()
        .into_iter()
        .map(|(name, _)| name)
        .collect();
    assert!(open.contains(&"receiver uncertainty width"));
    assert!(open.contains(&"linking"));
    assert!(open.contains(&"growth exponent at a pinch"));
    assert!(!open.contains(&"analytic width"), "the analytic width was taken");
    assert!(!open.contains(&"holonomy"), "the holonomy was taken");
    assert_eq!(invariants.station, 2);
    assert_eq!(invariants.jet_order.order, Some(1));
    assert!(invariants.domains.contains_key("geometric section"));
}

/// **What reversal does and does not undo.** The adjoint chain's transfer is the transpose, so the
/// rank bound is even; the dissipated power is identical, so the chain still decays either way;
/// the tube's flux reverses and changes sign; and a lossless chain's holonomy around the neck is
/// the identity while a dissipative one's is not.
#[test]
fn reversal_keeps_the_rank_and_the_dissipation_and_flips_the_flux() {
    let state = vec![int(2), int(-1), int(3), int(1)];
    let probes = vec![int(1), int(3)];

    let lossy = dissipative_chain(&[1, 0, 0]);
    let reading = lossy
        .reversal_reading(&probes, &state, &[int(5)])
        .expect("the reversal reads");
    assert!(reading.reciprocal(), "the adjoint transfer is the transpose");
    assert!(reading.rank_is_symmetric());
    assert!(
        reading.dissipation_is_even(),
        "reversal changed the dissipated power from {} to {}",
        reading.forward_dissipated(),
        reading.reversed_dissipated()
    );
    assert!(!reading.forward_dissipated().is_zero());
    let forward: Vec<Rat> = reading.forward_flux().to_vec();
    let reversed: Vec<Rat> = reading.reversed_flux().to_vec();
    assert_eq!(forward.len(), reversed.len());
    assert_eq!(
        reversed[0], -forward[forward.len() - 1].clone(),
        "the tube's flux reverses and changes sign"
    );
    assert_eq!(
        reading.forward_holonomy_is_identity(),
        Some(false),
        "a dissipative chain's holonomy around the neck is a circuit defect"
    );
    assert_eq!(
        reading.reversed_holonomy_is_identity(),
        Some(false),
        "and running the chain backwards does not undo it"
    );

    let lossless = skew_chain(&[1, 0, 0]);
    let clean = lossless
        .reversal_reading(&probes, &state, &[int(5)])
        .expect("the reversal reads");
    assert!(clean.forward_dissipated().is_zero());
    assert!(clean.dissipation_is_even());
    assert_eq!(
        clean.forward_holonomy_is_identity(),
        Some(true),
        "a lossless chain's holonomy around the neck is the identity"
    );
}

// =============================================================================================
// 5. the consumer: a protein hinge is a neck between two media
// =============================================================================================

/// Two rigid planar triangles joined by a single bar. Sites `1,2,3` are the first body, `4,5,6`
/// the second, and the bar `(3,4)` is the hinge between them.
fn two_triangles_and_a_hinge() -> RigidityJacobian {
    let configuration = ExactConfiguration::declared(
        2,
        [
            (ConstraintVertexId(1), places(&[0, 0])),
            (ConstraintVertexId(2), places(&[4, 0])),
            (ConstraintVertexId(3), places(&[0, 3])),
            (ConstraintVertexId(4), places(&[6, 0])),
            (ConstraintVertexId(5), places(&[10, 0])),
            (ConstraintVertexId(6), places(&[6, 3])),
        ],
    )
    .expect("a declared configuration");
    let mut constraints = BTreeMap::new();
    for (left, right) in [(1, 2), (1, 3), (2, 3), (4, 5), (4, 6), (5, 6), (3, 4)] {
        let (edge, _) = ConstraintEdge::new(ConstraintVertexId(left), ConstraintVertexId(right))
            .expect("a well-formed edge");
        constraints.insert(edge, EdgeProvenance::Polygonal);
    }
    RigidityJacobian::found("synthetic-hinge", &configuration, &constraints)
        .expect("the Jacobian returns")
}

/// **The hinge is found by computation, not declared**: it is the cut whose neck section is
/// minimal, and every other cut of the same structure has a wider section.
#[test]
fn the_hinge_is_the_cut_whose_neck_section_is_minimal() {
    let jacobian = two_triangles_and_a_hinge();
    let search = hinge_by_minimal_section(&jacobian, 1, CUT_CEILING).expect("the search returns");
    assert_eq!(search.scanned().len(), 5, "every cut of six sites was scanned");
    assert!(matches!(
        search.verdict(),
        HingeVerdict::Minimal { cut: 3, section: 1 }
    ));
    assert_eq!(search.cut(), 3);
    assert_eq!(search.section(), 1, "one channel crosses the hinge");
    assert!(search.ties().is_empty(), "the hinge of this structure is unique");
    for candidate in search.scanned() {
        if candidate.cut == 3 {
            assert_eq!(candidate.crossing_constraints, 1);
            assert_eq!(candidate.upstream_constraints, 3);
            assert_eq!(candidate.downstream_constraints, 3);
        } else {
            assert!(
                candidate.section > 1,
                "the cut at {} has section {}, which is not wider than the hinge",
                candidate.cut,
                candidate.section
            );
        }
    }
}

/// A bounded scan says so: a finite prefix of the candidate cuts proves nothing about the rest.
#[test]
fn a_bounded_hinge_scan_returns_a_bounded_verdict() {
    let jacobian = two_triangles_and_a_hinge();
    let search = hinge_by_minimal_section(&jacobian, 1, 2).expect("the search returns");
    assert_eq!(search.scanned().len(), 2);
    match search.verdict() {
        HingeVerdict::NotDecidedWithinBound {
            scanned, sites, ..
        } => {
            assert_eq!(*scanned, 2);
            assert_eq!(*sites, 6);
        }
        other => panic!("a truncated scan must say so, not {other:?}"),
    }
    assert!(
        search.section() > 1,
        "the prefix scanned does not contain the hinge, and the reading does not claim it does"
    );
}

/// **The whole chain read at the hinge, from one dynamics.** The faces are the measured rigidity
/// constraints, the neck is the crossing constraint, and every reading below is computed from the
/// same `A = −JᵀJ`.
#[test]
fn the_synthetic_hinge_chain_reads_as_one_tube() {
    let jacobian = two_triangles_and_a_hinge();
    let reading = rigidity_reading(&jacobian).expect("the rigidity reading returns");
    assert_eq!(reading.rank, 7.min(reading.rank));
    let search = hinge_by_minimal_section(&jacobian, 1, CUT_CEILING).expect("the search returns");
    let chain = elastic_chain("synthetic-hinge", &jacobian, search.cut()).expect("the chain builds");

    // Ω = 0, G = I, M = JᵀJ: the faces are the constraint rows, derived and not declared.
    assert_eq!(chain.interaction().media()[0].faces().len(), 3);
    assert_eq!(chain.interaction().media()[1].faces().len(), 3);
    assert_eq!(chain.interaction().contacts().len(), 1);
    assert_eq!(chain.interaction().joint_dimension(), 12);

    let coupling = chain.neck_coupling().expect("the coupling reads");
    assert_eq!(coupling.rank(), 1, "the hinge is a pinhole");
    assert!(coupling.is_dissipative());

    // The rank bound holds against a six-by-six transfer: every upstream coordinate is a port and
    // every downstream coordinate is read.
    let bound = chain
        .rank_bound(&[int(1), int(2), int(5)])
        .expect("the rank bound reads");
    assert_eq!(bound.bound(), 1);
    assert!(bound.bound_is_attained());
    for (_, rank) in bound.measured() {
        assert_eq!(*rank, 1);
    }

    // The power balance, at a declared state and input.
    let state: Vec<Rat> = (0..12).map(|at| int(at as i64 % 5 - 2)).collect();
    let input: Vec<Rat> = (0..6).map(|at| int(at as i64 - 3)).collect();
    let stations = chain.power_stations(&state, &input).expect("the stations read");
    assert!(stations.transport_residual().is_zero());
    assert!(stations.rate_form_residual().is_zero());
    assert!(stations.balances());
    assert_eq!(stations.face_power().len(), 7, "seven constraints, seven faces");
    assert!(stations.wall_loss().iter().all(|loss| !loss.is_negative()));

    // The tube, its sections and its neck reading.
    let tube = chain.tube_profile(&stations).expect("the tube reads");
    assert_eq!(tube.sections(), &[6, 6, 1, 6, 6]);
    assert_eq!(tube.profile().neck_index(), 2);
    assert_eq!(
        tube.profile().neck_reading(&int(1), &int(6)).arm(),
        "pinhole"
    );

    // The Markov staircase across the hinge.
    let staircase = chain.markov_staircase(4, 0, 0).expect("the staircase reads");
    assert!(staircase.has_no_direct_feedthrough());
    assert_eq!(staircase.relative_degree(), Some(1));

    // The interface at the hinge, and the holonomy around it.
    let interface = chain.interface_reading(&stations).expect("the interface reads");
    assert!(interface.balances());
    let neck_tube = chain.neck_tube(&stations).expect("the neck tube stands");
    let holonomy = neck_tube
        .holonomy_around_the_neck(0, Rat::one())
        .expect("the holonomy returns");
    assert!(
        !holonomy_is_identity(&holonomy),
        "a hinge with a dissipative face is not a lossless neck"
    );
}

/// A cut that does not split the sites into two nonempty domains is refused by name.
#[test]
fn a_cut_that_is_not_a_partition_is_refused() {
    let jacobian = two_triangles_and_a_hinge();
    assert!(matches!(
        cut_section(&jacobian, 0).expect_err("cut zero"),
        ChainRefusal::CutIsNotAPartition { .. }
    ));
    assert!(matches!(
        cut_section(&jacobian, 6).expect_err("cut at the end"),
        ChainRefusal::CutIsNotAPartition { .. }
    ));
    assert!(matches!(
        elastic_chain("synthetic-hinge", &jacobian, 6).expect_err("cut at the end"),
        ChainRefusal::CutIsNotAPartition { .. }
    ));
}

// =============================================================================================
// the measured M5 presentation
// =============================================================================================

const STRUCTURE_ROOT_ENV: &str = "HOLONICS_M5_STRUCTURE_ROOT";
const DEFAULT_STRUCTURE_ROOT: &str = "/home/b/Downloads/holonics-m5-rbx1-rank05";
/// The RBX1 chain is the one component present in all three presentations.
const RBX1_RESIDUES: usize = 108;
/// The residue window the chain is read on, declared here rather than inferred.
const WINDOW: usize = 12;
/// Eight angstroms, squared, on the exact decimal wire the intake reads.
const CONTACT_SQUARED: i64 = 64;

/// One alpha carbon, exactly: the deposited decimal is a rational and is used as one.
fn exact_decimal(token: &str) -> Result<Rat, String> {
    let token = token
        .strip_prefix('\'')
        .and_then(|body| body.strip_suffix('\''))
        .unwrap_or(token);
    let negative = token.starts_with('-');
    let unsigned = token.trim_start_matches(['-', '+']);
    let (whole, fraction) = unsigned.split_once('.').unwrap_or((unsigned, ""));
    if whole.is_empty()
        || !whole.chars().all(|character| character.is_ascii_digit())
        || !fraction.chars().all(|character| character.is_ascii_digit())
    {
        return Err(format!("coordinate token {token:?} is not a plain decimal"));
    }
    let digits = format!("{whole}{fraction}");
    let numerator = digits.parse::<BigInt>().map_err(|error| error.to_string())?;
    let denominator = BigInt::from(10_u8).pow(fraction.len() as u32);
    let value = Rat::new(numerator, denominator);
    Ok(if negative { -value } else { value })
}

/// The alpha carbons of every chain, in residue order, as exact rational places.
fn read_alpha_carbons(path: &Path) -> Result<BTreeMap<String, Vec<Vec<Rat>>>, String> {
    let text = std::fs::read_to_string(path).map_err(|error| error.to_string())?;
    let lines = text.lines().collect::<Vec<_>>();
    let mut headers = Vec::<String>::new();
    let mut rows = Vec::<Vec<&str>>::new();
    let mut at = 0usize;
    while at < lines.len() {
        if lines[at].trim() != "loop_" {
            at += 1;
            continue;
        }
        let mut cursor = at + 1;
        let mut candidate = Vec::<String>::new();
        while cursor < lines.len() && lines[cursor].trim_start().starts_with('_') {
            candidate.push(lines[cursor].trim().to_owned());
            cursor += 1;
        }
        if !candidate.iter().any(|name| name.starts_with("_atom_site.")) {
            at = cursor;
            continue;
        }
        headers = candidate;
        while cursor < lines.len() {
            let line = lines[cursor].trim();
            if line == "#" || line == "loop_" || line.starts_with('_') {
                break;
            }
            if !line.is_empty() {
                let fields = line.split_whitespace().collect::<Vec<_>>();
                if fields.len() != headers.len() {
                    return Err(format!(
                        "{} atom_site row {} has {} fields under {} headers",
                        path.display(),
                        cursor + 1,
                        fields.len(),
                        headers.len()
                    ));
                }
                rows.push(fields);
            }
            cursor += 1;
        }
        break;
    }
    if headers.is_empty() || rows.is_empty() {
        return Err(format!("{} has no atom_site loop", path.display()));
    }
    let column_of = |name: &str| -> Result<usize, String> {
        headers
            .iter()
            .position(|candidate| candidate == name)
            .ok_or_else(|| format!("{} has no {name} atom_site face", path.display()))
    };
    let atom = column_of("_atom_site.label_atom_id")?;
    let chain = column_of("_atom_site.label_asym_id")?;
    let x = column_of("_atom_site.Cartn_x")?;
    let y = column_of("_atom_site.Cartn_y")?;
    let z = column_of("_atom_site.Cartn_z")?;

    let mut chains: BTreeMap<String, Vec<Vec<Rat>>> = BTreeMap::new();
    for entry in rows {
        if entry[atom] != "CA" {
            continue;
        }
        let mut point = Vec::with_capacity(3);
        for axis in [x, y, z] {
            point.push(exact_decimal(entry[axis])?);
        }
        chains.entry(entry[chain].to_owned()).or_default().push(point);
    }
    Ok(chains)
}

fn squared_distance(left: &[Rat], right: &[Rat]) -> Rat {
    left.iter().zip(right).fold(Rat::zero(), |sum, (a, b)| {
        let difference = a - b;
        sum + &difference * &difference
    })
}

/// The rigidity Jacobian of one declared residue window of one M5 presentation.
fn measured_jacobian(
    lineage: &'static str,
    path: &Path,
    window: usize,
) -> Result<RigidityJacobian, String> {
    let chains = read_alpha_carbons(path)?;
    let rbx1 = chains
        .values()
        .filter(|places| places.len() == RBX1_RESIDUES)
        .collect::<Vec<_>>();
    if rbx1.len() != 1 {
        return Err(format!(
            "{} carries {} chains of {RBX1_RESIDUES} alpha carbons, not one",
            path.display(),
            rbx1.len()
        ));
    }
    let places = &rbx1[0][..window];
    let configuration = ExactConfiguration::declared(
        3,
        places
            .iter()
            .enumerate()
            .map(|(at, point)| (ConstraintVertexId(at as u64 + 1), point.clone())),
    )
    .map_err(|error| error.to_string())?;
    let aperture = Rat::from_integer(BigInt::from(CONTACT_SQUARED));
    let mut constraints = BTreeMap::new();
    for left in 0..window {
        for right in (left + 1)..window {
            let backbone = right == left + 1;
            if !backbone && squared_distance(&places[left], &places[right]) > aperture {
                continue;
            }
            let (edge, _) = ConstraintEdge::new(
                ConstraintVertexId(left as u64 + 1),
                ConstraintVertexId(right as u64 + 1),
            )
            .map_err(|error| error.to_string())?;
            constraints.insert(
                edge,
                if backbone {
                    EdgeProvenance::Polygonal
                } else {
                    EdgeProvenance::AdmittedContact
                },
            );
        }
    }
    RigidityJacobian::found(lineage, &configuration, &constraints).map_err(|error| error.to_string())
}

/// **The measured hinge reading of one authenticated M5 presentation, as one chain.**
///
/// The object is the rigidity receiver's own exact rational Jacobian on a declared twelve-residue
/// window of the RBX1 chain, in the elastic-network form `A = −JᵀJ` — which in this owner's terms
/// is `Ω = 0`, `G = I`, `M = JᵀJ` with **every constraint row a contact face**. The hinge is found
/// by scanning every candidate cut and taking the one whose cross-domain rank is smallest; the
/// chain is then built at that cut and read whole: the rank bound on the cross-domain transfer,
/// the power balance with its residual, the Markov order across the hinge, the neck reading and
/// the comparison against a cut placed elsewhere.
///
/// The joint chart is `3 × 12 = 36` coordinates, above [`ANALYTIC_EXTENT_CEILING`], so the analytic
/// width is returned **not decided within its bound** and no value is invented for it.
///
/// **Absent the release this test refuses.** Every law this module owns is checked without any
/// fixture by the synthetic tests above, in particular
/// `the_synthetic_hinge_chain_reads_as_one_tube`.
///
/// **`#[ignore]`d because it is a measurement, not a law.** Run it with
/// `cargo test -p holonic-engine --lib holonic_chain::tests::the_measured_hinge -- --ignored --nocapture`.
#[test]
#[ignore = "an exact measurement on the authenticated M5 release, not a law"]
fn the_measured_hinge_of_one_m5_presentation_reads_as_one_chain() {
    let root = std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_STRUCTURE_ROOT));
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the measured hinge reading cannot be \
         taken, and this test refuses to report success without taking it. Place the authenticated \
         release at that path, or set {STRUCTURE_ROOT_ENV} to the directory carrying \
         designed-free-rbx1.cif. Every law this module owns is checked without any fixture by the \
         synthetic tests above, in particular the_synthetic_hinge_chain_reads_as_one_tube.",
        root.display()
    );
    let started = std::time::Instant::now();
    let jacobian = measured_jacobian("designed-free", &root.join("designed-free-rbx1.cif"), WINDOW)
        .unwrap_or_else(|error| panic!("designed-free: {error}"));
    let rigidity = rigidity_reading(&jacobian).expect("the rigidity reading returns");
    eprintln!(
        "[measured] window {WINDOW} residues, {} coordinates, {} constraints, rank J = {}, \
         dim ker J = {}",
        3 * WINDOW,
        jacobian.constraint_count(),
        rigidity.rank,
        rigidity.motion_dimension
    );

    let search = hinge_by_minimal_section(&jacobian, 1, CUT_CEILING).expect("the search returns");
    for candidate in search.scanned() {
        eprintln!(
            "[measured] cut {:>2}: section {:>2}, crossing {:>2}, upstream {:>2}, downstream {:>2}",
            candidate.cut,
            candidate.section,
            candidate.crossing_constraints,
            candidate.upstream_constraints,
            candidate.downstream_constraints
        );
    }
    assert!(matches!(search.verdict(), HingeVerdict::Minimal { .. }));
    let hinge = search.cut();
    let hinge_section = search.section();
    // The same scan restricted to cuts that leave a real domain on each side. A terminal cut is
    // narrow because one residue has few neighbours, not because anything hinges there, and the
    // margin is the declared scope that says so.
    let interior = hinge_by_minimal_section(&jacobian, 4, CUT_CEILING).expect("the search returns");
    eprintln!(
        "[measured] margin 1: hinge at cut {hinge} with section {hinge_section}; margin {}: cut {} \
         with section {}",
        interior.margin(),
        interior.cut(),
        interior.section()
    );

    // A cut placed elsewhere in the same chain: the widest one scanned.
    let widest = search
        .scanned()
        .iter()
        .max_by_key(|candidate| candidate.section)
        .expect("the scan is nonempty");
    eprintln!(
        "[measured] hinge at cut {hinge} with section {hinge_section}; widest cut {} with section {}",
        widest.cut, widest.section
    );
    assert!(
        hinge_section <= widest.section,
        "the minimal section is not minimal"
    );

    // The chain is built at the **interior** hinge: a terminal cut leaves a single residue facing
    // the rest of the window, which is narrow without being a hinge.
    let chain = elastic_chain("designed-free|rbx1|hinge", &jacobian, interior.cut())
        .expect("the chain builds at the hinge");
    assert_eq!(chain.interaction().joint_dimension(), 3 * WINDOW);
    let coupling = chain.neck_coupling().expect("the coupling reads");
    assert_eq!(coupling.rank(), interior.section());
    eprintln!(
        "[measured] chain built at cut {} (section {}); the widest cut of the window has section {}",
        interior.cut(),
        interior.section(),
        widest.section
    );

    let bound = chain.rank_bound(&[int(1), int(7)]).expect("the rank bound reads");
    eprintln!(
        "[measured] neck section {} bounds the cross-domain transfer; measured ranks {:?}",
        bound.bound(),
        bound.measured().iter().map(|(_, rank)| *rank).collect::<Vec<_>>()
    );

    let extent = chain.interaction().joint_dimension();
    let state: Vec<Rat> = (0..extent).map(|at| int(at as i64 % 7 - 3)).collect();
    let ports = chain.interaction().source().ports().len();
    let input: Vec<Rat> = (0..ports).map(|at| int(at as i64 % 5 - 2)).collect();
    let stations = chain.power_stations(&state, &input).expect("the stations read");
    eprintln!(
        "[measured] injected {}, dissipated {}, storage rate {}, neck jump {}",
        stations.injected(),
        stations.dissipated(),
        stations.storage_rate_total(),
        stations.neck_jump()
    );
    eprintln!(
        "[measured] transport residual {}, rate-form residual {}",
        stations.transport_residual(),
        stations.rate_form_residual()
    );
    assert!(stations.transport_residual().is_zero());
    assert!(stations.rate_form_residual().is_zero());
    assert!(stations.balances());

    let tube = chain.tube_profile(&stations).expect("the tube reads");
    eprintln!("[measured] sections {:?}", tube.sections());
    let neck_reading = tube.profile().neck_reading(&int(2), &count(extent));
    eprintln!("[measured] neck reading: {}", neck_reading.arm());

    let staircase = chain.markov_staircase(4, 0, 0).expect("the staircase reads");
    eprintln!(
        "[measured] relative degree {:?} read to order {}",
        staircase.relative_degree(),
        staircase.read_to()
    );
    assert!(staircase.has_no_direct_feedthrough());

    // The analytic width stops at its declared bound rather than attempting a 36-coordinate exact
    // characteristic polynomial, and says so.
    let link = ConstitutiveLink::declare(
        "designed-free|link",
        "the declared receiving scope of this window",
        WidthFace::Geometric,
        WidthFace::Analytic,
        Rat::one(),
    )
    .expect("the link stands");
    let widths = chain
        .chain_widths(&stations, None, link)
        .expect("the widths read");
    eprintln!("[measured] analytic scope: {:?}", widths.scope());
    assert_eq!(
        widths.scope(),
        AnalyticScope::NotDecidedWithinBound {
            extent: 3 * WINDOW,
            ceiling: ANALYTIC_EXTENT_CEILING
        }
    );
    assert!(widths.analytic().is_none(), "no width was invented");

    eprintln!(
        "[measured] the whole chain reading cost {:.1} s of wall clock",
        started.elapsed().as_secs_f64()
    );
}

/// **A participating receiver takes power, and the balance still closes.** The receiver's own
/// block joins the state, the fourth gap carries the receiver interface's sink, and the delivered
/// power is the receiver block's own storage rate plus its dissipation.
#[test]
fn a_participating_receiver_takes_power_and_the_balance_still_closes() {
    let upstream = Medium::declared("test|upstream", identity(1), matrix(1, 1, &[0]), Vec::new())
        .expect("the upstream medium stands");
    let downstream = Medium::declared(
        "test|downstream",
        identity(2),
        matrix(2, 2, &[0, 1, -1, 0]),
        Vec::new(),
    )
    .expect("the downstream medium stands");
    let body = ReceiverBody::declared("test|body", identity(1), matrix(1, 1, &[0]))
        .expect("the receiver's body stands");
    let neck = Coupling::declared(
        "test|neck",
        Carrier::Medium(0),
        Carrier::Medium(1),
        matrix(2, 1, &[1, 0]),
    )
    .expect("the coupling stands");
    // The receiver is glued to the downstream medium by a dissipative face over the concatenated
    // chart `(downstream, receiver)`.
    let receiver_contact = MediumContact::declared(
        "test|receiver-contact",
        Carrier::Medium(1),
        Carrier::Perspective,
        ContactFace::declared(
            "test|receiver-face",
            matrix(1, 3, &[0, 1, -1]),
            identity(1),
            Rat::one(),
        )
        .expect("the face stands"),
    )
    .expect("the contact stands");
    let source = SourceCurrent::declared(
        "test|source",
        Carrier::Medium(0),
        matrix(1, 1, &[1]),
        vec!["drive".to_owned()],
    )
    .expect("the source stands");
    let perspective = Perspective::participating(
        "test|perspective",
        matrix(1, 1, &[1]),
        vec!["read".to_owned()],
        body,
    )
    .expect("the perspective stands");
    let interaction = HolonicInteraction::declared(
        "test|receiver-chain",
        source,
        vec![upstream, downstream],
        vec![receiver_contact],
        vec![neck],
        None,
        perspective,
    )
    .expect("the interaction stands");
    let chain = HolonicChain::over("test|receiver-chain", interaction).expect("the chain reads");
    assert!(chain.receiver_participates());

    let state = vec![int(2), int(-1), int(3), int(4)];
    let stations = chain
        .power_stations(&state, &[int(5)])
        .expect("the stations read");
    assert!(stations.transport_residual().is_zero());
    assert!(stations.rate_form_residual().is_zero());
    assert!(
        stations.balances(),
        "fluxes {:?} against sources {:?}",
        stations.flux(),
        stations.source()
    );
    assert!(
        !stations.delivered().is_zero(),
        "a participating receiver that is glued to the medium takes power"
    );
    assert_eq!(stations.flux()[4], *stations.delivered());
    assert!(
        stations.neck_is_lossless(),
        "the neck itself is a skew coupling; the loss is at the receiver's own interface"
    );
    // The local reading at the neck sees nothing dissipating upstream of it; the whole-chain
    // circuit sees the receiver interface and returns the defect.
    assert_eq!(chain.neck_holonomy(&stations).expect("the reading returns"), Some(true));
    assert_eq!(chain.chain_holonomy(&stations).expect("the reading returns"), Some(false));
}

/// **The hinge scan alone, over a longer measured window.**
///
/// The scan is ranks only — no resolvent, no characteristic polynomial — so a window five times
/// the chain reading's is affordable, and the shape of the section profile along the chain is what
/// the reading returns. `#[ignore]`d for the same reason as the chain reading: it is a
/// measurement.
///
/// Run it with
/// `cargo test -p holonic-engine --lib holonic_chain::tests::the_measured_hinge_scan -- --ignored --nocapture`.
#[test]
#[ignore = "an exact measurement on the authenticated M5 release, not a law"]
fn the_measured_hinge_scan_over_a_longer_window_returns_its_section_profile() {
    let root = std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_STRUCTURE_ROOT));
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the measured hinge scan cannot be \
         taken, and this test refuses to report success without taking it. Place the authenticated \
         release at that path, or set {STRUCTURE_ROOT_ENV} to the directory carrying \
         designed-free-rbx1.cif. Every law this module owns is checked without any fixture by the \
         synthetic tests above, in particular the_hinge_is_the_cut_whose_neck_section_is_minimal.",
        root.display()
    );
    const LONG_WINDOW: usize = 40;
    let started = std::time::Instant::now();
    let jacobian = measured_jacobian(
        "designed-free",
        &root.join("designed-free-rbx1.cif"),
        LONG_WINDOW,
    )
    .unwrap_or_else(|error| panic!("designed-free: {error}"));
    eprintln!(
        "[measured] window {LONG_WINDOW} residues, {} coordinates, {} constraints",
        3 * LONG_WINDOW,
        jacobian.constraint_count()
    );
    let search = hinge_by_minimal_section(&jacobian, 1, CUT_CEILING).expect("the search returns");
    let profile: Vec<(usize, usize)> = search
        .scanned()
        .iter()
        .map(|candidate| (candidate.cut, candidate.section))
        .collect();
    eprintln!("[measured] section profile (cut, section): {profile:?}");
    let interior = hinge_by_minimal_section(&jacobian, 5, CUT_CEILING).expect("the search returns");
    eprintln!(
        "[measured] margin 1: cut {} section {}; margin {}: cut {} section {}",
        search.cut(),
        search.section(),
        interior.margin(),
        interior.cut(),
        interior.section()
    );
    // Local minima of the section profile, which is what "a hinge" means along a chain.
    let local: Vec<(usize, usize)> = (1..profile.len() - 1)
        .filter(|at| {
            profile[*at].1 < profile[at - 1].1 && profile[*at].1 <= profile[at + 1].1
        })
        .map(|at| profile[at])
        .collect();
    eprintln!("[measured] interior local minima (cut, section): {local:?}");
    eprintln!(
        "[measured] the scan cost {:.1} s of wall clock",
        started.elapsed().as_secs_f64()
    );
    assert!(matches!(search.verdict(), HingeVerdict::Minimal { .. }));
}

/// The aperture chart a chain's perspective declares is carried, never guessed.
#[test]
fn the_aperture_chart_of_a_chain_is_the_downstream_block() {
    let chain = skew_chain(&[1, 0, 0]);
    assert_eq!(
        chain.interaction().perspective().chart(),
        ApertureChart::Block(Carrier::Medium(1))
    );
    assert_eq!(chain.upstream(), Carrier::Medium(0));
    assert_eq!(chain.downstream(), Carrier::Medium(1));
    assert!(!chain.receiver_participates());
    assert_eq!(chain.schema(), HOLONIC_CHAIN_SCHEMA);
    assert!(chain.poles(PoleReading::Named).is_ok());
}
