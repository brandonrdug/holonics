//! **One chain, read on synthetic exact bodies.**
//!
//! [definition] Every law this module owns is checked without any fixture.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{One, Zero};
use holonics::geometry::Rat;

use super::*;
use holonics::receiver::causal_chord::PoleReading;
use holonics::exact_linear::ExactRatMatrix;
use crate::holonic_interaction::{
    ApertureChart, Carrier, ContactFace, Coupling, HolonicInteraction, Medium, MediumContact,
    Perspective, ReceiverBody, SourceCurrent, SpectralLicence, StructuralPlacement,
};
use holonics::inertia::SymmetricForm;
use crate::neck::{
    AnalyticCertificate, ConstitutiveLink, NeckReading, RealSpectrumLicence, WidthFace,
};
use holonics::geometry::winding_inertia::Hand;
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

/// **A closed neck has no pole, so it has no analytic width — whatever the generator's spectrum.**
/// A width is a distance to a pole of the transfer; `H ≡ 0` has none. A structural placement of
/// the spectrum must not be read as a width of zero here (review finding, September 19).
#[test]
fn a_closed_neck_has_no_pole_and_therefore_no_analytic_width() {
    let chain = closed_chain();
    let state = vec![int(1), int(1), int(1), int(1)];
    let stations = chain.power_stations(&state, &[int(1)]).expect("the stations read");
    let link = ConstitutiveLink::declare(
        "test|closed-link",
        "the declared receiving scope of this chain",
        WidthFace::Geometric,
        WidthFace::Analytic,
        Rat::one(),
    )
    .expect("the link stands");
    let widths = chain
        .chain_widths(&stations, None, link)
        .expect("the widths read");
    assert_eq!(widths.scope(), AnalyticScope::TransferHasNoPole);
    assert!(!widths.scope().is_decided());
    assert!(widths.analytic().is_none(), "no pole, so no width is returned");
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

/// **The rank is determined by a theorem, and the measurement agrees — including at a probe the
/// Lean theorem does not cover.**
///
/// The chain is `|source⟩ → 1 mode → skew neck → 2 modes → ⟨perspective|` with a dissipative face
/// on the downstream medium's first coordinate. Both ports are identities on their blocks, so
/// `B₁` has full row rank and `C₂` full column rank and the determined arm applies:
/// `rank H(s) = rank A_↗ = 1` at every probe off the joint poles, with no resolvent formed.
///
/// `A₂₂ = [[−1, 0], [0, 0]]` has the eigenvalues `−1` and `0`, so `N₂₂ = sI − A₂₂` is **singular
/// at `s = −1`** — and the joint `N = sI − A` is not, because `−1` is not a joint pole. That is
/// exactly the probe `HolonicChain.lean::transfer_rank_le_neck_rank` cannot reach (its `hQ`
/// hypothesis asks for `N₂₂` invertible) and the Fiedler–Markham nullity theorem covers
/// unconditionally. The measured route is taken there and must agree with the determined one.
#[test]
fn the_determined_rank_agrees_with_the_measured_one_where_the_downstream_block_is_singular() {
    let upstream = Medium::declared("test|upstream", identity(1), matrix(1, 1, &[0]), Vec::new())
        .expect("the upstream medium stands");
    let downstream = Medium::declared(
        "test|downstream",
        identity(2),
        matrix(2, 2, &[0, 0, 0, 0]),
        vec![
            ContactFace::declared(
                "test|downstream-face",
                matrix(1, 2, &[1, 0]),
                identity(1),
                Rat::one(),
            )
            .expect("the face stands"),
        ],
    )
    .expect("the downstream medium stands");
    let coupling = Coupling::declared(
        "test|neck",
        Carrier::Medium(0),
        Carrier::Medium(1),
        matrix(2, 1, &[1, 0]),
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
        matrix(2, 2, &[1, 0, 0, 1]),
        vec!["read-0".to_owned(), "read-1".to_owned()],
    )
    .expect("the perspective stands");
    let interaction = HolonicInteraction::declared(
        "test|determined-chain",
        source,
        vec![upstream, downstream],
        Vec::new(),
        vec![coupling],
        None,
        perspective,
    )
    .expect("the interaction stands");
    let chain = HolonicChain::over("test|determined-chain", interaction).expect("the chain reads");

    // The blocks are what the argument says they are.
    let generator = chain.interaction().generator().expect("the generator assembles");
    let downstream_block = matrix(2, 2, &[-1, 0, 0, 0]);
    for row in 0..2 {
        for column in 0..2 {
            assert_eq!(
                generator.get(1 + row, 1 + column).expect("an entry"),
                downstream_block.get(row, column).expect("an entry"),
                "A₂₂ is the isolated downstream medium's own generator"
            );
        }
    }

    let ports = chain.port_ranks().expect("the port ranks read");
    assert!(ports.ports_are_separated);
    assert_eq!((ports.upstream_rank, ports.upstream_extent), (1, 1));
    assert_eq!((ports.downstream_rank, ports.downstream_extent), (2, 2));
    assert!(ports.are_full_rank_on_their_blocks);

    // The determined arm takes no probe at all and forms no resolvent.
    let determined = chain
        .rank_reading(RankRoute::Determined, &[])
        .expect("the determined rank reads with no probe");
    assert!(determined.is_determined());
    assert_eq!(determined.licence(), RankLicence::Determined { rank: 1 });
    assert_eq!(determined.bound(), 1);
    assert_eq!(determined.port_bound(), 1);
    assert_eq!(determined.attained(), 1);
    assert!(determined.bound_is_attained());
    assert!(
        determined.measured().is_empty(),
        "the determined arm measures nothing"
    );

    // `s = −1` is an eigenvalue of the isolated downstream medium, so `N₂₂` is singular there;
    // the joint `N` is not, because `−1` is not a root of `λ(λ² + λ + 1)`.
    let downstream_characteristic = downstream_block
        .characteristic_polynomial()
        .expect("the downstream characteristic polynomial");
    assert!(
        downstream_characteristic
            .evaluate(&int(-1))
            .is_zero(),
        "s = −1 is an eigenvalue of A₂₂, so N₂₂ is singular there"
    );
    let joint_characteristic = generator
        .characteristic_polynomial()
        .expect("the joint characteristic polynomial");
    assert!(
        !joint_characteristic.evaluate(&int(-1)).is_zero(),
        "and it is not a joint pole, so the resolvent exists there"
    );

    let measured = chain
        .rank_reading(RankRoute::Measured, &[int(-1), int(2), int(5)])
        .expect("the measured rank reads");
    assert!(!measured.is_determined());
    assert_eq!(measured.licence(), RankLicence::Bounded { bound: 1 });
    for (probe, rank) in measured.measured() {
        assert_eq!(
            *rank,
            determined.attained(),
            "the measured rank at the probe {probe} must be the determined one"
        );
    }
    assert_eq!(measured.attained(), determined.attained());
}

/// **A chain whose ports do not read their whole blocks takes the bound, not the theorem.**
///
/// The skew chain's aperture is one covector on a three-mode medium, so `C₂` has rank `1 < 3` and
/// the determined arm is withheld by name: the reading falls back to measuring at the declared
/// probes, and `port_bound` is the tighter `min(r, rank B₁, rank C₂)`.
#[test]
fn a_port_that_does_not_read_its_block_withholds_the_determined_arm() {
    let chain = skew_chain(&[1, 0, 0]);
    let ports = chain.port_ranks().expect("the port ranks read");
    assert!(ports.ports_are_separated);
    assert_eq!((ports.downstream_rank, ports.downstream_extent), (1, 3));
    assert!(!ports.are_full_rank_on_their_blocks);

    let reading = chain
        .rank_reading(RankRoute::Determined, &[int(1), int(2)])
        .expect("the reading falls back to measuring");
    assert!(!reading.is_determined());
    assert_eq!(reading.port_bound(), 1);
    assert_eq!(reading.measured().len(), 2);
    assert!(
        chain.rank_reading(RankRoute::Determined, &[]).is_err(),
        "with the theorem withheld there is nothing to read without a probe"
    );
}

/// **The analytic face of an elastic chain is decided by structure, at any extent, with no pole
/// computed.**
///
/// `Ω = 0`, `G = I`, `M = JᵀJ`: `A = −M` is self-adjoint in the `G`-pairing, so every eigenvalue
/// is real and `≤ 0`, every pole is real and the strip has closed. The twelve-coordinate synthetic
/// hinge is *below* [`ANALYTIC_EXTENT_CEILING`], so the two routes can be compared directly: the
/// pole atlas must agree with the placement.
#[test]
fn the_elastic_chain_decides_its_analytic_face_by_structure_and_the_atlas_agrees() {
    let jacobian = two_triangles_and_a_hinge();
    let search = hinge_by_minimal_section(&jacobian, 1, CUT_CEILING).expect("the search returns");
    let chain = elastic_chain("synthetic-hinge", &jacobian, search.cut()).expect("the chain builds");
    assert_eq!(chain.interaction().joint_dimension(), 12);

    let placement = chain
        .interaction()
        .structural_placement()
        .expect("the placement reads");
    assert_eq!(placement, StructuralPlacement::RealNonpositive);

    // At twelve coordinates the count is within its bound, so the placement is cross-checked
    // three ways at once: `right = 0` from the licence, the conservative core against the on-axis
    // count, and — the sharp one — the split of `G M G` against the whole half-plane count, which
    // is Sylvester's law standing in for the spectral theorem. A disagreement refuses; this call
    // returning at all is the check.
    let spectrum = chain
        .interaction()
        .spectral_reading()
        .expect("the spectral reading returns");
    assert_eq!(spectrum.licence(), SpectralLicence::RealNonpositive);
    assert!(spectrum.licenses_real_spectrum());
    assert!(spectrum.licenses_non_growth() && !spectrum.licenses_decay());
    let reading = rigidity_reading(&jacobian).expect("the rigidity reading returns");
    let half_plane = spectrum.half_plane().expect("the count is within its bound");
    assert_eq!(half_plane.right, 0, "nothing grows in an elastic network");
    assert_eq!(
        half_plane.left, reading.rank,
        "the constrained directions are the decaying ones"
    );
    assert_eq!(
        half_plane.axis,
        12 - reading.rank,
        "and ker J — the rigid motions and the mechanisms — is what stays on the axis"
    );
    let core = spectrum
        .conservative_core()
        .expect("the core is within its ceiling");
    assert_eq!(core.dimension(), 12 - reading.rank);
    assert_eq!(core.dimension(), core.basis().len());

    let state: Vec<Rat> = (0..12).map(|at| int(at as i64 % 5 - 2)).collect();
    let input: Vec<Rat> = (0..6).map(|at| int(at as i64 - 3)).collect();
    let stations = chain.power_stations(&state, &input).expect("the stations read");
    let link = ConstitutiveLink::declare(
        "synthetic|link",
        "the declared receiving scope of this chain",
        WidthFace::Geometric,
        WidthFace::Analytic,
        Rat::one(),
    )
    .expect("the link stands");
    let widths = chain
        .chain_widths(&stations, None, link)
        .expect("the widths read");
    assert_eq!(
        widths.scope(),
        AnalyticScope::StructurallyPlaced {
            licence: RealSpectrumLicence::GSelfAdjointNegativeSemidefinite
        }
    );
    assert!(widths.scope().is_decided());
    let analytic = widths.analytic().expect("the analytic face is decided");
    assert!(analytic.squared_half_width().is_zero());
    assert!(analytic.is_complete(), "nothing was left undecided");
    assert_eq!(
        analytic.attaining(),
        &AnalyticCertificate::StructurallyPlacedOnTheRealAxis {
            licence: RealSpectrumLicence::GSelfAdjointNegativeSemidefinite,
            extent: 12
        }
    );

    // The independent route, within its own ceiling: the pole atlas of the same chain. Its width
    // must be the same number, reached by computing poles rather than by placing them.
    let atlas = chain.poles(PoleReading::Named).expect("the atlas reads");
    let measured = crate::neck::analytic_width(&atlas).expect("the measured width reads");
    assert!(
        measured.squared_half_width().is_zero(),
        "a real spectrum closes the strip, however the width is reached"
    );
}

/// **The conservative core is the on-axis count, and dissipation is what removes it.**
///
/// A two-medium chain with one dissipative face at the neck: the modes the dissipation cannot see
/// are exactly the eigenvalues that stay on the axis, which is LaSalle's condition on a finite
/// chart. The core is computed from `M G, M G A, …` and compared with the exact half-plane count,
/// which knows nothing of invariant subspaces.
#[test]
fn the_conservative_core_is_the_on_axis_count_of_a_dissipative_chain() {
    let chain = dissipative_chain(&[1, 0, 0]);
    let spectrum = chain
        .interaction()
        .spectral_reading()
        .expect("the spectral reading returns");
    assert_eq!(
        spectrum.placement(),
        StructuralPlacement::NonGrowth,
        "the downstream medium carries a skew structure, so this is the general arm and not the \
         self-adjoint one"
    );
    let core = spectrum
        .conservative_core()
        .expect("the core is within its ceiling");
    let half_plane = spectrum
        .half_plane()
        .expect("the count is within its bound");
    assert_eq!(
        core.dimension(),
        half_plane.axis,
        "the largest A-invariant subspace inside ker(M G) is the on-axis count"
    );
    assert_eq!(half_plane.right, 0, "nothing grows");
    assert_eq!(
        spectrum.licenses_decay(),
        core.is_trivial(),
        "decay is licensed exactly when dissipation sees every mode"
    );
    // The split-and-hand wording, never a bare count of signs.
    assert_eq!(spectrum.storage().split, (4, 0));
    assert_eq!(spectrum.storage().hand, Hand::WithTheTurn);
    assert!(
        spectrum.storage().windings.is_some(),
        "the storage form of this chain is a symmetric circulant, so its passages are named"
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

/// **The five-station balance is a view of the core energy balance**, and the same point read
/// through the core Holon (`Holon/Element.lean::PortHolon.power_balance`) returns its numbers.
#[test]
fn the_power_stations_are_the_core_point_balance_with_the_same_numbers() {
    let state = vec![int(2), int(-1), int(3), int(1)];
    for chain in [dissipative_chain(&[1, 0, 0]), skew_chain(&[1, 0, 0])] {
        let stations = chain
            .power_stations(&state, &[int(5)])
            .expect("the stations read");
        let balance = stations.energy_balance();
        assert!(balance.is_exact());
        assert_eq!(balance.residual, -stations.transport_residual().clone());
        assert_eq!(&balance.stored_change, stations.storage_rate_total());
        assert_eq!(&balance.dissipated, stations.dissipated());
        assert_eq!(&balance.port, stations.injected());

        let point = chain
            .interaction()
            .power_balance_at(&state, &[int(5)])
            .expect("the core admits the point");
        assert!(point.residual().is_zero());
        assert_eq!(&point.storage_rate, stations.storage_rate_total());
        assert_eq!(&point.dissipated, stations.dissipated());
        assert_eq!(&point.port, stations.injected());
    }
}
