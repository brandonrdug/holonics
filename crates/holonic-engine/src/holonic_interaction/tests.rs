//! Tests for the Holonic Interaction unit: media, contact exchange, the derived modal response
//! and the interface between two media. Every value is exact; no float decides anything.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use holonics::geometry::Rat;

use super::*;
use holonics::receiver::causal_chord::PoleReading;
use crate::edit_rigidity::ExactMetric;
use crate::junction_law::{Interface, JointUnits, JunctionField, ResistiveNetwork, Side};

// ---------------------------------------------------------------------------------------------
// exact builders
// ---------------------------------------------------------------------------------------------

fn rat(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn int(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn vector(values: &[i64]) -> Vec<Rat> {
    values.iter().map(|value| int(*value)).collect()
}

fn matrix(rows: &[&[i64]]) -> ExactRatMatrix {
    let columns = rows.first().map_or(0, |row| row.len());
    ExactRatMatrix::shaped(
        rows.len(),
        columns,
        rows.iter().map(|row| vector(row)).collect(),
    )
    .expect("the declared shape stands")
}

fn form(rows: &[&[i64]]) -> SymmetricForm {
    SymmetricForm::from_rows(rows.iter().map(|row| vector(row)).collect())
        .expect("the declared form is symmetric")
}

/// A harmonic medium in port-Hamiltonian coordinates `(q, p)`: storage `diag(k, 1)` and the
/// canonical symplectic structure. Its generator `ΩG` has the spectrum `±i√k`.
fn oscillator(name: &str, stiffness: i64) -> Medium {
    Medium::declared(
        name,
        form(&[&[stiffness, 0], &[0, 1]]),
        matrix(&[&[0, 1], &[-1, 0]]),
        Vec::new(),
    )
    .expect("the medium stands")
}

// =============================================================================================
// (a) two lattice cells with one slipping face
// =============================================================================================

/// The face between two one-coordinate cells: its slip is the relative displacement.
fn slipping_face(name: &str, response: i64, weight: i64) -> ContactFace {
    ContactFace::declared(name, matrix(&[&[1, -1]]), form(&[&[response]]), int(weight))
        .expect("the face stands")
}

/// Lean: `quad_faceForm`, `quad_contactForm`, `contactForm_nonneg`.
#[test]
fn one_slipping_face_between_two_cells_dissipates_exactly_its_relative_motion() {
    let dissipation = ContactDissipation::assemble(
        "test|cells|contact",
        2,
        vec![slipping_face("test|cells|face", 1, 1)],
    )
    .expect("the assembly stands");

    // `M_contact = [[1,-1],[-1,1]]`: rank one, positive semidefinite, nullity one.
    assert!(dissipation.signature().is_positive_semidefinite());
    assert_eq!(dissipation.signature().positive, 1);
    assert_eq!(dissipation.signature().zero, 1);
    assert_eq!(dissipation.signature().negative, 0);

    // `P_diss` at the opposing motion, and at the rigid translation.
    assert_eq!(
        dissipation.power(&vector(&[1, -1])).expect("a motion"),
        int(4)
    );
    assert_eq!(
        dissipation.power(&vector(&[1, 1])).expect("a motion"),
        Rat::zero()
    );

    // The face population, not only its sum: `quad_contactForm`'s right-hand side, and the sum
    // is cross-checked against `power` rather than one calling the other.
    let by_face = dissipation
        .power_by_face(&vector(&[1, -1]))
        .expect("a motion");
    assert_eq!(by_face.len(), 1);
    let total = by_face
        .iter()
        .fold(Rat::zero(), |sum, (_, value)| sum + value);
    assert_eq!(total, dissipation.power(&vector(&[1, -1])).expect("a motion"));

    // `t_f = −D_f J_f v`: the traction opposes the slip.
    let face = &dissipation.faces()[0];
    assert_eq!(face.slip_of(&vector(&[1, -1])).expect("slip"), vector(&[2]));
    assert_eq!(
        face.traction_of(&vector(&[1, -1])).expect("traction"),
        vector(&[-2])
    );
}

/// Lean: `contactForm_kernel_iff` — the kernel is exactly the zero-slip motions.
#[test]
fn the_contact_kernel_is_the_motion_that_slips_on_no_face() {
    let dissipation = ContactDissipation::assemble(
        "test|cells|contact",
        2,
        vec![slipping_face("test|cells|face", 1, 1)],
    )
    .expect("the assembly stands");
    assert!(
        dissipation.every_face_is_dissipative(),
        "the response is definite on its face, which is the hypothesis of contactForm_kernel_iff"
    );
    let kernel = dissipation.kernel_basis().expect("a kernel");
    let zero_slip = dissipation.zero_slip_kernel().expect("a zero-slip kernel");
    assert_eq!(kernel.len(), 1, "the rigid translation, and nothing else");
    assert_eq!(
        kernel, zero_slip,
        "over dissipative faces the two subspaces are one subspace"
    );
    // And it really is the rigid translation: it slips nowhere.
    assert_eq!(
        dissipation.faces()[0]
            .slip_of(&kernel[0])
            .expect("the kernel vector is a motion"),
        vector(&[0])
    );
}

/// Lean: `clockedEnergy_eq_duration_times_power`, `clockedEnergy_scales_inversely`.
#[test]
fn a_position_edit_becomes_an_energy_only_once_its_clock_is_declared() {
    let dissipation = ContactDissipation::assemble(
        "test|cells|contact",
        2,
        vec![slipping_face("test|cells|face", 1, 1)],
    )
    .expect("the assembly stands");
    let edit = vector(&[1, -1]);

    let unit_clock = Clock::declared("test|clock|unit", int(1), "declared-energy-unit")
        .expect("a positive duration");
    let half_clock = Clock::declared("test|clock|half", rat(1, 2), "declared-energy-unit")
        .expect("a positive duration");

    let slow = dissipation
        .clocked_energy(&edit, &unit_clock)
        .expect("an energy");
    let quick = dissipation
        .clocked_energy(&edit, &half_clock)
        .expect("an energy");

    assert_eq!(*slow.quadratic(), int(4));
    assert_eq!(*slow.energy(), int(4));
    assert_eq!(*quick.quadratic(), int(4), "the edit did not change");
    assert_eq!(*quick.energy(), int(8), "halving the clock doubles the energy");
    assert_eq!(*quick.duration(), rat(1, 2));
    assert_eq!(
        quick.unit(),
        "declared-energy-unit",
        "the unit tag is carried with the number"
    );
}

// =============================================================================================
// how this differs from T4's `W²`
// =============================================================================================

/// A definite contact form on two coordinates: `M_contact = diag(2, 2)`.
fn definite_contact() -> ContactDissipation {
    ContactDissipation::assemble(
        "test|definite|contact",
        2,
        vec![
            ContactFace::declared("test|definite|x", matrix(&[&[1, 0]]), form(&[&[2]]), int(1))
                .expect("a face"),
            ContactFace::declared("test|definite|y", matrix(&[&[0, 1]]), form(&[&[2]]), int(1))
                .expect("a face"),
        ],
    )
    .expect("the assembly stands")
}

#[test]
fn a_declared_edit_metric_is_the_clocked_contact_form_exactly_at_the_clock_that_makes_it_so() {
    let dissipation = definite_contact();
    assert!(dissipation.signature().is_positive_definite());
    let metric = ExactMetric::unit("test|unit-metric", 2).expect("the unit metric");

    // At `h = 2`, `M_contact / h` is the unit metric: T4's `W²` here IS the clocked contact
    // energy of this medium.
    let matched = Clock::declared("test|clock|two", int(2), "declared-energy-unit")
        .expect("a positive duration");
    let reading = compare_edit_metric(&dissipation, &matched, &metric).expect("a reading");
    assert!(reading.is_clocked_contact_metric());
    match reading {
        EditMetricReading::ClockedContactMetric { duration, .. } => assert_eq!(duration, int(2)),
        other => panic!("expected the clocked contact metric, got {other:?}"),
    }

    // At `h = 1` the same declared metric is only an authored edit metric, and the whole
    // residual is returned rather than a verdict.
    let mismatched = Clock::declared("test|clock|one", int(1), "declared-energy-unit")
        .expect("a positive duration");
    let reading = compare_edit_metric(&dissipation, &mismatched, &metric).expect("a reading");
    match reading {
        EditMetricReading::AuthoredEditMetric {
            residual,
            offending,
            ..
        } => {
            assert_eq!(offending, vec![(0, 0), (1, 1)]);
            assert_eq!(*residual.at(0, 0), int(-1));
            assert_eq!(*residual.at(1, 1), int(-1));
            assert_eq!(*residual.at(0, 1), Rat::zero());
        }
        other => panic!("expected an authored edit metric, got {other:?}"),
    }
}

#[test]
fn a_degenerate_contact_form_is_not_an_edit_metric_at_any_clock() {
    let dissipation = ContactDissipation::assemble(
        "test|cells|contact",
        2,
        vec![slipping_face("test|cells|face", 1, 1)],
    )
    .expect("the assembly stands");
    let metric = ExactMetric::unit("test|unit-metric", 2).expect("the unit metric");
    let clock =
        Clock::declared("test|clock|one", int(1), "declared-energy-unit").expect("a duration");
    let reading = compare_edit_metric(&dissipation, &clock, &metric).expect("a reading");
    assert!(!reading.is_clocked_contact_metric());
    match reading {
        EditMetricReading::ContactFormIsDegenerate {
            nullity, kernel, ..
        } => {
            assert_eq!(nullity, 1);
            assert_eq!(kernel.len(), 1, "the zero-slip motion is returned, not a flag");
        }
        other => panic!("expected the degenerate reading, got {other:?}"),
    }
}

// =============================================================================================
// (b) a two-medium chain whose poles move off the axis when the shared face becomes dissipative
// =============================================================================================

/// Two harmonic media sharing one face, with `H_pert` standing by to make that face dissipative.
fn two_medium_chain() -> HolonicInteraction {
    let media = vec![
        oscillator("test|chain|medium-0", 1),
        oscillator("test|chain|medium-1", 4),
    ];
    // The shared face reads the difference of the two media's momentum coordinates, over the
    // concatenated chart `(q0, p0, q1, p1)`.
    let standing_face = ContactFace::declared(
        "test|chain|face|standing",
        matrix(&[&[0, 1, 0, -1]]),
        form(&[&[0]]),
        int(1),
    )
    .expect("a face with a vanishing response is lawful and not dissipative");
    let dissipative_face = ContactFace::declared(
        "test|chain|face|dissipative",
        matrix(&[&[0, 1, 0, -1]]),
        form(&[&[1]]),
        int(1),
    )
    .expect("a face");
    let contact = MediumContact::declared(
        "test|chain|contact",
        Carrier::Medium(0),
        Carrier::Medium(1),
        standing_face,
    )
    .expect("the contact stands");
    let source = SourceCurrent::declared(
        "test|chain|source",
        Carrier::Medium(0),
        matrix(&[&[0], &[1]]),
        vec!["drive".to_owned()],
    )
    .expect("the source stands");
    let perspective = Perspective::standing(
        "test|chain|perspective",
        Carrier::Medium(1),
        matrix(&[&[1, 0]]),
        vec!["far-displacement".to_owned()],
    )
    .expect("the perspective stands");
    HolonicInteraction::declared(
        "test|chain",
        source,
        media,
        vec![contact],
        Vec::new(),
        Some(Perturbation::Contact {
            contact: 0,
            replacement: dissipative_face,
        }),
        perspective,
    )
    .expect("the unit stands")
}

/// Lean: `port_storage_rate`, `port_storage_rate_zero_of_no_dissipation`, `storage_rate_nonpos`.
#[test]
fn the_chain_poles_leave_the_axis_exactly_when_the_shared_face_becomes_dissipative() {
    let unit = two_medium_chain();
    assert_eq!(unit.joint_dimension(), 4);

    let standing = unit.standing().expect("the standing unit");
    let standing_rate = standing.storage_rate().expect("a rate reading");
    assert!(
        standing_rate.agrees(),
        "AᵀG + GA must equal −2 G M G at every reading"
    );
    assert!(
        standing_rate.is_conservative(),
        "with no dissipation the storage rate vanishes"
    );
    let standing_spectrum = standing.spectral_reading().expect("a spectral reading");
    assert!(
        standing_spectrum.licenses_non_growth() && !standing_spectrum.licenses_decay(),
        "an undamped oscillator is licensed non-growth, never decay: all four poles sit on the axis"
    );
    // `G ≻ 0`, `M = 0`, `Ω ≠ 0`: the conservative arm, named by structure before any count.
    assert_eq!(
        standing_spectrum.placement(),
        StructuralPlacement::OnTheOrientationAxis
    );
    assert_eq!(
        standing_spectrum.licence(),
        SpectralLicence::OnTheOrientationAxis
    );
    // The split-and-hand wording, not a bare count of signs.
    assert_eq!(standing_spectrum.storage().split, (4, 0));
    assert_eq!(standing_spectrum.storage().hand, Hand::WithTheTurn);
    assert_eq!(standing_spectrum.storage().null, 0);
    // With `M = 0` nothing dissipates, so the whole chart is the conservative core — and it
    // agrees with the exact on-axis count, which is the cross-check.
    let core = standing_spectrum
        .conservative_core()
        .expect("the core is within its ceiling");
    assert_eq!(core.dimension(), 4);
    assert_eq!(
        core.dimension(),
        standing_spectrum
            .half_plane()
            .expect("the count is within its bound")
            .axis
    );
    assert_eq!(standing_spectrum.half_plane().expect("the count is within its bound").degree, 4);
    assert_eq!(standing_spectrum.half_plane().expect("the count is within its bound").axis, 4, "±i and ±2i");
    assert_eq!(standing_spectrum.half_plane().expect("the count is within its bound").left, 0);
    assert_eq!(standing_spectrum.half_plane().expect("the count is within its bound").right, 0);

    let modulated = unit.modulated().expect("the modulated unit");
    let modulated_rate = modulated.storage_rate().expect("a rate reading");
    assert!(modulated_rate.agrees());
    assert!(
        !modulated_rate.is_conservative(),
        "the dissipative face makes the storage rate nonzero"
    );
    assert_eq!(
        modulated_rate.rate_inertia().positive,
        0,
        "the rate form is negative semidefinite: the storage reading never grows"
    );
    // The rate at a motion that slips is strictly negative — strict decay on the slip-active
    // subspace, read from the rate form itself.
    let slipping = vector(&[0, 1, 0, -1]);
    assert!(
        modulated_rate
            .rate_at(&slipping)
            .expect("a motion")
            .is_negative(),
        "the storage reading strictly decays along a slipping motion"
    );

    let modulated_spectrum = modulated.spectral_reading().expect("a spectral reading");
    assert!(modulated_spectrum.licenses_non_growth());
    assert_eq!(
        modulated_spectrum.licenses_decay(),
        modulated_spectrum.half_plane().expect("the count is within its bound").axis == 0,
        "decay is licensed exactly when the exact count leaves no pole on the axis"
    );
    assert_eq!(modulated_spectrum.half_plane().expect("the count is within its bound").right, 0);
    assert!(
        modulated_spectrum.half_plane().expect("the count is within its bound").left > 0,
        "the dissipative face pulls poles into the left half plane"
    );
    assert!(
        modulated_spectrum.half_plane().expect("the count is within its bound").axis < 4,
        "and off the axis they went"
    );

    // The consumer call is real: the chord owner factors the denominator it was handed.
    let atlas = modulated
        .poles(PoleReading::Certified)
        .expect("the pole atlas");
    assert!(atlas.accounted() > 0);
}

/// The interface of the chain is the first of the 2026-08-24 populations.
#[test]
fn two_media_in_declared_contact_are_shared_incidence() {
    let unit = two_medium_chain().modulated().expect("the modulated unit");
    let classification = classify_convergence(&unit, Carrier::Medium(0), Carrier::Medium(1))
        .expect("a classification");
    match classification.population() {
        ConvergencePopulation::SharedIncidence {
            contact,
            left_support,
            right_support,
        } => {
            assert_eq!(*contact, 0);
            assert_eq!(*left_support, vec![1], "the momentum coordinate of medium 0");
            assert_eq!(*right_support, vec![1], "and of medium 1");
        }
        other => panic!("expected shared incidence, got {other:?}"),
    }
    assert!(classification.also_satisfied().is_empty());
}

// =============================================================================================
// (c) the indefinite-storage counterexample
// =============================================================================================

/// `G = diag(1, −1)` with `Ω = [[0,−1],[1,0]]`, so `A = ΩG = [[0,1],[1,0]]`.
fn indefinite_unit() -> HolonicInteraction {
    let medium = Medium::declared(
        "test|indefinite|medium",
        form(&[&[1, 0], &[0, -1]]),
        matrix(&[&[0, -1], &[1, 0]]),
        Vec::new(),
    )
    .expect("an indefinite storage form is a lawful medium");
    let source = SourceCurrent::declared(
        "test|indefinite|source",
        Carrier::Medium(0),
        matrix(&[&[1], &[0]]),
        vec!["drive".to_owned()],
    )
    .expect("the source stands");
    let perspective = Perspective::standing(
        "test|indefinite|perspective",
        Carrier::Medium(0),
        matrix(&[&[1, 0]]),
        vec!["displacement".to_owned()],
    )
    .expect("the perspective stands");
    HolonicInteraction::declared(
        "test|indefinite",
        source,
        vec![medium],
        Vec::new(),
        Vec::new(),
        None,
        perspective,
    )
    .expect("the unit stands")
}

/// Lean: `indefiniteStorage_rate_form_vanishes`, `swapGenerator_has_a_right_half_plane_mode`,
/// `vanishing_rate_form_places_no_spectrum`. **This exact defect was corrected in review.**
#[test]
fn a_vanishing_rate_form_over_an_indefinite_storage_form_licenses_no_spectral_placement() {
    let unit = indefinite_unit();
    assert_eq!(
        unit.generator().expect("a generator"),
        matrix(&[&[0, 1], &[1, 0]]),
        "A = (Ω − 0)G is the exchange generator"
    );

    let rate = unit.storage_rate().expect("a rate reading");
    assert!(rate.agrees(), "the identity holds for an indefinite G too");
    assert!(
        rate.is_conservative(),
        "AᵀG + GA = 0 exactly, which is the trap"
    );
    assert!(
        rate.storage_inertia().is_indefinite(),
        "and the storage form is indefinite, which is why the trap is a trap"
    );
    assert_eq!(rate.storage_inertia().signature(), (1, 1));

    let spectrum = unit.spectral_reading().expect("a spectral reading");
    assert!(
        !spectrum.licenses_decay(),
        "no decay may be claimed from a vanishing rate form without a definite storage form"
    );
    // **Not silence any more: a bounded licence.** `G` is indefinite and nondegenerate with the
    // split `1` against `1`, and the rate form vanishes, so the generator is `G`-skew: at most
    // `min(1, 1) = 1` eigenvalue lies strictly to the right, and the spectrum is symmetric under
    // `λ ↦ −λ̄`. The pair attains the bound exactly.
    assert_eq!(
        spectrum.placement(),
        StructuralPlacement::PontryaginBounded { right_at_most: 1 }
    );
    assert_eq!(
        spectrum.licence(),
        SpectralLicence::PontryaginBounded { right_at_most: 1 }
    );
    assert_eq!(spectrum.storage().split, (1, 1));
    assert_eq!(spectrum.storage().null, 0, "nondegenerate, which the bound needs");
    let half_plane = spectrum
        .half_plane()
        .expect("the count is within its bound");
    assert_eq!(half_plane.degree, 2);
    assert_eq!(half_plane.left, 1);
    assert_eq!(half_plane.right, 1, "the eigenvalue +1 is right there");
    assert_eq!(half_plane.axis, 0);
    assert_eq!(half_plane.right, 1, "and the bound min(p, q) = 1 is attained");
}

// =============================================================================================
// (d) a participating receiver
// =============================================================================================

/// Lean: the plan's "a changing receiving Holon participates in the joint state and differential".
#[test]
fn a_participating_receiver_joins_the_state_and_the_chord_reaches_its_own_coordinates() {
    let body = ReceiverBody::declared(
        "test|participating|body",
        form(&[&[1, 0], &[0, 1]]),
        matrix(&[&[0, 1], &[-1, 0]]),
    )
    .expect("the receiver's own body stands");
    let coupling = Coupling::declared(
        "test|participating|coupling",
        Carrier::Medium(0),
        Carrier::Perspective,
        matrix(&[&[0, 1], &[0, 0]]),
    )
    .expect("the coupling stands");
    let source = SourceCurrent::declared(
        "test|participating|source",
        Carrier::Medium(0),
        matrix(&[&[0], &[1]]),
        vec!["drive".to_owned()],
    )
    .expect("the source stands");
    let perspective = Perspective::participating(
        "test|participating|perspective",
        matrix(&[&[1, 0]]),
        vec!["receiver-displacement".to_owned()],
        body,
    )
    .expect("the perspective stands");
    let unit = HolonicInteraction::declared(
        "test|participating",
        source,
        vec![oscillator("test|participating|medium", 1)],
        Vec::new(),
        vec![coupling],
        None,
        perspective,
    )
    .expect("the unit stands");

    assert_eq!(
        unit.joint_dimension(),
        4,
        "the receiver's own coordinates are part of the state"
    );
    assert!(unit.perspective().participates());

    // The joint structure stays skew with the coupling placed antisymmetrically.
    let structure = unit.joint_structure().expect("a joint structure");
    assert_eq!(*structure.get(2, 1).expect("an entry"), int(1));
    assert_eq!(*structure.get(1, 2).expect("an entry"), int(-1));

    // The consumer call: the derived `(A, B, C_R)` goes through the causal chord owner, and the
    // source reaches the receiver's *own* coordinate through the coupling.
    let linearization = unit.linearization().expect("a linearization");
    assert_eq!(linearization.extent(), 4);
    assert_eq!(linearization.source_count(), 1);
    assert_eq!(linearization.receiver_count(), 1);
    let transfer = unit.transfer().expect("a transfer function");
    let entry = transfer.entry(0, 0).expect("the one path");
    assert!(
        !entry.reduced_numerator.is_zero(),
        "a participating receiver is reached by the source it participates with"
    );

    // And the convergence of the medium with the receiver is the third population.
    let classification = classify_convergence(&unit, Carrier::Medium(0), Carrier::Perspective)
        .expect("a classification");
    match classification.population() {
        ConvergencePopulation::ConstitutiveCoupling {
            coupling,
            later_consequence,
            ..
        } => {
            assert_eq!(*coupling, 0);
            assert_eq!(
                *later_consequence,
                matrix(&[&[0, 1], &[0, 0]]),
                "the off-diagonal response term returns a later consequence in the generator"
            );
        }
        other => panic!("expected a declared constitutive coupling, got {other:?}"),
    }
}

// =============================================================================================
// the receiver caustic and the raster-only convergence
// =============================================================================================

fn two_unconnected_media(aperture: ExactRatMatrix) -> HolonicInteraction {
    let source = SourceCurrent::declared(
        "test|caustic|source",
        Carrier::Medium(0),
        matrix(&[&[0], &[1]]),
        vec!["drive".to_owned()],
    )
    .expect("the source stands");
    let perspective = Perspective::over_joint(
        "test|caustic|perspective",
        aperture,
        vec!["projected".to_owned()],
    )
    .expect("the perspective stands");
    HolonicInteraction::declared(
        "test|caustic",
        source,
        vec![
            oscillator("test|caustic|medium-0", 1),
            oscillator("test|caustic|medium-1", 1),
        ],
        Vec::new(),
        Vec::new(),
        None,
        perspective,
    )
    .expect("the unit stands")
}

#[test]
fn two_media_the_aperture_cannot_separate_are_a_receiver_caustic_with_its_fibre_retained() {
    let unit = two_unconnected_media(matrix(&[&[1, 0, 1, 0]]));
    let classification = classify_convergence(&unit, Carrier::Medium(0), Carrier::Medium(1))
        .expect("a classification");
    match classification.population() {
        ConvergencePopulation::ReceiverCaustic {
            left_coordinate,
            right_coordinate,
            retained_fibre,
        } => {
            assert_eq!(*left_coordinate, 0);
            assert_eq!(*right_coordinate, 0);
            assert_eq!(
                *retained_fibre,
                vector(&[1, 0, -1, 0]),
                "the reconstruction fibre is returned, so depth is retained rather than lost"
            );
        }
        other => panic!("expected a receiver caustic, got {other:?}"),
    }
    assert!(classification.also_satisfied().is_empty());
}

#[test]
fn a_convergence_with_no_contact_no_caustic_and_no_coupling_mints_no_source_law() {
    let unit = two_unconnected_media(matrix(&[&[1, 0, 0, 0]]));
    let classification = classify_convergence(&unit, Carrier::Medium(0), Carrier::Medium(1))
        .expect("a classification");
    assert_eq!(
        *classification.population(),
        ConvergencePopulation::NoSourceRelation,
        "a rendered crossing is not a source relation"
    );
}

// =============================================================================================
// the interface between two media, through the junction owner
// =============================================================================================

/// The normal half of the interface law is `check_junction`'s, computed by that owner.
#[test]
fn the_interface_between_two_media_is_read_through_the_junction_owner() {
    let network = ResistiveNetwork::declare(
        "test|interface|chain",
        3,
        &[(0, 1, int(2)), (1, 2, int(3))],
    )
    .expect("the chain stands");
    let operator = network.operator();
    let units = JointUnits::electrostatic().expect("declared units");
    let potential = vec![Rat::zero(), int(1), rat(4, 3)];
    let field = operator
        .coboundary(0)
        .expect("a coboundary")
        .apply(&potential)
        .expect("it applies");
    let source = vec![int(-2), int(1), int(1)];
    let interface = Interface::declare(
        "test|interface|face",
        operator,
        0,
        BTreeMap::from([
            (operator.cells(1)[0], Side::Left),
            (operator.cells(1)[1], Side::Right),
        ]),
        BTreeSet::from([operator.cells(0)[1]]),
    )
    .expect("the interface stands");

    let reading = InterfaceReading::read(
        "test|interface",
        Carrier::Medium(0),
        Carrier::Medium(1),
        operator,
        &interface,
        &JunctionField {
            potential: &potential,
            field: &field,
            source: &source,
        },
        &units,
    )
    .expect("the reading returns");

    assert!(reading.balances(), "the normal jump equals the declared source");
    assert_eq!(reading.left(), Carrier::Medium(0));
    assert_eq!(reading.right(), Carrier::Medium(1));
    let remainder = reading
        .normal_remainder()
        .expect("a decided verdict returns its residual");
    assert!(
        remainder.values().all(Zero::is_zero),
        "the normal remainder is retained as a cochain and reads zero here"
    );
}

// =============================================================================================
// `H_pert` enters through the same constructors
// =============================================================================================

#[test]
fn a_perturbation_of_a_mediums_constitutive_data_goes_back_through_its_constructor() {
    let unit = HolonicInteraction::declared(
        "test|perturbed",
        SourceCurrent::declared(
            "test|perturbed|source",
            Carrier::Medium(0),
            matrix(&[&[1], &[0]]),
            vec!["drive".to_owned()],
        )
        .expect("a source"),
        vec![oscillator("test|perturbed|medium", 1)],
        Vec::new(),
        Vec::new(),
        Some(Perturbation::Storage {
            medium: 0,
            storage: form(&[&[9, 0], &[0, 1]]),
        }),
        Perspective::standing(
            "test|perturbed|perspective",
            Carrier::Medium(0),
            matrix(&[&[1, 0]]),
            vec!["displacement".to_owned()],
        )
        .expect("a perspective"),
    )
    .expect("the unit stands");

    let standing = unit.standing().expect("the standing unit");
    let modulated = unit.modulated().expect("the modulated unit");
    assert_eq!(
        standing.spectral_reading().expect("a reading").half_plane().expect("the count is within its bound").axis,
        2
    );
    assert_eq!(
        modulated
            .media()
            .first()
            .expect("one medium")
            .storage()
            .at(0, 0),
        &int(9),
        "the admitted change is installed"
    );
    assert!(
        modulated.storage_rate().expect("a reading").is_conservative(),
        "a change of storage alone does not dissipate"
    );
    // The modulated generator is `ΩG` with the new stiffness: `±3i`.
    assert_eq!(
        modulated.generator().expect("a generator"),
        matrix(&[&[0, 1], &[-9, 0]])
    );
}

// =============================================================================================
// (e) refusals — every one of them a typed return, never a panic
// =============================================================================================

#[test]
fn a_face_whose_response_is_indefinite_is_refused_by_name() {
    let refusal = ContactFace::declared(
        "test|refusal|indefinite",
        matrix(&[&[1, 0], &[0, 1]]),
        form(&[&[1, 0], &[0, -1]]),
        int(1),
    )
    .expect_err("an indefinite response is not a dissipative response");
    assert!(matches!(
        refusal,
        InteractionRefusal::ResponseNotPositiveSemidefinite { negative: 1, .. }
    ));
}

#[test]
fn a_face_whose_response_does_not_match_its_slip_map_is_refused() {
    let refusal = ContactFace::declared(
        "test|refusal|width",
        matrix(&[&[1, 0, 0], &[0, 1, 0]]),
        form(&[&[1]]),
        int(1),
    )
    .expect_err("a 2-row slip map needs a 2×2 response");
    assert!(matches!(
        refusal,
        InteractionRefusal::WidthDisagrees {
            declared: 2,
            found: 1,
            ..
        }
    ));
}

#[test]
fn a_non_positive_face_weight_is_refused() {
    let refusal = ContactFace::declared(
        "test|refusal|weight",
        matrix(&[&[1, -1]]),
        form(&[&[1]]),
        Rat::zero(),
    )
    .expect_err("a face of no measure carries no exchange");
    assert!(matches!(
        refusal,
        InteractionRefusal::NotStrictlyPositive { .. }
    ));
}

#[test]
fn a_non_positive_clock_is_refused() {
    assert!(matches!(
        Clock::declared("test|refusal|clock", Rat::zero(), "unit")
            .expect_err("a zero duration divides nothing"),
        InteractionRefusal::NotStrictlyPositive { .. }
    ));
    assert!(matches!(
        Clock::declared("test|refusal|clock", int(-1), "unit")
            .expect_err("a negative duration is not a duration"),
        InteractionRefusal::NotStrictlyPositive { .. }
    ));
}

#[test]
fn an_oversize_declaration_is_refused_before_anything_is_sized_by_it() {
    let refusal = ContactDissipation::assemble(
        "test|refusal|oversize",
        DECLARED_MODE_CEILING + 1,
        Vec::new(),
    )
    .expect_err("the declaration is above the ceiling");
    assert!(matches!(
        refusal,
        InteractionRefusal::DeclarationAboveCeiling {
            declared,
            ceiling,
            ..
        } if declared == DECLARED_MODE_CEILING + 1 && ceiling == DECLARED_MODE_CEILING
    ));
}

#[test]
fn a_structure_matrix_that_is_not_skew_is_refused() {
    let refusal = Medium::declared(
        "test|refusal|skew",
        form(&[&[1, 0], &[0, 1]]),
        matrix(&[&[0, 1], &[1, 0]]),
        Vec::new(),
    )
    .expect_err("a symmetric structure is not a Hamiltonian structure");
    assert!(matches!(
        refusal,
        InteractionRefusal::StructureNotSkew { .. }
    ));
}

#[test]
fn an_interface_face_that_does_not_span_the_two_blocks_it_joins_is_refused() {
    let face = ContactFace::declared(
        "test|refusal|interface",
        matrix(&[&[1, -1]]),
        form(&[&[1]]),
        int(1),
    )
    .expect("the face itself stands");
    let refusal = HolonicInteraction::declared(
        "test|refusal|chain",
        SourceCurrent::declared(
            "test|refusal|source",
            Carrier::Medium(0),
            matrix(&[&[1], &[0]]),
            vec!["drive".to_owned()],
        )
        .expect("a source"),
        vec![
            oscillator("test|refusal|medium-0", 1),
            oscillator("test|refusal|medium-1", 1),
        ],
        vec![
            MediumContact::declared(
                "test|refusal|contact",
                Carrier::Medium(0),
                Carrier::Medium(1),
                face,
            )
            .expect("the contact declaration stands"),
        ],
        Vec::new(),
        None,
        Perspective::standing(
            "test|refusal|perspective",
            Carrier::Medium(1),
            matrix(&[&[1, 0]]),
            vec!["displacement".to_owned()],
        )
        .expect("a perspective"),
    )
    .expect_err("a two-coordinate face cannot join two two-coordinate blocks");
    assert!(matches!(
        refusal,
        InteractionRefusal::WidthDisagrees {
            declared: 4,
            found: 2,
            ..
        }
    ));
}

#[test]
fn a_carrier_the_interaction_does_not_carry_is_refused() {
    let unit = indefinite_unit();
    assert!(matches!(
        unit.block_extent(Carrier::Medium(7))
            .expect_err("there is one medium"),
        InteractionRefusal::CarrierAbsent { .. }
    ));
    assert!(
        matches!(
            unit.block_extent(Carrier::Perspective)
                .expect_err("this perspective declares no body"),
            InteractionRefusal::CarrierAbsent { .. }
        ),
        "a non-participating perspective is not a block of the joint chart"
    );
}

#[test]
fn a_chain_with_no_media_is_refused() {
    let refusal = HolonicInteraction::declared(
        "test|refusal|empty",
        SourceCurrent::declared(
            "test|refusal|source",
            Carrier::Medium(0),
            matrix(&[&[1]]),
            vec!["drive".to_owned()],
        )
        .expect("a source"),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        None,
        Perspective::standing(
            "test|refusal|perspective",
            Carrier::Medium(0),
            matrix(&[&[1]]),
            vec!["displacement".to_owned()],
        )
        .expect("a perspective"),
    )
    .expect_err("a chain of no media is not a chain");
    assert!(matches!(
        refusal,
        InteractionRefusal::EmptyDeclaration { .. }
    ));
}

// =============================================================================================
// the composition with T4: `W²` at the clocked contact metric IS the dissipated energy
// =============================================================================================

/// **The consuming call into `edit_rigidity::rethreading_work`.**
///
/// The metric handed to T4 is `M_contact / h` itself, and the `W²` it returns is exactly the
/// clocked energy of the compensation it found. That equality is what
/// [`compare_edit_metric`]'s `ClockedContactMetric` arm asserts, checked here against the owner
/// rather than declared.
#[test]
fn t4_squared_work_at_the_clocked_contact_metric_is_the_dissipated_energy_of_its_compensation() {
    use crate::edit_rigidity::{
        AllowedCompensation, EditDirection, EditVerdict, KeptReceiverJacobian, rethreading_work,
    };

    let dissipation = definite_contact();
    let clock = Clock::declared("test|clock|two", int(2), "declared-energy-unit")
        .expect("a positive duration");
    let metric = dissipation
        .clocked_metric(&clock)
        .expect("a definite contact form is a metric at a declared clock");

    // The declared metric IS the clocked contact form; the reading says so and not a boolean.
    assert!(
        compare_edit_metric(&dissipation, &clock, &metric)
            .expect("a reading")
            .is_clocked_contact_metric()
    );

    // One kept face `x + y`, an edit that moves `x`, and the complement as the allowed subspace.
    let jacobian = KeptReceiverJacobian::from_linear_faces(
        "test|kept|sum",
        2,
        vec![("x+y".to_owned(), vector(&[1, 1]))],
    )
    .expect("the kept family stands");
    let edit = EditDirection::declared("test|edit|x", vector(&[1, 0])).expect("an edit");
    let allowed = AllowedCompensation::complement_of("test|allowed", 2, &edit.support())
        .expect("the allowed subspace stands");

    let receipt = rethreading_work(&jacobian, &edit, &allowed, &metric).expect("T4 returns");
    let EditVerdict::Compensable {
        compensation,
        squared_work,
        ..
    } = &receipt.verdict
    else {
        panic!("the edit is compensable inside the complement, got {}", receipt.verdict.arm());
    };
    assert_eq!(*compensation, vector(&[0, -1]));
    assert_eq!(*squared_work, int(1));

    let energy = dissipation
        .clocked_energy(compensation, &clock)
        .expect("an energy");
    assert_eq!(
        squared_work, energy.energy(),
        "at this metric and this clock T4's W² IS the dissipated energy of the compensation"
    );
    assert_eq!(*energy.quadratic(), int(2), "and the unclocked form reads twice it");
}

// ---------------------------------------------------------------------------------------------
// the sparse contact assembly
// ---------------------------------------------------------------------------------------------

/// A bar face between two three-dimensional occurrences on a joint chart of `dimension`
/// coordinates: one slip coordinate, a unit response, a unit weight, and a support of six.
fn bar_face(
    lineage: &str,
    dimension: usize,
    left: usize,
    right: usize,
    direction: [i64; 3],
) -> ContactFace {
    let mut row = vec![Rat::zero(); dimension];
    for axis in 0..3 {
        row[3 * left + axis] = int(direction[axis]);
        row[3 * right + axis] = int(-direction[axis]);
    }
    ContactFace::declared(
        lineage.to_owned(),
        ExactRatMatrix::shaped(1, dimension, vec![row]).expect("a slip map"),
        SymmetricForm::from_rows(vec![vec![Rat::one()]]).expect("a unit response"),
        Rat::one(),
    )
    .expect("a declared bar face")
}

/// A bar network on a chain of `points` occurrences: the backbone and two further strides, which
/// is the species the measured rigidity and chain consumers assemble.
fn bar_network(points: usize) -> (usize, Vec<ContactFace>) {
    let dimension = 3 * points;
    let mut faces = Vec::new();
    for stride in [1usize, 2, 3] {
        for left in 0..points.saturating_sub(stride) {
            let right = left + stride;
            let direction = [
                (left as i64 * 37) % 23 - 11,
                (left as i64 * 91) % 19 - 9,
                (right as i64 * 53) % 17 - 8 + 1,
            ];
            faces.push(bar_face(
                &format!("bar|{stride}|{left}"),
                dimension,
                left,
                right,
                direction,
            ));
        }
    }
    (dimension, faces)
}

#[test]
fn the_sparse_assembly_is_the_dense_sum_entry_for_entry() {
    let (dimension, faces) = bar_network(6);
    let assembled = ContactDissipation::assemble("sparse", dimension, faces.clone())
        .expect("the sparse assembly returns");

    // The dense definition, formed face by face exactly as the previous assembly formed it.
    let mut dense = ExactRatMatrix::zero(dimension, dimension).expect("a zero form");
    for face in &faces {
        dense = dense.add(&face.face_form().expect("a face form")).expect("added");
    }
    assert_eq!(
        assembled.matrix().expect("the assembled matrix"),
        dense,
        "the sparse accumulation writes exactly the entries the dense product writes"
    );
    assert!(matches!(
        assembled.signature_scope(),
        SignatureScope::Congruence
    ));
    assert!(assembled.signature().is_positive_semidefinite());
}

#[test]
fn a_faces_support_is_read_off_its_slip_map_and_not_declared() {
    let face = bar_face("bar", 30, 2, 7, [3, -1, 4]);
    assert_eq!(face.support().expect("support"), vec![6, 7, 8, 21, 22, 23]);
    // A face whose direction is zero along one axis does not claim that coordinate.
    let flat = bar_face("flat", 30, 2, 7, [3, 0, 4]);
    assert_eq!(flat.support().expect("support"), vec![6, 8, 21, 23]);
}

#[test]
fn the_612_coordinate_complex_that_the_dense_bound_refused_now_assembles() {
    // 204 occurrences, 612 joint coordinates: the extent Issue #50 records as refused by
    // `DECLARED_ASSEMBLY_CEILING`. The ceiling is unchanged; the quantity checked against it is
    // the arithmetic the assembly performs.
    let (dimension, faces) = bar_network(204);
    assert_eq!(dimension, 612);
    let population = faces.len();
    let widest = faces.iter().map(ContactFace::slip_extent).max().unwrap_or(1);

    // The dense bound the previous assembly checked, stated here so the refusal is not a claim.
    let dense_bound = population * widest * dimension * dimension;
    assert!(
        dense_bound > DECLARED_ASSEMBLY_CEILING,
        "the dense bound is {dense_bound}, past the unchanged ceiling {DECLARED_ASSEMBLY_CEILING}"
    );
    // The pullback portion of the synthetic sparse work, against the same ceiling.
    // Production additionally charges D*J and the signature probes; their bounds are tested below.
    let sparse_bound: usize = faces
        .iter()
        .map(|face| {
            let support = face.support().expect("support").len();
            sparse_face_work(face.slip_extent(), support).expect("bounded sparse work")
        })
        .sum();
    assert!(
        sparse_bound <= DECLARED_ASSEMBLY_CEILING,
        "the arithmetic the assembly performs is {sparse_bound}"
    );
    assert!(dimension * dimension <= DECLARED_ASSEMBLY_CEILING);

    let assembled = ContactDissipation::assemble("synthetic-204-site-bars", dimension, faces)
        .expect("the synthetic 612-coordinate bar network assembles");
    assert_eq!(assembled.dimension(), 612);
    assert!(assembled.signature().is_positive_semidefinite());
    assert_eq!(assembled.signature().negative, 0);
    assert_eq!(
        assembled.signature().positive + assembled.signature().zero,
        612
    );
    // Above the congruence ceiling the signature names how it was obtained, and the minor that
    // certified the rank.
    match assembled.signature_scope() {
        SignatureScope::ConstructionAndCertifiedRank {
            minor_modulus,
            faces,
        } => {
            assert!(*minor_modulus >= holonics::prime_image_algebra::DECLARED_PRIME_FLOOR);
            assert_eq!(*faces, population);
        }
        other => panic!("above the congruence ceiling the scope is the constructed one: {other:?}"),
    }

    // And the reading a consumer asks for still comes out: the contact kernel is the motion that
    // slips on no face, and it contains the six rigid motions of a three-dimensional frame.
    assert!(assembled.signature().zero >= 6);
}

#[test]
fn sparse_work_charges_the_pulled_contraction_when_support_is_narrow() {
    // A response/slip extent of 1024 touching one coordinate performs m²s + ms² work while
    // forming D·J and Jᵀ·(D·J). The old support-only charge was only m·s² and understated it.
    let work = sparse_face_work(1024, 1).expect("the individual terms fit");
    assert_eq!(work, 1024usize * 1024 + 1024);
    assert!(work > 1024, "the pulled contraction must be charged");
}

#[test]
fn prime_image_refusal_keeps_its_specific_cause() {
    use holonics::prime_image_algebra::PrimeImageRefusal;

    let refusal = InteractionRefusal::from(PrimeImageRefusal::PrimeCeiling {
        consumed: 7,
        ceiling: 8,
    });
    assert!(matches!(refusal, InteractionRefusal::PrimeImage(_)));
    assert!(refusal.to_string().contains("prime charts"));
}

#[test]
fn a_dense_face_population_still_meets_the_unchanged_ceiling() {
    // A face that touches every coordinate of a wide chart is not made cheap by the sparse
    // accumulation, and the same ceiling refuses it.
    let dimension = 1024;
    let row: Vec<Rat> = (0..dimension).map(|at| int(at as i64 % 7 + 1)).collect();
    let face = ContactFace::declared(
        "dense".to_owned(),
        ExactRatMatrix::shaped(1, dimension, vec![row]).expect("a slip map"),
        SymmetricForm::from_rows(vec![vec![Rat::one()]]).expect("a unit response"),
        Rat::one(),
    )
    .expect("a declared dense face");
    // Each such face costs `1 · 1024²` — a sixty-fourth of the ceiling on its own — so
    // sixty-five of them exceed it, and the running sum refuses before the sixty-fifth is formed.
    let population = DECLARED_ASSEMBLY_CEILING / (dimension * dimension) + 1;
    let refusal =
        ContactDissipation::assemble("dense", dimension, vec![face; population])
            .expect_err("a genuinely dense population is refused, as it always was");
    assert!(
        matches!(refusal, InteractionRefusal::DeclarationAboveCeiling { .. }),
        "{refusal}"
    );
}

#[test]
fn a_form_whose_kernel_no_face_is_blind_to_is_refused_by_the_construction_clause() {
    // The clause `constructed_signature` owes: a motion in the kernel of the assembled form must
    // be one every face dissipates nothing under. Checked directly on the face, because building
    // an assembly whose accumulation is wrong is not something this module's constructor permits.
    let (dimension, faces) = bar_network(4);
    let assembled = ContactDissipation::assemble("small", dimension, faces.clone())
        .expect("assembled");
    let kernel = assembled
        .matrix()
        .expect("matrix")
        .kernel_basis()
        .expect("the contact kernel");
    assert!(!kernel.is_empty(), "a bar network has rigid motions");
    for motion in &kernel {
        for face in &faces {
            let support = face.support().expect("support");
            assert!(
                face.response_is_blind_to(motion, &support)
                    .expect("the clause evaluates"),
                "a kernel motion dissipates nothing at any face"
            );
        }
        assert!(
            assembled.power(motion).expect("power").is_zero(),
            "and the assembled power agrees"
        );
    }
    // A motion outside the kernel is one some face does see.
    let mut probe = vec![Rat::zero(); dimension];
    probe[0] = Rat::one();
    let seen = faces.iter().any(|face| {
        let support = face.support().expect("support");
        !face
            .response_is_blind_to(&probe, &support)
            .expect("the clause evaluates")
    });
    assert!(seen, "the clause can fail, which is what makes it a check");
}

/// **A doubled face is what the blindness clause cannot see, and the probe clause can.**
///
/// [counterexample] The Wave 10 reviewer proved the earlier claim wrong: for a sum of positive
/// semidefinite terms `ker M = ⋂_f ker(term_f)`, so accumulating one face twice repeats a kernel
/// that already contains the intersection. The kernel, the certified rank and the whole returned
/// signature are **identical** to the correct assembly's, and only the form itself is wrong. This
/// holds both halves of that statement at an extent above the congruence ceiling, where the
/// constructed signature is the one taken.
#[test]
fn a_doubled_face_leaves_the_signature_right_and_the_form_wrong() {
    let (dimension, faces) = bar_network(30);
    assert!(dimension > DECLARED_ASSEMBLY_CONGRUENCE_CEILING);
    let honest = ContactDissipation::assemble("honest", dimension, faces.clone())
        .expect("the honest assembly returns");

    let mut doubled_faces = faces.clone();
    doubled_faces.push(faces[0].clone());
    let doubled = ContactDissipation::assemble("doubled", dimension, doubled_faces)
        .expect("the doubled assembly also returns — it is a lawful declaration");

    // The signature cannot tell them apart, which is exactly why a second clause was owed.
    assert_eq!(honest.signature(), doubled.signature());
    assert_eq!(honest.signature().negative, 0);

    // The form can. This is the difference the probe clause reads.
    let honest_body = honest.matrix().expect("the honest body");
    let doubled_body = doubled.matrix().expect("the doubled body");
    let mut differs = false;
    for row in 0..dimension {
        for column in 0..dimension {
            if honest_body.get(row, column).expect("an entry")
                != doubled_body.get(row, column).expect("an entry")
            {
                differs = true;
            }
        }
    }
    assert!(
        differs,
        "a doubled face changes the body even though it moves no signature"
    );
}

/// **The assembly's defining identity is cross-examined, and a wrong body disagrees with it.**
///
/// The probe clause reads `Σ_f w_f ⟨J_f v, D_f J_f v⟩` from the faces and `⟨v, M v⟩` from the
/// assembled body, so a scaled or double-counted accumulation is caught at the first probe that
/// does not vanish on it. Here the body is corrupted directly, which is the failure mode the
/// congruence used to catch below the ceiling.
#[test]
fn a_body_that_does_not_carry_its_faces_disagrees_at_a_declared_probe() {
    let (dimension, faces) = bar_network(30);
    let honest = ContactDissipation::assemble("honest", dimension, faces)
        .expect("the honest assembly returns");

    let honest_body = honest.matrix().expect("the honest body");
    let probe: Vec<Rat> = (0..dimension)
        .map(|slot| int(i64::try_from((slot * 7) % 11).unwrap_or(0) - 5))
        .collect();
    let mut through_the_body = Rat::zero();
    for row in 0..dimension {
        for column in 0..dimension {
            through_the_body +=
                &probe[row] * honest_body.get(row, column).expect("an entry") * &probe[column];
        }
    }
    assert!(
        through_the_body.is_positive(),
        "the declared probe is not blind to this network, so a scaling of the body moves it"
    );
    // A uniformly scaled body reads a different power under the same probe while the faces do not
    // move at all: that difference is what `constructed_signature`'s second clause refuses.
    assert_ne!(&through_the_body * int(2), through_the_body);
}

// =============================================================================================
// the interaction as a core Holon (plan phase 3)
// =============================================================================================

mod core_holon {
    use holonics::conformance::{
        check_exact_advance, check_interaction, check_restriction, check_run, check_tellegen,
    };
    use holonics::holon::{HolonError, HolonState};
    use holonics::law::{HolonLaw, Scheme};
    use holonics::restriction::PortMap;

    use super::*;

    fn dissipative_chain() -> HolonicInteraction {
        two_medium_chain().modulated().expect("the modulated unit")
    }

    /// `Holon/Conformance.lean::medium_admits` and `ssm_port_output`: the core Holon admits the
    /// interaction's own port-Hamiltonian motion `q̇ = (Ω − M)Gq + Bu`, and its point balance is
    /// the storage-rate reading's and the contact form's, number for number.
    #[test]
    fn the_interaction_holon_admits_its_own_motion_and_the_readings_are_its_balance() {
        for unit in [two_medium_chain(), dissipative_chain()] {
            let holon = unit.holon().expect("a core Holon");
            check_tellegen(holon.port_holon().dirac()).expect("a Dirac structure");
            assert_eq!(holon.ports().expect("named ports").len(), 4 + 1 + 1);
            let q = vector(&[1, -2, 3, 1]);
            let effort = form_matrix(&unit.joint_storage().unwrap())
                .unwrap()
                .apply(&q)
                .unwrap();
            let point = unit.power_balance_at(&q, &vector(&[2])).expect("admitted");
            assert!(point.residual().is_zero());
            assert_eq!(
                point.dissipated,
                unit.joint_dissipation().unwrap().power(&effort).unwrap()
            );

            // The storage-rate reading at `u = 0` is the core point balance.
            let rest = unit.power_balance_at(&q, &vector(&[0])).expect("admitted");
            let reading = unit.storage_rate().unwrap();
            let balance = reading.energy_balance_at(&q).unwrap();
            assert!(balance.is_exact());
            assert_eq!(balance.stored_change, rest.storage_rate);
            assert_eq!(balance.stored_change, reading.rate_at(&q).unwrap() / int(2));
            assert_eq!(balance.dissipated, rest.dissipated);
        }
    }

    /// `ClockedEnergy` is the core resistive dissipation over its clock: `⟨δq, Mδq⟩/h = h⟨v, Rv⟩`.
    #[test]
    fn the_clocked_energy_is_the_core_resistive_dissipation_over_its_clock() {
        let dissipation = definite_contact();
        let resistive = dissipation.resistive_relation().unwrap();
        let edit = vector(&[1, -3]);
        for duration in [int(1), rat(1, 2), int(3)] {
            let clock =
                Clock::declared("test|clock", duration.clone(), "declared-energy-unit").unwrap();
            let energy = dissipation.clocked_energy(&edit, &clock).unwrap();
            let balance = energy.energy_balance();
            assert!(balance.is_exact());
            assert_eq!(&balance.dissipated, energy.energy());
            let velocity: Vec<Rat> = edit.iter().map(|value| value / &duration).collect();
            assert_eq!(
                balance.dissipated,
                &duration * resistive.dissipation(&velocity).unwrap()
            );
        }
    }

    /// The exact law: one midpoint word is `q⁺ − q = h((Ω − M)G q̄ + B u)`, and the generic core
    /// conformance checks pass against it.
    #[test]
    fn the_interaction_law_passes_the_core_conformance_checks() {
        let unit = dissipative_chain();
        let step = rat(1, 2);
        let law = unit.law(step.clone(), Scheme::Midpoint).unwrap();
        let state = HolonState::new(vector(&[1, 0, -1, 2]));
        let input = vector(&[3]);
        let advance = check_exact_advance(&law, &state, &input).unwrap();
        let midpoint: Vec<Rat> = state
            .configuration
            .iter()
            .zip(&advance.state.configuration)
            .map(|(a, b)| (a + b) / int(2))
            .collect();
        let rate: Vec<Rat> = unit
            .generator()
            .unwrap()
            .apply(&midpoint)
            .unwrap()
            .iter()
            .zip(unit.excitation().unwrap().apply(&input).unwrap())
            .map(|(a, b)| a + b)
            .collect();
        for ((after, before), rate) in advance
            .state
            .configuration
            .iter()
            .zip(&state.configuration)
            .zip(&rate)
        {
            assert_eq!((after - before) / &step, *rate);
        }
        assert!(advance.balance.dissipated > Rat::zero());

        let (_, total) = check_run(&law, &state, &input, 3).unwrap();
        assert!(total.is_exact());
        let (joined, _) = check_interaction(
            &law,
            &law,
            &[(0, 0)],
            &state.configuration,
            &vector(&[0, 1, 0, 0]),
            &[],
        )
        .unwrap();
        assert_eq!(joined.holon().port_holon().counts().storage, 8);
        let ports = law.holon().port_holon().counts().total();
        let identity = PortMap::new(ExactRatMatrix::identity(ports).unwrap());
        let flow: Vec<Rat> = (0..ports as i64).map(int).collect();
        check_restriction(&law, &identity, &flow, &flow).unwrap();
    }

    /// The standing perspective is a passive coholon: its reader draws zero power and reads
    /// `C_R q` through the storage effort.
    #[test]
    fn the_perspective_is_a_passive_coholons_reading() {
        let unit = dissipative_chain();
        let law = unit.law(int(1), Scheme::Midpoint).unwrap();
        let state = HolonState::new(vector(&[2, -1, 5, 3]));
        let reading = law
            .receive(&state, &unit.perspective_reader().unwrap())
            .unwrap();
        assert!(reading.power.is_zero());
        assert_eq!(
            reading.value,
            unit.readout().unwrap().apply(&state.configuration).unwrap()
        );
    }

    fn participating_unit() -> HolonicInteraction {
        let body = ReceiverBody::declared(
            "test|participating|body",
            form(&[&[1, 0], &[0, 2]]),
            matrix(&[&[0, 1], &[-1, 0]]),
        )
        .unwrap();
        let coupling = Coupling::declared(
            "test|participating|coupling",
            Carrier::Medium(0),
            Carrier::Perspective,
            matrix(&[&[0, 1], &[2, 0]]),
        )
        .unwrap();
        let medium = Medium::declared(
            "test|participating|medium",
            form(&[&[1, 0], &[0, 1]]),
            matrix(&[&[0, 1], &[-1, 0]]),
            vec![
                ContactFace::declared(
                    "test|participating|face",
                    matrix(&[&[1, -1]]),
                    form(&[&[1]]),
                    int(1),
                )
                .unwrap(),
            ],
        )
        .unwrap();
        HolonicInteraction::declared(
            "test|participating",
            SourceCurrent::declared(
                "test|participating|source",
                Carrier::Medium(0),
                matrix(&[&[0], &[1]]),
                vec!["drive".to_owned()],
            )
            .unwrap(),
            vec![medium],
            Vec::new(),
            vec![coupling],
            None,
            Perspective::participating(
                "test|participating|perspective",
                matrix(&[&[1, 0]]),
                vec!["receiver-displacement".to_owned()],
                body,
            )
            .unwrap(),
        )
        .unwrap()
    }

    /// The participating receiver is its own Holon joined at gyrating link ports, and the joined
    /// Holon is the interaction's: the same Dirac subspace, storage and resistance.
    #[test]
    fn the_participating_receiver_is_a_holon_joined_at_its_link_ports() {
        let unit = participating_unit();
        let whole = unit.holon().unwrap();
        let receiver = unit
            .receiver_holon()
            .unwrap()
            .expect("a participating body");
        check_tellegen(receiver.port_holon().dirac()).unwrap();
        let joined = unit.joined_holon().unwrap();
        assert!(
            joined
                .port_holon()
                .dirac()
                .same_subspace(whole.port_holon().dirac())
        );
        assert_eq!(joined.port_holon().counts(), whole.port_holon().counts());
        assert_eq!(joined.port_holon().storage(), whole.port_holon().storage());
        assert_eq!(
            joined.port_holon().resistance(),
            whole.port_holon().resistance()
        );

        // A standing perspective has no body to join.
        assert!(matches!(
            two_medium_chain().joined_holon(),
            Err(InteractionRefusal::Holon(HolonError::Unsupported { .. }))
        ));
    }

    /// `Holon/Deposition.lean::commit_balance`: a storage perturbation commits as deposition work
    /// and the balance closes exactly; a face perturbation deposits nothing.
    #[test]
    fn a_perturbation_commits_its_storage_change_as_deposition_work() {
        let unit = HolonicInteraction::declared(
            "test|perturbed",
            SourceCurrent::declared(
                "test|perturbed|source",
                Carrier::Medium(0),
                matrix(&[&[1], &[0]]),
                vec!["drive".to_owned()],
            )
            .unwrap(),
            vec![oscillator("test|perturbed|medium", 1)],
            Vec::new(),
            Vec::new(),
            Some(Perturbation::Storage {
                medium: 0,
                storage: form(&[&[9, 0], &[0, 1]]),
            }),
            Perspective::standing(
                "test|perturbed|perspective",
                Carrier::Medium(0),
                matrix(&[&[1, 0]]),
                vec!["displacement".to_owned()],
            )
            .unwrap(),
        )
        .unwrap();
        assert_eq!(
            unit.perturbation_deposition_work(&vector(&[1, 5])).unwrap(),
            int(4)
        );
        let state = HolonState::new(vector(&[1, 2]));
        let (advance, next) = unit
            .perturbed_commit(rat(1, 3), Scheme::Midpoint, &state, &vector(&[1]))
            .unwrap();
        assert!(advance.balance.is_exact());
        assert_eq!(
            advance.balance.deposition_work,
            unit.perturbation_deposition_work(&advance.state.configuration)
                .unwrap()
        );
        assert_eq!(
            next.holon().port_holon().storage(),
            &unit.modulated().unwrap().joint_storage().unwrap()
        );
        assert!(
            two_medium_chain()
                .perturbation_deposition_work(&vector(&[1, 2, 3, 4]))
                .unwrap()
                .is_zero()
        );
    }
}

// ---------------------------------------------------------------------------------------------
// one clock: the declaration over the core clock
// ---------------------------------------------------------------------------------------------

/// The declared clock is the core clock with lineage and unit attached; its wire is byte-identical
/// to the former derived `{lineage, duration, unit}` shape, and a ticked core clock is refused.
#[test]
fn the_declared_clock_is_the_core_clock_with_an_unchanged_wire() {
    #[derive(serde::Serialize)]
    #[serde(rename = "Clock")]
    struct FormerClock {
        lineage: String,
        duration: Rat,
        unit: String,
    }
    let clock = Clock::declared("test|clock|wire", rat(3, 7), "declared-energy-unit").unwrap();
    let former = FormerClock {
        lineage: "test|clock|wire".to_owned(),
        duration: rat(3, 7),
        unit: "declared-energy-unit".to_owned(),
    };
    assert_eq!(
        serde_json::to_vec(&clock).unwrap(),
        serde_json::to_vec(&former).unwrap()
    );
    assert_eq!(
        serde_json::to_vec_pretty(&clock).unwrap(),
        serde_json::to_vec_pretty(&former).unwrap()
    );
    // The core chart: step h, no ring, at rest.
    assert_eq!(clock.core().step(), &rat(3, 7));
    assert!(clock.core().radices().is_empty() && clock.core().is_at_rest());
    assert_eq!(
        Clock::from_core(
            "test|clock|wire",
            clock.core().clone(),
            "declared-energy-unit"
        )
        .unwrap(),
        clock
    );
    let ring = clock.on_ring(vec![5u32.into()]).unwrap();
    assert_eq!(ring.step(), clock.duration());
    assert!(matches!(
        Clock::from_core("test|clock|wire", ring, "unit"),
        Err(InteractionRefusal::ClockNotDeclarable { levels: 1, .. })
    ));
    let mut ticked = clock.core().clone();
    ticked.advance(&2u32.into());
    assert!(matches!(
        Clock::from_core("test|clock|wire", ticked, "unit"),
        Err(InteractionRefusal::ClockNotDeclarable { levels: 0, .. })
    ));
}
