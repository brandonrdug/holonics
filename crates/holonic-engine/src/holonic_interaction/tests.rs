//! Tests for the Holonic Interaction unit: media, contact exchange, the derived modal response
//! and the interface between two media. Every value is exact; no float decides anything.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;

use super::*;
use crate::causal_chord::PoleReading;
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
