use super::*;
use holonics::geometry::{RatVec3, ScrewGenerator, SituatedScrew};

fn int(value: i64) -> Rat {
    Rat::from_integer(value.into())
}

fn pair() -> ScrewPair {
    ScrewPair::new(
        SituatedScrew::new(
            ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
            RatVec3::from_i64(1, 0, 0),
        ),
        SituatedScrew::new(
            ScrewGenerator::new(RatVec3::zero(), RatVec3::zero()),
            RatVec3::from_i64(0, 0, 0),
        ),
    )
}

fn adapter() -> HelicalPairInteraction {
    HelicalPairInteraction::declared(
        "test|pair",
        pair(),
        ExactRatMatrix::identity(2).unwrap(),
        SymmetricForm::from_diagonal(vec![int(1), int(1), int(1)]),
        int(2),
        Clock::declared("test|clock", int(1), "joule").unwrap(),
        PairUnits::declared("frame-xyz", ["s".into(), "t".into()]),
    )
    .unwrap()
}

#[test]
fn public_adapter_returns_checked_interaction_and_c_j_d_j_c() {
    let adapter = adapter();
    assert_eq!(adapter.pair_slip().rows(), 3);
    assert_eq!(adapter.pair_slip().columns(), 2);
    assert_eq!(adapter.effective_slip(), adapter.pair_slip());
    assert_eq!(adapter.interaction().contacts().len(), 1);
    let contact = adapter.interaction().contacts()[0].face();
    assert_eq!(contact.slip(), adapter.effective_slip());
    let dissipation = adapter.contact_dissipation().unwrap();
    assert_eq!(dissipation.power(&[int(2), int(3)]).unwrap(), int(8));
}

#[test]
fn feature_pullback_keeps_delta_quadrance_and_gradient_terms() {
    let adapter = adapter();
    let covector = PairFeatureCovector::new([int(0), int(1), int(0)], int(1), [int(1), int(0)]);
    let returned = adapter.feature_pullback(&covector);
    // Jᵀ λ_delta = (1,0), while DQ and the geometric Hessian both vanish here: the
    // rotational acceleration cancels the Gram term at this radius-one configuration.
    assert_eq!(returned, [int(1), int(0)]);
}

#[test]
fn feature_pullback_retains_nonzero_gradient_and_geometric_hessian_terms() {
    let translating_pair = ScrewPair::new(
        SituatedScrew::new(
            ScrewGenerator::new(RatVec3::zero(), RatVec3::from_i64(1, 0, 0)),
            RatVec3::from_i64(1, 0, 0),
        ),
        SituatedScrew::new(
            ScrewGenerator::new(RatVec3::zero(), RatVec3::zero()),
            RatVec3::zero(),
        ),
    );
    let adapter = HelicalPairInteraction::declared(
        "test|feature-translation",
        translating_pair,
        ExactRatMatrix::identity(2).unwrap(),
        SymmetricForm::from_diagonal(vec![int(1), int(1), int(1)]),
        int(1),
        Clock::declared("test|clock", int(1), "joule").unwrap(),
        PairUnits::declared("frame-xyz", ["s".into(), "t".into()]),
    )
    .unwrap();
    let covector = PairFeatureCovector::new([int(1), int(0), int(0)], int(3), [int(4), int(0)]);
    // Jᵀλ_delta=(1,0), λ_Q DQ=(6,0), and Hᵀλ_DQ=(8,0).
    assert_eq!(adapter.feature_pullback(&covector), [int(15), int(0)]);
}

#[test]
fn material_and_kinematic_kernels_are_separate_readings() {
    let adapter = adapter();
    assert_eq!(
        adapter.material_kernel().unwrap(),
        adapter.no_slip_kernel().unwrap()
    );
    assert!(adapter.material_is_definite());
    assert!(matches!(
        adapter.lock_reading(1.into(), 1.into()),
        PairLockReading::NotLocked
    ));
}

#[test]
fn an_ambient_port_requires_and_honours_an_explicit_block_split() {
    let port = ExactRatMatrix::shaped(
        2,
        3,
        vec![vec![int(1), int(0), int(0)], vec![int(0), int(1), int(0)]],
    )
    .unwrap();
    let error = HelicalPairInteraction::declared(
        "test|ambient",
        pair(),
        port.clone(),
        SymmetricForm::from_diagonal(vec![int(1), int(1), int(1)]),
        int(1),
        Clock::declared("test|clock", int(1), "joule").unwrap(),
        PairUnits::declared("frame-xyz", ["s".into(), "t".into()]),
    )
    .unwrap_err();
    assert!(matches!(
        error,
        HelicalRefusal::AmbientSplitRequired { columns: 3 }
    ));

    let adapter = HelicalPairInteraction::declared_with_blocks(
        "test|ambient",
        pair(),
        port,
        1,
        2,
        SymmetricForm::from_diagonal(vec![int(1), int(1), int(1)]),
        int(1),
        Clock::declared("test|clock", int(1), "joule").unwrap(),
        PairUnits::declared("frame-xyz", ["s".into(), "t".into()]),
    )
    .unwrap();
    assert_eq!(adapter.interaction().joint_dimension(), 3);
    assert_eq!(adapter.effective_slip().columns(), 3);
}

#[test]
fn material_null_is_checked_on_attainable_slips() {
    let on_attainable = HelicalPairInteraction::declared(
        "test|singular-attainable",
        pair(),
        ExactRatMatrix::identity(2).unwrap(),
        SymmetricForm::from_diagonal(vec![int(0), int(1), int(1)]),
        int(1),
        Clock::declared("test|clock", int(1), "joule").unwrap(),
        PairUnits::declared("frame-xyz", ["s".into(), "t".into()]),
    )
    .unwrap();
    assert!(!on_attainable.material_is_definite());
    assert!(on_attainable.material_power_implies_no_slip().unwrap());

    let blind = HelicalPairInteraction::declared(
        "test|singular-blind",
        pair(),
        ExactRatMatrix::identity(2).unwrap(),
        SymmetricForm::from_diagonal(vec![int(1), int(0), int(0)]),
        int(1),
        Clock::declared("test|clock", int(1), "joule").unwrap(),
        PairUnits::declared("frame-xyz", ["s".into(), "t".into()]),
    )
    .unwrap();
    assert!(!blind.material_power_implies_no_slip().unwrap());
    assert_ne!(
        blind.material_kernel().unwrap(),
        blind.no_slip_kernel().unwrap()
    );
}

/// `Holon/Conformance.lean::pairContact_resistive`: the pair contact is a core resistive element on
/// relative slip, its bond power is minus the existing contact form, and the pair unit is a core
/// Holon whose words close exactly.
#[test]
fn the_pair_contact_is_a_core_resistive_element_on_relative_slip() {
    use holonics::conformance::{check_exact_advance, check_tellegen};
    use holonics::holon::HolonState;
    use holonics::law::Scheme;

    let adapter = adapter();
    let element = adapter.contact_element().unwrap();
    assert_eq!(element.inertia().negative, 0);
    for motion in [[int(2), int(3)], [int(-1), int(4)], [int(0), int(0)]] {
        let bond = adapter.contact_bond(&motion).unwrap();
        let contact_form = adapter
            .contact_dissipation()
            .unwrap()
            .power(&motion)
            .unwrap();
        assert_eq!(bond.power(), -contact_form.clone());
        assert_eq!(element.dissipation(bond.flow()).unwrap(), contact_form);
        assert_eq!(
            bond.flow(),
            adapter.effective_slip().apply(&motion).unwrap()
        );
    }

    let holon = adapter.interaction().holon().unwrap();
    check_tellegen(holon.port_holon().dirac()).unwrap();
    assert_eq!(holon.port_holon().counts().resistive, 3);
    assert_eq!(holon.port_holon().resistance(), &element);
    let law = adapter
        .interaction()
        .law(Rat::new(1.into(), 2.into()), Scheme::Midpoint)
        .unwrap();
    let advance =
        check_exact_advance(&law, &HolonState::new(vec![int(1), int(-2)]), &[int(1)]).unwrap();
    assert!(advance.balance.dissipated > Rat::zero());
}
