use super::*;
use num_traits::Zero;
use relational_geometry::{HingeAxis, rat};

#[test]
fn cayley_generator_uses_half_angle_differential_and_pivot_arm() {
    let motion = JointMotion::revolute(
        HingeAxis::Z,
        RatVec3::from_i64(1, 0, 0),
        rat(1, 2),
        rat(3, 1),
    );
    let generator = motion.parameter_generator();
    assert_eq!(
        generator.angular(),
        &RatVec3::new(rat(0, 1), rat(0, 1), rat(8, 5))
    );
    assert_eq!(
        generator.advance(),
        &RatVec3::new(rat(0, 1), rat(-8, 5), rat(0, 1))
    );
    assert_eq!(motion.clock_generator().angular().z, rat(24, 5));
    assert_eq!(
        motion.finite_map().linear,
        HingeAxis::Z.rotation(&rat(1, 2))
    );
}

#[test]
fn ordered_product_and_recharted_columns_are_exact() {
    let first_motion = JointMotion::revolute(HingeAxis::Z, RatVec3::zero(), rat(1, 1), Rat::one());
    let first = SerialJoint::new(
        SituatedScrew::new(
            first_motion.parameter_generator(),
            RatVec3::from_i64(1, 0, 0),
        ),
        first_motion.clone(),
        Some(JointLimit::new(rat(0, 1), rat(2, 1)).unwrap()),
    )
    .unwrap();
    let second_motion = JointMotion::prismatic(RatVec3::from_i64(1, 0, 0), rat(2, 1), Rat::one());
    let second = SerialJoint::new(
        SituatedScrew::new(
            second_motion.parameter_generator(),
            RatVec3::from_i64(0, 0, 0),
        ),
        second_motion,
        None,
    )
    .unwrap();
    let chain = SerialChain::new(AffineMap3::identity(), vec![first, second]).unwrap();
    assert_eq!(chain.link_transforms().len(), 2);
    assert_eq!(
        chain.endpoint().apply(&RatVec3::zero()),
        RatVec3::from_i64(0, 2, 0)
    );
    let columns = chain.spatial_jacobian().unwrap();
    assert_eq!(columns[0].angular(), &RatVec3::from_i64(0, 0, 1));
    assert_eq!(columns[1].advance(), &RatVec3::from_i64(0, 1, 0));
}

#[test]
fn contact_row_and_pullback_preserve_orientation() {
    let motion = JointMotion::prismatic(RatVec3::from_i64(1, 0, 0), Rat::zero(), Rat::one());
    let joint = SerialJoint::new(
        SituatedScrew::new(motion.parameter_generator(), RatVec3::zero()),
        motion,
        None,
    )
    .unwrap();
    let second_motion = JointMotion::prismatic(RatVec3::from_i64(1, 0, 0), Rat::zero(), Rat::one());
    let second = SerialJoint::new(
        SituatedScrew::new(second_motion.parameter_generator(), RatVec3::zero()),
        second_motion,
        None,
    )
    .unwrap();
    let chain = SerialChain::new(AffineMap3::identity(), vec![joint, second]).unwrap();
    let jacobian = chain
        .contact_jacobian(&LinkContact {
            first_link: 0,
            second_link: 1,
            first_point: RatVec3::zero(),
            second_point: RatVec3::from_i64(0, 1, 0),
            orientation: RatVec3::from_i64(1, 0, 0),
        })
        .unwrap();
    assert_eq!(jacobian.row, vec![Rat::zero(), rat(-1, 1)]);
    assert_eq!(jacobian.pullback(&rat(3, 1)), vec![Rat::zero(), rat(-3, 1)]);
    assert_eq!(
        jacobian.pullback_force(&RatVec3::from_i64(2, 0, 0)),
        vec![Rat::zero(), rat(-2, 1)]
    );
}

#[test]
fn closure_control_retains_plural_and_null_fibres() {
    let motion = JointMotion::prismatic(RatVec3::from_i64(1, 0, 0), Rat::zero(), Rat::one());
    let joint = SerialJoint::new(
        SituatedScrew::new(motion.parameter_generator(), RatVec3::zero()),
        motion,
        None,
    )
    .unwrap();
    let chain = SerialChain::new(AffineMap3::identity(), vec![joint]).unwrap();
    let endpoint = chain.endpoint();
    let candidate = ClosureCandidate {
        parameters: vec![Rat::zero()],
    };
    assert!(matches!(
        chain
            .closure_control(endpoint.clone(), vec![candidate.clone()])
            .unwrap(),
        ClosureFamily::Unique { .. }
    ));
    assert!(matches!(
        chain
            .closure_control(endpoint.clone(), vec![candidate.clone(), candidate])
            .unwrap(),
        ClosureFamily::Plural { .. }
    ));
    assert!(matches!(
        chain
            .closure_control(AffineMap3::identity(), Vec::new())
            .unwrap(),
        ClosureFamily::Null { .. }
    ));
}

#[test]
fn prismatic_endpoint_fibre_keeps_exact_kernel() {
    let first_motion = JointMotion::prismatic(RatVec3::from_i64(1, 0, 0), Rat::zero(), Rat::one());
    let second_motion = JointMotion::prismatic(RatVec3::from_i64(1, 0, 0), Rat::zero(), Rat::one());
    let first = SerialJoint::new(
        SituatedScrew::new(first_motion.parameter_generator(), RatVec3::zero()),
        first_motion,
        Some(JointLimit::new(rat(0, 1), rat(1, 1)).unwrap()),
    )
    .unwrap();
    let second = SerialJoint::new(
        SituatedScrew::new(second_motion.parameter_generator(), RatVec3::zero()),
        second_motion,
        Some(JointLimit::new(rat(0, 1), rat(1, 1)).unwrap()),
    )
    .unwrap();
    let chain = SerialChain::new(AffineMap3::identity(), vec![first, second]).unwrap();
    let target = AffineMap3 {
        linear: relational_geometry::RatMat3::identity(),
        translation: RatVec3::from_i64(3, 0, 0),
    };
    let fibre = match chain.prismatic_endpoint_fibre(&target).unwrap() {
        PrismaticEndpointInference::Fibre(fibre) => fibre,
        other => panic!("expected prismatic fibre, got {other:?}"),
    };
    assert_eq!(fibre.particular().iter().sum::<Rat>(), rat(3, 1));
    assert_eq!(fibre.kernel().len(), 1);
    assert!(!fibre.admits(fibre.particular()));
    assert!(!fibre.admits(&[rat(0, 1), rat(0, 1)]));
}

#[test]
fn noncommuting_endpoint_difference_matches_parameter_column() {
    let first_motion = JointMotion::revolute(HingeAxis::Z, RatVec3::zero(), rat(1, 2), Rat::zero());
    let second_motion = JointMotion::prismatic(RatVec3::from_i64(1, 0, 0), rat(1, 1), Rat::zero());
    let first = SerialJoint::new(
        SituatedScrew::new(first_motion.parameter_generator(), RatVec3::zero()),
        first_motion,
        None,
    )
    .unwrap();
    let second = SerialJoint::new(
        SituatedScrew::new(second_motion.parameter_generator(), RatVec3::zero()),
        second_motion,
        None,
    )
    .unwrap();
    let chain = SerialChain::new(AffineMap3::identity(), vec![first, second]).unwrap();
    let plus = chain
        .endpoint_for_parameters(&[rat(1, 2), rat(8, 7)])
        .unwrap();
    let minus = chain
        .endpoint_for_parameters(&[rat(1, 2), rat(6, 7)])
        .unwrap();
    let derivative = plus
        .translation
        .subtract(&minus.translation)
        .scale(&rat(7, 2));
    assert_eq!(
        derivative,
        chain.spatial_jacobian().unwrap()[1].advance().clone()
    );
}

#[test]
fn clock_rate_changes_velocity_columns_without_changing_parameter_columns() {
    let zero_rate = JointMotion::prismatic(RatVec3::from_i64(0, 1, 0), Rat::zero(), Rat::zero());
    let fast_rate = JointMotion::prismatic(RatVec3::from_i64(0, 1, 0), Rat::zero(), rat(2, 1));
    let zero_joint = SerialJoint::new(
        SituatedScrew::new(zero_rate.parameter_generator(), RatVec3::zero()),
        zero_rate,
        None,
    )
    .unwrap();
    let fast_joint = SerialJoint::new(
        SituatedScrew::new(fast_rate.parameter_generator(), RatVec3::zero()),
        fast_rate,
        None,
    )
    .unwrap();
    let zero_chain = SerialChain::new(AffineMap3::identity(), vec![zero_joint]).unwrap();
    let fast_chain = SerialChain::new(AffineMap3::identity(), vec![fast_joint]).unwrap();
    assert_eq!(
        zero_chain.spatial_jacobian().unwrap(),
        fast_chain.spatial_jacobian().unwrap()
    );
    assert_eq!(
        fast_chain.spatial_velocity_jacobian().unwrap()[0].advance(),
        &RatVec3::from_i64(0, 2, 0)
    );
}

#[test]
fn contact_face_keeps_cross_joint_quadratic_terms() {
    let contact = LinkContact {
        first_link: 0,
        second_link: 1,
        first_point: RatVec3::zero(),
        second_point: RatVec3::zero(),
        orientation: RatVec3::from_i64(1, 0, 0),
    };
    let jacobian = LinkContactJacobian {
        contact,
        first_link: 0,
        second_link: 1,
        orientation: RatVec3::from_i64(1, 0, 0),
        velocity_columns: vec![RatVec3::from_i64(1, 0, 0), RatVec3::from_i64(1, 0, 0)],
        row: vec![Rat::one(), Rat::one()],
    };
    let response = SymmetricForm::from_rows(vec![
        vec![Rat::one(), Rat::zero(), Rat::zero()],
        vec![Rat::zero(), Rat::one(), Rat::zero()],
        vec![Rat::zero(), Rat::zero(), Rat::one()],
    ])
    .unwrap();
    let face = jacobian
        .contact_face("serial-cross-joint", response, Rat::one())
        .unwrap();
    assert_eq!(face.power(&[Rat::one(), Rat::one()]).unwrap(), rat(4, 1));
    let form = face.face_form().unwrap();
    assert_eq!(form.get(0, 1).unwrap(), &Rat::one());
}

#[test]
fn chain_derived_face_retains_common_joint_cancellation_and_cross_terms() {
    let joints = (0..3)
        .map(|_| {
            let motion =
                JointMotion::prismatic(RatVec3::from_i64(1, 0, 0), Rat::zero(), Rat::one());
            SerialJoint::new(
                SituatedScrew::new(motion.parameter_generator(), RatVec3::zero()),
                motion,
                None,
            )
            .unwrap()
        })
        .collect();
    let chain = SerialChain::new(AffineMap3::identity(), joints).unwrap();
    let jacobian = chain
        .contact_jacobian(&LinkContact {
            first_link: 0,
            second_link: 2,
            first_point: RatVec3::zero(),
            second_point: RatVec3::zero(),
            orientation: RatVec3::from_i64(1, 0, 0),
        })
        .unwrap();
    let face = jacobian
        .contact_face(
            "chain-pair",
            SymmetricForm::from_diagonal(vec![Rat::one(); 3]),
            Rat::one(),
        )
        .unwrap();
    assert_eq!(
        face.power(&[rat(7, 1), Rat::one(), Rat::one()]).unwrap(),
        rat(4, 1)
    );
    assert_eq!(face.face_form().unwrap().get(1, 2).unwrap(), &Rat::one());
    assert_eq!(
        face.power(&[rat(7, 1), Rat::one(), rat(-1, 1)]).unwrap(),
        Rat::zero()
    );
}

#[test]
fn cayley_secant_remainder_matches_the_instantaneous_serial_column() {
    let t = rat(1, 2);
    let h = rat(1, 7);
    let revolute = JointMotion::revolute(HingeAxis::Z, RatVec3::zero(), t.clone(), Rat::zero());
    let prismatic = JointMotion::prismatic(RatVec3::from_i64(1, 0, 0), Rat::one(), Rat::zero());
    let joints = [revolute, prismatic]
        .into_iter()
        .map(|motion| {
            SerialJoint::new(
                SituatedScrew::new(motion.parameter_generator(), RatVec3::zero()),
                motion,
                None,
            )
            .unwrap()
        })
        .collect();
    let chain = SerialChain::new(AffineMap3::identity(), joints).unwrap();
    let plus = chain
        .endpoint_for_parameters(&[&t + &h, Rat::one()])
        .unwrap()
        .translation;
    let minus = chain
        .endpoint_for_parameters(&[&t - &h, Rat::one()])
        .unwrap()
        .translation;
    let secant = plus
        .subtract(&minus)
        .scale(&(Rat::one() / (rat(2, 1) * &h)));
    let a = Rat::one() + (&t + &h) * (&t + &h);
    let b = Rat::one() + (&t - &h) * (&t - &h);
    let base = Rat::one() + &t * &t;
    let denominator = &base * &base;
    // Exact rational secant identity: after putting over the derivative's denominator,
    // the only remainder is the displayed 2h² term. No floating epsilon is used.
    let corrected = secant
        .scale(&(a * b / &denominator))
        .subtract(&RatVec3::new(
            Rat::zero(),
            rat(2, 1) * &h * &h / &denominator,
            Rat::zero(),
        ));
    assert_eq!(
        corrected,
        chain.spatial_jacobian().unwrap()[0].velocity(&chain.endpoint().translation)
    );
}
