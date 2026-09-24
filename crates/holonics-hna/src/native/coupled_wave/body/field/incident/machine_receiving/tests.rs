use super::*;
use num_bigint::BigInt;
use holonics::geometry::{AffineMap3, Rat, RatVec3, cayley_rotation_z};

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn clock() -> ClockSpec {
    ClockSpec {
        lineage: "receiving-clock".into(),
        duration: rat(1),
        unit: "s".into(),
    }
}

#[test]
fn signed_translation_and_cayley_powers_are_exact_and_checked() {
    let translation = AffineMap3 {
        linear: holonics::geometry::RatMat3::identity(),
        translation: RatVec3::from_i64(1, 0, 0),
    };
    assert_eq!(
        signed_affine_power(&translation, -2).unwrap().translation,
        RatVec3::from_i64(-2, 0, 0)
    );
    assert_eq!(
        signed_affine_power(&AffineMap3::identity(), i64::MIN).unwrap(),
        AffineMap3::identity()
    );
    let cayley = AffineMap3 {
        linear: cayley_rotation_z(&(rat(1) / rat(2))),
        translation: RatVec3::zero(),
    };
    let forward = signed_affine_power(&cayley, 2).unwrap();
    let round_trip = forward.followed_by(&signed_affine_power(&forward, -1).unwrap());
    assert_eq!(round_trip, AffineMap3::identity());
}

#[test]
fn invalid_binding_rejects_missing_ports_and_nonpositive_clock() {
    let binding = GeneratorPhaseReceiverBinding {
        receiver_id: "boundary-receiver".into(),
        ports: vec![],
        clock: ClockSpec {
            lineage: "receiving-clock".into(),
            duration: rat(0),
            unit: "s".into(),
        },
        aperture: 0,
        termination_receiver_id: "boundary-termination".into(),
    };
    assert!(binding.validate().is_err());
}

#[test]
fn phase_binding_wire_roundtrips() {
    let binding = GeneratorPhaseReceiverBinding {
        receiver_id: "text".into(),
        termination_receiver_id: "stop".into(),
        ports: vec![GeneratorPhasePort {
            site_id: "b".into(),
            origin_exponent: -1,
            step_exponent: 2,
        }],
        clock: clock(),
        aperture: 3,
    };
    let wire = serde_json::to_value(&binding).unwrap();
    assert_eq!(
        serde_json::from_value::<GeneratorPhaseReceiverBinding>(wire).unwrap(),
        binding
    );
}
