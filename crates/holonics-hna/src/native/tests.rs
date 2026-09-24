use super::*;

#[test]
fn exact_wire_has_no_json_number_or_float_loss() {
    let rational = RationalWire {
        numerator: "9007199254740993".into(),
        denominator: "7".into(),
    };
    let bytes = serde_json::to_vec(&rational).unwrap();
    assert!(std::str::from_utf8(&bytes)
        .unwrap()
        .contains("\"9007199254740993\""));
    let decoded: RationalWire = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(decoded.rational().unwrap(), rational.rational().unwrap());
    let current = CurrentWire {
        real: RationalWire {
            numerator: "1".into(),
            denominator: "3".into(),
        },
        imaginary: RationalWire {
            numerator: "1".into(),
            denominator: "2".into(),
        },
    };
    assert_eq!(
        current.native().unwrap().current(),
        current.current().unwrap()
    );
    assert!(RationalWire {
        numerator: "1".into(),
        denominator: "0".into()
    }
    .rational()
    .is_err());
    assert!(RationalWire {
        numerator: "1".into(),
        denominator: "-2".into()
    }
    .rational()
    .is_err());
    assert!(RationalWire {
        numerator: "0.5".into(),
        denominator: "1".into()
    }
    .rational()
    .is_err());
}
