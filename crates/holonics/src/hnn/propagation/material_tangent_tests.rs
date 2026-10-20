//! Admission is checked at the actual Word, before any tangent mutation (Refs #63 #62).

use super::*;
use crate::hnn::tests::support::{contact, small_field};
use crate::hnn::word::Word;
use crate::hnn::word::continuation::{MaterialDirection, MaterialTangent};
use crate::hnn::ring::ResonatorMaterial;

#[test]
fn material_tangent_admission_refuses_actual_nonquadratic_words_atomically() {
    let field = small_field(&[2, 3], vec![contact(0, 1, 1, 0)], 1);
    let current = Current::at_rest(&field);
    let material = crate::hnn::tests::learning::generic(&field, 81);
    let exact = Operands::exact_at_cut(&field, &material, &current).unwrap();
    let charted = Operands::at_cut(&field, &material, &current).unwrap().unsplit().unwrap();
    assert!(charted.rings[0].chart().is_some());
    assert!(charted.contacts[0].chart().is_some());
    let width = field.ring(0).width();
    let quadratic = ResonatorMaterial::new(
        ExactRatMatrix::identity(width).unwrap(),
        ExactRatMatrix::zero(width, width).unwrap(),
        ExactRatMatrix::zero(width, width).unwrap(),
        None,
    ).unwrap();
    let saturated = quadratic.clone().with_symmetric_saturation(crate::ratio::rat(1, 16)).unwrap();
    let loaded = |mut ops: Operands, law: &ResonatorMaterial| {
        ops.resonators[0] = Some(ResonatorOperands::at_cut(
            0, law, ops.rings[0].admittance(), &ops.step, None,
        ).unwrap());
        ops
    };
    let base = loaded(exact.clone(), &quadratic);
    let mut ring_chart = base.clone();
    ring_chart.rings[0] = charted.rings[0].clone();
    let mut contact_chart = base.clone();
    contact_chart.contacts[0] = charted.contacts[0].clone();
    let mut lattice = base.clone();
    lattice.lattice = Some(WordLattice::by_rule(16, 2, width as u64, 2));
    let variants = [
        ("ring chart", ring_chart),
        ("contact chart", contact_chart),
        ("saturation", loaded(exact, &saturated)),
        ("transient lattice", lattice),
    ];
    let storage: Vec<Vec<Rat>> = field.rings().iter().map(|r| vec![Rat::zero(); r.width()]).collect();
    let direction = MaterialDirection {
        contact: 0,
        storage: Some(ExactRatMatrix::identity(base.contacts[0].width()).unwrap()),
        stiffness: None,
        dissipation: None,
    };
    let mut admitted = Word::on_operands(&field, base.clone(), storage.clone()).unwrap();
    let mut positive = MaterialTangent::held_opening(&admitted, 7, direction.clone()).unwrap();
    positive.rebind(&admitted, 9).unwrap();
    admitted.tick().unwrap();
    positive.step(&admitted).unwrap();
    assert_eq!(positive.commit(), 9);

    for (name, ops) in variants {
        let mut actual = Word::on_operands(&field, ops, storage.clone()).unwrap();
        let before_word = actual.change().unwrap();
        assert!(MaterialTangent::held_opening(&actual, 7, direction.clone()).is_err(), "{name}: opening");
        assert_eq!(actual.change().unwrap(), before_word, "{name}: opening unchanged");

        let opening = Word::on_operands(&field, base.clone(), storage.clone()).unwrap();
        let mut tangent = MaterialTangent::held_opening(&opening, 7, direction.clone()).unwrap();
        let before = tangent.clone();
        assert!(tangent.rebind(&actual, 99).is_err(), "{name}: rebind");
        assert_eq!(tangent, before, "{name}: rebind preserves every tangent field");

        // A real full tick and the same opening clock keep an earlier record/clock refusal
        // from standing in for the new branch admission at step.
        actual.tick().unwrap();
        assert!(!actual.recorded()[0].rates.is_empty());
        assert!(tangent.step(&actual).is_err(), "{name}: step");
        assert_eq!(tangent, before, "{name}: step preserves every tangent field");
    }
}
