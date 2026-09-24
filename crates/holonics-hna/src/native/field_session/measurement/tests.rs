use super::*;

#[test]
fn exact_bit_counts_use_reduced_numerators_and_denominators() {
    let mut count = ExactBitCount::default();
    count.dyadic(0, 48);
    count.dyadic(1 << 47, 48); // 1/2: 1 + 1 + 2
    count.dyadic(-3, 2); // -3/4: 2 + 1 + 3
    assert_eq!(count.values, 3);
    assert_eq!(count.bits, 2 + 4 + 6);
    let mut json = ExactBitCount::default();
    json.json(&json!({"a":["1/2","-3/4","0"],"id":"g0","n":7}));
    let wire = serde_json::to_value(Rat::new((-6).into(), 8.into())).unwrap();
    json.json(&json!({"centre":[wire]}));
    assert_eq!(json.values, 4);
    assert_eq!(json.bits, 4 + 6 + 2 + 6);
}
