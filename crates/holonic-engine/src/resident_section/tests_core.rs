use super::*;
use num_traits::One;
const HALF: u16 = 0x3F00;

fn rat(n: i64, d: i64) -> Rat {
    Rat::new(BigInt::from(n), BigInt::from(d))
}

#[test]
fn a_binary64_word_is_an_exact_dyadic_and_its_value_is_the_word() {
    let scale = Dyadic::of_binary64_bits(0x3fe9884533d43651).expect("dyadic");
    assert_eq!(scale.octaves(), 53);
    assert_eq!(scale.exponent, -53);
    assert!(scale.value() < Rat::one() && scale.value() > rat(1, 2));
    assert_eq!(
        Dyadic::of_bfloat16_bits(HALF).expect("half").value(),
        rat(1, 2)
    );
}
