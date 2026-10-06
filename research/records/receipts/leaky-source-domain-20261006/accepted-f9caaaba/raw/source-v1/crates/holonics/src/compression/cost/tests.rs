//! One test per law of Lean `Compression/Core/Cost` this owner realizes: the description and
//! literal codes, the pay-off as a comparison of two codes, the alternator witnesses computed from
//! its codec, and the partial pivot's residual code.

use super::*;

fn one_bit_maps() -> Vec<Box<dyn Fn(&bool) -> bool>> {
    vec![
        Box::new(|_| false),
        Box::new(|_| true),
        Box::new(|bit| *bit),
        Box::new(|bit| !bit),
    ]
}

/// Lean `oneBitMaps`, `oneBit`: every one-bit map as a step and as a read, and both initial
/// configurations.
fn one_bit_family() -> CodecFamily<bool, bool> {
    CodecFamily::new(one_bit_maps(), vec![false, true], one_bit_maps()).unwrap()
}

fn bits() -> Alphabet<bool> {
    Alphabet::new(vec![false, true]).unwrap()
}

/// Lean `alternating`: `false, true, false, …` of length `n`.
fn alternating(length: usize) -> Vec<bool> {
    (0..length).map(|k| k % 2 == 1).collect()
}

/// Lean `alternatorIndex`, `alternator_codec`: the step `not`, the initial configuration `false`,
/// the identity read.
fn alternator(family: &CodecFamily<bool, bool>) -> NavigatorCodec<'_, bool, bool> {
    family.codec(3, 0, 2).unwrap()
}

fn every_codec(family: &CodecFamily<bool, bool>) -> Vec<NavigatorCodec<'_, bool, bool>> {
    let mut codecs = Vec::new();
    for step in 0..4 {
        for initial in 0..2 {
            for read in 0..4 {
                codecs.push(family.codec(step, initial, read).unwrap());
            }
        }
    }
    codecs
}

/// Lean `decode_succ`, `decode_take`: the release is causal; the next face is appended to what
/// was released, and a prefix does not depend on later ticks.
#[test]
fn the_decompression_is_causal() {
    let family = CodecFamily::new(
        vec![Box::new(|state: &u64| (3 * state + 1) % 11) as Box<dyn Fn(&u64) -> u64>],
        vec![4u64],
        vec![Box::new(|state: &u64| state % 3) as Box<dyn Fn(&u64) -> u64>],
    )
    .unwrap();
    let codec = family.codec(0, 0, 0).unwrap();
    for length in 0..20 {
        let mut state = 4u64;
        for _ in 0..length {
            state = (3 * state + 1) % 11;
        }
        let mut extended = codec.decode(length);
        extended.push(state % 3);
        assert_eq!(codec.decode(length + 1), extended);
        for later in 0..6 {
            assert_eq!(
                codec.decode(length + later)[..length].to_vec(),
                codec.decode(length)
            );
        }
    }
}

/// Lean `Nat.clog 2`: the least `k` with `t ≤ 2^k`.
#[test]
fn the_log_term_is_a_bit_length() {
    for (value, expected) in [
        (0u32, 0u64),
        (1, 0),
        (2, 1),
        (3, 2),
        (4, 2),
        (5, 3),
        (64, 6),
        (65, 7),
    ] {
        assert_eq!(ceil_log2(&BigUint::from(value)), expected);
    }
}

/// Lean `oneBit_descriptionBits`, `CodecFamily.describe_length`, `readIndex_describe`,
/// `ofDescription_describe`, `describe_injective`, `ofDescription_length`,
/// `oneBit_truncated_refused`: the description is the code the decoder reads,
/// `⌈log₂ 4⌉ + ⌈log₂ 2⌉ + ⌈log₂ 4⌉ = 5` bits for every one-bit codec, decoding it returns the same
/// codec, and distinct codecs have distinct descriptions. A truncated, overlong or out-of-family
/// code is refused.
#[test]
fn the_description_is_an_actual_code() {
    let family = one_bit_family();
    for codec in every_codec(&family) {
        let description = codec.description();
        assert_eq!(description.len(), 5);
        let decoded = family.codec_of(&description).unwrap();
        assert_eq!(decoded.description(), description);
        assert_eq!(decoded.decode(9), codec.decode(9));
        assert_eq!(
            family.codec_of(&description[..4]).unwrap_err(),
            CompressionError::TruncatedCode
        );
        let mut overlong = description.clone();
        overlong.push(false);
        assert_eq!(
            family.codec_of(&overlong).unwrap_err(),
            CompressionError::TrailingCode
        );
    }
    let mut descriptions: Vec<Vec<bool>> = every_codec(&family)
        .iter()
        .map(NavigatorCodec::description)
        .collect();
    descriptions.sort();
    descriptions.dedup();
    assert_eq!(descriptions.len(), 4 * 2 * 4, "describe is injective");
    let three_steps = CodecFamily::new(
        one_bit_maps().into_iter().take(3).collect(),
        vec![false],
        one_bit_maps(),
    )
    .unwrap();
    assert_eq!(
        three_steps
            .codec_of(&[true, true, false, false])
            .unwrap_err(),
        CompressionError::IndexOutside {
            index: 3,
            population: 3
        }
    );
}

/// Lean `alternator_regenerates`, `alternatorPivot_kt`, `literalBits_alternating`,
/// `alternator_pays_off_iff`, `alternator_pays_off_iff_pow`: the alternator's pay-off computed from
/// its codec, `Kt(n) = 5 + ⌈log₂ n⌉` against `ℓ = n`, so it pays off exactly from length `10`; on
/// lengths `2^m` exactly from `m = 4`, and at `8` it only breaks even.
#[test]
fn the_alternator_pays_off_from_ten() {
    let family = one_bit_family();
    let codec = alternator(&family);
    for length in 0..300 {
        let material = alternating(length);
        assert!(codec.regenerates(&material));
        let cost = codec.pivot(&bits(), &material).unwrap().cost();
        assert_eq!(cost.description, BigUint::from(5u32));
        assert_eq!(cost.residual, BigUint::from(0u32));
        assert_eq!(
            cost.kt,
            BigUint::from(5 + ceil_log2(&BigUint::from(length)))
        );
        assert_eq!(cost.literal, BigUint::from(length));
        assert_eq!(cost.pays_off(), length >= 10);
    }
    for m in 0u32..10 {
        let cost = codec.pivot(&bits(), &alternating(1 << m)).unwrap().cost();
        assert_eq!(cost.pays_off(), m >= 4);
    }
    let eight = codec.pivot(&bits(), &alternating(8)).unwrap().cost();
    assert_eq!(eight.saved_bits(), BigInt::from(0));
}

/// Lean `alternation_witnesses`: on `64` symbols `Kt = 11 < 64`; on `4` symbols `Kt = 7 > 4`.
#[test]
fn the_alternator_beats_the_literal_at_sixty_four_and_loses_at_four() {
    let family = one_bit_family();
    let codec = alternator(&family);
    let long = codec.pivot(&bits(), &alternating(64)).unwrap().cost();
    assert_eq!(long.kt, BigUint::from(11u32));
    assert_eq!(long.literal, BigUint::from(64u32));
    assert!(long.pays_off());
    assert_eq!(long.saved_bits(), BigInt::from(53));
    let short = codec.pivot(&bits(), &alternating(4)).unwrap().cost();
    assert_eq!(short.kt, BigUint::from(7u32));
    assert_eq!(short.literal, BigUint::from(4u32));
    assert!(!short.pays_off());
    assert_eq!(short.saved_bits(), BigInt::from(-3));
}

/// Lean `no_one_bit_navigator_regenerates`: no codec of the one-bit family regenerates
/// `(false, false, true)`, so no whole pivot of it exists.
#[test]
fn material_outside_the_navigator_family_has_no_whole_pivot() {
    let family = one_bit_family();
    let material = vec![false, false, true];
    for codec in every_codec(&family) {
        assert!(!codec.regenerates(&material));
        assert_eq!(
            codec.pivot(&bits(), &material).unwrap_err(),
            CompressionError::NotRegenerated { length: 3 }
        );
    }
}

/// Lean `CodecPivot.release_code`, `CodecFamily.partialRelease_partialCode`: the decoder carried by
/// every pivot releases the material from its code alone, whole or partial, for every codec of the
/// family.
#[test]
fn every_pivot_releases_its_material_from_its_code() {
    let family = one_bit_family();
    let mut flipped = alternating(37);
    flipped[5] = !flipped[5];
    flipped[30] = !flipped[30];
    for material in [vec![false, false, true], alternating(12), flipped] {
        for codec in every_codec(&family) {
            let pivot = codec.partial_pivot(&bits(), &material).unwrap();
            assert_eq!(
                family
                    .release(&bits(), pivot.code(), material.len(), PivotForm::Partial)
                    .unwrap(),
                material
            );
            if let Ok(whole) = codec.pivot(&bits(), &material) {
                assert_eq!(
                    family
                        .release(&bits(), whole.code(), material.len(), PivotForm::Whole)
                        .unwrap(),
                    material
                );
            }
        }
    }
}

/// Lean `CodecFamily.partialCode_length`, `foundedFaces_eq_nil_iff`, `one_founded_face_pays_off`,
/// `outside_material_stays_literal`: RIDE and FOUND in bits. The faces the navigator regenerates
/// add nothing past the residual's count, and each face outside its image founds one patch of
/// `⌈log₂ n⌉ + ⌈log₂ |A|⌉` bits. The alternator with one flipped face in `64` still pays off;
/// `(false, false, true)` is cheaper literally than through any codec of the family.
#[test]
fn a_residual_face_founds_its_own_patch() {
    let family = one_bit_family();
    let codec = alternator(&family);
    for founded in 0..5usize {
        let mut material = alternating(64);
        for position in 0..founded {
            material[7 * position + 3] = !material[7 * position + 3];
        }
        let cost = codec.partial_pivot(&bits(), &material).unwrap().cost();
        let count_bits = ceil_log2(&BigUint::from(65u32));
        let patch_bits = ceil_log2(&BigUint::from(64u32)) + 1;
        assert_eq!(
            cost.residual,
            BigUint::from(count_bits + founded as u64 * patch_bits)
        );
        assert_eq!(
            cost.kt,
            &cost.description + &cost.residual + BigUint::from(6u32)
        );
    }
    let mut once = alternating(64);
    once[10] = !once[10];
    assert!(codec.pivot(&bits(), &once).is_err());
    let partial = codec.partial_pivot(&bits(), &once).unwrap().cost();
    assert_eq!(partial.kt, BigUint::from(5u32 + 7 + 7 + 6));
    assert!(partial.pays_off());
    let outside = vec![false, false, true];
    let cheapest = every_codec(&family)
        .iter()
        .map(|codec| codec.partial_pivot(&bits(), &outside).unwrap().cost().kt)
        .min()
        .unwrap();
    assert!(cheapest >= literal_bits(&bits(), outside.len()));
}

/// Lean `literalCode_length`, `readLiteral_literalCode`, `CodecPivot.PaysOff`,
/// `CodecPivot.paysOff_iff_code_shorter`: **the literal is a code too**, of `⌈log₂ |A|⌉ · n` bits,
/// read back by its decoder, and a pivot pays off exactly when its code plus `⌈log₂ n⌉` is shorter
/// than the literal's actual code: the comparison of two codes.
#[test]
fn paying_off_compares_two_actual_codes() {
    let digits = Alphabet::new(vec!['a', 'b', 'c']).unwrap();
    let material: Vec<char> = "abcabcbbca".chars().collect();
    let code = digits.literal(&material).unwrap();
    assert_eq!(
        BigUint::from(code.len()),
        literal_bits(&digits, material.len())
    );
    assert_eq!(code.len(), 2 * material.len());
    assert_eq!(
        digits.read_literal(&code, material.len()).unwrap(),
        material
    );
    assert_eq!(
        digits.read_literal(&code[..code.len() - 1], material.len()),
        Err(CompressionError::TruncatedCode)
    );
    let mut trailing = code.clone();
    trailing.push(true);
    assert_eq!(
        digits.read_literal(&trailing, material.len()),
        Err(CompressionError::TrailingCode)
    );
    assert_eq!(
        digits.read_literal(&[true, true], 1),
        Err(CompressionError::IndexOutside {
            index: 3,
            population: 3
        })
    );
    let family = one_bit_family();
    let codec = alternator(&family);
    for length in 0..70 {
        let material = alternating(length);
        let pivot = codec.pivot(&bits(), &material).unwrap();
        let literal = bits().literal(&material).unwrap();
        assert_eq!(bits().read_literal(&literal, length).unwrap(), material);
        let shorter =
            pivot.code().len() as u64 + ceil_log2(&BigUint::from(length)) < literal.len() as u64;
        assert_eq!(pivot.cost().pays_off(), shorter);
    }
}

/// A symbol outside the alphabet, a repeating alphabet and an empty family are refused.
#[test]
fn an_undeclared_symbol_is_refused() {
    assert_eq!(
        Alphabet::new(vec![true, true]).unwrap_err(),
        CompressionError::RepeatedSymbol { index: 1 }
    );
    let only_false = Alphabet::new(vec![false]).unwrap();
    assert_eq!(
        only_false.literal(&[false, true]).unwrap_err(),
        CompressionError::SymbolOutside
    );
    assert_eq!(
        CodecFamily::<bool, bool>::new(Vec::new(), vec![false], one_bit_maps()).unwrap_err(),
        CompressionError::EmptyFamily { what: "steps" }
    );
}
