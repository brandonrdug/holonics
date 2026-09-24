use crate::ratio::ring::section as section_layout_cuda;

// D3 — the exact `Z/(2^61 - 1)` arithmetic the section triple compiles for both nvptx and the host
// ---------------------------------------------------------------------------------------------

/// The operand spread every pairwise assertion below runs over: the ring boundary (`0`, `1`, `2`,
/// `p-2`, `p-1`), the first words *past* it (`p`, `p+1`), the power-of-two boundaries the fold
/// straddles (`2^61`, `2^61+1`, `2^62`, `2^63`), the widest word (`u64::MAX`), and a deterministic
/// spread that includes the observed counterexample's own operands.  Products of this set reach
/// near `2^122` (`2^61 · 2^61`) and near `2^128` (`u64::MAX · u64::MAX`), which are precisely the
/// two regimes a narrowing fold loses.
const RING_PROBES: [u64; 18] = [
    0,
    1,
    2,
    section_layout_cuda::MODULUS - 2,
    section_layout_cuda::MODULUS - 1,
    section_layout_cuda::MODULUS,
    section_layout_cuda::MODULUS + 1,
    1u64 << 61,
    (1u64 << 61) + 1,
    1u64 << 62,
    1u64 << 63,
    u64::MAX,
    17_678_129_737_304_986_966,
    2_305_843_009_213_693_949,
    1_234_567_890_123_456_789,
    9_876_543_210_987_654_321,
    (1u64 << 63) + (1u64 << 61) + 7,
    u64::MAX - 1,
];

#[test]
fn the_section_ring_is_total_on_every_boundary_pair() {
    let modulus = section_layout_cuda::MODULUS as u128;
    for value in RING_PROBES {
        let canonical = section_layout_cuda::canonical(value);
        assert_eq!(canonical, ((value as u128) % modulus) as u64, "canonical({value})");
        assert!(
            section_layout_cuda::is_canonical(canonical),
            "canonical({value}) is canonical"
        );
        assert_eq!(
            section_layout_cuda::is_canonical(value),
            value < section_layout_cuda::MODULUS,
            "is_canonical({value})"
        );
    }
    for left in RING_PROBES {
        for right in RING_PROBES {
            let sum = (left as u128) + (right as u128);
            let product = (left as u128) * (right as u128);
            assert_eq!(
                section_layout_cuda::add(left, right),
                (sum % modulus) as u64,
                "add({left}, {right})"
            );
            assert_eq!(
                section_layout_cuda::mul(left, right),
                (product % modulus) as u64,
                "mul({left}, {right})"
            );
            // The two folds are the same map on the same word, whichever mouth reaches them.
            assert_eq!(
                section_layout_cuda::reduce(sum),
                (sum % modulus) as u64,
                "reduce({sum})"
            );
            assert_eq!(
                section_layout_cuda::reduce(product),
                (product % modulus) as u64,
                "reduce({product})"
            );
        }
    }
}

#[test]
fn the_section_fold_holds_over_the_whole_128_bit_word() {
    // The fold's domain is stated as every `u128`, not merely every `u64 × u64` product; the two
    // regimes a narrowing fold loses are a high half past `2^64` (products at or above `2^125`)
    // and a `low + high` sum past `2^64`.  Both are named here explicitly.
    let modulus = section_layout_cuda::MODULUS as u128;
    let words: [u128; 12] = [
        0,
        1,
        modulus - 1,
        modulus,
        modulus + 1,
        1u128 << 61,
        1u128 << 64,
        1u128 << 122,
        1u128 << 125,
        1u128 << 127,
        u128::MAX,
        (u64::MAX as u128) * (u64::MAX as u128),
    ];
    for word in words {
        assert_eq!(
            section_layout_cuda::reduce(word),
            (word % modulus) as u64,
            "reduce({word})"
        );
    }
}

#[test]
fn the_section_ring_is_associative_and_commutative_over_non_canonical_words() {
    // The accumulating scatter folds whatever the global field already holds, so associativity and
    // commutativity are owed over the **whole** `u64` domain and not only over `[0, p)`.
    for a in RING_PROBES {
        for b in RING_PROBES {
            assert_eq!(section_layout_cuda::add(a, b), section_layout_cuda::add(b, a));
            assert_eq!(section_layout_cuda::mul(a, b), section_layout_cuda::mul(b, a));
            for c in RING_PROBES {
                assert_eq!(
                    section_layout_cuda::add(section_layout_cuda::add(a, b), c),
                    section_layout_cuda::add(a, section_layout_cuda::add(b, c)),
                    "({a} + {b}) + {c}"
                );
                assert_eq!(
                    section_layout_cuda::mul(section_layout_cuda::mul(a, b), c),
                    section_layout_cuda::mul(a, section_layout_cuda::mul(b, c)),
                    "({a} * {b}) * {c}"
                );
            }
        }
    }
}
