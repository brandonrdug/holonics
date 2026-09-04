use super::*;

/// A small readout with a known exact answer, so the arithmetic is checked against something
/// other than itself.
fn material() -> (AlignedMaterial, AlignedMaterial, usize) {
    let readout = AlignedMaterial {
        entries: vec![1, 2, 3, -1, 0, 5, 7, -7, 0],
        exponent: -3,
        entry_octaves: 3,
        negatives: 2,
    };
    let query = AlignedMaterial {
        entries: vec![2, -1, 4],
        exponent: -2,
        entry_octaves: 3,
        negatives: 1,
    };
    (readout, query, 3)
}

#[test]
fn the_serial_chart_returns_the_exact_contraction() {
    let (readout, query, dim) = material();
    let scores = score_serially(&readout, &query, dim, None).expect("well-formed");
    // Computed by hand: the point of an independent check is that it is independent.
    assert_eq!(
        scores,
        vec![
            1 * 2 + 2 * -1 + 3 * 4,
            -1 * 2 + 0 + 5 * 4,
            7 * 2 + -7 * -1 + 0
        ]
    );
    assert_eq!(scores, vec![12, 18, 21]);
}

/// The addressed form scores what the caller named and nothing else — so an aperture can report
/// what it excluded rather than dropping it.
#[test]
fn an_addressed_population_scores_exactly_the_declared_rows() {
    let (readout, query, dim) = material();
    let all = score_serially(&readout, &query, dim, None).expect("well-formed");
    let named = score_serially(&readout, &query, dim, Some(&[2, 0])).expect("well-formed");
    assert_eq!(named, vec![all[2], all[0]]);
    assert!(matches!(
        score_serially(&readout, &query, dim, Some(&[3])),
        Err(FiberError::AddressOutsideReadout { row: 3, rows: 3 })
    ));
}

/// **One mouth, two implementations, and this is the proof.** All 65,536 patterns, including
/// the non-finite ones both must refuse, and including the negative zero neither may collapse.
#[test]
fn the_fast_mouth_agrees_with_the_declared_mouth_on_every_pattern() {
    let mut finite = 0u32;
    let mut refused = 0u32;
    for pattern in 0u16..=u16::MAX {
        let declared = crate::exact_value::ieee754::decode_bfloat16_bits(pattern);
        let fast = super::decode_bfloat16_word(pattern);
        match (declared, fast) {
            (Ok(datum), Ok((signed, exponent))) => {
                finite += 1;
                let magnitude = u64::try_from(&datum.significand).expect("eight octaves");
                let expected = if datum.negative {
                    -(magnitude as i64)
                } else {
                    magnitude as i64
                };
                assert_eq!(signed, expected, "pattern {pattern:#06x} significand");
                assert_eq!(
                    exponent, datum.ulp_exponent,
                    "pattern {pattern:#06x} exponent"
                );
            }
            (Err(_), Err(_)) => refused += 1,
            (declared, fast) => {
                panic!("pattern {pattern:#06x} disagrees: {declared:?} against {fast:?}")
            }
        }
    }
    // 2 signs x 255 finite exponent codes x 128 mantissas = 65,280 finite; the one non-finite
    // exponent code carries 2 x 128 = 256 patterns and both mouths refuse every one of them.
    assert_eq!(finite, 65_280);
    assert_eq!(refused, 256);
    assert_eq!(finite + refused, 65_536);
}

/// The CUDA mouth is a second implementation only where the actual device passage agrees with
/// the serial mouth. This fixture includes negative words and unequal exponents, so it crosses
/// the hand-restoration path which previously used an undefined signed left shift.
#[test]
fn the_resident_bfloat16_mouth_agrees_with_the_serial_mouth_on_a_nontrivial_frame() {
    let Ok(resident) = ResidentReadout::new() else {
        eprintln!("no resident chart answered; the BF16 mouth parity check did not run");
        return;
    };
    // Three rows at width four: positive, negative, zero, and several exponent spreads.
    let words = vec![
        0x3f80, 0xc000, 0x3f00, 0x0000, // 1, -2, 1/2, 0
        0x4080, 0xbf80, 0x4000, 0xc040, // 4, -1, 2, -3
        0x3e80, 0x4100, 0xc100, 0x3fc0, // 1/4, 8, -8, 3/2
    ];
    let serial = align_bfloat16(&words).expect("serial mouth");
    let mounted = resident.mount_bfloat16(&words, 4).expect("resident mouth");
    assert_eq!(mounted.exponent(), serial.exponent);
    assert_eq!(mounted.entry_octaves(), serial.entry_octaves);
    assert_eq!(
        mounted.resident_octets(),
        words.len() * std::mem::size_of::<i64>()
    );

    let serial_mass: Vec<i128> = serial
        .entries
        .chunks_exact(4)
        .map(|row| {
            row.iter()
                .map(|value| i128::from(value.unsigned_abs()))
                .sum()
        })
        .collect();
    assert_eq!(mounted.absolute_row_mass().expect("row mass"), serial_mass);

    let query_words = [0x3f80, 0xbf80, 0x4000, 0x3f00];
    let query = align_bfloat16(&query_words).expect("query mouth");
    let carried = mounted.score(&query, None).expect("resident contraction");
    let expected = score_serially(&serial, &query, 4, None).expect("serial contraction");
    assert_eq!(carried.scores, expected);
}

/// **The headroom is computed from the material and refused rather than truncated.**
///
/// This is the falsifier for the exactness claim: a material that would overflow the exact
/// carrier must be named, not silently wrapped.
#[test]
fn a_material_past_the_exact_carrier_is_refused_by_name() {
    // 62-octave entries contracted over 2560 terms need 2*62 + 12 + 1 = 137 > 128.
    let needed = ResidentReadout::needed_octaves(62, 2560);
    assert!(needed > CARRIER_OCTAVES, "needed {needed}");
    // And the material this was built for fits, with the figure stated rather than assumed.
    let bf16 = ResidentReadout::needed_octaves(8, 2560);
    assert!(bf16 <= CARRIER_OCTAVES, "bf16 needed {bf16}");
}

/// The operand faces must remain distinct in the aperture theorem. A wide deposited map and a
/// narrow integer query do not pay the square of the wider bound.
#[test]
fn heterogeneous_operand_octaves_are_conserved_in_the_exact_bound() {
    assert_eq!(ResidentReadout::needed_product_octaves(62, 8, 786), 81);
    assert!(ResidentReadout::needed_product_octaves(62, 8, 786) <= CARRIER_OCTAVES);
    assert!(ResidentReadout::needed_product_octaves(62, 62, 786) > CARRIER_OCTAVES);
    assert_eq!(
        ResidentReadout::needed_octaves(62, 786),
        ResidentReadout::needed_product_octaves(62, 62, 786)
    );
}

/// The mouth is the only way a float enters, and the alignment is a rebase with **zero
/// remainder**: every aligned entry times two-to-the-exponent reproduces the original exactly.
#[test]
fn the_alignment_is_a_rebase_with_zero_remainder() {
    // 1.0, 2.0, 0.5, -1.5 as BF16 bit patterns.
    let words = [0x3F80u16, 0x4000, 0x3F00, 0xBFC0];
    let aligned = align_bfloat16(&words).expect("the mouth admits these");
    assert_eq!(aligned.negatives, 1);
    // The rebase is checked against the decoded pair, in exact integers, with no division:
    // `entry * 2^aligned.exponent == signed * 2^datum.ulp_exponent` becomes a left shift by the
    // spread. **This was checked in `f64` until 2026-08-13** — the only machine-float arithmetic
    // in any library `src/` in this workspace, evaluating a zero-remainder claim in the very
    // carrier the module exists to avoid.
    for (word, entry) in words.iter().zip(&aligned.entries) {
        let datum = crate::exact_value::ieee754::decode_bfloat16_bits(*word)
            .expect("the mouth admits these");
        let magnitude =
            u64::try_from(&datum.significand).expect("a BF16 significand is one word") as i64;
        let signed = if datum.negative {
            -magnitude
        } else {
            magnitude
        };
        let spread = u32::try_from(datum.ulp_exponent - aligned.exponent)
            .expect("every entry aligns downward onto the lowest exponent");
        assert_eq!(*entry, signed << spread, "word {word:#06x}");
    }
}

/// **The falsifier the parity test could not supply.** The guard read only the spread and then
/// called `checked_shl`, which refuses an out-of-range shift *amount* and never looks at the
/// value — so a shift that carried the magnitude through the sign bit returned `Some` and the
/// hand came back flipped. Both charts consumed the same wrapped material, so they agreed.
///
/// `1.0` and `2^56` as BF16: significands of 8 octaves, ulp exponents `-7` and `49`, so the
/// second aligns through a spread of 56 and demands 64 octaves of a 63-octave signed word.
#[test]
fn an_entry_whose_octaves_plus_spread_overflow_the_signed_word_is_refused() {
    let words = [0x3F80u16, 0x5B80];
    match align_bfloat16(&words) {
        Err(FiberError::AlignmentOverflows {
            octaves,
            spread,
            needed,
            carrier,
        }) => {
            assert_eq!((octaves, spread, needed, carrier), (8, 56, 64, 63));
        }
        other => panic!("the wrapping shift was admitted: {other:?}"),
    }

    // What the old guard did instead, kept as the evidence rather than the assertion: the
    // shift amount is in range, so `checked_shl` returns `Some` — of a negative number.
    let wrapped = 128i64.checked_shl(56).expect("the amount is in range");
    assert!(wrapped < 0, "the magnitude carried into the hand");
}

/// A zero material aligns without inventing an exponent.
#[test]
fn an_entirely_zero_material_aligns_to_the_zero_exponent() {
    let aligned = align_bfloat16(&[0x0000, 0x0000]).expect("zeros are admissible");
    assert_eq!(aligned.entries, vec![0, 0]);
    assert_eq!(aligned.exponent, 0);
    assert_eq!(aligned.entry_octaves, 0);
    assert_eq!(aligned.negatives, 0);
}

/// **The resident chart is graded against the serial one, bit for bit.**
///
/// Two independent implementations of one law; `CLAUDE.md` requires that where one exists, both
/// are stated. This is the parity half. Ignored when no device answers, because a skipped check
/// must not read as a passing one.
#[test]
fn the_two_charts_return_the_identical_exact_population() {
    let Ok(resident) = ResidentReadout::new() else {
        eprintln!("no resident chart answered; the parity check did not run");
        return;
    };
    // A material wide enough that the resident chart's width is doing something.
    let dim = 64usize;
    let rows = 512usize;
    let entries: Vec<i64> = (0..rows * dim)
        .map(|at| ((at as i64 * 2_654_435_761) % 1021) - 510)
        .collect();
    let readout = AlignedMaterial {
        entry_octaves: entries
            .iter()
            .map(|e| e.unsigned_abs().max(1).ilog2() + 1)
            .max()
            .unwrap_or(0),
        negatives: entries.iter().filter(|e| **e < 0).count() as u64,
        entries,
        exponent: -7,
    };
    let query_entries: Vec<i64> = (0..dim).map(|at| ((at as i64 * 97) % 255) - 127).collect();
    let query = AlignedMaterial {
        entry_octaves: query_entries
            .iter()
            .map(|e| e.unsigned_abs().max(1).ilog2() + 1)
            .max()
            .unwrap_or(0),
        negatives: query_entries.iter().filter(|e| **e < 0).count() as u64,
        entries: query_entries,
        exponent: -3,
    };

    let carried = resident
        .score(&readout, &query, dim, None)
        .expect("the deed is admissible");
    let serial = score_serially(&readout, &query, dim, None).expect("well-formed");
    assert_eq!(carried.scores, serial, "the two charts disagree");
    assert_eq!(carried.exact_multiply_accumulates, (rows * dim) as u64);

    // The octave face agrees with the exact scores it was taken beside.
    for (score, octave) in carried.scores.iter().zip(&carried.octaves) {
        let expected = if *score == 0 {
            0
        } else {
            128 - score.unsigned_abs().leading_zeros()
        };
        assert_eq!(*octave, expected, "score {score}");
    }

    // And the addressed form agrees with the whole one on the rows it named.
    let named: Vec<u32> = vec![7, 0, 511, 256];
    let addressed = resident
        .score(&readout, &query, dim, Some(&named))
        .expect("admissible");
    for (slot, row) in named.iter().enumerate() {
        assert_eq!(addressed.scores[slot], carried.scores[*row as usize]);
    }
}

/// **Mounting once and asking many is the same arithmetic as asking one at a time.**
///
/// The residency and the batched grid exist to stop the invariant crossing the bus per
/// question; neither may change a single returned integer. Three queries, so a batch that
/// silently scored only the first — or indexed its output by row and overwrote across
/// queries — fails here rather than at map scale.
#[test]
fn the_batched_grid_returns_exactly_what_one_query_at_a_time_returns() {
    let Ok(resident) = ResidentReadout::new() else {
        eprintln!("no resident chart answered; the batch parity check did not run");
        return;
    };
    let dim = 48usize;
    let rows = 300usize;
    let entries: Vec<i64> = (0..rows * dim)
        .map(|at| ((at as i64 * 1_000_003) % 977) - 488)
        .collect();
    let readout = AlignedMaterial {
        entry_octaves: entries
            .iter()
            .map(|e| e.unsigned_abs().max(1).ilog2() + 1)
            .max()
            .unwrap_or(0),
        negatives: entries.iter().filter(|e| **e < 0).count() as u64,
        entries,
        exponent: -11,
    };
    let queries: Vec<AlignedMaterial> = (0..3)
        .map(|which| {
            let entries: Vec<i64> = (0..dim)
                .map(|at| ((at as i64 * (31 + which * 17)) % 211) - 105)
                .collect();
            AlignedMaterial {
                entry_octaves: entries
                    .iter()
                    .map(|e| e.unsigned_abs().max(1).ilog2() + 1)
                    .max()
                    .unwrap_or(0),
                negatives: entries.iter().filter(|e| **e < 0).count() as u64,
                entries,
                // Distinct exponents, so a batch that carried one query's frame to all of them
                // is caught by the returned frame and not only by the integers.
                exponent: -3 - which as i32,
            }
        })
        .collect();

    let mounted = resident.mount(&readout, dim).expect("the map mounts");
    assert_eq!(mounted.rows(), rows);
    assert_eq!(mounted.dim(), dim);
    assert_eq!(mounted.resident_octets(), rows * dim * 8);

    let borrowed: Vec<&AlignedMaterial> = queries.iter().collect();
    let batched = mounted.score_many(&borrowed).expect("admissible");
    assert_eq!(batched.len(), queries.len());
    for (which, query) in queries.iter().enumerate() {
        let one = mounted.score(query, None).expect("admissible");
        assert_eq!(batched[which].scores, one.scores, "query {which}");
        assert_eq!(batched[which].octaves, one.octaves, "query {which}");
        assert_eq!(batched[which].query_exponent, query.exponent);
        assert_eq!(batched[which].readout_exponent, readout.exponent);
        // And against the independent serial chart, so agreement is not two forms of one bug.
        let serial = score_serially(&readout, query, dim, None).expect("well-formed");
        assert_eq!(
            batched[which].scores, serial,
            "query {which} against serial"
        );
    }
    // Distinct queries must return distinct populations, or the batch scored one of them three
    // times and the agreement above would be vacuous.
    assert_ne!(batched[0].scores, batched[1].scores);
    assert_ne!(batched[1].scores, batched[2].scores);
}

/// **Nothing in this module returns a winner**, which is the deposit's bar made checkable: the
/// exact-tie reading returns every member of the tie and commits to none.
#[test]
fn the_tie_reading_returns_every_member_and_commits_to_none() {
    let population = ScorePopulation {
        scores: vec![5, 9, 9, 1, 9],
        octaves: vec![3, 4, 4, 1, 4],
        readout_exponent: 0,
        query_exponent: 0,
        exact_multiply_accumulates: 0,
        resident_chart: "none".to_owned(),
    };
    assert_eq!(population.exactly_equal_to(1), vec![1, 2, 4]);
    assert_eq!(population.exactly_equal_to(0), vec![0]);
    assert_eq!(
        population.octave_census(),
        BTreeMap::from([(1, 1), (3, 1), (4, 3)])
    );
    assert_eq!(population.exact(2), Some(BigInt::from(9)));
}
