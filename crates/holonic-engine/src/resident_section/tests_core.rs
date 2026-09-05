use super::*;
use num_traits::One;

fn surface() -> Option<(&'static ResidentReadout, &'static ResidentSurface<'static>)> {
    let readout = match ResidentReadout::new() {
        Ok(readout) => Box::leak(Box::new(readout)),
        Err(_) => {
            eprintln!("no resident chart answered; the resident-section tests did not run");
            return None;
        }
    };
    let surface = Box::leak(Box::new(ResidentSurface::on(readout).ok()?));
    Some((readout, surface))
}

/// bf16 words for small dyadics: 1.0 = 0x3F80, 2.0 = 0x4000, -1.5 = 0xBFC0, 0.5 = 0x3F00
const ONE: u16 = 0x3F80;
const TWO: u16 = 0x4000;
const HALF: u16 = 0x3F00;
const MINUS_ONE_AND_HALF: u16 = 0xBFC0;
const THREE: u16 = 0x4040;
const FOUR: u16 = 0x4080;

fn rat(n: i64, d: i64) -> Rat {
    Rat::new(BigInt::from(n), BigInt::from(d))
}

#[test]
fn an_exact_section_rest_round_trips_and_remounts_without_replaying_its_law() {
    let rest = ResidentSectionRest::found(
        2,
        2,
        ResidentGrain(20),
        7,
        vec![(-3, -1), (0, 0), (2, 5), (9, 9)],
    )
    .expect("rest");
    let bytes = rest.canonical_bytes().expect("canonical");
    assert_eq!(ResidentSectionRest::read(&bytes).expect("read"), rest);

    let Some((_, surface)) = surface() else {
        return;
    };
    let mounted = surface.mount_section_rest(&rest).expect("mount");
    let returned = surface.detach_section(&mounted, 7).expect("detach");
    assert_eq!(returned, rest);
    assert_eq!(
        returned.sha256().expect("identity"),
        rest.sha256().expect("identity")
    );
}

#[test]
#[ignore = "requires CUDA; exact interval subrange readback"]
fn terminal_row_readback_preserves_full_source_without_device_allocation() {
    let readout=ResidentReadout::new().expect("CUDA");
    let surface=ResidentSurface::on(&readout).unwrap();
    let rest=ResidentSectionRest::found(3,2,ResidentGrain(20),7,
        vec![(-3,-1),(0,0),(2,5),(9,9),(-11,-7),(13,17)]).unwrap();
    let source=surface.mount_section_rest(&rest).unwrap();
    let before=surface.census();
    assert_eq!(surface.read_out_terminal_row(&source).unwrap(),vec![(-11,-7),(13,17)]);
    let after=surface.census();
    assert_eq!(after.egress_section_octets-before.egress_section_octets,32);
    assert_eq!(after.allocations,before.allocations);
    assert_eq!(after.deed_launches,before.deed_launches);
    assert_eq!(surface.read_out(&source).unwrap(),rest.intervals);
}

/// A one-occurrence passage entering `words` at `grain`, launched, and read out.
fn enter_once(
    surface: &'static ResidentSurface<'static>,
    words: &[u16],
    rows: usize,
    width: usize,
    scale: Dyadic,
    grain: ResidentGrain,
) -> (Vec<(i64, i64)>, PassageReading) {
    let staged = surface.stage_words(words, rows, width).expect("stage");
    let shape = surface
        .shape_enter(rows, width, scale, grain, words)
        .expect("shape");
    let out = surface.fresh_section(rows, width, grain).expect("section");
    let mut builder = surface.begin_passage(&[vec![]]).expect("begin");
    let lane = builder.open(0, &[]).expect("open");
    surface
        .record_enter(&lane, &staged, scale, &out)
        .expect("record");
    builder.close(0, &out, shape.needed).expect("close");
    let passage = builder.finish().expect("finish");
    let reading = passage.launch().expect("launch");
    let read = surface.read_out(&out).expect("read");
    (read, reading)
}

/// A bf16 word from a signed 8-bit significand and a binary exponent, so a fixture's octaves are
/// declared rather than hoped for.
fn bfloat16(significand: i32, exponent: i32) -> u16 {
    let negative = significand < 0;
    let magnitude = significand.unsigned_abs();
    assert!(
        magnitude != 0 && magnitude < 256,
        "a bf16 significand is eight octaves"
    );
    let bits = 32 - magnitude.leading_zeros();
    let normalized = magnitude << (8 - bits);
    let unbiased = exponent + (bits as i32) - 1;
    let biased = unbiased + 127;
    assert!(
        biased > 0 && biased < 255,
        "the fixture exponent must be a normal bf16"
    );
    ((negative as u16) << 15) | ((biased as u16) << 7) | ((normalized & 0x7f) as u16)
}

#[test]
fn the_terminal_receiver_retains_the_exact_last_row_without_materializing_the_prefix() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let rows = 3;
    let width = 4;
    let grain = ResidentGrain(8);
    let words = [
        ONE,
        TWO,
        THREE,
        FOUR,
        HALF,
        ONE,
        TWO,
        THREE,
        MINUS_ONE_AND_HALF,
        HALF,
        THREE,
        FOUR,
    ];
    let staged = surface.stage_words(&words, rows, width).expect("stage");
    let entered_shape = surface
        .shape_enter(rows, width, Dyadic::ONE, grain, &words)
        .expect("enter shape");
    let terminal_shape = surface
        .shape_terminal_row(rows, width, entered_shape.needed)
        .expect("terminal shape");
    assert_eq!((terminal_shape.rows, terminal_shape.width), (1, width));
    let entered = surface.fresh_section(rows, width, grain).expect("entered");
    let terminal = surface.fresh_section(1, width, grain).expect("terminal");
    let mut builder = surface.begin_passage(&[vec![], vec![0]]).expect("begin");
    let enter_lane = builder.open(0, &[]).expect("enter lane");
    surface
        .record_enter(&enter_lane, &staged, Dyadic::ONE, &entered)
        .expect("record enter");
    builder
        .close(0, &entered, entered_shape.needed)
        .expect("close enter");
    let terminal_lane = builder.open(1, &[0]).expect("terminal lane");
    surface
        .record_terminal_row(&terminal_lane, &entered, &terminal)
        .expect("record terminal");
    builder
        .close(1, &terminal, terminal_shape.needed)
        .expect("close terminal");
    let reading = builder.finish().expect("finish").launch().expect("launch");
    assert!(
        reading.obstruction.refusals.is_empty(),
        "{:?}",
        reading.obstruction
    );
    let full = surface.read_out(&entered).expect("full face");
    let received = surface.read_out(&terminal).expect("terminal face");
    assert_eq!(received, full[(rows - 1) * width..].to_vec());
}

#[test]
fn the_partition_receiver_integrates_every_addressed_source_row_and_retains_the_predecessor() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let rows = 5;
    let width = 2;
    let grain = ResidentGrain(8);
    let words = [
        ONE,
        TWO,
        THREE,
        FOUR,
        HALF,
        ONE,
        TWO,
        THREE,
        MINUS_ONE_AND_HALF,
        HALF,
    ];
    let boundaries = [0u32, 2, 5];
    let mounted = surface.mount_positions(&boundaries).expect("boundaries");
    let staged = surface.stage_words(&words, rows, width).expect("stage");
    let entered_shape = surface
        .shape_enter(rows, width, Dyadic::ONE, grain, &words)
        .expect("enter shape");
    let mean_shape = surface
        .shape_partition_mean(rows, width, entered_shape.needed, &boundaries)
        .expect("partition shape");
    assert_eq!((mean_shape.rows, mean_shape.width), (2, width));
    let entered = surface.fresh_section(rows, width, grain).expect("entered");
    let means = surface.fresh_section(2, width, grain).expect("means");
    let mut builder = surface.begin_passage(&[vec![], vec![0]]).expect("begin");
    let enter_lane = builder.open(0, &[]).expect("enter lane");
    surface
        .record_enter(&enter_lane, &staged, Dyadic::ONE, &entered)
        .expect("record enter");
    builder
        .close(0, &entered, entered_shape.needed)
        .expect("close enter");
    let mean_lane = builder.open(1, &[0]).expect("mean lane");
    surface
        .record_partition_mean(&mean_lane, &entered, &mounted, &means)
        .expect("record means");
    builder
        .close(1, &means, mean_shape.needed)
        .expect("close means");
    let reading = builder.finish().expect("finish").launch().expect("launch");
    assert!(reading.obstruction.is_empty(), "{:?}", reading.slots);
    let predecessor = surface.read_out(&entered).expect("predecessor");
    assert_eq!(predecessor.len(), rows * width);
    let received = surface.read_out(&means).expect("means");
    assert_eq!(received[0], (2 << grain.0, 2 << grain.0));
    assert_eq!(received[1], (3 << grain.0, 3 << grain.0));
    let contains = |enclosure: (i64, i64), value: &Rat| {
        word_value(enclosure.0, grain) <= *value && *value <= word_value(enclosure.1, grain)
    };
    assert!(contains(received[2], &rat(1, 3)), "{:?}", received[2]);
    assert!(contains(received[3], &rat(3, 2)), "{:?}", received[3]);
    assert!(received[2].1 - received[2].0 <= 1);
    assert!(received[3].1 - received[3].0 <= 1);
}

/// **PART B: the block-aggregated census and the per-thread-atomic control, on one section.**
/// Every slot word, plural shapes, and the poisoned-lineage entry. The a-priori is that max, or
/// and add are the same commutative and associative receivers the atomics implemented, so the
/// fold's grouping cannot move a word; this measures it instead of asserting it.
#[test]
fn the_block_aggregated_census_returns_the_serial_controls_census_word_for_word() {
    let Some((_, surface)) = surface() else {
        return;
    };
    // 205 · 2^-11 falls below a grain of 8, so the mouth returns a GENUINE interval and the
    // width faces are exercised rather than sitting at zero.
    let narrow = bfloat16(205, -11);
    // A grain of 8 leaves the low three bits of 205·2^-11 below it, so those words enter as
    // genuine intervals; a grain of 20 carries every fixture word exactly, so its widths are all
    // zero — both are shapes the census must return, and the second is not a degenerate case.
    let shapes: [(usize, usize, u32); 5] = [
        (1, 1, 8),
        (1, 32, 8),
        (7, 129, 8),
        (4, 1024, 8),
        (2, 64, 20),
    ];
    for (rows, width, grain) in shapes {
        let grain = ResidentGrain(grain);
        let words: Vec<u16> = (0..rows * width)
            .map(|i| match i % 5 {
                0 => narrow,
                1 => ONE,
                2 => MINUS_ONE_AND_HALF,
                3 => bfloat16(-205, -11),
                _ => HALF,
            })
            .collect();
        let staged = surface.stage_words(&words, rows, width).expect("stage");
        let shape = surface
            .shape_enter(rows, width, Dyadic::ONE, grain, &words)
            .expect("shape");
        let section = surface.fresh_section(rows, width, grain).expect("section");
        let mut builder = surface.begin_passage(&[vec![]]).expect("begin");
        let lane = builder.open(0, &[]).expect("open");
        surface
            .record_enter(&lane, &staged, Dyadic::ONE, &section)
            .expect("record");
        builder.close(0, &section, shape.needed).expect("close");
        builder.finish().expect("finish").launch().expect("launch");
        // (a) a standing occurrence: nothing refuses and both forms are exactly order-free.
        let (aggregated, control) = surface
            .census_both(&section, shape.needed, 0)
            .expect("census");
        assert_eq!(
            aggregated, control,
            "the census disagrees at {rows}x{width} grain {}",
            grain.0
        );
        assert!(aggregated.written && aggregated.max_octave > 0);
        if grain.0 < 11 {
            assert!(
                aggregated.width_sum > 0 && aggregated.nonzero_widths > 0,
                "the interval fixture must exercise the width faces"
            );
        } else {
            assert_eq!(
                (
                    aggregated.width_sum,
                    aggregated.nonzero_widths,
                    aggregated.max_width
                ),
                (0, 0, 0),
                "an exactly carried fixture has no width, under both forms"
            );
        }
        assert!(!aggregated.inverted && aggregated.refused == 0);
        // (b) a refused occurrence's census still measures nothing, under both forms.
        for poison in [REFUSED_UPSTREAM, REFUSED_MALFORMED, REFUSED_CARRIER] {
            let (aggregated, control) = surface
                .census_both(&section, shape.needed, poison)
                .expect("census");
            assert_eq!(
                aggregated, control,
                "the poisoned census disagrees at {rows}x{width}"
            );
            assert_eq!(
                aggregated.refused, poison,
                "a refused occurrence acquires no second refusal from its own census"
            );
            assert!(aggregated.written, "the census still marks that it ran");
            assert_eq!(
                (
                    aggregated.max_octave,
                    aggregated.max_width,
                    aggregated.width_sum,
                    aggregated.nonzero_widths
                ),
                (0, 0, 0, 0),
                "and it measures nothing"
            );
        }
        // (c) the bound refuted: both forms raise it, and both are stable across repetitions.
        // This is the ONE order-dependent class, and it is inherited: both forms decide whether
        // to measure by reading the same word they OR into. The refusal itself is order-free.
        let low = 1u32;
        let mut readings = Vec::new();
        for _ in 0..4 {
            let (aggregated, control) = surface.census_both(&section, low, 0).expect("census");
            assert_eq!(aggregated.refused & REFUSED_BOUND, REFUSED_BOUND);
            assert_eq!(control.refused & REFUSED_BOUND, REFUSED_BOUND);
            assert!(aggregated.bound_violated && control.bound_violated);
            readings.push((aggregated, control));
        }
        assert!(
            readings
                .windows(2)
                .all(|w| w[0].0.refused == w[1].0.refused),
            "the refusal is order-free even where the measurement is not"
        );
    }
}

/// **PART D: the mouth's a-priori bound is read off the entering words.** The shape's carrier
/// admission and the `enter` law's a-priori bound are one function, so a population whose
/// exponent is large is admitted for what it is rather than refused BOUND at the mouth.
#[test]
fn the_mouths_a_priori_bound_is_read_off_the_entering_words_and_not_authored_from_scale_and_grain()
{
    let Some((_, surface)) = surface() else {
        return;
    };
    let grain = ResidentGrain(8);
    let authored = 8 + Dyadic::ONE.octaves() + grain.0 + 8; // what the bound was until 2026-08-19
    // (i) a wide population: the authored bound is BELOW the octaves the words occupy, so the
    //     mouth used to refuse its own material. The reading is above them.
    let wide = [bfloat16(255, 46), bfloat16(-255, 46), ONE];
    let read = ResidentSurface::entering_octaves(&wide, Dyadic::ONE, grain);
    assert!(
        read > authored,
        "the wide fixture is exactly the population the authored bound could not carry: read {read}, authored {authored}"
    );
    let shape = surface
        .shape_enter(1, 3, Dyadic::ONE, grain, &wide)
        .expect("shape");
    assert_eq!(shape.needed, read);
    // and the words the mouth actually writes sit inside it
    let (words, reading) = enter_once(surface, &wide, 1, 3, Dyadic::ONE, grain);
    assert_eq!(
        reading.slots[0].refused, 0,
        "the mouth no longer refuses the material it was handed"
    );
    let measured = words
        .iter()
        .map(|(lo, hi)| 64 - lo.unsigned_abs().max(hi.unsigned_abs()).leading_zeros())
        .max()
        .expect("words");
    assert!(
        measured <= read,
        "measured {measured} octaves against an a-priori bound of {read}"
    );
    assert_eq!(reading.slots[0].max_octave, measured);
    // (ii) a narrow population: the reading is far BELOW the authored bound, so the admission is
    //      no longer a constant wearing a derivation.
    let narrow = [HALF, bfloat16(205, -11)];
    let narrow_read = ResidentSurface::entering_octaves(&narrow, Dyadic::ONE, grain);
    assert!(
        narrow_read < authored,
        "read {narrow_read} against authored {authored}"
    );
    // (iii) the shape and the law take the same reading, so the census cannot compare against a
    //       different bound from the one the carrier admitted.
    use crate::resident_law::{Enter, EnteringRows, ResidentLaw, ResidentMaterial};
    let mut material = ResidentMaterial::empty();
    material.entering.insert(
        "x".to_owned(),
        EnteringRows {
            words: wide.to_vec(),
            rows: 1,
            width: 3,
        },
    );
    let law = Enter {
        population: "x".to_owned(),
        scale: Dyadic::ONE,
    };
    assert_eq!(law.bound_octaves(grain, &[], &material), i64::from(read));
    // (iv) an empty population reads one octave rather than a negative bound.
    assert_eq!(
        ResidentSurface::entering_octaves(&[], Dyadic::ONE, grain),
        1
    );
}

#[test]
fn the_production_cone_gate_names_what_it_finds_and_only_that() {
    let clean = [("resident", "use crate::exact_work::ExactWork;")];
    assert!(production_cone_reaches_the_reference(&clean).is_empty());
    let dirty = [("driver", "use holonic_engine::ported_reference::realize;")];
    assert!(
        production_cone_reaches_the_reference(&dirty)
            .iter()
            .any(|(_, token)| *token == "ported_reference")
    );
    let loop_shaped = [("owner", "impl EnactsInOrder for X {}")];
    assert!(
        production_cone_reaches_the_reference(&loop_shaped)
            .iter()
            .any(|(_, token)| *token == "impl EnactsInOrder")
    );
}

#[test]
fn this_owner_does_not_reach_the_quarantined_interpreter() {
    let own = include_str!("../resident_section.rs");
    let body: String = own
        .split("#[cfg(test)]")
        .next()
        .expect("the owner precedes its tests")
        .lines()
        .filter(|line| !line.trim_start().starts_with('"'))
        .collect::<Vec<_>>()
        .join("\n");
    let reached = production_cone_reaches_the_reference(&[("resident_section.rs", &body)]);
    assert!(reached.is_empty(), "{reached:?}");
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

#[test]
fn the_surface_binds_one_apparatus_occurrence_and_states_its_mode() {
    let Some((readout, surface)) = surface() else {
        return;
    };
    assert_eq!(surface.device_name(), readout.device_name());
    assert_eq!(
        surface.cover().device().map(|d| d.name.as_str()),
        Some(surface.device_name())
    );
    let mode = surface.mode();
    assert_eq!(mode.kernel_content.as_deref(), Some(surface.ptx_sha256()));
    assert!(mode.device.is_some());
    assert_eq!(surface.declaration().warp_size, surface.derived_launch().2);
}

#[test]
fn a_passage_of_one_occurrence_launches_once_synchronizes_once_and_reads_once() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let grain = ResidentGrain(20);
    let (words, reading) = enter_once(
        surface,
        &[ONE, TWO, HALF, MINUS_ONE_AND_HALF],
        2,
        2,
        Dyadic::ONE,
        grain,
    );
    let unit = 1i64 << 20;
    assert_eq!(
        words,
        vec![
            (unit, unit),
            (2 * unit, 2 * unit),
            (unit / 2, unit / 2),
            (-3 * unit / 2, -3 * unit / 2)
        ]
    );
    assert_eq!(reading.slots[0].max_octave, 22);
    assert_eq!(reading.slots[0].max_width, 0);
    assert!(reading.slots[0].written);
    assert!(reading.obstruction.is_empty());
    assert_eq!(
        reading.slots[0].lineage_inspected, 0,
        "an entering occurrence inspects no predecessor"
    );
    let (before, after) = (&reading.census_before, &reading.census_after);
    assert_eq!(after.deed_launches, before.deed_launches + 1);
    assert_eq!(after.synchronizations, before.synchronizations + 1);
    assert_eq!(
        after.captured_launches, before.captured_launches,
        "no launch is issued during the deed"
    );
    assert_eq!(
        after.egress_receipt_octets - before.egress_receipt_octets,
        (SLOT_WORDS * 4) as u64
    );
    assert_eq!(
        after.egress_section_octets, before.egress_section_octets,
        "the deed itself reads no section"
    );
}

#[test]
fn a_dyadic_scale_finer_than_the_grain_widens_by_one_grain_and_never_rounds_toward_a_value() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let (words, _) = enter_once(
        surface,
        &[HALF],
        1,
        1,
        Dyadic {
            significand: 3,
            exponent: -20,
        },
        ResidentGrain(20),
    );
    assert_eq!(words, vec![(1, 2)]);
}

/// A two-front passage: `enter x` then co-present `{scale x by 2, hadamard x·x, re-entry x+x}`,
/// with the graph's own census read back beside what was intended.
#[test]
fn a_two_front_passage_binds_the_bonds_as_edges_and_the_co_present_members_share_no_edge() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let grain = ResidentGrain(20);
    let words = [ONE, TWO, HALF, MINUS_ONE_AND_HALF];
    let staged = surface.stage_words(&words, 1, 4).expect("stage");
    let enter = surface
        .shape_enter(1, 4, Dyadic::ONE, grain, &words)
        .expect("shape");
    let by = DyadicEnclosure {
        lo: 2,
        hi: 2,
        grain: 0,
    };
    let scale = surface.shape_scale(1, 4, 22, by).expect("shape");
    let hadamard = surface.shape_hadamard(1, 4, 22, 22).expect("shape");
    let re_entry = surface.shape_re_entry(1, 4, 22, 22).expect("shape");
    let x = surface.fresh_section(1, 4, grain).expect("x");
    let scaled = surface.fresh_section(1, 4, grain).expect("s");
    let squared = surface.fresh_section(1, 4, grain).expect("h");
    let doubled = surface.fresh_section(1, 4, grain).expect("r");
    let mut builder = surface
        .begin_passage(&[vec![], vec![0], vec![0, 0], vec![0, 0]])
        .expect("begin");
    let lane = builder.open(0, &[]).expect("open");
    surface
        .record_enter(&lane, &staged, Dyadic::ONE, &x)
        .expect("enter");
    builder.close(0, &x, enter.needed).expect("close");
    let lane = builder.open(1, &[0]).expect("open");
    surface.record_scale(&lane, &x, by, &scaled).expect("scale");
    builder.close(1, &scaled, scale.needed).expect("close");
    let lane = builder.open(2, &[0, 0]).expect("open");
    surface
        .record_hadamard(&lane, &x, &x, &squared)
        .expect("hadamard");
    builder.close(2, &squared, hadamard.needed).expect("close");
    let lane = builder.open(3, &[0, 0]).expect("open");
    surface
        .record_re_entry(&lane, &x, &x, &doubled)
        .expect("re-entry");
    builder.close(3, &doubled, re_entry.needed).expect("close");
    let passage = builder.finish().expect("finish");
    // memset + 4 × (kernel + census) = 9 nodes; edges: memset→enter (1), enter.census→{scale,
    // hadamard, re-entry} (3), kernel→census (4) = 8.
    assert_eq!(passage.intended(), (9, 8));
    assert_eq!(
        passage.graph_census().nodes,
        9,
        "{:?}",
        passage.graph_census()
    );
    assert_eq!(
        passage.graph_census().edges,
        8,
        "{:?}",
        passage.graph_census()
    );
    assert_eq!(passage.graph_census().kernel_nodes, 8);
    assert_eq!(passage.graph_census().memset_nodes, 1);
    let reading = passage.launch().expect("launch");
    assert!(reading.obstruction.is_empty());
    assert_eq!(
        reading.slots[2].lineage_inspected, 1,
        "a doubled bond is one predecessor slot, read once"
    );
    let unit = 1i64 << 20;
    assert_eq!(
        surface.read_out(&scaled).expect("read"),
        vec![
            (2 * unit, 2 * unit),
            (4 * unit, 4 * unit),
            (unit, unit),
            (-3 * unit, -3 * unit)
        ]
    );
    let sq = surface.read_out(&squared).expect("read");
    assert_eq!(sq[3], (9 * unit / 4, 9 * unit / 4));
    assert_eq!(
        surface.read_out(&doubled).expect("read")[1],
        (4 * unit, 4 * unit)
    );
    // Launching the same bound passage again returns the same faces: it is a graph, not a replay.
    let again = passage.launch().expect("launch again");
    assert_eq!(again.slots, reading.slots);
    assert_eq!(
        surface.read_out(&scaled).expect("read")[0],
        (2 * unit, 2 * unit)
    );
}

#[test]
fn a_refuted_a_priori_bound_refuses_downstream_on_the_card_and_names_the_occurrence() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let grain = ResidentGrain(20);
    let staged = surface.stage_words(&[TWO], 1, 1).expect("stage");
    let x = surface.fresh_section(1, 1, grain).expect("x");
    let y = surface.fresh_section(1, 1, grain).expect("y");
    let mut builder = surface.begin_passage(&[vec![], vec![0]]).expect("begin");
    let lane = builder.open(0, &[]).expect("open");
    surface
        .record_enter(&lane, &staged, Dyadic::ONE, &x)
        .expect("enter");
    // Admit the entry at 3 octaves; the word 2·2^20 occupies 22. The census must refute it.
    builder.close(0, &x, 3).expect("close");
    let lane = builder.open(1, &[0]).expect("open");
    surface
        .record_scale(
            &lane,
            &x,
            DyadicEnclosure {
                lo: 2,
                hi: 2,
                grain: 0,
            },
            &y,
        )
        .expect("scale");
    builder.close(1, &y, 30).expect("close");
    let passage = builder.finish().expect("finish");
    let reading = passage.launch().expect("launch");
    assert!(reading.slots[0].bound_violated);
    assert!(matches!(
        reading.slots[0].refusal("enter", 3),
        Some(ResidentRefusal::BoundRefuted {
            admitted: 3,
            measured: 22,
            ..
        })
    ));
    assert!(matches!(
        reading.slots[1].refusal("scale", 30),
        Some(ResidentRefusal::Upstream { .. })
    ));
    assert_eq!(reading.slots[1].upstream_first, Some(0));
    assert_eq!(reading.slots[1].upstream_count, 1);
    assert_eq!(
        reading.slots[1].upstream_flags & REFUSED_BOUND,
        REFUSED_BOUND
    );
    let lineage = &reading.obstruction;
    assert_eq!(lineage.refusals.len(), 2);
    assert!(lineage.refusals[0].origin && lineage.refusals[0].index == 0);
    assert!(
        !lineage.refusals[1].origin
            && lineage.refusals[1].index == 1
            && lineage.refusals[1].upstream_first == Some(0)
    );
    assert!(lineage.joined_flags() & (REFUSED_BOUND | REFUSED_UPSTREAM) != 0);
    // The successor wrote nothing plausible: its section holds only what allocation left, and
    // its census marker still says the census ran.
    assert!(reading.slots[1].written);
}

#[test]
fn the_rms_rebase_encloses_the_exact_value_and_a_finer_grain_nests() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let coarse = ResidentGrain(24);
    let fine = ResidentGrain(40);
    let eps = Dyadic {
        significand: 1,
        exponent: -30,
    };
    let radicand = rat(25, 2) + eps.value();
    let mut runs = Vec::new();
    for grain in [coarse, fine] {
        let staged = surface.stage_words(&[THREE, FOUR], 1, 2).expect("stage");
        let enter = surface
            .shape_enter(1, 2, Dyadic::ONE, grain, &[THREE, FOUR])
            .expect("shape");
        let rms = surface
            .shape_rms_rebase(1, 2, 2, grain.0 + 3, None)
            .expect("shape");
        assert!(
            rms.couplings
                .iter()
                .any(|c| c.coupling.contains("quadratic"))
        );
        let x = surface.fresh_section(1, 2, grain).expect("x");
        let y = surface.fresh_section(1, 2, grain).expect("y");
        let mut builder = surface.begin_passage(&[vec![], vec![0]]).expect("begin");
        let lane = builder.open(0, &[]).expect("open");
        surface
            .record_enter(&lane, &staged, Dyadic::ONE, &x)
            .expect("enter");
        builder.close(0, &x, enter.needed).expect("close");
        let lane = builder.open(1, &[0]).expect("open");
        surface
            .record_rms_rebase(&lane, &x, 2, None, eps, &rms, &y)
            .expect("rms");
        builder.close(1, &y, rms.needed).expect("close");
        let passage = builder.finish().expect("finish");
        let reading = passage.launch().expect("launch");
        assert!(reading.obstruction.is_empty(), "{:?}", reading.slots);
        assert!(reading.slots[1].written);
        let out = surface.read_out(&y).expect("read");
        for (enclosure, x) in out.iter().zip([rat(3, 1), rat(4, 1)]) {
            let lo = word_value(enclosure.0, grain);
            let hi = word_value(enclosure.1, grain);
            assert!(lo >= Rat::from_integer(BigInt::from(0)));
            assert!(
                &lo * &lo * &radicand <= &x * &x,
                "lower bound below the value"
            );
            assert!(
                &hi * &hi * &radicand >= &x * &x,
                "upper bound above the value"
            );
        }
        runs.push(
            out.into_iter()
                .map(|(l, h)| (word_value(l, grain), word_value(h, grain)))
                .collect::<Vec<_>>(),
        );
    }
    for ((cl, ch), (fl, fh)) in runs[0].iter().zip(&runs[1]) {
        assert!(cl <= fl && fh <= ch, "finer grain must nest");
        assert!(fh - fl < ch - cl, "and be strictly narrower");
    }
}

#[test]
fn the_tanh_adjoint_factor_encloses_one_minus_the_square_and_the_placement_is_exact() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let grain = ResidentGrain(24);
    // t = 3/4 exactly: 1 − t² = 7/16.
    let unit = 1i64 << grain.0;
    let t = surface
        .mount_section_rest(&ResidentSectionRest {
            rows: 1,
            width: 2,
            grain,
            bound_octaves: grain.0 + 1,
            intervals: vec![(3 * unit / 4, 3 * unit / 4), (-unit / 2, -unit / 2)],
        })
        .expect("mount");
    let shape = surface
        .shape_one_minus_square(1, 2, grain.0 + 1, grain)
        .expect("shape");
    let g = surface.fresh_section(1, 2, grain).expect("g");
    let placed = surface.fresh_section(1, 5, grain).expect("placed");
    let place = surface
        .shape_place_columns(1, 2, 5, 2, grain.0 + 1)
        .expect("shape");
    let mut builder = surface.begin_passage(&[vec![], vec![0]]).expect("begin");
    let lane = builder.open(0, &[]).expect("open");
    surface.record_one_minus_square(&lane, &t, &g).expect("record");
    builder.close(0, &g, shape.needed).expect("close");
    let lane = builder.open(1, &[0]).expect("open");
    surface.record_place_columns(&lane, &g, 2, &placed).expect("place");
    builder.close(1, &placed, place.needed).expect("close");
    let reading = builder.finish().expect("finish").launch().expect("launch");
    assert!(reading.obstruction.is_empty(), "{:?}", reading.slots);
    let out = surface.read_out(&g).expect("read");
    assert_eq!(out[0], (7 * unit / 16, 7 * unit / 16));
    assert_eq!(out[1], (3 * unit / 4, 3 * unit / 4));
    let placed = surface.read_out(&placed).expect("read");
    assert_eq!(placed, vec![(0, 0), (0, 0), out[0], out[1], (0, 0)]);
}

#[test]
fn the_gelu_derivative_encloses_one_half_at_zero_and_a_finer_grain_nests() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let c1 = Dyadic::of_binary64_bits(0x3fe9_8845_33d4_3651).expect("c1");
    let c2 = Dyadic::of_binary64_bits(0x3fa6_e4e2_6d48_01f7).expect("c2");
    let terms = SeriesAperture(14);
    let mut runs = Vec::new();
    for grain in [ResidentGrain(24), ResidentGrain(40)] {
        let unit = 1i64 << grain.0;
        let x = surface
            .mount_section_rest(&ResidentSectionRest {
                rows: 1,
                width: 2,
                grain,
                bound_octaves: grain.0 + 1,
                intervals: vec![(0, 0), (unit, unit)],
            })
            .expect("mount");
        let shape = surface
            .shape_gelu_tanh_derivative(1, 2, grain.0 + 1, grain, c1, c2, terms)
            .expect("shape");
        let y = surface.fresh_section(1, 2, grain).expect("y");
        let mut builder = surface.begin_passage(&[vec![]]).expect("begin");
        let lane = builder.open(0, &[]).expect("open");
        surface
            .record_gelu_tanh_derivative(&lane, &x, c1, c2, terms, &y)
            .expect("record");
        builder.close(0, &y, shape.needed).expect("close");
        let reading = builder.finish().expect("finish").launch().expect("launch");
        assert!(reading.obstruction.is_empty(), "{:?}", reading.slots);
        let out = surface.read_out(&y).expect("read");
        // y'(0) = ½ exactly.
        assert!(out[0].0 <= unit / 2 && unit / 2 <= out[0].1, "{:?}", out[0]);
        assert!(out[0].1 - out[0].0 <= 4, "{:?}", out[0]);
        // y'(1) lies in (1.08, 1.09).
        assert!(out[1].0 > unit + unit / 13 && out[1].1 < unit + unit / 11, "{:?}", out[1]);
        runs.push(
            out.into_iter()
                .map(|(l, h)| (word_value(l, grain), word_value(h, grain)))
                .collect::<Vec<_>>(),
        );
    }
    for ((cl, ch), (fl, fh)) in runs[0].iter().zip(&runs[1]) {
        assert!(cl <= fl && fh <= ch, "finer grain must nest");
    }
}

#[test]
fn the_rms_adjoint_encloses_the_exact_derivative_and_a_finer_grain_nests() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let eps = Dyadic {
        significand: 1,
        exponent: -30,
    };
    // x = (3, 4), dy = (1, 0), no gain, n = 2:  rad = 25/2 + eps,  r = rad^{-1/2},
    //   dx_0 = r (1 − 9/2 / rad) = r · (rad − 9/2) / rad,   dx_1 = −6 r / rad.
    let radicand = rat(25, 2) + eps.value();
    let c0 = (&radicand - rat(9, 2)) / &radicand;
    let m1 = rat(6, 1) / &radicand;
    let mut runs = Vec::new();
    for grain in [ResidentGrain(24), ResidentGrain(40)] {
        let unit = 1i64 << grain.0;
        let x = surface
            .mount_section_rest(&ResidentSectionRest {
                rows: 1,
                width: 2,
                grain,
                bound_octaves: grain.0 + 3,
                intervals: vec![(3 * unit, 3 * unit), (4 * unit, 4 * unit)],
            })
            .expect("x");
        let dy = surface
            .mount_section_rest(&ResidentSectionRest {
                rows: 1,
                width: 2,
                grain,
                bound_octaves: grain.0 + 1,
                intervals: vec![(unit, unit), (0, 0)],
            })
            .expect("dy");
        let shape = surface
            .shape_rms_rebase_adjoint(1, 2, 2, grain.0 + 3, grain.0 + 1, None)
            .expect("shape");
        let dx = surface.fresh_section(1, 2, grain).expect("dx");
        let mut builder = surface.begin_passage(&[vec![]]).expect("begin");
        let lane = builder.open(0, &[]).expect("open");
        surface
            .record_rms_rebase_adjoint(&lane, &x, &dy, 2, None, eps, &shape, &dx)
            .expect("record");
        builder.close(0, &dx, shape.needed).expect("close");
        let reading = builder.finish().expect("finish").launch().expect("launch");
        assert!(reading.obstruction.is_empty(), "{:?}", reading.slots);
        let out = surface.read_out(&dx).expect("read");
        let zero = Rat::from_integer(BigInt::from(0));
        // dx_0 = r · c0 > 0:  lo ≤ r c0  ⟺  lo² · rad ≤ c0²  (lo ≥ 0), and hi² · rad ≥ c0².
        let (lo, hi) = (word_value(out[0].0, grain), word_value(out[0].1, grain));
        assert!(lo >= zero, "dx_0 lower endpoint negative: {:?}", out[0]);
        assert!(&lo * &lo * &radicand <= &c0 * &c0, "dx_0 lower bound above the value");
        assert!(&hi * &hi * &radicand >= &c0 * &c0, "dx_0 upper bound below the value");
        // dx_1 = −m1 r < 0:  (−lo)² · rad ≥ m1², and if hi ≤ 0 then (−hi)² · rad ≤ m1².
        let (lo, hi) = (word_value(out[1].0, grain), word_value(out[1].1, grain));
        let neg_lo = -lo;
        assert!(neg_lo >= zero, "dx_1 lower endpoint positive: {:?}", out[1]);
        assert!(&neg_lo * &neg_lo * &radicand >= &m1 * &m1, "dx_1 lower bound above the value");
        if hi <= zero {
            let neg_hi = -hi;
            assert!(&neg_hi * &neg_hi * &radicand <= &m1 * &m1, "dx_1 upper bound below the value");
        }
        runs.push(
            out.into_iter()
                .map(|(l, h)| (word_value(l, grain), word_value(h, grain)))
                .collect::<Vec<_>>(),
        );
    }
    for ((cl, ch), (fl, fh)) in runs[0].iter().zip(&runs[1]) {
        assert!(cl <= fl && fh <= ch, "finer grain must nest");
    }
}

#[test]
fn the_contact_adjoint_returns_exact_dyadics_when_the_weights_are_exact() {
    let Some((_, surface)) = surface() else {
        return;
    };
    // Two rows, one head of width two, complete reach.  Equal keys make row one's two scores
    // equal, so its weights are exactly ½ each and every adjoint is an exact dyadic:
    //   dw_10 = ⟨do_1, v_0⟩ = 2, dw_11 = 0, M_1 = 1, ds_10 = ½, ds_11 = −½,
    //   dq_1 = ½ k_0 − ½ k_1 = 0, dk_0 = ½ q_1 = (½, 0), dk_1 = (−½, 0),
    //   dv_0 = w_00 do_0 + w_10 do_1 = (½, 0), dv_1 = (½, 0); row zero returns nothing.
    let grain = ResidentGrain(24);
    let unit = 1i64 << grain.0;
    let point = |values: &[i64]| -> Vec<(i64, i64)> {
        values.iter().map(|value| (value * unit, value * unit)).collect()
    };
    let mount = |values: &[i64]| {
        surface
            .mount_section_rest(&ResidentSectionRest {
                rows: 2,
                width: 2,
                grain,
                bound_octaves: grain.0 + 2,
                intervals: point(values),
            })
            .expect("mount")
    };
    let q = mount(&[0, 0, 1, 0]);
    let k = mount(&[1, 1, 1, 1]);
    let v = mount(&[2, 0, 0, 2]);
    let d = mount(&[0, 0, 1, 0]);
    let terms = SeriesAperture(14);
    let shape = surface
        .shape_contact_adjoint_queries(2, 1, 1, 2, 2, terms, grain, grain.0 + 2, grain.0 + 2, grain.0 + 2, grain.0 + 2)
        .expect("shape");
    let family = surface
        .shape_contact_adjoint_family(2, 1, 1, 2, 2, grain, grain.0 + 2, grain.0 + 2)
        .expect("shape");
    let dq = surface.fresh_section(2, 2, grain).expect("dq");
    let dk = surface.fresh_section(2, 2, grain).expect("dk");
    let dv = surface.fresh_section(2, 2, grain).expect("dv");
    let weights = surface.fresh_section(2, 2, grain).expect("w");
    let differentials = surface.fresh_section(2, 2, grain).expect("ds");
    let mut builder = surface.begin_passage(&[vec![], vec![0], vec![0]]).expect("begin");
    let lane = builder.open(0, &[]).expect("open");
    surface
        .record_contact_adjoint_queries(&lane, &q, &k, &v, &d, 1, 1, 2, 2, terms, &shape, &dq, &weights, &differentials)
        .expect("queries");
    builder.close(0, &dq, shape.needed).expect("close");
    let lane = builder.open(1, &[0]).expect("open");
    surface
        .record_contact_adjoint_family(&lane, &q, &differentials, 1, 1, 2, 2, false, &dk)
        .expect("keys");
    builder.close(1, &dk, family.needed).expect("close");
    let lane = builder.open(2, &[0]).expect("open");
    surface
        .record_contact_adjoint_family(&lane, &d, &weights, 1, 1, 2, 2, true, &dv)
        .expect("values");
    builder.close(2, &dv, family.needed).expect("close");
    let reading = builder.finish().expect("finish").launch().expect("launch");
    assert!(reading.obstruction.is_empty(), "{:?}", reading.slots);
    let half = unit / 2;
    let contains = |enclosure: (i64, i64), value: i64| enclosure.0 <= value && value <= enclosure.1 && enclosure.1 - enclosure.0 <= 8;
    let dq = surface.read_out(&dq).expect("dq");
    assert!(dq.iter().all(|enclosure| contains(*enclosure, 0)), "{dq:?}");
    let dk = surface.read_out(&dk).expect("dk");
    assert!(contains(dk[0], half) && contains(dk[1], 0), "{dk:?}");
    assert!(contains(dk[2], -half) && contains(dk[3], 0), "{dk:?}");
    let dv = surface.read_out(&dv).expect("dv");
    assert!(contains(dv[0], half) && contains(dv[1], 0), "{dv:?}");
    assert!(contains(dv[2], half) && contains(dv[3], 0), "{dv:?}");
}

fn candidate(
    tile: TileGeometry,
    registers: u32,
    resident_blocks: u32,
    shared: u32,
) -> LaunchCandidate {
    LaunchCandidate {
        tile,
        symbol: "section_contract_tiled_r1_l32",
        block: tile.block(),
        shared_octets: shared,
        registers,
        local_octets: 0,
        resident_blocks,
        occupancy: (resident_blocks * tile.block(), 1536),
        blocks: 512,
        residency_waves: (512, u64::from(resident_blocks) * 80),
        lane_waves: (512 * u64::from(tile.block()), 122_880),
        serial_k_per_lane: 2560 / u64::from(tile.lanes),
        dependency_span: 2560 / u64::from(tile.lanes) + 5,
        bound_by: "registers",
    }
}

#[test]
fn a_contract_tiled_geometry_outside_the_emitted_family_refuses_by_name() {
    // the module carries an entry for (T_t, L) = (1, 32) and none for (3, 32)
    let admitted = TileGeometry {
        tile_rows: 1,
        lanes: 32,
        outs_per_block: 4,
        k_tile: 256,
        splits: 1,
    };
    assert_eq!(
        admitted.symbol("contract-tiled").expect("emitted"),
        "section_contract_tiled_r1_l32"
    );
    assert_eq!(admitted.block(), 128);
    assert_eq!(admitted.shared_octets(), 1 * 256 * 16);
    let unemitted = TileGeometry {
        tile_rows: 3,
        lanes: 32,
        outs_per_block: 4,
        k_tile: 256,
        splits: 1,
    };
    assert!(matches!(
        unemitted.symbol("contract-tiled"),
        Err(ResidentRefusal::Declaration { .. })
    ));
    // a partial block of lanes, a lane count past the warp, a split that is not a power of two,
    // a block past the module's ceiling and a staged tile past the device — each refuses, and
    // each names which aperture it left
    assert!(
        TileGeometry {
            tile_rows: 1,
            lanes: 8,
            outs_per_block: 3,
            k_tile: 0,
            splits: 1
        }
        .admit("t", 512, 32, 49_152)
        .is_err()
    );
    assert!(
        TileGeometry {
            tile_rows: 1,
            lanes: 64,
            outs_per_block: 1,
            k_tile: 0,
            splits: 1
        }
        .admit("t", 512, 32, 49_152)
        .is_err()
    );
    assert!(
        TileGeometry {
            tile_rows: 1,
            lanes: 32,
            outs_per_block: 4,
            k_tile: 0,
            splits: 3
        }
        .admit("t", 512, 32, 49_152)
        .is_err()
    );
    assert!(
        TileGeometry {
            tile_rows: 1,
            lanes: 32,
            outs_per_block: 32,
            k_tile: 0,
            splits: 1
        }
        .admit("t", 512, 32, 49_152)
        .is_err()
    );
    assert!(
        TileGeometry {
            tile_rows: 4,
            lanes: 32,
            outs_per_block: 4,
            k_tile: 1024,
            splits: 1
        }
        .admit("t", 512, 32, 49_152)
        .is_err()
    );
    assert!(admitted.admit("t", 512, 32, 49_152).is_ok());
    // the blocks the geometry launches, including both tails
    assert_eq!(admitted.blocks(5, 2048), 512 * 5);
    assert_eq!(admitted.blocks(3, 2049), 513 * 3);
    let split = TileGeometry {
        tile_rows: 1,
        lanes: 32,
        outs_per_block: 4,
        k_tile: 256,
        splits: 8,
    };
    assert_eq!(split.blocks(1, 512), 128 * 8);
    assert_eq!(
        split.symbol("contract-split-k").expect("emitted"),
        "section_contract_partial_r1_l32"
    );
}

#[test]
fn the_contract_tiled_candidate_family_is_finite_and_the_retained_set_moves_with_the_declared_axes()
{
    // every enumerated member is a whole-warp block the device could carry
    let family = TileGeometry::enumerate();
    assert!(!family.is_empty());
    for tile in &family {
        assert_eq!(tile.block() % 32, 0);
        assert!(tile.block() <= 512);
        assert!(tile.shared_octets() <= 49_152);
    }
    // domination is the receiver's declaration, and the retained set moves when it changes
    let candidates = vec![
        candidate(
            TileGeometry {
                tile_rows: 1,
                lanes: 32,
                outs_per_block: 4,
                k_tile: 0,
                splits: 1,
            },
            40,
            10,
            0,
        ),
        candidate(
            TileGeometry {
                tile_rows: 4,
                lanes: 32,
                outs_per_block: 4,
                k_tile: 256,
                splits: 1,
            },
            64,
            6,
            16_384,
        ),
        candidate(
            TileGeometry {
                tile_rows: 2,
                lanes: 32,
                outs_per_block: 4,
                k_tile: 0,
                splits: 1,
            },
            47,
            9,
            0,
        ),
    ];
    let coarse = non_dominated(
        &candidates,
        &[CandidateAxis::ResidentBlocksUp, CandidateAxis::SharedDown],
    );
    // the four-row tile is dominated on both coarse axes by the one-row tile
    assert_eq!(coarse, vec![0]);
    let with_reuse = non_dominated(
        &candidates,
        &[
            CandidateAxis::ResidentBlocksUp,
            CandidateAxis::SharedDown,
            CandidateAxis::MapReuseUp,
        ],
    );
    assert_eq!(with_reuse, vec![0, 1, 2]);
    // and a declaration that reads only one axis retains only its extremum
    assert_eq!(
        non_dominated(&candidates, &[CandidateAxis::MapReuseUp]),
        vec![1]
    );
}

#[test]
fn the_contract_tiled_shape_admits_exactly_what_the_scalar_owner_admits_and_prices_the_tile_beside_it()
 {
    let Some((readout, surface)) = surface() else {
        return;
    };
    let map = readout
        .mount_bfloat16(&[ONE, TWO, MINUS_ONE_AND_HALF, HALF], 2)
        .expect("map");
    let scalar = surface
        .shape_contract(1, 2, 22, &map)
        .expect("scalar shape");
    let tile = TileGeometry {
        tile_rows: 1,
        lanes: 32,
        outs_per_block: 4,
        k_tile: 256,
        splits: 1,
    };
    let tiled = surface
        .shape_contract_tiled(1, 2, 22, &map, tile)
        .expect("tiled shape");
    // the same octave admission, by the subset-monotone argument, and the same output shape
    assert_eq!(tiled.needed, scalar.needed);
    assert_eq!((tiled.rows, tiled.width), (scalar.rows, scalar.width));
    // and the apparatus beside it: the tile's block, its staged extent, its launches
    assert_eq!(tiled.block, 128);
    assert_eq!(tiled.shared_octets, 4_096);
    assert_eq!(tiled.launches, 2);
    assert_eq!(tiled.couplings.len(), 1);
    // a split-K geometry records three launches, because the join is the third
    let split = TileGeometry {
        tile_rows: 1,
        lanes: 32,
        outs_per_block: 4,
        k_tile: 256,
        splits: 4,
    };
    assert_eq!(
        surface
            .shape_contract_tiled(1, 2, 22, &map, split)
            .expect("split shape")
            .launches,
        3
    );
    // a geometry the module emits no entry for refuses at the shape, before any launch
    let unemitted = TileGeometry {
        tile_rows: 8,
        lanes: 32,
        outs_per_block: 4,
        k_tile: 256,
        splits: 1,
    };
    assert!(
        surface
            .shape_contract_tiled(1, 2, 22, &map, unemitted)
            .is_err()
    );
    // a width that disagrees with the map refuses by name
    assert!(surface.shape_contract_tiled(1, 3, 22, &map, tile).is_err());
}

#[test]
fn the_contract_tiled_family_reads_its_registers_from_the_loaded_module() {
    let Some((_, surface)) = surface() else {
        return;
    };
    // every emitted entry answers, and the scalar owner's own measured count stands beside them
    for symbol in [
        "section_contract",
        "section_contract_tiled_r1_l32",
        "section_contract_tiled_r4_l32",
        "section_contract_partial_r1_l32",
        "section_contract_join",
    ] {
        let registers = surface.measured_registers(symbol).expect("registers");
        assert!(
            registers > 0 && registers <= 255,
            "{symbol} reported {registers} registers"
        );
    }
    // the module-wide block derivation did not move when the family was added
    assert_eq!(surface.derived_launch().0, 512);
    for symbol in KERNELS {
        assert!(
            surface.measured_block_ceiling(symbol).expect("ceiling") >= 512,
            "{symbol} admits fewer than 512 threads"
        );
    }
    let limits = surface.multiprocessor_limits();
    assert!(limits.max_blocks > 0 && limits.max_registers > 0 && limits.max_shared_octets > 0);
    let family = surface.contract_candidates(5, 2560, 2048).expect("family");
    assert!(!family.is_empty());
    for member in &family {
        assert!(
            member.resident_blocks >= 1,
            "{member:?} is resident nowhere"
        );
        assert!(member.registers > 0);
    }
}

#[test]
fn a_contract_tiled_return_is_bit_equal_to_the_scalar_owner_and_the_reversed_tree_agrees() {
    let Some((readout, surface)) = surface() else {
        return;
    };
    let map = readout
        .mount_bfloat16(&[ONE, TWO, MINUS_ONE_AND_HALF, HALF], 2)
        .expect("map");
    let grain = ResidentGrain(20);
    let staged = surface.stage_words(&[ONE, TWO], 1, 2).expect("stage");
    let enter = surface
        .shape_enter(1, 2, Dyadic::ONE, grain, &[ONE, TWO])
        .expect("shape");
    let scalar_shape = surface
        .shape_contract(1, 2, enter.needed.min(22), &map)
        .expect("shape");
    let tile = TileGeometry {
        tile_rows: 1,
        lanes: 32,
        outs_per_block: 2,
        k_tile: 128,
        splits: 1,
    };
    let tiled_shape = surface
        .shape_contract_tiled(1, 2, enter.needed.min(22), &map, tile)
        .expect("shape");
    let x = surface.fresh_section(1, 2, grain).expect("x");
    let scalar_out = surface.fresh_section(1, 2, grain).expect("scalar");
    let descending = surface.fresh_section(1, 2, grain).expect("descending");
    let ascending = surface.fresh_section(1, 2, grain).expect("ascending");
    let mut builder = surface
        .begin_passage(&[vec![], vec![0], vec![0], vec![0]])
        .expect("begin");
    let lane = builder.open(0, &[]).expect("open");
    surface
        .record_enter(&lane, &staged, Dyadic::ONE, &x)
        .expect("enter");
    builder.close(0, &x, enter.needed).expect("close");
    let lane = builder.open(1, &[0]).expect("open");
    surface
        .record_contract(&lane, &x, &map, &scalar_out)
        .expect("scalar");
    builder
        .close(1, &scalar_out, scalar_shape.needed)
        .expect("close");
    let lane = builder.open(2, &[0]).expect("open");
    surface
        .record_contract_tiled(
            &lane,
            &x,
            &map,
            tile,
            ResidentSurface::carrier_octaves(),
            LaneTree::Descending,
            &descending,
        )
        .expect("tiled");
    builder
        .close(2, &descending, tiled_shape.needed)
        .expect("close");
    let lane = builder.open(3, &[0]).expect("open");
    surface
        .record_contract_tiled(
            &lane,
            &x,
            &map,
            tile,
            ResidentSurface::carrier_octaves(),
            LaneTree::Ascending,
            &ascending,
        )
        .expect("tiled");
    builder
        .close(3, &ascending, tiled_shape.needed)
        .expect("close");
    let passage = builder.finish().expect("finish");
    let reading = passage.launch().expect("launch");
    assert!(reading.obstruction.is_empty(), "{:?}", reading.obstruction);
    let scalar_words = surface.read_out(&scalar_out).expect("read");
    assert_eq!(surface.read_out(&descending).expect("read"), scalar_words);
    assert_eq!(surface.read_out(&ascending).expect("read"), scalar_words);
    // the census words of the three occurrences agree, not only the sections
    for at in [2usize, 3] {
        assert_eq!(reading.slots[at].max_octave, reading.slots[1].max_octave);
        assert_eq!(reading.slots[at].max_width, reading.slots[1].max_width);
        assert_eq!(reading.slots[at].width_sum, reading.slots[1].width_sum);
        assert_eq!(
            reading.slots[at].nonzero_widths,
            reading.slots[1].nonzero_widths
        );
        assert_eq!(reading.slots[at].refused, reading.slots[1].refused);
    }
}

#[test]
fn a_declared_site_population_is_withdrawn_at_every_row_out_of_place() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let grain = ResidentGrain(20);
    let rest = ResidentSectionRest::found(
        2,
        4,
        grain,
        4,
        vec![(1, 1), (2, 2), (-3, -3), (4, 5), (5, 5), (-6, -6), (7, 7), (8, 8)],
    )
    .expect("rest");
    let input = surface.mount_section_rest(&rest).expect("mount");
    let withdraw = |mask: &SiteMask<'static>, offset: usize| {
        let shape = surface.shape_withdraw_sites(2, 4, 4).expect("shape");
        let out = surface.fresh_section(2, 4, grain).expect("section");
        let mut builder = surface.begin_passage(&[vec![]]).expect("begin");
        let lane = builder.open(0, &[]).expect("open");
        surface
            .record_withdraw_sites(&lane, &input, mask, offset, &out)
            .expect("record");
        builder.close(0, &out, shape.needed).expect("close");
        let reading = builder.finish().expect("finish").launch().expect("launch");
        assert!(reading.obstruction.is_empty());
        surface.read_out(&out).expect("read")
    };
    let mask = surface
        .mount_site_mask(&[false, true, false, true])
        .expect("mask");
    assert_eq!(mask.withdrawn(), 2);
    assert_eq!(
        withdraw(&mask, 0),
        vec![(1, 1), (0, 0), (-3, -3), (0, 0), (5, 5), (0, 0), (7, 7), (0, 0)]
    );
    // The predecessor is untouched: the intervention is out of place.
    assert_eq!(surface.read_out(&input).expect("read"), rest.intervals);
    // A tile reads its own span of one wider mask through an offset.
    let wide = surface
        .mount_site_mask(&[true, true, false, false, true, false])
        .expect("mask");
    assert_eq!(
        withdraw(&wide, 2),
        vec![(1, 1), (2, 2), (0, 0), (4, 5), (5, 5), (-6, -6), (0, 0), (8, 8)]
    );
    // A span past the mask's sites is refused before anything is recorded.
    let out = surface.fresh_section(2, 4, grain).expect("section");
    let mut builder = surface.begin_passage(&[vec![]]).expect("begin");
    let lane = builder.open(0, &[]).expect("open");
    assert!(surface.record_withdraw_sites(&lane, &input, &mask, 1, &out).is_err());
}
