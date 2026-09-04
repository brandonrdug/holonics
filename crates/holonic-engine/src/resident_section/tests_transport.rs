use super::*;

#[test]
#[ignore = "requires CUDA; explicit partial-standing lifetime regression"]
fn releasing_partial_standings_keeps_no_replacement_allocation() {
    let readout = ResidentReadout::new().expect("CUDA readout");
    let surface = ResidentSurface::on(&readout).expect("resident surface");
    let before = surface.census().resident_octets_now;
    for _ in 0..64 {
        let standing = surface.retain_partials(2, 3, 16).expect("partial standing");
        surface.zero_partials(&standing).expect("zero standing");
        surface.release_partials(&standing).expect("release without allocating");
        assert!(surface.partials.borrow()[standing.index].is_none());
        assert!(surface.release_partials(&standing).is_err());
        assert!(surface.zero_partials(&standing).is_err());
        assert_eq!(surface.census().resident_octets_now, before);
    }
}

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
fn rank_one_factorized_front_is_bit_equal_to_sequential_contracts_on_common_i64_aperture() {
    let Some((readout, surface)) = surface() else {
        return;
    };
    // Thirty-three output rows force the complete front past one warp.  This fixture stays on
    // the common i64 aperture: the factors include negative entries, a zero row, and a
    // fractional input so both directed placements and the exact-zero branch are exercised.
    let u_words: Vec<u16> = (0..33)
        .map(|row| match row % 5 {
            0 => 0,
            1 => MINUS_ONE_AND_HALF,
            2 => TWO,
            3 => HALF,
            _ => bfloat16(-3, -1),
        })
        .collect();
    let u = readout.mount_bfloat16(&u_words, 1).expect("u=[V,1]");
    let v = readout
        .mount_bfloat16(&[MINUS_ONE_AND_HALF, TWO], 2)
        .expect("v=[1,H]");
    let grain = ResidentGrain(20);
    let staged = surface.stage_words(&[ONE, HALF], 1, 2).expect("stage h");
    let enter = surface
        .shape_enter(1, 2, Dyadic::ONE, grain, &[ONE, HALF])
        .expect("enter shape");
    let scalar = surface
        .shape_contract(1, 2, enter.needed, &v)
        .expect("v contract shape");
    let sequential = surface
        .shape_contract(1, 1, scalar.needed, &u)
        .expect("u contract shape");
    let fused = surface
        .shape_factorized_contract(1, 2, enter.needed, &u, &v, 1)
        .expect("factorized shape");
    assert_eq!((fused.rows, fused.width), (1, 33));
    assert!(fused.width >= 32);
    assert!(fused.shared_octets > 0 && fused.block >= 32);
    assert_eq!(
        fused.predicted.multiplications,
        &scalar.predicted.multiplications + &sequential.predicted.multiplications
    );
    assert!(
        fused.predicted.multiplications < BigUint::from(33u32 * 2u32),
        "the rank-one work must not be priced as a dense 33×2 product"
    );
    assert_eq!(
        fused.predicted.entries_written,
        &scalar.predicted.entries_written + &sequential.predicted.entries_written,
        "the internal scalar materialization remains in the work receipt"
    );
    let x = surface.fresh_section(1, 2, grain).expect("x");
    let scalar_out = surface.fresh_section(1, 1, grain).expect("scalar");
    let sequential_out = surface.fresh_section(1, 33, grain).expect("sequential");
    let fused_out = surface.fresh_section(1, 33, grain).expect("fused");
    let mut builder = surface
        .begin_passage(&[vec![], vec![0], vec![1], vec![0]])
        .expect("begin");
    let lane = builder.open(0, &[]).expect("enter lane");
    surface
        .record_enter(&lane, &staged, Dyadic::ONE, &x)
        .expect("record enter");
    builder.close(0, &x, enter.needed).expect("close enter");
    let lane = builder.open(1, &[0]).expect("v lane");
    surface
        .record_contract(&lane, &x, &v, &scalar_out)
        .expect("record v");
    builder
        .close(1, &scalar_out, scalar.needed)
        .expect("close v");
    let lane = builder.open(2, &[1]).expect("u lane");
    surface
        .record_contract(&lane, &scalar_out, &u, &sequential_out)
        .expect("record u");
    builder
        .close(2, &sequential_out, sequential.needed)
        .expect("close u");
    let lane = builder.open(3, &[0]).expect("fused lane");
    surface
        .record_factorized_contract(&lane, &x, &u, &v, &fused, &fused_out)
        .expect("record fused");
    builder
        .close(3, &fused_out, fused.needed)
        .expect("close fused");
    let reading = builder.finish().expect("finish").launch().expect("launch");
    assert!(
        reading.obstruction.is_empty(),
        "factorized passage refused: {:?}",
        reading.obstruction
    );
    assert_eq!(
        surface.read_out(&fused_out).expect("read fused"),
        surface.read_out(&sequential_out).expect("read sequential")
    );
    // The fused output has a complete resident extent, including the exact zero rows.
    assert_eq!(reading.slots[3].written, true);
    assert_eq!(
        reading.slots[3].nonzero_widths,
        reading.slots[2].nonzero_widths
    );
}

#[test]
fn derived_rank_front_is_the_exact_sum_of_its_rank_one_atoms() {
    let Some((readout, surface)) = surface() else {
        return;
    };
    // U=[[1,0],[0,1],[1,1]], V=[[2,0],[0,3]], h=[4,1].  The image rank is two and
    // U(Vh)=[8,3,11].  The sequential control materializes the junction while the derived
    // front keeps both atoms inside one semantic kernel.
    let u = readout
        .mount_bfloat16(&[ONE, 0, 0, ONE, ONE, ONE], 2)
        .expect("u=[3,2]");
    let v = readout
        .mount_bfloat16(&[TWO, 0, 0, THREE], 2)
        .expect("v=[2,2]");
    let grain = ResidentGrain(0);
    let staged = surface.stage_words(&[FOUR, ONE], 1, 2).expect("stage h");
    let enter = surface
        .shape_enter(1, 2, Dyadic::ONE, grain, &[FOUR, ONE])
        .expect("enter shape");
    let junction = surface
        .shape_contract(1, 2, enter.needed, &v)
        .expect("junction shape");
    let sequential = surface
        .shape_contract(1, 2, junction.needed, &u)
        .expect("sequential shape");
    let derived = surface
        .shape_factorized_contract(1, 2, enter.needed, &u, &v, 2)
        .expect("derived-rank shape");
    assert_eq!((derived.rows, derived.width), (1, 3));

    let x = surface.fresh_section(1, 2, grain).expect("x");
    let junction_out = surface.fresh_section(1, 2, grain).expect("junction");
    let sequential_out = surface.fresh_section(1, 3, grain).expect("sequential");
    let derived_out = surface.fresh_section(1, 3, grain).expect("derived");
    let mut builder = surface
        .begin_passage(&[vec![], vec![0], vec![1], vec![0]])
        .expect("begin");
    let lane = builder.open(0, &[]).expect("enter lane");
    surface
        .record_enter(&lane, &staged, Dyadic::ONE, &x)
        .expect("record enter");
    builder.close(0, &x, enter.needed).expect("close enter");
    let lane = builder.open(1, &[0]).expect("v lane");
    surface
        .record_contract(&lane, &x, &v, &junction_out)
        .expect("record v");
    builder
        .close(1, &junction_out, junction.needed)
        .expect("close v");
    let lane = builder.open(2, &[1]).expect("u lane");
    surface
        .record_contract(&lane, &junction_out, &u, &sequential_out)
        .expect("record u");
    builder
        .close(2, &sequential_out, sequential.needed)
        .expect("close u");
    let lane = builder.open(3, &[0]).expect("derived lane");
    surface
        .record_factorized_contract(&lane, &x, &u, &v, &derived, &derived_out)
        .expect("record derived");
    builder
        .close(3, &derived_out, derived.needed)
        .expect("close derived");
    let reading = builder.finish().expect("finish").launch().expect("launch");
    assert!(reading.obstruction.is_empty(), "{:?}", reading.obstruction);
    assert_eq!(
        surface.read_out(&derived_out).expect("read derived"),
        surface.read_out(&sequential_out).expect("read sequential")
    );
    assert_eq!(
        surface.read_out(&derived_out).expect("read derived"),
        vec![(8, 8), (3, 3), (11, 11)]
    );
}

#[test]
fn rank_one_factorized_front_keeps_a_wide_internal_scalar_that_sequential_i64_cannot() {
    let Some((readout, surface)) = surface() else {
        return;
    };
    // h = 2^40 and v = 2^40 produce a rounded scalar 2^80: it is inside the resident wide
    // carrier but outside the sequential Contract section's i64 word.  u = 2^-20 brings the
    // final factorized output back to 2^60, which fits the final i64 section exactly.
    let h_word = bfloat16(1, 40);
    let v = readout.mount_bfloat16(&[h_word], 1).expect("v=[1,1]");
    let u = readout
        .mount_bfloat16(&[bfloat16(1, -20)], 1)
        .expect("u=[1,1]");
    let grain = ResidentGrain(0);
    let staged = surface.stage_words(&[h_word], 1, 1).expect("stage h");
    let enter = surface
        .shape_enter(1, 1, Dyadic::ONE, grain, &[h_word])
        .expect("enter shape");
    let sequential_v = surface
        .shape_contract(1, 1, enter.needed, &v)
        .expect("sequential v shape");
    let fused = surface
        .shape_factorized_contract(1, 1, enter.needed, &u, &v, 1)
        .expect("wide factorized shape");
    assert!(sequential_v.needed <= ResidentSurface::carrier_octaves());
    assert!(fused.needed <= ResidentSurface::carrier_octaves());
    let positive_u = readout
        .mount_bfloat16(&[bfloat16(1, 60)], 1)
        .expect("positive u exponent");
    assert!(
        surface
            .shape_factorized_contract(1, 1, enter.needed, &positive_u, &v, 1)
            .is_err(),
        "a positive final u shift must be admitted against the wide carrier"
    );
    let x = surface.fresh_section(1, 1, grain).expect("x");
    let sequential_scalar = surface
        .fresh_section(1, 1, grain)
        .expect("sequential scalar");
    let fused_out = surface.fresh_section(1, 1, grain).expect("fused output");
    let mut builder = surface
        .begin_passage(&[vec![], vec![0], vec![0]])
        .expect("begin");
    let lane = builder.open(0, &[]).expect("enter lane");
    surface
        .record_enter(&lane, &staged, Dyadic::ONE, &x)
        .expect("record enter");
    builder.close(0, &x, enter.needed).expect("close enter");
    let lane = builder.open(1, &[0]).expect("sequential lane");
    surface
        .record_contract(&lane, &x, &v, &sequential_scalar)
        .expect("record sequential v");
    builder
        .close(1, &sequential_scalar, sequential_v.needed)
        .expect("close sequential v");
    let lane = builder.open(2, &[0]).expect("fused lane");
    surface
        .record_factorized_contract(&lane, &x, &u, &v, &fused, &fused_out)
        .expect("record fused");
    builder
        .close(2, &fused_out, fused.needed)
        .expect("close fused");
    let reading = builder.finish().expect("finish").launch().expect("launch");
    assert_eq!(
        reading.slots[1].refused & REFUSED_CARRIER,
        REFUSED_CARRIER,
        "sequential Contract must refuse its i64 intermediate"
    );
    assert_eq!(
        reading.slots[2].refused, 0,
        "the factorized wide junction must remain admitted"
    );
    assert_eq!(
        surface.read_out(&fused_out).expect("read fused"),
        vec![(1_i64 << 60, 1_i64 << 60)]
    );
}

#[test]
fn canonical_rank_one_gauge_admits_the_carrier_where_the_old_left_scale_reaches_the_horizon() {
    let Some((readout, surface)) = surface() else {
        return;
    };
    let mut entries = vec![0_i64; 4096];
    entries[0] = 1_i64 << 37;
    let old_v = readout
        .mount(
            &crate::embedding_fiber::AlignedMaterial {
                entries: entries.clone(),
                exponent: -46,
                entry_octaves: 38,
                negatives: 0,
            },
            4096,
        )
        .expect("old v");
    let canonical_v = readout
        .mount(
            &crate::embedding_fiber::AlignedMaterial {
                entries,
                exponent: -35,
                entry_octaves: 38,
                negatives: 0,
            },
            4096,
        )
        .expect("canonical v");
    let old_u = readout
        .mount(
            &crate::embedding_fiber::AlignedMaterial {
                entries: vec![1],
                exponent: 11,
                entry_octaves: 1,
                negatives: 0,
            },
            1,
        )
        .expect("old u");
    let canonical_u = readout
        .mount(
            &crate::embedding_fiber::AlignedMaterial {
                entries: vec![1],
                exponent: 0,
                entry_octaves: 1,
                negatives: 0,
            },
            1,
        )
        .expect("canonical u");
    let old = surface.shape_factorized_contract(1, 4096, 63, &old_u, &old_v, 1);
    let canonical = surface
        .shape_factorized_contract(1, 4096, 63, &canonical_u, &canonical_v, 1)
        .expect("canonical gauge admits");
    assert!(
        old.is_err(),
        "the old positive left scale must reach the wide carrier horizon"
    );
    assert!(canonical.needed < ResidentSurface::carrier_octaves());
}

#[test]
fn a_contract_tiled_node_aperture_refuses_where_the_scalar_owner_wraps_silently() {
    let Some((readout, surface)) = surface() else {
        return;
    };
    // a one-octave node aperture is narrower than any real accumulation: the tiled kernel
    // refuses at the node and names REFUSED_CARRIER; the scalar owner has no per-step check
    // at all and returns the same words it always did. That is the behavioural difference.
    let map = readout
        .mount_bfloat16(&[ONE, TWO, MINUS_ONE_AND_HALF, HALF], 2)
        .expect("map");
    let grain = ResidentGrain(20);
    let staged = surface.stage_words(&[ONE, TWO], 1, 2).expect("stage");
    let enter = surface
        .shape_enter(1, 2, Dyadic::ONE, grain, &[ONE, TWO])
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
    let out = surface.fresh_section(1, 2, grain).expect("out");
    let mut builder = surface.begin_passage(&[vec![], vec![0]]).expect("begin");
    let lane = builder.open(0, &[]).expect("open");
    surface
        .record_enter(&lane, &staged, Dyadic::ONE, &x)
        .expect("enter");
    builder.close(0, &x, enter.needed).expect("close");
    let lane = builder.open(1, &[0]).expect("open");
    surface
        .record_contract_tiled(&lane, &x, &map, tile, 1, LaneTree::Descending, &out)
        .expect("tiled");
    builder.close(1, &out, tiled_shape.needed).expect("close");
    let passage = builder.finish().expect("finish");
    let reading = passage.launch().expect("launch");
    assert_eq!(reading.slots[1].refused & REFUSED_CARRIER, REFUSED_CARRIER);
    assert!(
        reading
            .obstruction
            .origins()
            .any(|refusal| refusal.index == 1)
    );
}

#[test]
fn a_split_k_partial_is_exact_and_the_join_rounds_once() {
    let Some((readout, surface)) = surface() else {
        return;
    };
    // four inner coordinates, split two ways: each partial carries an exact 128-bit sum at the
    // product grain, and only the join places anything at the section's grain.
    let map_words = [ONE, TWO, THREE, FOUR, HALF, ONE, TWO, HALF];
    let map = readout.mount_bfloat16(&map_words, 4).expect("map");
    let grain = ResidentGrain(20);
    let staged = surface
        .stage_words(&[ONE, TWO, ONE, FOUR], 1, 4)
        .expect("stage");
    let enter = surface
        .shape_enter(1, 4, Dyadic::ONE, grain, &[ONE, TWO, ONE, FOUR])
        .expect("shape");
    let scalar_shape = surface
        .shape_contract(1, 4, enter.needed.min(24), &map)
        .expect("shape");
    let tile = TileGeometry {
        tile_rows: 1,
        lanes: 32,
        outs_per_block: 2,
        k_tile: 128,
        splits: 2,
    };
    let split_shape = surface
        .shape_contract_tiled(1, 4, enter.needed.min(24), &map, tile)
        .expect("shape");
    let standing = surface.retain_partials(1, 2, 2).expect("partials");
    let x = surface.fresh_section(1, 4, grain).expect("x");
    let scalar_out = surface.fresh_section(1, 2, grain).expect("scalar");
    let split_out = surface.fresh_section(1, 2, grain).expect("split");
    let mut builder = surface
        .begin_passage(&[vec![], vec![0], vec![0]])
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
        .record_contract_split_k(
            &lane,
            &x,
            &map,
            tile,
            &standing,
            ResidentSurface::carrier_octaves(),
            LaneTree::Descending,
            &split_out,
        )
        .expect("split");
    builder
        .close(2, &split_out, split_shape.needed)
        .expect("close");
    let passage = builder.finish().expect("finish");
    let reading = passage.launch().expect("launch");
    assert!(reading.obstruction.is_empty(), "{:?}", reading.obstruction);
    assert_eq!(
        surface.read_out(&split_out).expect("read"),
        surface.read_out(&scalar_out).expect("read")
    );
    // the partials themselves: two per output coordinate, and their exact sum is the whole
    let partials = surface.read_partials(&standing).expect("partials");
    assert_eq!(partials.len(), 2 * 1 * 2);
    for column in 0..2usize {
        let (a_lo, a_hi) = partials[column];
        let (b_lo, b_hi) = partials[2 + column];
        let whole_lo = a_lo + b_lo;
        let whole_hi = a_hi + b_hi;
        // the join's one rounding takes the exact sum at 2^(map_e − F) down to 2^-F
        let exponent = map.exponent();
        let floor = |value: i128| -> i128 {
            if exponent >= 0 {
                value << exponent
            } else {
                value >> (-exponent)
            }
        };
        let read = surface.read_out(&split_out).expect("read")[column];
        assert_eq!(
            floor(whole_lo),
            i128::from(read.0),
            "the lower word is the floor of the exact sum"
        );
        assert!(i128::from(read.1) >= floor(whole_hi));
    }
}

#[test]
fn a_contract_through_a_mounted_map_is_the_exact_product() {
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
    let contract = surface
        .shape_contract(1, 2, enter.needed.min(22), &map)
        .expect("shape");
    assert!(contract.needed <= ResidentSurface::carrier_octaves());
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
        .record_contract(&lane, &x, &map, &y)
        .expect("contract");
    builder.close(1, &y, contract.needed).expect("close");
    let passage = builder.finish().expect("finish");
    let reading = passage.launch().expect("launch");
    assert!(reading.obstruction.is_empty());
    let unit = 1i64 << 20;
    assert_eq!(
        surface.read_out(&y).expect("read"),
        vec![(5 * unit, 5 * unit), (-unit / 2, -unit / 2)]
    );
}

#[test]
fn the_contact_carries_a_convex_combination_inside_the_hull_and_the_negative_numerator_law_holds() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let grain = ResidentGrain(24);
    let q_words = [ONE, 0, ONE, 0];
    let v_words = [MINUS_ONE_AND_HALF, TWO, HALF, ONE];
    let sq = surface.stage_words(&q_words, 2, 2).expect("stage");
    let sk = surface.stage_words(&q_words, 2, 2).expect("stage");
    let sv = surface.stage_words(&v_words, 2, 2).expect("stage");
    let enter = surface
        .shape_enter(2, 2, Dyadic::ONE, grain, &q_words)
        .expect("shape");
    let contact = surface
        .shape_contact(
            2,
            2,
            2,
            2,
            1,
            1,
            2,
            512,
            SeriesAperture(12),
            grain,
            26,
            26,
            26,
        )
        .expect("shape");
    assert_eq!(contact.couplings.len(), 3);
    let q = surface.fresh_section(2, 2, grain).expect("q");
    let k = surface.fresh_section(2, 2, grain).expect("k");
    let v = surface.fresh_section(2, 2, grain).expect("v");
    let out = surface.fresh_section(2, 2, grain).expect("out");
    let mut builder = surface
        .begin_passage(&[vec![], vec![], vec![], vec![0, 1, 2]])
        .expect("begin");
    for (index, (staged, section)) in [(&sq, &q), (&sk, &k), (&sv, &v)].into_iter().enumerate() {
        let lane = builder.open(index, &[]).expect("open");
        surface
            .record_enter(&lane, staged, Dyadic::ONE, section)
            .expect("enter");
        builder.close(index, section, enter.needed).expect("close");
    }
    let lane = builder.open(3, &[0, 1, 2]).expect("open");
    surface
        .record_contact(
            &lane,
            &q,
            &k,
            &v,
            1,
            1,
            2,
            512,
            SeriesAperture(12),
            None,
            &contact,
            &out,
        )
        .expect("contact");
    builder.close(3, &out, contact.needed).expect("close");
    let passage = builder.finish().expect("finish");
    let reading = passage.launch().expect("launch");
    assert!(reading.obstruction.is_empty(), "{:?}", reading.slots);
    assert_eq!(reading.slots[3].lineage_inspected, 3);
    assert_eq!(reading.slots[3].reach, 2);
    let words = surface.read_out(&out).expect("read");
    let contains = |enclosure: (i64, i64), value: &Rat| {
        word_value(enclosure.0, grain) <= *value && *value <= word_value(enclosure.1, grain)
    };
    assert!(contains(words[0], &rat(-3, 2)) && words[0].0 == words[0].1);
    assert!(contains(words[1], &rat(2, 1)) && words[1].0 == words[1].1);
    assert!(contains(words[2], &rat(-1, 2)), "{:?}", words[2]);
    assert!(
        word_value(words[2].0, grain) >= rat(-3, 2) && word_value(words[2].1, grain) <= rat(1, 2)
    );
    assert!(contains(words[3], &rat(3, 2)), "{:?}", words[3]);
    assert!(
        words[2].1 - words[2].0 <= 1 && words[3].1 - words[3].0 <= 1,
        "{:?} {:?}",
        words[2],
        words[3]
    );
}

#[test]
fn partition_terminals_return_each_addressed_causal_endpoint_exactly() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let grain = ResidentGrain(20);
    let words = [ONE, TWO, THREE, FOUR];
    let staged = surface.stage_words(&words, 4, 1).expect("stage");
    let boundaries = surface.mount_positions(&[0, 2, 4]).expect("boundaries");
    let enter = surface
        .shape_enter(4, 1, Dyadic::ONE, grain, &words)
        .expect("enter shape");
    let terminals = surface
        .shape_partition_terminal_rows(4, 1, enter.needed, &[0, 2, 4])
        .expect("terminal shape");
    let entered = surface.fresh_section(4, 1, grain).expect("entered");
    let returned = surface.fresh_section(2, 1, grain).expect("returned");
    let mut builder = surface.begin_passage(&[vec![], vec![0]]).expect("begin");
    let lane = builder.open(0, &[]).expect("enter lane");
    surface
        .record_enter(&lane, &staged, Dyadic::ONE, &entered)
        .expect("enter");
    builder
        .close(0, &entered, enter.needed)
        .expect("close enter");
    let lane = builder.open(1, &[0]).expect("terminal lane");
    surface
        .record_partition_terminal_rows(&lane, &entered, &boundaries, &returned)
        .expect("terminals");
    builder
        .close(1, &returned, terminals.needed)
        .expect("close terminals");
    let reading = builder.finish().expect("finish").launch().expect("launch");
    assert!(reading.obstruction.is_empty(), "{:?}", reading.slots);
    let unit = 1i64 << grain.0;
    assert_eq!(
        surface.read_out(&returned).expect("read"),
        vec![(2 * unit, 2 * unit), (4 * unit, 4 * unit)]
    );
}

#[test]
fn partitioned_contact_cannot_cross_an_adjacent_section_boundary() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let grain = ResidentGrain(20);
    let unit_words = [ONE, ONE];
    let carried_words = [ONE, FOUR];
    let staged_q = surface.stage_words(&unit_words, 2, 1).expect("stage q");
    let staged_k = surface.stage_words(&unit_words, 2, 1).expect("stage k");
    let staged_v = surface.stage_words(&carried_words, 2, 1).expect("stage v");
    let boundaries = surface.mount_positions(&[0, 1, 2]).expect("boundaries");
    let enter = surface
        .shape_enter(2, 1, Dyadic::ONE, grain, &unit_words)
        .expect("enter shape");
    let contact = surface
        .shape_contact(
            2,
            1,
            1,
            1,
            1,
            1,
            1,
            2,
            SeriesAperture(2),
            grain,
            enter.needed,
            enter.needed,
            enter.needed,
        )
        .expect("contact shape");
    let q = surface.fresh_section(2, 1, grain).expect("q");
    let k = surface.fresh_section(2, 1, grain).expect("k");
    let v = surface.fresh_section(2, 1, grain).expect("v");
    let out = surface.fresh_section(2, 1, grain).expect("out");
    let mut builder = surface
        .begin_passage(&[vec![], vec![], vec![], vec![0, 1, 2]])
        .expect("begin");
    for (index, (staged, section)) in [(&staged_q, &q), (&staged_k, &k), (&staged_v, &v)]
        .into_iter()
        .enumerate()
    {
        let lane = builder.open(index, &[]).expect("enter lane");
        surface
            .record_enter(&lane, staged, Dyadic::ONE, section)
            .expect("enter");
        builder
            .close(index, section, enter.needed)
            .expect("close enter");
    }
    let lane = builder.open(3, &[0, 1, 2]).expect("contact lane");
    surface
        .record_contact(
            &lane,
            &q,
            &k,
            &v,
            1,
            1,
            1,
            2,
            SeriesAperture(2),
            Some(&boundaries),
            &contact,
            &out,
        )
        .expect("contact");
    builder
        .close(3, &out, contact.needed)
        .expect("close contact");
    let reading = builder.finish().expect("finish").launch().expect("launch");
    assert!(reading.obstruction.is_empty(), "{:?}", reading.slots);
    assert_eq!(reading.slots[3].reach, 1);
    let unit = 1i64 << grain.0;
    assert_eq!(
        surface.read_out(&out).expect("read"),
        vec![(unit, unit), (4 * unit, 4 * unit)]
    );
}

#[test]
fn partition_reach_removes_cross_section_accumulation_from_the_carrier_bound() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let rows = 1024;
    let full = surface.shape_contact(
        rows,
        1,
        1,
        1,
        1,
        1,
        1,
        rows,
        SeriesAperture(2),
        ResidentGrain(20),
        20,
        20,
        100,
    );
    assert!(matches!(full, Err(ResidentRefusal::CarrierRange { .. })));
    let partitioned = surface
        .shape_contact_with_declared_reach(
            rows,
            1,
            1,
            1,
            1,
            1,
            1,
            1,
            rows as u64,
            SeriesAperture(2),
            ResidentGrain(20),
            20,
            20,
            100,
        )
        .expect("one-row partition reach fits the physical carrier");
    assert_eq!(partitioned.needed, 122);
}

#[test]
fn the_contact_tiles_a_reach_larger_than_one_block_without_a_history_sized_shared_allocation() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let rows = 513;
    let width = 1;
    let grain = ResidentGrain(20);
    let words = vec![ONE; rows];
    let staged_q = surface.stage_words(&words, rows, width).expect("stage q");
    let staged_k = surface.stage_words(&words, rows, width).expect("stage k");
    let staged_v = surface.stage_words(&words, rows, width).expect("stage v");
    let enter = surface
        .shape_enter(rows, width, Dyadic::ONE, grain, &words)
        .expect("enter shape");
    let contact = surface
        .shape_contact(
            rows,
            width,
            width,
            width,
            1,
            1,
            1,
            rows,
            SeriesAperture(2),
            grain,
            enter.needed,
            enter.needed,
            enter.needed,
        )
        .expect("tiled contact shape");
    assert_eq!(contact.shared_octets, 2 * contact.block * 16);
    assert!(contact.shared_octets < (4 * rows * 16) as u32);

    let q = surface.fresh_section(rows, width, grain).expect("q");
    let k = surface.fresh_section(rows, width, grain).expect("k");
    let v = surface.fresh_section(rows, width, grain).expect("v");
    let out = surface.fresh_section(rows, width, grain).expect("out");
    let mut builder = surface
        .begin_passage(&[vec![], vec![], vec![], vec![0, 1, 2]])
        .expect("begin");
    for (index, &(staged, section)) in [(&staged_q, &q), (&staged_k, &k), (&staged_v, &v)]
        .iter()
        .enumerate()
    {
        let lane = builder.open(index, &[]).expect("open");
        surface
            .record_enter(&lane, staged, Dyadic::ONE, section)
            .expect("enter");
        builder
            .close(index, section, enter.needed)
            .expect("close enter");
    }
    let lane = builder.open(3, &[0, 1, 2]).expect("contact lane");
    surface
        .record_contact(
            &lane,
            &q,
            &k,
            &v,
            1,
            1,
            1,
            rows,
            SeriesAperture(2),
            None,
            &contact,
            &out,
        )
        .expect("record contact");
    builder
        .close(3, &out, contact.needed)
        .expect("close contact");
    let reading = builder.finish().expect("finish").launch().expect("launch");
    assert!(reading.obstruction.is_empty(), "{:?}", reading.slots);
    let unit = 1i64 << grain.0;
    assert!(
        surface
            .read_out(&out)
            .expect("read")
            .iter()
            .all(|face| *face == (unit, unit))
    );
}

#[test]
fn a_carrier_range_is_refused_before_any_launch_and_names_the_octaves() {
    let Some((_, surface)) = surface() else {
        return;
    };
    // a product of sixty-four and sixty-three octaves would need one hundred and twenty-seven
    let launches = surface.census().captured_launches;
    let outcome = surface.shape_hadamard(1, 1, 64, 63);
    assert!(
        matches!(
            outcome,
            Err(ResidentRefusal::CarrierRange {
                operation: "hadamard",
                needed: 127,
                admitted: 126
            })
        ),
        "{outcome:?}"
    );
    assert_eq!(
        surface.census().captured_launches,
        launches,
        "no launch on a refused budget"
    );
    // and a word that leaves the signed carrier ON the card raises the carrier flag, typed
    let (words, reading) = enter_once(surface, &[TWO], 1, 1, Dyadic::ONE, ResidentGrain(62));
    assert_eq!(words, vec![(0, 0)]);
    assert!(matches!(
        reading.slots[0].refusal("enter", 80),
        Some(ResidentRefusal::CarrierLeft { .. })
    ));
}

/// **The lineage falsifiers.** Two branches enter side by side; branch B's entering material
/// carries a non-finite codeword at a NONZERO coordinate, so its kernel refuses `MALFORMED` at
/// runtime. Every successor of B refuses `UPSTREAM` naming B; branch A and A's successor are
/// bit-identical to the unpoisoned run; the join of A and B refuses upstream naming B alone;
/// and the complete obstruction lineage is one reading under the co-present schedule, the
/// serialized schedule, and the serialized schedule with the front opened in reverse.
fn two_branch_passage(
    surface: &'static ResidentSurface<'static>,
    poison: bool,
    schedule: Schedule,
    reverse_front: bool,
) -> (
    PassageReading,
    Vec<(i64, i64)>,
    Vec<(i64, i64)>,
    Vec<(i64, i64)>,
    Vec<(i64, i64)>,
) {
    let grain = ResidentGrain(20);
    let a_words = [ONE, TWO, HALF, FOUR];
    // 0x7F80 is +inf in bfloat16: a non-finite stored codeword, at coordinate 2.
    let b_words = if poison {
        [ONE, TWO, 0x7F80, THREE]
    } else {
        [ONE, TWO, HALF, THREE]
    };
    let sa = surface.stage_words(&a_words, 1, 4).expect("stage");
    let sb = surface.stage_words(&b_words, 1, 4).expect("stage");
    let enter = surface
        .shape_enter(1, 4, Dyadic::ONE, grain, &a_words)
        .expect("shape");
    let by = DyadicEnclosure {
        lo: 2,
        hi: 2,
        grain: 0,
    };
    let scale = surface.shape_scale(1, 4, 23, by).expect("shape");
    let join = surface.shape_re_entry(1, 4, 24, 24).expect("shape");
    let a = surface.fresh_section(1, 4, grain).expect("a");
    let b = surface.fresh_section(1, 4, grain).expect("b");
    let a2 = surface.fresh_section(1, 4, grain).expect("a2");
    let b2 = surface.fresh_section(1, 4, grain).expect("b2");
    let joined = surface.fresh_section(1, 4, grain).expect("j");
    // occurrences: 0 enter A · 1 enter B · 2 scale A · 3 scale B · 4 re-entry(A2, B2)
    let lineage = vec![vec![], vec![], vec![0], vec![1], vec![2, 3]];
    let mut builder = surface
        .begin_passage_scheduled(&lineage, schedule)
        .expect("begin");
    let front0: Vec<usize> = if reverse_front {
        vec![1, 0]
    } else {
        vec![0, 1]
    };
    for index in front0 {
        let (staged, out) = if index == 0 { (&sa, &a) } else { (&sb, &b) };
        let lane = builder.open(index, &[]).expect("open");
        surface
            .record_enter(&lane, staged, Dyadic::ONE, out)
            .expect("enter");
        builder.close(index, out, enter.needed).expect("close");
    }
    let front1: Vec<usize> = if reverse_front {
        vec![3, 2]
    } else {
        vec![2, 3]
    };
    for index in front1 {
        let (input, out, producer) = if index == 2 {
            (&a, &a2, 0)
        } else {
            (&b, &b2, 1)
        };
        let lane = builder.open(index, &[producer]).expect("open");
        surface.record_scale(&lane, input, by, out).expect("scale");
        builder.close(index, out, scale.needed).expect("close");
    }
    let lane = builder.open(4, &[2, 3]).expect("open");
    surface
        .record_re_entry(&lane, &a2, &b2, &joined)
        .expect("join");
    builder.close(4, &joined, join.needed).expect("close");
    let passage = builder.finish().expect("finish");
    let reading = passage.launch().expect("launch");
    let ra = surface.read_out(&a).expect("read");
    let ra2 = surface.read_out(&a2).expect("read");
    let rb2 = surface.read_out(&b2).expect("read");
    let rj = surface.read_out(&joined).expect("read");
    (reading, ra, ra2, rb2, rj)
}

#[test]
fn a_runtime_refusal_at_a_nonzero_coordinate_travels_only_along_its_lineage_and_the_sibling_is_bit_identical()
 {
    let Some((_, surface)) = surface() else {
        return;
    };
    let (clean, clean_a, clean_a2, clean_b2, clean_j) =
        two_branch_passage(surface, false, Schedule::CoPresent, false);
    assert!(clean.obstruction.is_empty(), "{:?}", clean.slots);
    let (poisoned, a, a2, b2, j) = two_branch_passage(surface, true, Schedule::CoPresent, false);
    // B refused at runtime, of its own: MALFORMED, originating.
    assert!(
        matches!(
            poisoned.slots[1].refusal("enter", 30),
            Some(ResidentRefusal::Malformed { .. })
        ),
        "{:?}",
        poisoned.slots[1]
    );
    assert!(poisoned.slots[1].originates_refusal());
    // every successor of B refuses UPSTREAM, deterministically, naming B
    assert!(matches!(
        poisoned.slots[3].refusal("scale", 30),
        Some(ResidentRefusal::Upstream { .. })
    ));
    assert_eq!(poisoned.slots[3].upstream_first, Some(1));
    assert_eq!(poisoned.slots[3].upstream_count, 1);
    assert_eq!(poisoned.slots[3].upstream_flags, REFUSED_MALFORMED);
    // the join of A and B refuses upstream naming B's successor alone (A's stood)
    assert!(matches!(
        poisoned.slots[4].refusal("re-entry", 30),
        Some(ResidentRefusal::Upstream { .. })
    ));
    assert_eq!(poisoned.slots[4].upstream_first, Some(3));
    assert_eq!(
        poisoned.slots[4].upstream_count, 1,
        "A's successor did not refuse; only B's did"
    );
    assert_eq!(poisoned.slots[4].lineage_inspected, 2);
    // the unrelated sibling and its successor are bit-identical to the clean run
    assert_eq!(a, clean_a);
    assert_eq!(a2, clean_a2);
    assert_eq!(poisoned.slots[0], clean.slots[0]);
    assert_eq!(poisoned.slots[2], clean.slots[2]);
    assert!(poisoned.obstruction.stands(0) && poisoned.obstruction.stands(2));
    // B's own section and the join are NOT standing: partially written words are refused by
    // the lineage, whatever they hold.
    assert!(
        !poisoned.obstruction.stands(1)
            && !poisoned.obstruction.stands(3)
            && !poisoned.obstruction.stands(4)
    );
    let _ = (b2, j, clean_b2, clean_j);
    // the complete lineage, as a population: origins {1}, carried {3, 4}
    let origins: Vec<usize> = poisoned.obstruction.origins().map(|r| r.index).collect();
    assert_eq!(origins, vec![1]);
    assert_eq!(
        poisoned
            .obstruction
            .refusals
            .iter()
            .map(|r| r.index)
            .collect::<Vec<_>>(),
        vec![1, 3, 4]
    );
}

#[test]
fn the_complete_obstruction_lineage_is_one_reading_under_every_legal_schedule() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let (co_present, ..) = two_branch_passage(surface, true, Schedule::CoPresent, false);
    let (serialized, ..) = two_branch_passage(surface, true, Schedule::Serialized, false);
    let (reversed, ..) = two_branch_passage(surface, true, Schedule::Serialized, true);
    assert_eq!(co_present.obstruction, serialized.obstruction);
    assert_eq!(co_present.obstruction, reversed.obstruction);
    assert_eq!(co_present.slots, serialized.slots);
    assert_eq!(co_present.slots, reversed.slots);
    // and the co-present deed launched again is the same reading
    let (again, ..) = two_branch_passage(surface, true, Schedule::CoPresent, false);
    assert_eq!(again.obstruction, co_present.obstruction);
}

#[test]
fn a_lineage_that_disagrees_with_the_producers_opened_is_a_declaration_error_not_a_silent_read() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let grain = ResidentGrain(20);
    let staged = surface.stage_words(&[ONE], 1, 1).expect("stage");
    let x = surface.fresh_section(1, 1, grain).expect("x");
    let mut builder = surface.begin_passage(&[vec![], vec![0]]).expect("begin");
    let lane = builder.open(0, &[]).expect("open");
    surface
        .record_enter(&lane, &staged, Dyadic::ONE, &x)
        .expect("enter");
    builder.close(0, &x, 30).expect("close");
    assert!(
        matches!(
            builder.open(1, &[]),
            Err(ResidentRefusal::Declaration { .. })
        ),
        "opening with an undeclared lineage must refuse"
    );
    // a predecessor not earlier in the passage is refused at declaration
    assert!(matches!(
        surface.begin_passage(&[vec![1], vec![]]),
        Err(ResidentRefusal::Declaration { .. })
    ));
}

/// The kernel's helpers against an independent exact reference: signed minimum, its negation,
/// negative shifts both ways, shifts by the carrier width, zero, positive and negative interval
/// products, denominators touching zero, and the negative quotient enclosure.
#[test]
fn the_arithmetic_helpers_agree_with_the_serial_exact_reference_on_the_signed_edge_cases() {
    let Some((_, surface)) = surface() else {
        return;
    };
    let cases: Vec<(i64, i64, i32, i64)> = vec![
        (i64::MIN, 3, 0, 0),
        (i64::MIN, 3, -1, 0),
        (i64::MIN, 3, 40, 0),
        (i64::MIN + 1, 7, -3, 0),
        (-7, 2, -1, 0),
        (-7, 2, 1, 0),
        (7, 2, -1, 0),
        (-1, 1, -70, 0),
        (1, 1, -70, 0),
        (0, 5, 60, 0),
        (-2, 1, 1, 1), // interval quotient N=[-2,-1], D=[1,2] lifted by 1
        (-2, 1, 0, 1), // corners of [-2,-1]·[1,2]
        (3, 4, 0, 2),  // corners of [3,5]·[4,6]
        (-5, 3, 0, 4), // corners of [-5,-1]·[3,7]
        (i64::MAX, i64::MAX, 0, 0),
        (-i64::MAX, i64::MAX, 3, 0),
        (5, 0, 0, 0),   // denominator zero: refused, not divided
        (5, 1, 126, 0), // shift by the carrier width refuses
        (1, 1, 127, 0),
    ];
    let a: Vec<i64> = cases.iter().map(|c| c.0).collect();
    let b: Vec<i64> = cases.iter().map(|c| c.1).collect();
    let s: Vec<i32> = cases.iter().map(|c| c.2).collect();
    let span: Vec<i64> = cases.iter().map(|c| c.3).collect();
    let (results, flags) = surface
        .arithmetic_control(&a, &b, &s, &span)
        .expect("control");
    let two = BigInt::from(2);
    let pow = |k: u32| BigInt::from(BigUint::from(1u8) << k as usize);
    let floor_div = |n: &BigInt, d: &BigInt| -> BigInt {
        let q = n / d;
        if (n % d) != BigInt::from(0) && ((n < &BigInt::from(0)) != (d < &BigInt::from(0))) {
            q - 1
        } else {
            q
        }
    };
    let ceil_div = |n: &BigInt, d: &BigInt| -> BigInt {
        let q = n / d;
        if (n % d) != BigInt::from(0) && ((n < &BigInt::from(0)) == (d < &BigInt::from(0))) {
            q + 1
        } else {
            q
        }
    };
    let carrier = pow(127);
    for (i, (av, bv, sv, sp)) in cases.iter().enumerate() {
        let a = BigInt::from(*av);
        let b = BigInt::from(*bv);
        let row = results[i];
        let flag = flags[i];
        // shift_floor / shift_ceil against the exact rational
        let (expected_floor, expected_ceil, overflow) = if *sv >= 0 {
            let value = &a * pow(*sv as u32);
            let overflow = value.magnitude() >= carrier.magnitude();
            (value.clone(), value, overflow)
        } else {
            let d = pow((-*sv) as u32);
            (floor_div(&a, &d), ceil_div(&a, &d), false)
        };
        if overflow {
            assert!(
                flag & REFUSED_CARRIER != 0,
                "case {i}: an overflowing shift must refuse"
            );
        } else {
            assert_eq!(BigInt::from(row[0]), expected_floor, "case {i} floor");
            assert_eq!(BigInt::from(row[1]), expected_ceil, "case {i} ceil");
        }
        // product_shift(a, b, |s|): floor and ceil of a·b / 2^|s|
        let k = sv.unsigned_abs();
        let product = &a * &b;
        let d = pow(k);
        if product.magnitude() < pow(253).magnitude() {
            let pf = floor_div(&product, &d);
            let pc = ceil_div(&product, &d);
            if pf.magnitude() <= pow(126).magnitude() && pc.magnitude() <= pow(126).magnitude() {
                assert_eq!(BigInt::from(row[2]), pf, "case {i} product floor");
                assert_eq!(BigInt::from(row[3]), pc, "case {i} product ceil");
            }
        }
        // div_floor / div_ceil for b > 0
        if *bv > 0 {
            assert_eq!(
                BigInt::from(row[4]),
                floor_div(&a, &b),
                "case {i} div floor"
            );
            assert_eq!(BigInt::from(row[5]), ceil_div(&a, &b), "case {i} div ceil");
            // the interval quotient of [a, a+span] / [b, b+span], lifted by one
            let n_lo = &a * &two;
            let n_hi = (&a + BigInt::from(*sp)) * &two;
            let d_lo = b.clone();
            let d_hi = &b + BigInt::from(*sp);
            let q_lo = floor_div(&n_lo, if n_lo < BigInt::from(0) { &d_lo } else { &d_hi });
            let q_hi = ceil_div(&n_hi, if n_hi < BigInt::from(0) { &d_hi } else { &d_lo });
            if n_lo.magnitude() < carrier.magnitude() && n_hi.magnitude() < carrier.magnitude() {
                assert_eq!(BigInt::from(row[6]), q_lo, "case {i} quotient lo");
                assert_eq!(BigInt::from(row[7]), q_hi, "case {i} quotient hi");
            }
        } else {
            assert!(
                flag & REFUSED_MALFORMED != 0,
                "case {i}: a non-positive denominator must refuse"
            );
        }
        // corners of [a, a+span]·[b, b+span]
        let ends = [
            &a * &b,
            &a * (&b + BigInt::from(*sp)),
            (&a + BigInt::from(*sp)) * &b,
            (&a + BigInt::from(*sp)) * (&b + BigInt::from(*sp)),
        ];
        let c_lo = ends.iter().min().cloned().expect("four");
        let c_hi = ends.iter().max().cloned().expect("four");
        if c_lo.magnitude() < carrier.magnitude() && c_hi.magnitude() < carrier.magnitude() {
            assert_eq!(BigInt::from(row[8]), c_lo, "case {i} corners lo");
            assert_eq!(BigInt::from(row[9]), c_hi, "case {i} corners hi");
        }
    }
    // The named negative quotient: N=[-2,-1] over D=[1,2] is exactly [-2, -1/2].
    let named = cases
        .iter()
        .position(|c| *c == (-2, 1, 1, 1))
        .expect("the named case");
    assert_eq!(results[named][6], -4, "lo = -2 at half-grain resolution");
    assert_eq!(results[named][7], -1, "hi = -1/2 at half-grain resolution");
    assert_eq!(flags[named], 0);
}
