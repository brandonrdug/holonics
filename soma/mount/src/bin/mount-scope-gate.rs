//! mount-scope-gate — CUDA LADDER RUNG 3. It gates the CUDA/PTX port of the §XXVIII-b SCOPE entry
//! family (`scope_felt` · `scope_founded`) BYTE-EXACT against the host reference, on the headless
//! RTX 4080 SUPER.
//!
//!   stage a bounded co-present cohort of raw-light lineages (each a short distinct light ⊕ two-byte
//!   founding frame) over an immutable pre-light standing plane, exactly the buffer contract the
//!   SPIR-V/PTX scope entries bind -> compute the HOST REFERENCE by carving each lane's disjoint OWN
//!   ⊕ carrier/K spans and running `body::carriage::carry_dense_stroke` / `carry_founded_stroke`
//!   with `SliceWordSeam` (the SAME law the card runs, only the host lowering) -> upload -> dispatch
//!   one thread per lane (block 64 × 1, with the 100-lane case deliberately crossing a second grid
//!   row through the runtime X-thread stride) -> read back ->
//!   assert the card's OWN reservation, carrier/K rows, per-lane term counts, and every word of the
//!   formed radiation aperture are BYTE-EXACT.
//!
//! Both substrates call the identical `body::carriage` code; the gate therefore proves the nvptx
//! lowering ⊕ the shell's span carving reproduce the host lowering word-for-word. Nothing is scored.
//! Five lane counts are swept — 1 · 2 · 3 · 64 (one whole block) · 100 (a non-multiple of 64) — so the
//! block-boundary and guard paths are exercised. The founded reservation opens the exact manifested
//! `RADIATION_WORDS` aperture over a fresh zeroed buffer, matching the observed wgpu mouth. On any
//! driver fault the exact CUresult name prints and the gate stops — no retry.
//! One further single-lineage gate carries the fixed long passage from body::carriage with one
//! interior move per launch. The same complete grid is presented unconditionally until the carried
//! cursor reaches the light's true end; OWN, carrier/K, radiation, and accumulated counts must then
//! equal the uninterrupted host sibling while all eight continuation phases have crossed.
//!
//! This binary takes NO arguments. The card run is conducted by the main line only; the reference
//! path itself is gated host-side (no GPU) by the `#[cfg(test)]` self-checks below.

use std::ffi::c_void;
use std::time::Instant;

use body::carriage::{
    carry_dense_stroke, carry_founded_stroke, rebase_carrier_row, required_carrier_rebase_depth,
    LineageStroke, WordSpan,
};
use body::manifold::{
    self, carrier_row_words, OWN_CELL_WORDS, RADIATION_BRICK, RADIATION_BRICK_LIVE, RADIATION_CUT,
    RADIATION_FLAGS, RADIATION_FOLD, RADIATION_FORM, RADIATION_GRIP, RADIATION_ROTOR,
    RADIATION_STEP, RADIATION_WORDS,
};
use body::medium::{RegionalForm, FORM_WORDS};
use body::num::COG_WORDS;
use body::seam::SliceWordSeam;
use mount::{Context, DeviceBuffer, Dim3, Function, Module, Result};

/// The committed PTX boundary artifact, built by soma-kernel-cuda/build-ptx.sh.
const PTX: &[u8] = include_bytes!("../../soma-kernel-cuda/soma_kernel_cuda.ptx");

const BLOCK: u32 = 64; // mirrors the SPIR-V `threads(64)` and the wgpu X workgroup width
const DRIVE: u32 = 137; // coprime to the quantum — remainders stand, the reads are non-vacuous
const STROKE_ATOMS: u32 = 0; // 0 carries each worldline through the raw light's true end
const DENSE_AXIS: i64 = 8;
const DENSE_CELLS: usize = (DENSE_AXIS * DENSE_AXIS) as usize; // one square dense chart per lane
const STANDING_AXIS: usize = 8;
const STANDING_CELLS: usize = STANDING_AXIS * STANDING_AXIS; // the founded receiving chart
const DEPTH: usize = 8; // the declared carrier reservation; RESERVATION_LIMITED_LANES states its excess
/// Lane counts swept: single · pair · triple · one whole block · a non-multiple of 64.
const LANE_COUNTS: [usize; 5] = [1, 2, 3, 64, 100];
/// Exact `(FOLD, STEP, CUT)` counts emitted by the shared host/body producer for each swept cohort.
/// This pins the radiation fixture itself before CUDA parity: an empty or weakened aperture fails.
///
/// **Regenerated 2026-08-07 against the carriage law, not against a prior receipt.** The 64- and
/// 100-lane entries stood at `(256, 160, 38)` and `(408, 250, 67)` from the commit that first pinned
/// them (laboratory `687e0899`) and were never regenerated across the ten later commits that
/// changed `body::carriage`. Two of those commits moved the tuple, and each is a deliberate
/// correction that updated its own in-crate tests in the same commit:
///
/// - laboratory `323522b7`, *publish the current Soma production spine* — a lineage that exhausted
///   its carrier reservation used to fold a channel and unwind, manufacturing one FOLD and one STEP
///   out of a capacity limit. That branch was replaced by preservation of the live continuation plus
///   the explicit `required_carrier_rebase_depth` / `rebase_carrier_row` boundary. 64 lanes:
///   `(256, 160, 38)` -> `(254, 158, 38)`.
/// - laboratory `f6c3a688`, *stabilize Soma lifecycle and navigation baseline* — a completed
///   enclosure has already handed its composite on, so `release_co_present` releases its lower
///   arrivals before the triggering successor is admitted. 64 lanes: `(254, 158, 38)` ->
///   `(255, 159, 35)`. Measured consequence: lane 32 now completes INSIDE the declared depth-8
///   reservation, where under the prior law it demanded depth 9.
///
/// The implementation was graded, not the receipt. Host x86-64 and device nvptx64 `sm_89` return
/// **byte-identical** radiation for every swept cohort — `radiation EXACT · canonical EXACT` — and
/// the stale constant was the only disagreeing party.
const EXPECTED_RADIATION_SPECIES: [(usize, usize, usize); 5] = [
    (3, 1, 1),
    (5, 2, 1),
    (8, 4, 1),
    (255, 159, 35),
    (407, 249, 62),
];
/// The lanes still standing at the declared carrier reservation when their stroke ends —
/// `required_carrier_rebase_depth` returns `Some(DEPTH + 1)` for exactly these and `None` for every
/// other lane. `founded_reference` carries one fixed row per lane and never rebases, so such a
/// lane's later octets stand as exact zero padding rather than as construction, and
/// `validate_radiation` accepts that padding as a canonical species. Pinning the set makes the
/// truncation a stated fact instead of a silent one.
///
/// **Raising `DEPTH` does not empty this set.** Measured 2026-08-07 at reservations 8, 9, 10, 12 and
/// 16: lane 86 demands `reserved + 1` at every one of them. Its enclosure descent is not bounded by
/// any reservation this gate can declare, so the gate keeps its declared aperture and states the
/// excess rather than chasing it.
///
/// Only the host-side self-checks read it, so it is `cfg(test)`. Left at module scope it made the
/// binary build emit `constant is never used` — a warning the receipt that introduced it did not
/// report.
#[cfg(test)]
const RESERVATION_LIMITED_LANES: [&[usize]; 5] = [&[], &[], &[], &[], &[86]];
/// The exact long worldline used by body::carriage's within-atom continuation gate.
const CONTINUATION_LIGHT: &[u8] =
    b"the cat sat on the mat and then it ran to see an old dog who was far too shy \
now the cat sat on the mat again and the dog ran to see the old cat by the mat";
const CONTINUATION_DEPTH: usize = 4;
const CONTINUATION_INSTALLMENT: usize = 1;

/// Shape this bounded instrument's largest existing case across two grid rows. This is only a CUDA
/// gate aperture: the kernel receives the resulting X-thread stride explicitly and still carries
/// every lineage in one dispatch.
fn scope_grid(lanes: usize) -> (Dim3, u32) {
    assert!(lanes != 0 && lanes <= u32::MAX as usize);
    let groups = (lanes as u32).div_ceil(BLOCK);
    let x = if lanes == 100 { 1 } else { groups };
    let y = groups.div_ceil(x);
    (Dim3 { x, y, z: 1 }, x * BLOCK)
}

/// Pass an owned scalar (a device pointer or a length) as a `cuLaunchKernel` argument slot.
fn arg(v: &mut u64) -> *mut c_void {
    v as *mut u64 as *mut c_void
}

fn face(ok: bool) -> &'static str {
    if ok {
        "EXACT"
    } else {
        "MISMATCH"
    }
}

/// Deterministic staging of one lineage's raw light (≥ 2 bytes so every worldline carries at least
/// one adjacent difference). Pure host construction — the card reads the identical packed bytes.
fn lane_light(lane: usize) -> Vec<u8> {
    let len = 6 + (lane % 11); // 6..=16 bytes
    (0..len)
        .map(|i| {
            (lane
                .wrapping_mul(31)
                .wrapping_add(i.wrapping_mul(17))
                .wrapping_add(7)
                & 0xff) as u8
        })
        .collect()
}

/// The two-byte founding frame seed (construction, not an identity label).
fn lane_seed(lane: usize) -> [u8; 2] {
    [
        ((lane * 13 + 1) & 0xff) as u8,
        ((lane * 7 + 3) & 0xff) as u8,
    ]
}

/// The founded reservation axis for a lane — a power of two, alternating so both single- and
/// multi-cell charts, and thus varying `own_cell_offset` strides, are exercised.
fn founded_own_axis(lane: usize) -> usize {
    if lane % 2 == 0 {
        2
    } else {
        4
    }
}

/// The complete staged octet extent. Founded lane offsets are contiguous by construction; keeping
/// this proof beside the aperture validator makes every radiation word belong to exactly one lane.
fn founded_light_bytes(rows: &[u32]) -> Option<usize> {
    if rows.len() % 8 != 0 {
        return None;
    }
    let mut expected_offset = 0usize;
    for row in rows.chunks_exact(8) {
        if row[0] as usize != expected_offset {
            return None;
        }
        expected_offset = expected_offset.checked_add(row[1] as usize)?;
    }
    Some(expected_offset)
}

/// Validate one current manifested radiation row by composing the boundary codecs owned by body.
/// The flag masks here are only the `AtomEvent` species: STEP follows the same atom's FOLD, while a
/// CUT and its live BRICK are one completion. Numeric and form anatomy are not repeated here.
fn validate_radiation_row(row: &[u32]) -> std::result::Result<(), &'static str> {
    if row.len() != RADIATION_WORDS {
        return Err("one radiation row has the manifested word extent");
    }
    let flags = row[RADIATION_FLAGS];
    let fold_step = RADIATION_FOLD | RADIATION_STEP;
    let completion = fold_step | RADIATION_CUT | RADIATION_BRICK_LIVE;
    if !matches!(flags, 0 | RADIATION_FOLD) && flags != fold_step && flags != completion {
        return Err("one radiation row carries a canonical AtomEvent flag species");
    }

    if flags & RADIATION_STEP == 0 {
        if row[RADIATION_GRIP..].iter().any(|word| *word != 0) {
            return Err("a row without STEP carries no dormant payload");
        }
        return Ok(());
    }

    if row[RADIATION_GRIP] as usize >= STANDING_CELLS {
        return Err("a stepped grip lies inside the declared standing chart");
    }
    RegionalForm::unpack_compact_checked(row, RADIATION_FORM)
        .map_err(|_| "a stepped row carries one canonical RegionalForm")?;
    if !body::num::packed_cog_is_canonical(row, RADIATION_ROTOR)
        || !body::num::packed_cog_is_canonical(row, RADIATION_ROTOR + COG_WORDS)
    {
        return Err("a stepped row carries two canonical meeting-rotor Cogs");
    }

    let cut = flags & RADIATION_CUT != 0;
    let cross = manifold::unpack_cog(row, RADIATION_ROTOR);
    let aim = manifold::unpack_cog(row, RADIATION_ROTOR + COG_WORDS);
    if cut && cross.mag == 0 && aim.mag == 0 {
        return Err("a cut carries a formed meeting rotor");
    }

    if flags & RADIATION_BRICK_LIVE == 0 {
        if row[RADIATION_BRICK..].iter().any(|word| *word != 0) {
            return Err("a non-completion carries no dormant brick payload");
        }
    } else {
        if !manifold::packed_node_is_canonical(row, RADIATION_BRICK) {
            return Err("a live brick carries one canonical Node");
        }
        if manifold::unpack_node(row, RADIATION_BRICK).len == 0 {
            return Err("a live brick is not the absent node");
        }
    }
    Ok(())
}

/// Validate the whole concatenated aperture, including every lineage's structural row-zero
/// padding. The contiguous lane proof above ensures this loop accounts for every returned word.
fn validate_radiation(radiation: &[u32], rows: &[u32]) -> std::result::Result<(), String> {
    let light_bytes = founded_light_bytes(rows)
        .ok_or_else(|| "founded lane extents are contiguous and representable".to_string())?;
    let expected_words = light_bytes
        .checked_mul(RADIATION_WORDS)
        .ok_or_else(|| "the radiation aperture extent is representable".to_string())?;
    if radiation.len() != expected_words {
        return Err(format!(
            "radiation extent is {} words, expected {expected_words}",
            radiation.len()
        ));
    }

    for (lane, lane_row) in rows.chunks_exact(8).enumerate() {
        let offset = lane_row[0] as usize;
        let count = lane_row[1] as usize;
        if count == 0 {
            return Err(format!("lane {lane} has no delivered octet"));
        }
        let lane_start = offset * RADIATION_WORDS;
        let lane_end = (offset + count) * RADIATION_WORDS;
        let lane_words = &radiation[lane_start..lane_end];
        if lane_words[..RADIATION_WORDS].iter().any(|word| *word != 0) {
            return Err(format!(
                "lane {lane} row zero is not exact aperture padding"
            ));
        }
        for (atom, row) in lane_words.chunks_exact(RADIATION_WORDS).enumerate() {
            validate_radiation_row(row)
                .map_err(|message| format!("lane {lane} atom {atom}: {message}"))?;
        }
    }
    Ok(())
}

fn radiation_species(radiation: &[u32]) -> (usize, usize, usize) {
    radiation.chunks_exact(RADIATION_WORDS).fold(
        (0usize, 0usize, 0usize),
        |(folds, steps, cuts), row| {
            let flags = row[RADIATION_FLAGS];
            (
                folds + usize::from(flags & RADIATION_FOLD != 0),
                steps + usize::from(flags & RADIATION_STEP != 0),
                cuts + usize::from(flags & RADIATION_CUT != 0),
            )
        },
    )
}

fn expected_radiation_species(lanes: usize) -> Option<(usize, usize, usize)> {
    LANE_COUNTS
        .iter()
        .position(|count| *count == lanes)
        .map(|at| EXPECTED_RADIATION_SPECIES[at])
}

// --- DENSE SCOPE (scope_felt) --------------------------------------------------------------------

/// Pack the cohort's raw lights into one concatenated word buffer and the 6-word dense lane rows,
/// exactly as `surface::FeltSurface::pack_light` does. Worldline bases are zero (resident mount).
fn pack_dense_light(lanes: usize) -> (Vec<u32>, Vec<u32>) {
    let lights: Vec<Vec<u8>> = (0..lanes).map(lane_light).collect();
    let total: usize = lights.iter().map(|l| l.len()).sum();
    let mut packed = vec![0u32; total.div_ceil(4).max(1)];
    let mut rows = Vec::with_capacity(lanes * 6);
    let mut offset = 0usize;
    for (lane, light) in lights.iter().enumerate() {
        for (i, &b) in light.iter().enumerate() {
            let at = offset + i;
            packed[at >> 2] |= (b as u32) << ((at & 3) * 8);
        }
        let seed = lane_seed(lane);
        rows.extend_from_slice(&[
            offset as u32,
            light.len() as u32,
            seed[0] as u32,
            seed[1] as u32,
            0,
            0,
        ]);
        offset += light.len();
    }
    (packed, rows)
}

/// The HOST REFERENCE for the dense scope: carve each lane's disjoint OWN plane ⊕ carrier/K row
/// (the same spans `dense_ranges` carves on the card) and run the shared `carry_dense_stroke`.
fn dense_reference(
    lanes: usize,
    standing: &[u32],
    packed: &[u32],
    rows: &[u32],
) -> (Vec<u32>, Vec<u32>, Vec<u64>) {
    let row_words = carrier_row_words(DEPTH);
    let own_words = DENSE_CELLS * FORM_WORDS;
    let mut owns = vec![0u32; lanes * own_words];
    let mut carriers = vec![0u32; lanes * row_words];
    let mut counts = vec![0u64; lanes * 4];
    for lane in 0..lanes {
        let lane_at = lane * 6;
        let offset = rows[lane_at] as usize;
        let count = rows[lane_at + 1] as usize;
        let worldline_base = rows[lane_at + 4] as u64 | ((rows[lane_at + 5] as u64) << 32);
        let stroke = LineageStroke::dense(
            DENSE_AXIS,
            DENSE_CELLS,
            offset,
            count,
            rows[lane_at + 2],
            rows[lane_at + 3],
            worldline_base,
            STROKE_ATOMS as usize,
            DRIVE,
        );
        let own = WordSpan::new(lane * own_words, own_words);
        let carrier = WordSpan::new(lane * row_words, row_words);
        if let Some(result) = carry_dense_stroke::<SliceWordSeam>(
            standing,
            &mut owns,
            own,
            &mut carriers,
            carrier,
            packed,
            stroke,
        ) {
            counts[lane * 4] += result.terms.ride;
            counts[lane * 4 + 1] += result.terms.found_this;
            counts[lane * 4 + 2] += result.terms.found_that;
            counts[lane * 4 + 3] += result.terms.dark;
        }
    }
    (owns, carriers, counts)
}

/// One swept dense size: stage, host-reference, dispatch scope_felt, read back, assert BYTE-EXACT.
fn dense_case(ctx: &Context, felt: &Function, lanes: usize) -> Result<bool> {
    let row_words = carrier_row_words(DEPTH);
    let own_words = DENSE_CELLS * FORM_WORDS;
    let standing_words = DENSE_CELLS * FORM_WORDS;
    let standing = vec![0u32; standing_words]; // immutable pre-light (all UNBORN), like the M4b gate
    let (packed, rows) = pack_dense_light(lanes);
    let (host_owns, host_carriers, host_counts) = dense_reference(lanes, &standing, &packed, &rows);

    let owns_len = lanes * own_words;
    let carriers_len = lanes * row_words;
    let counts_len = lanes * 4;

    let standing_b: DeviceBuffer<u32> = DeviceBuffer::alloc(standing_words)?;
    standing_b.copy_from_slice(&standing)?;
    let owns_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(owns_len)?;
    let carriers_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(carriers_len)?;
    let bytes_b: DeviceBuffer<u32> = DeviceBuffer::alloc(packed.len())?;
    bytes_b.copy_from_slice(&packed)?;
    let lanes_b: DeviceBuffer<u32> = DeviceBuffer::alloc(rows.len())?;
    lanes_b.copy_from_slice(&rows)?;
    let counts_b: DeviceBuffer<u64> = DeviceBuffer::alloc_zeroed(counts_len)?;
    let (grid, x_thread_stride) = scope_grid(lanes);
    let params: [u32; 8] = [
        DENSE_AXIS as u32,
        DENSE_CELLS as u32,
        lanes as u32,
        row_words as u32,
        STROKE_ATOMS,
        DRIVE,
        x_thread_stride,
        0,
    ];
    let params_b: DeviceBuffer<u32> = DeviceBuffer::alloc(params.len())?;
    params_b.copy_from_slice(&params)?;

    let (mut p_st, mut l_st) = (standing_b.device_ptr(), standing_words as u64);
    let (mut p_ow, mut l_ow) = (owns_b.device_ptr(), owns_len as u64);
    let (mut p_ca, mut l_ca) = (carriers_b.device_ptr(), carriers_len as u64);
    let (mut p_by, mut l_by) = (bytes_b.device_ptr(), packed.len() as u64);
    let (mut p_la, mut l_la) = (lanes_b.device_ptr(), rows.len() as u64);
    let (mut p_co, mut l_co) = (counts_b.device_ptr(), counts_len as u64);
    let (mut p_pr, mut l_pr) = (params_b.device_ptr(), params.len() as u64);

    let t = Instant::now();
    {
        // scope_felt(standing, owns, carriers, bytes, lanes, counts, params) — the SPIR-V binding order.
        let mut a: [*mut c_void; 14] = [
            arg(&mut p_st),
            arg(&mut l_st),
            arg(&mut p_ow),
            arg(&mut l_ow),
            arg(&mut p_ca),
            arg(&mut l_ca),
            arg(&mut p_by),
            arg(&mut l_by),
            arg(&mut p_la),
            arg(&mut l_la),
            arg(&mut p_co),
            arg(&mut l_co),
            arg(&mut p_pr),
            arg(&mut l_pr),
        ];
        felt.launch(grid, Dim3::x(BLOCK), &mut a)?;
        ctx.synchronize()?;
    }
    let carry_us = t.elapsed().as_micros();

    let mut card_owns = vec![0u32; owns_len];
    owns_b.copy_to_slice(&mut card_owns)?;
    let mut card_carriers = vec![0u32; carriers_len];
    carriers_b.copy_to_slice(&mut card_carriers)?;
    let mut card_counts = vec![0u64; counts_len];
    counts_b.copy_to_slice(&mut card_counts)?;

    let owns_ok = card_owns == host_owns;
    let carriers_ok = card_carriers == host_carriers;
    let counts_ok = card_counts == host_counts;
    let terms: [u64; 4] = host_counts.chunks_exact(4).fold([0u64; 4], |mut acc, c| {
        for j in 0..4 {
            acc[j] += c[j];
        }
        acc
    });
    println!(
        "  lanes {:>3}: owns {} · carriers {} · counts {}  (grid {}×{} · {} own u32 · {} carrier u32 · Σ[ride {} found_this {} found_that {} dark {}] · {} us)",
        lanes, face(owns_ok), face(carriers_ok), face(counts_ok),
        grid.x, grid.y, owns_len, carriers_len, terms[0], terms[1], terms[2], terms[3], carry_us,
    );
    if !(owns_ok && carriers_ok && counts_ok) {
        report_divergence(
            "dense",
            &card_owns,
            &host_owns,
            &card_carriers,
            &host_carriers,
        );
    }
    Ok(owns_ok && carriers_ok && counts_ok)
}

// --- FOUNDED SCOPE (scope_founded) ---------------------------------------------------------------

/// Pack the cohort's raw lights and the 8-word founded lane rows (dense row ⊕ `own_cell_offset` ⊕
/// `own_axis`), exactly as `surface::FeltSurface::pack_founded_light`. Returns the total founded
/// cell count, so the concatenated OWN reservation can be sized exactly.
fn pack_founded_light(lanes: usize) -> (Vec<u32>, Vec<u32>, usize) {
    let lights: Vec<Vec<u8>> = (0..lanes).map(lane_light).collect();
    let total: usize = lights.iter().map(|l| l.len()).sum();
    let mut packed = vec![0u32; total.div_ceil(4).max(1)];
    let mut rows = Vec::with_capacity(lanes * 8);
    let mut offset = 0usize;
    let mut own_cell_offset = 0usize;
    for (lane, light) in lights.iter().enumerate() {
        for (i, &b) in light.iter().enumerate() {
            let at = offset + i;
            packed[at >> 2] |= (b as u32) << ((at & 3) * 8);
        }
        let seed = lane_seed(lane);
        let own_axis = founded_own_axis(lane);
        rows.extend_from_slice(&[
            offset as u32,
            light.len() as u32,
            seed[0] as u32,
            seed[1] as u32,
            0,
            0,
            own_cell_offset as u32,
            own_axis as u32,
        ]);
        offset += light.len();
        own_cell_offset += own_axis * own_axis;
    }
    (packed, rows, own_cell_offset)
}

/// The HOST REFERENCE for the founded scope: carve each lane's reservation-sized OWN chart ⊕
/// carrier/K row (the spans `founded_header`/`founded_ranges` carve) and run `carry_founded_stroke`.
fn founded_reference(
    lanes: usize,
    standing: &[u32],
    packed: &[u32],
    rows: &[u32],
    total_own_cells: usize,
) -> (Vec<u32>, Vec<u32>, Vec<u64>, Vec<u32>) {
    let row_words = carrier_row_words(DEPTH);
    let mut owns = vec![0u32; total_own_cells * OWN_CELL_WORDS];
    let mut carriers = vec![0u32; lanes * row_words];
    let mut counts = vec![0u64; lanes * 4];
    let light_bytes = founded_light_bytes(rows).expect("the staged founded lights are contiguous");
    let mut radiation = vec![0u32; light_bytes * RADIATION_WORDS];
    for lane in 0..lanes {
        let lane_at = lane * 8;
        let offset = rows[lane_at] as usize;
        let count = rows[lane_at + 1] as usize;
        let worldline_base = rows[lane_at + 4] as u64 | ((rows[lane_at + 5] as u64) << 32);
        let own_cell_base = rows[lane_at + 6] as usize;
        let own_axis = rows[lane_at + 7] as usize;
        let own_cells = own_axis * own_axis;
        let stroke = LineageStroke::founded(
            STANDING_AXIS as i64,
            own_axis as i64,
            STANDING_CELLS,
            own_cells,
            offset,
            count,
            rows[lane_at + 2],
            rows[lane_at + 3],
            worldline_base,
            STROKE_ATOMS as usize,
            DRIVE,
            RADIATION_WORDS,
        );
        let own = WordSpan::new(own_cell_base * OWN_CELL_WORDS, own_cells * OWN_CELL_WORDS);
        let carrier = WordSpan::new(lane * row_words, row_words);
        let radiation_words = WordSpan::new(offset * RADIATION_WORDS, count * RADIATION_WORDS);
        if let Some(result) = carry_founded_stroke::<SliceWordSeam>(
            standing,
            &mut owns,
            own,
            &mut carriers,
            carrier,
            packed,
            &mut radiation,
            radiation_words,
            stroke,
        ) {
            counts[lane * 4] += result.terms.ride;
            counts[lane * 4 + 1] += result.terms.found_this;
            counts[lane * 4 + 2] += result.terms.found_that;
            counts[lane * 4 + 3] += result.terms.dark;
        }
    }
    (owns, carriers, counts, radiation)
}

/// One swept founded size: stage, host-reference, dispatch scope_founded, read back, assert BYTE-EXACT.
fn founded_case(ctx: &Context, founded: &Function, lanes: usize) -> Result<bool> {
    let row_words = carrier_row_words(DEPTH);
    let standing_words = STANDING_CELLS * FORM_WORDS;
    let standing = vec![0u32; standing_words];
    let (packed, rows, total_own_cells) = pack_founded_light(lanes);
    let (host_owns, host_carriers, host_counts, host_radiation) =
        founded_reference(lanes, &standing, &packed, &rows, total_own_cells);
    let host_radiation_valid = validate_radiation(&host_radiation, &rows);

    let owns_len = total_own_cells * OWN_CELL_WORDS;
    let carriers_len = lanes * row_words;
    let counts_len = lanes * 4;
    let radiation_len = host_radiation.len();

    let standing_b: DeviceBuffer<u32> = DeviceBuffer::alloc(standing_words)?;
    standing_b.copy_from_slice(&standing)?;
    let owns_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(owns_len)?;
    let carriers_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(carriers_len)?;
    let bytes_b: DeviceBuffer<u32> = DeviceBuffer::alloc(packed.len())?;
    bytes_b.copy_from_slice(&packed)?;
    let lanes_b: DeviceBuffer<u32> = DeviceBuffer::alloc(rows.len())?;
    lanes_b.copy_from_slice(&rows)?;
    let counts_b: DeviceBuffer<u64> = DeviceBuffer::alloc_zeroed(counts_len)?;
    let radiation_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(radiation_len)?;
    let (grid, x_thread_stride) = scope_grid(lanes);
    let params: [u32; 9] = [
        STANDING_AXIS as u32,
        STANDING_CELLS as u32,
        lanes as u32,
        row_words as u32,
        STROKE_ATOMS,
        DRIVE,
        RADIATION_WORDS as u32,
        x_thread_stride,
        0,
    ];
    let params_b: DeviceBuffer<u32> = DeviceBuffer::alloc(params.len())?;
    params_b.copy_from_slice(&params)?;

    let (mut p_st, mut l_st) = (standing_b.device_ptr(), standing_words as u64);
    let (mut p_ow, mut l_ow) = (owns_b.device_ptr(), owns_len as u64);
    let (mut p_ca, mut l_ca) = (carriers_b.device_ptr(), carriers_len as u64);
    let (mut p_by, mut l_by) = (bytes_b.device_ptr(), packed.len() as u64);
    let (mut p_la, mut l_la) = (lanes_b.device_ptr(), rows.len() as u64);
    let (mut p_co, mut l_co) = (counts_b.device_ptr(), counts_len as u64);
    let (mut p_pr, mut l_pr) = (params_b.device_ptr(), params.len() as u64);
    let (mut p_ra, mut l_ra) = (radiation_b.device_ptr(), radiation_len as u64);

    let t = Instant::now();
    {
        // scope_founded(standing, owns, carriers, bytes, lanes, counts, params, radiation).
        let mut a: [*mut c_void; 16] = [
            arg(&mut p_st),
            arg(&mut l_st),
            arg(&mut p_ow),
            arg(&mut l_ow),
            arg(&mut p_ca),
            arg(&mut l_ca),
            arg(&mut p_by),
            arg(&mut l_by),
            arg(&mut p_la),
            arg(&mut l_la),
            arg(&mut p_co),
            arg(&mut l_co),
            arg(&mut p_pr),
            arg(&mut l_pr),
            arg(&mut p_ra),
            arg(&mut l_ra),
        ];
        founded.launch(grid, Dim3::x(BLOCK), &mut a)?;
        ctx.synchronize()?;
    }
    let carry_us = t.elapsed().as_micros();

    let mut card_owns = vec![0u32; owns_len];
    owns_b.copy_to_slice(&mut card_owns)?;
    let mut card_carriers = vec![0u32; carriers_len];
    carriers_b.copy_to_slice(&mut card_carriers)?;
    let mut card_counts = vec![0u64; counts_len];
    counts_b.copy_to_slice(&mut card_counts)?;
    let mut card_radiation = vec![0u32; radiation_len];
    radiation_b.copy_to_slice(&mut card_radiation)?;

    let owns_ok = card_owns == host_owns;
    let carriers_ok = card_carriers == host_carriers;
    let counts_ok = card_counts == host_counts;
    let radiation_ok = card_radiation == host_radiation;
    let card_radiation_valid = validate_radiation(&card_radiation, &rows);
    let radiation_valid = host_radiation_valid.is_ok() && card_radiation_valid.is_ok();
    let terms: [u64; 4] = host_counts.chunks_exact(4).fold([0u64; 4], |mut acc, c| {
        for j in 0..4 {
            acc[j] += c[j];
        }
        acc
    });
    let radiation_rows = radiation_len / RADIATION_WORDS;
    let species = radiation_species(&host_radiation);
    let (radiated_folds, radiated_steps, radiated_cuts) = species;
    let radiation_nonvacuous = expected_radiation_species(lanes) == Some(species);
    println!(
        "  lanes {:>3}: owns {} · carriers {} · counts {} · radiation {} · canonical {} · nonvacuous {}  (grid {}×{} · {} founded cells · {} own u32 · {} carrier u32 · {} radiation rows / {} folds / {} steps / {} cuts · Σ[ride {} found_this {} found_that {} dark {}] · {} us)",
        lanes, face(owns_ok), face(carriers_ok), face(counts_ok), face(radiation_ok), face(radiation_valid), face(radiation_nonvacuous),
        grid.x, grid.y, total_own_cells, owns_len, carriers_len, radiation_rows, radiated_folds, radiated_steps, radiated_cuts,
        terms[0], terms[1], terms[2], terms[3], carry_us,
    );
    if let Err(error) = &host_radiation_valid {
        eprintln!("  founded: HOST radiation is noncanonical: {error}");
    }
    if let Err(error) = &card_radiation_valid {
        eprintln!("  founded: card radiation is noncanonical: {error}");
    }
    if !(owns_ok && carriers_ok && counts_ok) {
        report_divergence(
            "founded",
            &card_owns,
            &host_owns,
            &card_carriers,
            &host_carriers,
        );
    }
    if !radiation_ok {
        report_radiation_divergence(&card_radiation, &host_radiation);
    }
    Ok(owns_ok
        && carriers_ok
        && counts_ok
        && radiation_ok
        && radiation_valid
        && radiation_nonvacuous)
}

// --- WITHIN-ATOM CONTINUATION -------------------------------------------------------------------

#[derive(Debug, PartialEq, Eq)]
struct ContinuationTrace {
    owns: Vec<u32>,
    carriers: Vec<u32>,
    radiation: Vec<u32>,
    counts: [u64; 4],
    phase_mask: u32,
    deepest: usize,
    resumed_deposit: bool,
}

fn pack_continuation_light() -> Vec<u32> {
    let mut packed = vec![0u32; CONTINUATION_LIGHT.len().div_ceil(4)];
    for (at, &octet) in CONTINUATION_LIGHT.iter().enumerate() {
        packed[at >> 2] |= (octet as u32) << ((at & 3) * 8);
    }
    packed
}

fn continuation_dense_row() -> [u32; 6] {
    [
        0,
        CONTINUATION_LIGHT.len() as u32,
        CONTINUATION_LIGHT[0] as u32,
        CONTINUATION_LIGHT[1] as u32,
        0,
        0,
    ]
}

fn continuation_founded_row() -> [u32; 8] {
    [
        0,
        CONTINUATION_LIGHT.len() as u32,
        CONTINUATION_LIGHT[0] as u32,
        CONTINUATION_LIGHT[1] as u32,
        0,
        0,
        0,
        STANDING_AXIS as u32,
    ]
}

fn continuation_cursor(carriers: &[u32]) -> u64 {
    carriers[manifold::CARRIER_CURSOR_LO] as u64
        | ((carriers[manifold::CARRIER_CURSOR_HI] as u64) << 32)
}

fn continuation_face(carriers: &[u32]) -> (u32, usize) {
    let carrier_depth = manifold::carrier_row_depth(carriers.len());
    let at = manifold::carrier_continuation_base(carrier_depth);
    let phase = carriers[at + manifold::CARRIER_CONTINUATION_PHASE];
    let depth = carriers[at + manifold::CARRIER_CONTINUATION_DEPTH_LO] as u64
        | ((carriers[at + manifold::CARRIER_CONTINUATION_DEPTH_HI] as u64) << 32);
    (phase, depth as usize)
}

fn observe_continuation(carriers: &[u32], phase_mask: &mut u32, deepest: &mut usize) {
    let (phase, depth) = continuation_face(carriers);
    *phase_mask |= 1u32
        .checked_shl(phase)
        .expect("one carrier continuation phase belongs to the eight-face mask");
    *deepest = (*deepest).max(depth);
}

fn continuation_stroke(founded: bool, interior_installment: usize) -> LineageStroke {
    let stroke = if founded {
        LineageStroke::founded(
            STANDING_AXIS as i64,
            STANDING_AXIS as i64,
            STANDING_CELLS,
            STANDING_CELLS,
            0,
            CONTINUATION_LIGHT.len(),
            CONTINUATION_LIGHT[0] as u32,
            CONTINUATION_LIGHT[1] as u32,
            0,
            0,
            DRIVE,
            RADIATION_WORDS,
        )
    } else {
        LineageStroke::dense(
            DENSE_AXIS,
            DENSE_CELLS,
            0,
            CONTINUATION_LIGHT.len(),
            CONTINUATION_LIGHT[0] as u32,
            CONTINUATION_LIGHT[1] as u32,
            0,
            0,
            DRIVE,
        )
    };
    stroke.with_interior_installment(interior_installment)
}

/// Run the fixed single lineage through the host lowering. Installment zero is the uninterrupted
/// sibling; installment one returns after every exact interior move and is presented again until
/// the carried cursor reaches the light's true end.
fn continuation_host(founded: bool, interior_installment: usize) -> ContinuationTrace {
    let standing = vec![0u32; STANDING_CELLS * FORM_WORDS];
    let packed = pack_continuation_light();
    let own_words = if founded {
        STANDING_CELLS * OWN_CELL_WORDS
    } else {
        DENSE_CELLS * FORM_WORDS
    };
    let mut owns = vec![0u32; own_words];
    let mut carriers = vec![0u32; carrier_row_words(CONTINUATION_DEPTH)];
    let mut radiation = if founded {
        vec![0u32; CONTINUATION_LIGHT.len() * RADIATION_WORDS]
    } else {
        Vec::new()
    };
    let mut counts = [0u64; 4];
    let mut phase_mask = 0u32;
    let mut deepest = 0usize;
    let mut resumed_deposit = false;

    loop {
        let carrier_depth = manifold::carrier_row_depth(carriers.len());
        let prior_phase = continuation_face(&carriers).0;
        let own = WordSpan::new(0, owns.len());
        let carrier = WordSpan::new(0, carriers.len());
        let result = if founded {
            let radiation_words = WordSpan::new(0, radiation.len());
            carry_founded_stroke::<SliceWordSeam>(
                &standing,
                &mut owns,
                own,
                &mut carriers,
                carrier,
                &packed,
                &mut radiation,
                radiation_words,
                continuation_stroke(true, interior_installment),
            )
        } else {
            carry_dense_stroke::<SliceWordSeam>(
                &standing,
                &mut owns,
                own,
                &mut carriers,
                carrier,
                &packed,
                continuation_stroke(false, interior_installment),
            )
        }
        .expect("the fixed continuation lineage has one formed host layout");

        if manifold::continuation_is_efferent(prior_phase) && result.terms.total() != 0 {
            resumed_deposit = true;
        }
        counts[0] += result.terms.ride;
        counts[1] += result.terms.found_this;
        counts[2] += result.terms.found_that;
        counts[3] += result.terms.dark;
        observe_continuation(&carriers, &mut phase_mask, &mut deepest);
        if let Some(required_depth) = required_carrier_rebase_depth(&carriers) {
            let required_depth = usize::try_from(required_depth)
                .expect("the host gate can address its required carrier depth");
            let mut fresh = vec![0u32; carrier_row_words(required_depth)];
            assert_eq!(
                rebase_carrier_row(&carriers, &mut fresh),
                Some((carrier_depth, required_depth)),
                "the host gate mounts exactly the enclosure reached by the live continuation"
            );
            carriers = fresh;
            continue;
        }
        if result.cursor == CONTINUATION_LIGHT.len() as u64 {
            break;
        }
    }

    ContinuationTrace {
        owns,
        carriers,
        radiation,
        counts,
        phase_mask,
        deepest,
        resumed_deposit,
    }
}

/// The CUDA lowering of the same one-move dense continuation. OWN, carrier/K, and counts remain
/// resident; every launch presents the identical complete one-lineage grid.
fn continuation_cuda_dense(ctx: &Context, felt: &Function) -> Result<ContinuationTrace> {
    let standing_words = DENSE_CELLS * FORM_WORDS;
    let own_words = DENSE_CELLS * FORM_WORDS;
    let carrier_words = carrier_row_words(CONTINUATION_DEPTH);
    let standing = vec![0u32; standing_words];
    let packed = pack_continuation_light();
    let row = continuation_dense_row();
    let (grid, x_thread_stride) = scope_grid(1);
    let mut params: [u32; 8] = [
        DENSE_AXIS as u32,
        DENSE_CELLS as u32,
        1,
        carrier_words as u32,
        0,
        DRIVE,
        x_thread_stride,
        CONTINUATION_INSTALLMENT as u32,
    ];

    let standing_b: DeviceBuffer<u32> = DeviceBuffer::alloc(standing_words)?;
    standing_b.copy_from_slice(&standing)?;
    let owns_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(own_words)?;
    let mut carriers_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(carrier_words)?;
    let bytes_b: DeviceBuffer<u32> = DeviceBuffer::alloc(packed.len())?;
    bytes_b.copy_from_slice(&packed)?;
    let lanes_b: DeviceBuffer<u32> = DeviceBuffer::alloc(row.len())?;
    lanes_b.copy_from_slice(&row)?;
    let counts_b: DeviceBuffer<u64> = DeviceBuffer::alloc_zeroed(4)?;
    let params_b: DeviceBuffer<u32> = DeviceBuffer::alloc(params.len())?;
    params_b.copy_from_slice(&params)?;

    let (mut p_st, mut l_st) = (standing_b.device_ptr(), standing_words as u64);
    let (mut p_ow, mut l_ow) = (owns_b.device_ptr(), own_words as u64);
    let (mut p_ca, mut l_ca) = (carriers_b.device_ptr(), carrier_words as u64);
    let (mut p_by, mut l_by) = (bytes_b.device_ptr(), packed.len() as u64);
    let (mut p_la, mut l_la) = (lanes_b.device_ptr(), row.len() as u64);
    let (mut p_co, mut l_co) = (counts_b.device_ptr(), 4u64);
    let (mut p_pr, mut l_pr) = (params_b.device_ptr(), params.len() as u64);

    let mut carriers = vec![0u32; carrier_words];
    let mut counts = [0u64; 4];
    let mut phase_mask = 0u32;
    let mut deepest = 0usize;
    let mut resumed_deposit = false;
    loop {
        let prior_phase = continuation_face(&carriers).0;
        let prior_counts = counts;
        {
            let mut a: [*mut c_void; 14] = [
                arg(&mut p_st),
                arg(&mut l_st),
                arg(&mut p_ow),
                arg(&mut l_ow),
                arg(&mut p_ca),
                arg(&mut l_ca),
                arg(&mut p_by),
                arg(&mut l_by),
                arg(&mut p_la),
                arg(&mut l_la),
                arg(&mut p_co),
                arg(&mut l_co),
                arg(&mut p_pr),
                arg(&mut l_pr),
            ];
            felt.launch(grid, Dim3::x(BLOCK), &mut a)?;
            ctx.synchronize()?;
        }
        carriers_b.copy_to_slice(&mut carriers)?;
        counts_b.copy_to_slice(&mut counts)?;
        let mut emitted = false;
        for term in 0..4 {
            assert!(
                counts[term] >= prior_counts[term],
                "card term counts only accumulate"
            );
            emitted |= counts[term] != prior_counts[term];
        }
        if manifold::continuation_is_efferent(prior_phase) && emitted {
            resumed_deposit = true;
        }
        observe_continuation(&carriers, &mut phase_mask, &mut deepest);
        if let Some(required_depth) = required_carrier_rebase_depth(&carriers) {
            let old_depth = manifold::carrier_row_depth(carriers.len());
            let required_depth = usize::try_from(required_depth)
                .expect("the CUDA gate host can address its required carrier depth");
            let mut fresh = vec![0u32; carrier_row_words(required_depth)];
            assert_eq!(
                rebase_carrier_row(&carriers, &mut fresh),
                Some((old_depth, required_depth)),
                "the CUDA gate remounts exactly the enclosure reached by the live continuation"
            );
            let fresh_b: DeviceBuffer<u32> = DeviceBuffer::alloc(fresh.len())?;
            fresh_b.copy_from_slice(&fresh)?;
            carriers_b = fresh_b;
            p_ca = carriers_b.device_ptr();
            l_ca = fresh.len() as u64;
            params[3] = u32::try_from(fresh.len())
                .expect("the CUDA carrier row extent fits the native parameter word");
            params_b.copy_from_slice(&params)?;
            carriers = fresh;
            continue;
        }
        if continuation_cursor(&carriers) == CONTINUATION_LIGHT.len() as u64 {
            break;
        }
    }

    let mut owns = vec![0u32; own_words];
    owns_b.copy_to_slice(&mut owns)?;
    Ok(ContinuationTrace {
        owns,
        carriers,
        radiation: Vec::new(),
        counts,
        phase_mask,
        deepest,
        resumed_deposit,
    })
}

/// Founded continuation keeps the complete radiation aperture resident beside the same persistent
/// OWN and carrier/K buffers; no relaunch clears or replaces any prior atom's row.
fn continuation_cuda_founded(ctx: &Context, founded: &Function) -> Result<ContinuationTrace> {
    let standing_words = STANDING_CELLS * FORM_WORDS;
    let own_words = STANDING_CELLS * OWN_CELL_WORDS;
    let carrier_words = carrier_row_words(CONTINUATION_DEPTH);
    let radiation_words = CONTINUATION_LIGHT.len() * RADIATION_WORDS;
    let standing = vec![0u32; standing_words];
    let packed = pack_continuation_light();
    let row = continuation_founded_row();
    let (grid, x_thread_stride) = scope_grid(1);
    let mut params: [u32; 9] = [
        STANDING_AXIS as u32,
        STANDING_CELLS as u32,
        1,
        carrier_words as u32,
        0,
        DRIVE,
        RADIATION_WORDS as u32,
        x_thread_stride,
        CONTINUATION_INSTALLMENT as u32,
    ];

    let standing_b: DeviceBuffer<u32> = DeviceBuffer::alloc(standing_words)?;
    standing_b.copy_from_slice(&standing)?;
    let owns_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(own_words)?;
    let mut carriers_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(carrier_words)?;
    let bytes_b: DeviceBuffer<u32> = DeviceBuffer::alloc(packed.len())?;
    bytes_b.copy_from_slice(&packed)?;
    let lanes_b: DeviceBuffer<u32> = DeviceBuffer::alloc(row.len())?;
    lanes_b.copy_from_slice(&row)?;
    let counts_b: DeviceBuffer<u64> = DeviceBuffer::alloc_zeroed(4)?;
    let params_b: DeviceBuffer<u32> = DeviceBuffer::alloc(params.len())?;
    params_b.copy_from_slice(&params)?;
    let radiation_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(radiation_words)?;

    let (mut p_st, mut l_st) = (standing_b.device_ptr(), standing_words as u64);
    let (mut p_ow, mut l_ow) = (owns_b.device_ptr(), own_words as u64);
    let (mut p_ca, mut l_ca) = (carriers_b.device_ptr(), carrier_words as u64);
    let (mut p_by, mut l_by) = (bytes_b.device_ptr(), packed.len() as u64);
    let (mut p_la, mut l_la) = (lanes_b.device_ptr(), row.len() as u64);
    let (mut p_co, mut l_co) = (counts_b.device_ptr(), 4u64);
    let (mut p_pr, mut l_pr) = (params_b.device_ptr(), params.len() as u64);
    let (mut p_ra, mut l_ra) = (radiation_b.device_ptr(), radiation_words as u64);

    let mut carriers = vec![0u32; carrier_words];
    let mut counts = [0u64; 4];
    let mut phase_mask = 0u32;
    let mut deepest = 0usize;
    let mut resumed_deposit = false;
    loop {
        let prior_phase = continuation_face(&carriers).0;
        let prior_counts = counts;
        {
            let mut a: [*mut c_void; 16] = [
                arg(&mut p_st),
                arg(&mut l_st),
                arg(&mut p_ow),
                arg(&mut l_ow),
                arg(&mut p_ca),
                arg(&mut l_ca),
                arg(&mut p_by),
                arg(&mut l_by),
                arg(&mut p_la),
                arg(&mut l_la),
                arg(&mut p_co),
                arg(&mut l_co),
                arg(&mut p_pr),
                arg(&mut l_pr),
                arg(&mut p_ra),
                arg(&mut l_ra),
            ];
            founded.launch(grid, Dim3::x(BLOCK), &mut a)?;
            ctx.synchronize()?;
        }
        carriers_b.copy_to_slice(&mut carriers)?;
        counts_b.copy_to_slice(&mut counts)?;
        let mut emitted = false;
        for term in 0..4 {
            assert!(
                counts[term] >= prior_counts[term],
                "card term counts only accumulate"
            );
            emitted |= counts[term] != prior_counts[term];
        }
        if manifold::continuation_is_efferent(prior_phase) && emitted {
            resumed_deposit = true;
        }
        observe_continuation(&carriers, &mut phase_mask, &mut deepest);
        if let Some(required_depth) = required_carrier_rebase_depth(&carriers) {
            let old_depth = manifold::carrier_row_depth(carriers.len());
            let required_depth = usize::try_from(required_depth)
                .expect("the CUDA gate host can address its required carrier depth");
            let mut fresh = vec![0u32; carrier_row_words(required_depth)];
            assert_eq!(
                rebase_carrier_row(&carriers, &mut fresh),
                Some((old_depth, required_depth)),
                "the CUDA gate remounts exactly the enclosure reached by the live continuation"
            );
            let fresh_b: DeviceBuffer<u32> = DeviceBuffer::alloc(fresh.len())?;
            fresh_b.copy_from_slice(&fresh)?;
            carriers_b = fresh_b;
            p_ca = carriers_b.device_ptr();
            l_ca = fresh.len() as u64;
            params[3] = u32::try_from(fresh.len())
                .expect("the CUDA carrier row extent fits the native parameter word");
            params_b.copy_from_slice(&params)?;
            carriers = fresh;
            continue;
        }
        if continuation_cursor(&carriers) == CONTINUATION_LIGHT.len() as u64 {
            break;
        }
    }

    let mut owns = vec![0u32; own_words];
    owns_b.copy_to_slice(&mut owns)?;
    let mut radiation = vec![0u32; radiation_words];
    radiation_b.copy_to_slice(&mut radiation)?;
    Ok(ContinuationTrace {
        owns,
        carriers,
        radiation,
        counts,
        phase_mask,
        deepest,
        resumed_deposit,
    })
}

fn continuation_case(ctx: &Context, function: &Function, founded: bool) -> Result<bool> {
    let tag = if founded { "founded" } else { "dense" };
    let whole = continuation_host(founded, 0);
    let stepped = continuation_host(founded, CONTINUATION_INSTALLMENT);
    let card = if founded {
        continuation_cuda_founded(ctx, function)?
    } else {
        continuation_cuda_dense(ctx, function)?
    };

    let host_owns = stepped.owns == whole.owns;
    let host_carriers = stepped.carriers == whole.carriers;
    let host_radiation = stepped.radiation == whole.radiation;
    let host_counts = stepped.counts == whole.counts;
    let host_phases = stepped.phase_mask == 0xff;
    let expected_depth = whole.deepest;
    let host_deepest = stepped.deepest == expected_depth;
    let host_resumed = stepped.resumed_deposit;
    let card_owns = card.owns == whole.owns;
    let card_carriers = card.carriers == whole.carriers;
    let card_radiation = card.radiation == whole.radiation;
    let card_counts = card.counts == whole.counts;
    let card_phases = card.phase_mask == 0xff;
    let card_deepest = card.deepest == expected_depth;
    let card_resumed = card.resumed_deposit;
    let rows = continuation_founded_row();
    let host_canonical = !founded
        || (validate_radiation(&whole.radiation, &rows).is_ok()
            && validate_radiation(&stepped.radiation, &rows).is_ok());
    let card_canonical = !founded || validate_radiation(&card.radiation, &rows).is_ok();

    println!(
        "  {tag} host one-move: OWN {} · carrier/K {} · radiation {} · counts {} {:?} · canonical {} · phase {:#04x} {} · deepest {}/{} {} · resumed efferent deposit {}",
        face(host_owns), face(host_carriers), face(host_radiation), face(host_counts), stepped.counts,
        face(host_canonical), stepped.phase_mask, face(host_phases), stepped.deepest,
        expected_depth, face(host_deepest), face(host_resumed),
    );
    println!(
        "  {tag} CUDA one-move: OWN {} · carrier/K {} · radiation {} · counts {} {:?} · canonical {} · phase {:#04x} {} · deepest {}/{} {} · resumed efferent deposit {}",
        face(card_owns), face(card_carriers), face(card_radiation), face(card_counts), card.counts,
        face(card_canonical), card.phase_mask, face(card_phases), card.deepest,
        expected_depth, face(card_deepest), face(card_resumed),
    );
    if !(host_owns && host_carriers) {
        report_divergence(
            &format!("{tag} host continuation"),
            &stepped.owns,
            &whole.owns,
            &stepped.carriers,
            &whole.carriers,
        );
    }
    if !(card_owns && card_carriers) {
        report_divergence(
            &format!("{tag} CUDA continuation"),
            &card.owns,
            &whole.owns,
            &card.carriers,
            &whole.carriers,
        );
    }
    if !host_radiation {
        report_radiation_divergence(&stepped.radiation, &whole.radiation);
    }
    if !card_radiation {
        report_radiation_divergence(&card.radiation, &whole.radiation);
    }

    Ok(host_owns
        && host_carriers
        && host_radiation
        && host_counts
        && host_canonical
        && host_phases
        && host_deepest
        && host_resumed
        && card_owns
        && card_carriers
        && card_radiation
        && card_counts
        && card_canonical
        && card_phases
        && card_deepest
        && card_resumed)
}

fn report_radiation_divergence(card: &[u32], host: &[u32]) {
    if let Some(word) = card.iter().zip(host).position(|(card, host)| card != host) {
        eprintln!(
            "  founded: radiation diverges at row {} word {}: card {} host {}",
            word / RADIATION_WORDS,
            word % RADIATION_WORDS,
            card[word],
            host[word],
        );
    }
}

/// Print the first diverging OWN and carrier word, so a real drift bisects immediately.
fn report_divergence(
    tag: &str,
    card_owns: &[u32],
    host_owns: &[u32],
    card_carriers: &[u32],
    host_carriers: &[u32],
) {
    if let Some(i) = card_owns.iter().zip(host_owns).position(|(c, h)| c != h) {
        eprintln!(
            "  {tag}: OWN diverges at word {i}: card {} host {}",
            card_owns[i], host_owns[i]
        );
    }
    if let Some(i) = card_carriers
        .iter()
        .zip(host_carriers)
        .position(|(c, h)| c != h)
    {
        eprintln!(
            "  {tag}: carrier diverges at word {i}: card {} host {}",
            card_carriers[i], host_carriers[i]
        );
    }
}

fn run() -> Result<()> {
    let t_all = Instant::now();

    mount::cuda::init()?;
    let count = mount::Device::count()?;
    if count < 1 {
        eprintln!("FAILED: no CUDA device visible (cuDeviceGetCount == 0)");
        std::process::exit(1);
    }
    let mut chosen: Option<mount::Device> = None;
    for ord in 0..count {
        let dev = mount::Device::get(ord)?;
        if dev.name.contains("4080") {
            chosen = Some(dev);
            break;
        }
    }
    let device = match chosen {
        Some(d) => d,
        None => {
            eprintln!("FAILED: no device whose name contains \"4080\" (refusing to run elsewhere)");
            std::process::exit(1);
        }
    };
    println!("device: {}", device.name);
    let ctx = Context::create(&device)?;

    let ptx_head = String::from_utf8_lossy(PTX)
        .lines()
        .find(|l| l.trim_start().starts_with(".target"))
        .unwrap_or("<no .target>")
        .trim()
        .to_string();
    println!("ptx:    {} ({} bytes)", ptx_head, PTX.len());
    let module = Module::load_ptx(PTX)?;
    let felt = module.function("scope_felt")?;
    let founded = module.function("scope_founded")?;
    println!(
        "staged: dense axis {} ({} cells/lane) · founded standing axis {} ({} cells) · carrier depth {} · block {}",
        DENSE_AXIS, DENSE_CELLS, STANDING_AXIS, STANDING_CELLS, DEPTH, BLOCK
    );

    let mut all_ok = true;
    println!("== dense scope (scope_felt) — one thread, one dense lineage ==");
    for lanes in LANE_COUNTS {
        all_ok &= dense_case(&ctx, &felt, lanes)?;
    }
    println!("== founded scope (scope_founded) — one thread, one founded lineage ==");
    for lanes in LANE_COUNTS {
        all_ok &= founded_case(&ctx, &founded, lanes)?;
    }
    println!("== within-atom continuation — one move per full-grid relaunch ==");
    all_ok &= continuation_case(&ctx, &felt, false)?;
    all_ok &= continuation_case(&ctx, &founded, true)?;

    println!("total:  {} us", t_all.elapsed().as_micros());
    if all_ok {
        println!("mount scope gate: EXACT");
        Ok(())
    } else {
        println!("mount scope gate: MISMATCH");
        std::process::exit(1);
    }
}

fn main() {
    if let Err(e) = run() {
        eprintln!("FAILED: {}", e); // the driver's own error name + description (e.g. an Xid), then stop
        std::process::exit(2);
    }
}

#[cfg(test)]
mod tests {
    //! Host-side gates of the reference path (no GPU). They exercise the exact
    //! `carry_dense_stroke`/`carry_founded_stroke` calls the card is compared against, proving the
    //! reference is deterministic (the property byte-exactness relies on) and non-vacuous (the
    //! carrier/K row is always packed on a completed stroke), before the card is ever touched.
    use super::*;

    #[test]
    fn two_dimensional_scope_grid_names_each_lineage_once() {
        let lanes = 100usize;
        let (grid, x_thread_stride) = scope_grid(lanes);
        assert_eq!((grid.x, grid.y, grid.z), (1, 2, 1));
        assert_eq!(x_thread_stride, BLOCK);

        let mut visits = vec![0u8; lanes];
        for y in 0..grid.y {
            for x in 0..x_thread_stride {
                let lane = x as usize + y as usize * x_thread_stride as usize;
                if lane < lanes {
                    visits[lane] += 1;
                }
            }
        }
        assert!(visits.into_iter().all(|visits| visits == 1));
    }

    #[test]
    fn one_move_continuation_is_the_uninterrupted_construction_for_both_species() {
        for founded in [false, true] {
            let tag = if founded { "founded" } else { "dense" };
            let whole = continuation_host(founded, 0);
            let stepped = continuation_host(founded, CONTINUATION_INSTALLMENT);
            assert_eq!(
                stepped.owns, whole.owns,
                "{tag} one-move continuation preserves final OWN"
            );
            assert_eq!(
                stepped.carriers, whole.carriers,
                "{tag} one-move continuation preserves the whole carrier/K row"
            );
            assert_eq!(
                stepped.radiation, whole.radiation,
                "{tag} one-move continuation preserves every radiation word"
            );
            assert_eq!(
                stepped.counts, whole.counts,
                "{tag} one-move continuation accumulates the uninterrupted term counts"
            );
            assert_eq!(
                stepped.phase_mask, 0xff,
                "{tag} continuation crosses all eight phase faces"
            );
            assert_eq!(
                stepped.deepest, whole.deepest,
                "{tag} continuation crosses the same deepest enclosure as uninterrupted carriage"
            );
            assert!(
                stepped.deepest > CONTINUATION_DEPTH,
                "{tag} initial carrier reservation is not a construction ceiling"
            );
            assert!(
                stepped.resumed_deposit,
                "{tag} continuation deposits after resuming an efferent seam"
            );
            assert_eq!(
                continuation_cursor(&stepped.carriers),
                CONTINUATION_LIGHT.len() as u64,
                "{tag} continuation stops only at the light's true end"
            );
            assert!(stepped.owns.iter().any(|&word| word != 0));
            assert!(stepped.carriers.iter().any(|&word| word != 0));
            assert!(stepped.counts.iter().copied().sum::<u64>() != 0);
            if founded {
                let rows = continuation_founded_row();
                assert_eq!(validate_radiation(&stepped.radiation, &rows), Ok(()));
                let species = radiation_species(&stepped.radiation);
                assert!(species.0 != 0 && species.1 != 0 && species.2 != 0);
            } else {
                assert!(stepped.radiation.is_empty());
            }
        }
    }

    #[test]
    fn dense_reference_path_is_deterministic_and_nonvacuous() {
        for lanes in [1usize, 3, 64] {
            let standing = vec![0u32; DENSE_CELLS * FORM_WORDS];
            let (packed, rows) = pack_dense_light(lanes);
            let a = dense_reference(lanes, &standing, &packed, &rows);
            let b = dense_reference(lanes, &standing, &packed, &rows);
            assert_eq!(
                a, b,
                "the dense host reference is deterministic ({lanes} lanes)"
            );
            assert!(
                a.1.iter().any(|&w| w != 0),
                "the dense carrier/K rows are non-vacuous ({lanes} lanes)"
            );
            assert_eq!(a.2.len(), lanes * 4, "one 4-word count aperture per lane");
        }
    }

    #[test]
    fn founded_reference_path_is_deterministic_and_nonvacuous() {
        for (at, lanes) in LANE_COUNTS.into_iter().enumerate() {
            let expected_species = EXPECTED_RADIATION_SPECIES[at];
            let standing = vec![0u32; STANDING_CELLS * FORM_WORDS];
            let (packed, rows, total_own_cells) = pack_founded_light(lanes);
            let a = founded_reference(lanes, &standing, &packed, &rows, total_own_cells);
            let b = founded_reference(lanes, &standing, &packed, &rows, total_own_cells);
            assert_eq!(
                a, b,
                "the founded host reference is deterministic ({lanes} lanes)"
            );
            assert!(
                a.1.iter().any(|&w| w != 0),
                "the founded carrier/K rows are non-vacuous ({lanes} lanes)"
            );
            assert_eq!(
                a.0.len(),
                total_own_cells * OWN_CELL_WORDS,
                "the concatenated founded reservation is sized to the cohort"
            );
            assert_eq!(
                validate_radiation(&a.3, &rows),
                Ok(()),
                "every host radiation row is typed and every lane begins with zero padding ({lanes} lanes)"
            );
            assert_eq!(
                a.3.len(),
                founded_light_bytes(&rows).unwrap() * RADIATION_WORDS,
                "one complete radiation row stands beside every delivered octet"
            );
            assert_eq!(
                radiation_species(&a.3),
                expected_species,
                "the founded radiation fixture retains its exact non-vacuous FOLD/STEP/CUT species ({lanes} lanes)"
            );
            // The species tuple above is only readable beside the aperture it was measured at: a
            // lane still standing at the reservation contributed a truncated construction, and
            // nothing else in this gate would say so.
            let row_words = carrier_row_words(DEPTH);
            let limited: Vec<usize> = (0..lanes)
                .filter(|lane| {
                    required_carrier_rebase_depth(&a.1[lane * row_words..(lane + 1) * row_words])
                        .is_some()
                })
                .collect();
            assert_eq!(
                limited,
                RESERVATION_LIMITED_LANES[at],
                "exactly the pinned lanes are still standing at the declared carrier reservation ({lanes} lanes)"
            );
        }
    }

    /// A fixture that cannot be made to disagree is not measuring the path it names. Perturb one
    /// octet of the staged founded light — nothing else — and confirm the species tuple leaves its
    /// pinned value in every swept cohort. Without this, regenerating the constant against its own
    /// output would test nothing at all.
    #[test]
    fn the_founded_species_fixture_moves_when_the_reference_path_is_perturbed() {
        for (at, lanes) in LANE_COUNTS.into_iter().enumerate() {
            let standing = vec![0u32; STANDING_CELLS * FORM_WORDS];
            let (mut packed, rows, total_own_cells) = pack_founded_light(lanes);
            packed[0] ^= 0x5a; // one octet of lane zero's raw light
            let perturbed = founded_reference(lanes, &standing, &packed, &rows, total_own_cells);
            assert_ne!(
                radiation_species(&perturbed.3),
                EXPECTED_RADIATION_SPECIES[at],
                "the pinned species tuple is a live measurement of the founded reference path ({lanes} lanes)"
            );
        }
    }

    #[test]
    fn radiation_validation_rejects_noncanonical_flags_and_dormant_payload() {
        let rows = [0, 2, 1, 3, 0, 0, 0, 2];
        let mut radiation = vec![0u32; 2 * RADIATION_WORDS];
        assert_eq!(validate_radiation(&radiation, &rows), Ok(()));

        radiation[RADIATION_WORDS + RADIATION_FLAGS] = RADIATION_STEP;
        assert!(validate_radiation(&radiation, &rows)
            .unwrap_err()
            .contains("canonical AtomEvent flag species"));

        radiation[RADIATION_WORDS + RADIATION_FLAGS] = RADIATION_FOLD;
        radiation[RADIATION_WORDS + RADIATION_GRIP] = 1;
        assert!(validate_radiation(&radiation, &rows)
            .unwrap_err()
            .contains("no dormant payload"));

        radiation[RADIATION_WORDS..].fill(0);
        radiation[RADIATION_WORDS + RADIATION_FLAGS] = RADIATION_FOLD | RADIATION_STEP;
        radiation[RADIATION_WORDS + RADIATION_BRICK] = 1;
        assert!(validate_radiation(&radiation, &rows)
            .unwrap_err()
            .contains("no dormant brick payload"));

        radiation[RADIATION_WORDS..].fill(0);
        radiation[0] = RADIATION_FOLD;
        assert!(validate_radiation(&radiation, &rows)
            .unwrap_err()
            .contains("row zero"));
    }
}
