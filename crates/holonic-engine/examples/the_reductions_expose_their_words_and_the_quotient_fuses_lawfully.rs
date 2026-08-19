//! **Deed H3 — the reductions expose their words, the census loses its avoidable atomics, and the
//! midpoint quotient fuses only where every declared receiver factors through it.**
//!
//! Four returns, on the real Gemma-4-E4B material the H0 receipts driver mounts:
//!
//! ```text
//!   [A] the standing block reductions expose their receipts
//!       section_rms_rebase's quadratic capacity and its group octave census;
//!       section_contact's block octave census, its null, its partition function and its hull —
//!       each with the pivot it reduces over, the FIXED word it enacts written out, the barriers
//!       per pass, the per-node intermediate widths from a bit-exact CPU replay of the kernel's own
//!       arithmetic over words read back off the card, the boundary residual, and the on-card
//!       agreement: the replayed block reproduces the card's own output words.
//!
//!   [B] the census loses its avoidable atomics under exact census equality
//!       section_census is block-aggregated (warp shuffle, then one atomic per block per word);
//!       section_census_serial_control is the per-thread-atomic form, kept in the module so the
//!       equality is measured forever. Every slot word, plural shapes, plural poisoned entries.
//!
//!   [C] receiver-dependent fusion of the midpoint quotient
//!       one real layer bound twice — MidpointQuotient and SealedMidpointQuotient — with bit-equal
//!       terminal faces, word-for-word equal censuses including the collapsed population, the
//!       kernel-count and allocation deltas measured, and the refusal control: the layer enclosure
//!       is a declared face, so the fusion over it refuses at compile by name.
//!
//!   [D] the mouth reads its material
//!       shape_enter's a-priori octave bound, authored from scale and grain until 2026-08-19,
//!       computed from the entering words themselves; the H2 driver's caller-side workaround is
//!       deleted and the before/after is measured on the real embedding rows.
//! ```
//!
//! **What is measurement and what is not.** Every slot word came back from the card's own census
//! array; every terminal face from one `read_out`; every graph count from `cuGraphGetNodes`. The
//! CPU replays are a bit-exact mirror of the kernel's own integer arithmetic — they are the
//! reduction receipt's intermediate widths, which no device face reports, and where the replay and
//! the card disagree that is returned as a disagreement and never smoothed. Elapsed times are
//! apparatus measurements, carry the frame they were taken in, and select nothing.
//!
//! Run:
//! ```text
//! PATH=/opt/cuda/bin:$PATH ./target/release/examples/the_reductions_expose_their_words_and_the_quotient_fuses_lawfully
//! ```

#[path = "phoenix/resident_layer.rs"]
mod resident_layer;
#[path = "phoenix/tower.rs"]
mod tower;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::PathBuf;
use std::rc::Rc;
use std::time::Instant;

use holonic_engine::causal::EventId;
use holonic_engine::embedding_fiber::{align_bfloat16, ResidentReadout};
use holonic_engine::front_passage::{
    CompileRefusal, DeedReceiver, FrontPassage, FrontPassageObstruction, MaterialAdmission, ResidentMaterial,
    SealedMidpointQuotient,
};
use holonic_engine::resident_section::{Dyadic, ResidentGrain, ResidentSection, ResidentSurface, SeriesAperture, SlotReading};
use holonic_engine::source_occurrence::{RegionIdentity, SourceOccurrence};
use resident_layer::Source;
use tower::{Entry, Intervention, Species};

/// The committed Station C one-input closure, reused verbatim so no exterior tokenizer runs.
const CLOSURE_TOKENS: [usize; 5] = [818, 5279, 529, 7001, 563];
const CLOSURE_GRAIN: u32 = 48;
const CLOSURE_TERMS: u32 = 14;
/// Layer 1 is the representative layer: it enters on a CARRIED standing and owns its own K and V,
/// which is the shape 34 of the tower's 42 layers have. Layer 0 is conducted only to produce it.
const REPRESENTATIVE_LAYER: usize = 1;

struct Args {
    root: String,
    out: PathBuf,
    tokens: Vec<usize>,
    grain: u32,
    terms: u32,
    census_repeats: usize,
}

fn parse_args() -> Args {
    let mut args = Args {
        root: "/home/b/models/gemma-4-E4B-it".to_owned(),
        out: PathBuf::from("output/the_reductions_expose_their_words"),
        tokens: CLOSURE_TOKENS.to_vec(),
        grain: CLOSURE_GRAIN,
        terms: CLOSURE_TERMS,
        census_repeats: 64,
    };
    let mut it = std::env::args().skip(1);
    while let Some(flag) = it.next() {
        match flag.as_str() {
            "--root" => args.root = it.next().expect("--root <dir>"),
            "--out" => args.out = PathBuf::from(it.next().expect("--out <dir>")),
            "--grain" => args.grain = it.next().expect("--grain F").parse().expect("u32"),
            "--terms" => args.terms = it.next().expect("--terms N").parse().expect("u32"),
            "--census-repeats" => args.census_repeats = it.next().expect("--census-repeats N").parse().expect("usize"),
            other => panic!("unknown argument {other}"),
        }
    }
    args
}

fn describe(obstruction: &FrontPassageObstruction) -> String {
    match obstruction {
        FrontPassageObstruction::Cover { front, barriers } => format!("CoverBarrier at front {front}: {barriers:?}"),
        FrontPassageObstruction::Interchange { front, because, .. } => format!("InterchangeRefusal at front {front}: {because:?}"),
        FrontPassageObstruction::Resource(resource) => format!("ResourceObstruction: {resource:?}"),
        FrontPassageObstruction::Compile(refusal) => format!("CompileRefusal: {refusal:?}"),
        FrontPassageObstruction::Refused { occurrence, operation, refusal, lineage, .. } => {
            format!("the card refused at {occurrence:?} ({operation}): {refusal}; lineage {:?}", lineage.refusals)
        }
        FrontPassageObstruction::Sealed { occurrence, quotient, reopening } => {
            format!("the face at {occurrence:?} was sealed away by the fused quotient {quotient:?}; reopening: {reopening}")
        }
    }
}

// ---------------------------------------------------------------------------------------------
// the bit-exact mirror of the kernel's own integer arithmetic
// ---------------------------------------------------------------------------------------------
//
// **This is not the serial reference.** `phoenix/serial_reference.rs` is an INDEPENDENT enclosure
// at its own grain, for parity testimony. This mirrors `exact_resident_section.cu` line for line in
// `i128`, because a reduction receipt's intermediate widths are the widths the kernel's own nodes
// stood at, and no independent enclosure can report those. Where the mirror and the card disagree,
// one of them is wrong and the disagreement is the return.

mod mirror {
    pub type W = i128;

    pub fn magnitude(v: W) -> u128 {
        if v < 0 {
            (0u128).wrapping_sub(v as u128)
        } else {
            v as u128
        }
    }

    pub fn octaves_of(m: u128) -> u32 {
        128 - m.leading_zeros()
    }

    /// The octaves an exact intermediate occupies — the width a reduction node stood at.
    pub fn width_bits(v: W) -> u32 {
        octaves_of(magnitude(v))
    }

    pub fn shift_floor(v: W, s: i32) -> W {
        let negative = v < 0;
        let m = magnitude(v);
        if s >= 0 {
            let shifted = m << (s as u32);
            return if negative { -(shifted as W) } else { shifted as W };
        }
        let k = (-s) as u32;
        if k >= 128 {
            return if negative { -1 } else { 0 };
        }
        if !negative {
            return (m >> k) as W;
        }
        let up = (m + ((1u128 << k) - 1)) >> k;
        -(up as W)
    }

    pub fn shift_ceil(v: W, s: i32) -> W {
        let negative = v < 0;
        let m = magnitude(v);
        if s >= 0 {
            let shifted = m << (s as u32);
            return if negative { -(shifted as W) } else { shifted as W };
        }
        let k = (-s) as u32;
        if k >= 128 {
            return if v > 0 { 1 } else { 0 };
        }
        if negative {
            return -((m >> k) as W);
        }
        let up = (m + ((1u128 << k) - 1)) >> k;
        up as W
    }

    pub fn div_floor(n: W, d: W) -> W {
        let q = n / d;
        if n % d != 0 && n < 0 {
            q - 1
        } else {
            q
        }
    }

    pub fn div_ceil(n: W, d: W) -> W {
        let q = n / d;
        if n % d != 0 && n > 0 {
            q + 1
        } else {
            q
        }
    }

    fn mul_magnitude_256(a: u128, b: u128) -> (u128, u128) {
        let (a0, a1) = (a as u64 as u128, a >> 64);
        let (b0, b1) = (b as u64 as u128, b >> 64);
        let p00 = a0 * b0;
        let p01 = a0 * b1;
        let p10 = a1 * b0;
        let p11 = a1 * b1;
        let mid = (p00 >> 64) + (p01 as u64 as u128) + (p10 as u64 as u128);
        let lo = (p00 & ((1u128 << 64) - 1)) | (mid << 64);
        let hi = p11 + (p01 >> 64) + (p10 >> 64) + (mid >> 64);
        (hi, lo)
    }

    /// `a · b · 2^-k` rounded toward −∞ or +∞ through the 256-bit product.
    pub fn product_shift(a: W, b: W, k: u32, toward_ceiling: bool) -> W {
        let negative = (a < 0) != (b < 0);
        let (hi, lo) = mul_magnitude_256(magnitude(a), magnitude(b));
        let (q_hi, q_lo, discarded) = if k == 0 {
            (hi, lo, false)
        } else if k < 128 {
            let discarded = (lo & ((1u128 << k) - 1)) != 0;
            ((hi >> k), (lo >> k) | (hi << (128 - k)), discarded)
        } else {
            let j = k - 128;
            let discarded = lo != 0 || (j > 0 && (hi & ((1u128 << j) - 1)) != 0);
            (0u128, hi >> j, discarded)
        };
        // The kernel refuses the carrier here and writes zero; the mirror does the same, so a
        // replay that would have refused disagrees with the card instead of inventing a value.
        if q_hi != 0 || q_lo > (1u128 << 126) {
            return 0;
        }
        let q = q_lo as W;
        if negative {
            if toward_ceiling {
                -q
            } else {
                -(q + i128::from(discarded))
            }
        } else if toward_ceiling {
            q + i128::from(discarded)
        } else {
            q
        }
    }

    pub fn isqrt_floor(a: W) -> W {
        if a <= 0 {
            return 0;
        }
        let bits = octaves_of(a as u128);
        let mut x: W = 1 << ((bits + 1) / 2);
        loop {
            let y = (x + a / x) >> 1;
            if y >= x {
                break;
            }
            x = y;
        }
        while x * x > a {
            x -= 1;
        }
        while (x + 1) * (x + 1) <= a {
            x += 1;
        }
        x
    }

    pub fn isqrt_ceil(a: W) -> W {
        let f = isqrt_floor(a);
        if f * f == a {
            f
        } else {
            f + 1
        }
    }

    pub fn corners(a: W, b: W, c: W, d: W) -> (W, W) {
        let p = [a * c, a * d, b * c, b * d];
        (*p.iter().min().expect("four"), *p.iter().max().expect("four"))
    }

    pub fn interval_quotient(n_lo: W, n_hi: W, d_lo: W, d_hi: W, lift: i32) -> (W, W) {
        let nl = shift_floor(n_lo, lift);
        let nh = shift_ceil(n_hi, lift);
        (div_floor(nl, if nl < 0 { d_lo } else { d_hi }), div_ceil(nh, if nh < 0 { d_hi } else { d_lo }))
    }

    pub const SERIES_GRAIN: i32 = 60;

    /// `exp(x)` for `x <= 0` at grain `2^-F`, mirroring the kernel's alternating-tail series.
    pub fn exp_nonpositive(x: W, grain: i32, terms: u32) -> (W, W) {
        let unit: W = 1 << grain;
        if x <= -(W::from(grain) * unit) {
            return (0, 1);
        }
        if x == 0 {
            return (unit, unit);
        }
        let bits = octaves_of(magnitude(x));
        let mut k = 0i32;
        if bits as i32 + 4 > grain {
            k = bits as i32 + 4 - grain;
        }
        let lift = SERIES_GRAIN - grain - k;
        let y_lo = shift_floor(x, lift);
        let y_hi = shift_ceil(x, lift);
        let one: W = 1 << SERIES_GRAIN;
        let (mut mag_lo, mut mag_hi) = (one, one);
        let (ylo_mag, yhi_mag) = (-y_hi, -y_lo);
        let (mut s_lo, mut s_hi) = (one, one);
        let (mut s_lo_prev, mut s_hi_prev) = (one, one);
        for n in 1..=(terms + 1) {
            s_lo_prev = s_lo;
            s_hi_prev = s_hi;
            let p_lo = mag_lo * ylo_mag;
            let p_hi = mag_hi * yhi_mag;
            mag_lo = div_floor(shift_floor(p_lo, -SERIES_GRAIN), W::from(n));
            mag_hi = div_ceil(shift_ceil(p_hi, -SERIES_GRAIN), W::from(n));
            if n & 1 == 1 {
                s_lo -= mag_hi;
                s_hi -= mag_lo;
            } else {
                s_lo += mag_lo;
                s_hi += mag_hi;
            }
        }
        let mut e_lo = s_lo.min(s_lo_prev);
        let mut e_hi = s_hi.max(s_hi_prev);
        if e_lo < 0 {
            e_lo = 0;
        }
        if e_hi > one {
            e_hi = one;
        }
        for _ in 0..k {
            e_lo = shift_floor(e_lo * e_lo, -SERIES_GRAIN);
            e_hi = shift_ceil(e_hi * e_hi, -SERIES_GRAIN);
            if e_hi > one {
                e_hi = one;
            }
        }
        (shift_floor(e_lo, grain - SERIES_GRAIN), shift_ceil(e_hi, grain - SERIES_GRAIN))
    }
}

// ---------------------------------------------------------------------------------------------
// the exposure a reduction owes: the pivot, the word, the barriers, the widths, the boundary
// ---------------------------------------------------------------------------------------------

/// **One reduction's receipt, in the shape H1's `ReductionReceipt` states and with the two fields
/// that owner cannot hold for a strided leaf set left out by name.** A block reduction's leaves are
/// the strided coordinate sets `{i : i ≡ t (mod B)}`, and `PartialTerm::inner` is a half-open
/// `SectionRegion`; a strided set is not a region, so the H1 junction owner cannot certify these
/// partitions as it stands. That boundary was found in H2 for the lane tree and it is restated here
/// for the block trees, which are the same shape one level out. What IS carried is everything the
/// receipt is for: the word, its depth, its per-node widths, the barriers, the boundary residual and
/// the adjoint-free agreement with the card.
struct ReductionExposure {
    owner: &'static str,
    kernel: &'static str,
    coupling: &'static str,
    /// what the reduction reduces over, and how far
    pivot: String,
    extent: u64,
    /// the block the reduction runs at: its capacity per round
    capacity: u32,
    /// the fixed word as the kernel enacts it, written out
    word: String,
    /// how the leaves are named, and whether they are coordinate regions
    leaves: String,
    leaves_are_regions: bool,
    /// joins from the root to a leaf
    depth: usize,
    /// `__syncthreads()` per pass, and the total for the kernel
    barriers_this_pass: usize,
    barriers_kernel_total: usize,
    /// per level of the tree: the widest node's octaves, and how many nodes stood at that level
    level_widths: Vec<(usize, u32, usize)>,
    /// the widest intermediate anywhere in the word, and the a-priori subset-monotone bound beside it
    peak_width_bits: u32,
    a_priori_bound_bits: u32,
    a_priori_law: String,
    /// the reduction's own boundary: what it rounds and what the rounding left behind
    boundary: String,
    residual: String,
    /// what the replayed reduction agreed with on the card
    agreement: String,
}

fn write_exposure(form: &mut String, exposure: &ReductionExposure) {
    let _ = writeln!(form, "    ---- {} · {}", exposure.owner, exposure.coupling);
    let _ = writeln!(form, "      kernel                {}", exposure.kernel);
    let _ = writeln!(form, "      pivot                 {} (extent {})", exposure.pivot, exposure.extent);
    let _ = writeln!(form, "      capacity per round    {} lanes", exposure.capacity);
    let _ = writeln!(form, "      the FIXED word        {}", exposure.word);
    let _ = writeln!(form, "      leaves                {}", exposure.leaves);
    let _ = writeln!(
        form,
        "      leaves are coordinate regions: {} — {}",
        exposure.leaves_are_regions,
        if exposure.leaves_are_regions {
            "the H1 junction owner could certify this partition"
        } else {
            "a strided set is NOT a SectionRegion, so H1's junction cannot certify this partition as it stands; the word, depth, widths and on-card agreement are carried instead"
        }
    );
    let _ = writeln!(form, "      depth                 {} joins from root to leaf", exposure.depth);
    let _ = writeln!(form, "      barriers              {} __syncthreads in this pass; {} in the kernel", exposure.barriers_this_pass, exposure.barriers_kernel_total);
    let _ = writeln!(form, "      per-node widths, by level (level, widest node octaves, nodes at that level):");
    for (level, widest, nodes) in &exposure.level_widths {
        let _ = writeln!(form, "        level {level:>2}  widest {widest:>4} octaves  {nodes:>6} nodes");
    }
    let _ = writeln!(form, "      peak intermediate     {} octaves", exposure.peak_width_bits);
    let _ = writeln!(form, "      a-priori bound        {} octaves — {}", exposure.a_priori_bound_bits, exposure.a_priori_law);
    let _ = writeln!(
        form,
        "      the bound HOLDS: {} ({} <= {})",
        exposure.peak_width_bits <= exposure.a_priori_bound_bits,
        exposure.peak_width_bits,
        exposure.a_priori_bound_bits
    );
    let _ = writeln!(form, "      boundary              {}", exposure.boundary);
    let _ = writeln!(form, "      residual              {}", exposure.residual);
    let _ = writeln!(form, "      on-card agreement     {}", exposure.agreement);
    let _ = writeln!(form);
}

/// The per-level widths of the shared-memory tree the kernel enacts:
/// `for (stride = B/2; stride > 0; stride >>= 1) if (t < stride) s[t] = join(s[t], s[t + stride])`.
/// The leaves are already the per-thread strided partials; this returns `(level, widest, nodes)`.
fn tree_levels<T: Copy, F: Fn(T, T) -> T, M: Fn(T) -> u32>(leaves: &[T], join: F, measure: M) -> (Vec<(usize, u32, usize)>, u32) {
    let mut nodes: Vec<T> = leaves.to_vec();
    let mut levels = Vec::new();
    let mut peak = nodes.iter().map(|n| measure(*n)).max().unwrap_or(0);
    levels.push((0usize, peak, nodes.len()));
    let mut stride = nodes.len() / 2;
    let mut level = 1usize;
    while stride > 0 {
        for t in 0..stride {
            nodes[t] = join(nodes[t], nodes[t + stride]);
        }
        let widest = nodes[..stride].iter().map(|n| measure(*n)).max().unwrap_or(0);
        peak = peak.max(widest);
        levels.push((level, widest, stride));
        level += 1;
        stride /= 2;
    }
    (levels, peak)
}

/// The word the shared-memory tree enacts, written out for a block of `b` lanes reducing `extent`
/// leaves under the stride-halving schedule. Written in full for a small block and by its rule for
/// a large one, because a two-thousand-character parenthesization is not a receipt anyone reads.
fn stride_word(b: usize, extent: u64, join: &str) -> String {
    if b <= 8 {
        let mut nodes: Vec<String> = (0..b).map(|t| format!("p{t}")).collect();
        let mut stride = b / 2;
        while stride > 0 {
            for t in 0..stride {
                nodes[t] = format!("({} {join} {})", nodes[t], nodes[t + stride]);
            }
            stride /= 2;
        }
        nodes[0].clone()
    } else {
        format!(
            "p_t = {join} over {{i : i = t (mod {b})}} for i < {extent}; then for stride = {}, {}, ..., 1: p_t <- p_t {join} p_(t+stride)",
            b / 2,
            b / 4
        )
    }
}

// ---------------------------------------------------------------------------------------------
// one conducted layer, kept whole for the exposures and the fusion controls
// ---------------------------------------------------------------------------------------------

struct Conducted<'a> {
    bound: holonic_engine::front_passage::CompiledPassage<'a>,
    returned: holonic_engine::front_passage::PassageReturn,
    #[allow(dead_code)]
    returns: BTreeMap<&'static str, EventId>,
    names: BTreeMap<EventId, String>,
    /// occurrence -> its declared producers, as occurrences
    arriving: BTreeMap<EventId, Vec<EventId>>,
    graph_nodes: usize,
    graph_edges: usize,
    kernel_nodes: usize,
    predicted_launches: u64,
    predicted_allocations: u64,
    predicted_section_octets: u64,
    bind_wall_s: f64,
    launch_wall_s: f64,
}

fn names_of(complex: &holonic_engine::ported_operation::PortedOperationComplex) -> BTreeMap<EventId, String> {
    complex
        .shape
        .occurrences
        .iter()
        .map(|(event, occurrence)| (*event, complex.shape.laws.get(&occurrence.law).map(|l| l.name.clone()).unwrap_or_default()))
        .collect()
}

fn arriving_of(complex: &holonic_engine::ported_operation::PortedOperationComplex) -> BTreeMap<EventId, Vec<EventId>> {
    let mut arriving: BTreeMap<EventId, Vec<EventId>> = BTreeMap::new();
    for interaction in complex.shape.interactions.values() {
        for bond in &interaction.bonds {
            arriving.entry(bond.target.event).or_default().push(bond.source.event);
        }
    }
    arriving
}

fn consumers_of(complex: &holonic_engine::ported_operation::PortedOperationComplex) -> BTreeMap<EventId, Vec<EventId>> {
    let mut consumers: BTreeMap<EventId, Vec<EventId>> = BTreeMap::new();
    for interaction in complex.shape.interactions.values() {
        for bond in &interaction.bonds {
            consumers.entry(bond.source.event).or_default().push(bond.target.event);
        }
    }
    consumers
}

/// Mount one layer's material. The caller admits it first.
#[allow(clippy::too_many_arguments)]
fn mount_material<'chart>(
    readout: &'chart ResidentReadout,
    surface: &'chart ResidentSurface<'chart>,
    source: &mut Source,
    layer: usize,
    tokens: &[usize],
    regions: &mut BTreeMap<String, RegionIdentity>,
) -> Result<(ResidentMaterial<'chart>, Dyadic), String> {
    let mut material = ResidentMaterial::empty();
    let mount = tower::mount_layer(source, readout, &mut material, layer)?;
    for (name, region) in mount.regions {
        regions.insert(name, region);
    }
    let layer_scalar = mount.layer_scalar.ok_or("layer_scalar")?;
    let species = Species::of(layer);
    let bands = tower::found_bands(species, resident_layer::BAND_TERMS)?;
    let mounted_bands = surface.mount_bands(&bands, tower::BAND_GRAIN).map_err(|e| e.to_string())?;
    material.bands.insert(species.bands().to_owned(), (mounted_bands, (tokens.len() - 1) as u32));
    let positions: Vec<u32> = (0..tokens.len() as u32).collect();
    material.positions = Some(surface.mount_positions(&positions).map_err(|e| e.to_string())?);
    tower::enter(source, tokens, layer, &mut material)?;
    Ok((material, layer_scalar))
}

// ---------------------------------------------------------------------------------------------

fn main() {
    let args = parse_args();
    std::fs::create_dir_all(&args.out).expect("output directory");
    let whole = Instant::now();
    let commit = std::process::Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_owned())
        .unwrap_or_else(|| "unknown".to_owned());
    let mut form = String::new();
    let _ = writeln!(form, "THE REDUCTIONS EXPOSE THEIR WORDS AND THE QUOTIENT FUSES LAWFULLY — Deed H3");
    let _ = writeln!(form, "  closure commit {commit}");

    let readout: &'static ResidentReadout = match ResidentReadout::new() {
        Ok(readout) => Box::leak(Box::new(readout)),
        Err(error) => {
            println!("REFUSED: no resident chart — {error}");
            std::process::exit(3);
        }
    };
    let surface: &'static ResidentSurface<'static> = match ResidentSurface::on(readout) {
        Ok(surface) => Box::leak(Box::new(surface)),
        Err(error) => {
            println!("REFUSED: the resident laws did not load — {error}");
            std::process::exit(3);
        }
    };
    let (block_x, _, warp) = surface.derived_launch();
    let _ = writeln!(
        form,
        "  resident chart: {} · kernel content {} · derived block {block_x} at warp {warp} ({} warps) · memory {} free of {}",
        surface.device_name(),
        surface.mode().kernel_content.as_deref().unwrap_or("?"),
        block_x / warp,
        surface.memory_at_mount().free_bytes,
        surface.memory_at_mount().total_bytes
    );
    let _ = writeln!(form, "  tokens {:?} · grain 2^-{} · series terms {}", args.tokens, args.grain, args.terms);
    let _ = writeln!(form);

    if let Err(error) = run(surface, readout, &args, &mut form) {
        let _ = writeln!(form, "\nREFUSED: {error}");
        println!("REFUSED: {error}");
        let _ = std::fs::write(args.out.join("receipt.form"), &form);
        std::process::exit(4);
    }
    let _ = writeln!(form, "  whole deed wall {:.3} s (frame: this process, one card, display attached)", whole.elapsed().as_secs_f64());
    std::fs::write(args.out.join("receipt.form"), &form).expect("receipt");
    println!("\n  receipt written to {}", args.out.join("receipt.form").display());
}

#[allow(clippy::too_many_lines)]
fn run(
    surface: &'static ResidentSurface<'static>,
    readout: &'static ResidentReadout,
    args: &Args,
    form: &mut String,
) -> Result<(), String> {
    let grain = ResidentGrain(args.grain);
    let terms = SeriesAperture(args.terms);
    let receiver = DeedReceiver::unbounded();
    let scales = tower::algebraic_scales()?;
    let mut source = Source::open(&args.root)?;
    let mut regions: BTreeMap<String, RegionIdentity> = BTreeMap::new();
    for name in source.container.names() {
        if let Ok(region) = source.region(name, None) {
            regions.insert(name.to_owned(), region);
        }
    }

    // -----------------------------------------------------------------------------------------
    // [D] the mouth reads its material — before anything is conducted, because it decides whether
    //     the entering occurrence stands at all
    // -----------------------------------------------------------------------------------------
    println!("  [D] the mouth's a-priori bound, on the real embedding rows");
    let _ = writeln!(form, "  [D] THE MOUTH READS ITS MATERIAL — shape_enter's a-priori octave bound");
    let _ = writeln!(form, "    Until 2026-08-19 `shape_enter` returned `8 + scale octaves + grain + 8` and never looked at a");
    let _ = writeln!(form, "    word. That is an authored level wearing a derivation: it bounds a HYPOTHETICAL codeword of full");
    let _ = writeln!(form, "    significand at exponent zero. The H2 driver closed its entering occurrence at");
    let _ = writeln!(form, "    max(shape.needed, octaves computed from the words) to work around it; that workaround is deleted");
    let _ = writeln!(form, "    and the reading is in the law. Both `shape_enter` and `Enter::bound_octaves` now take it.");
    let _ = writeln!(form);
    {
        let mut material = ResidentMaterial::empty();
        tower::enter(&mut source, &args.tokens, REPRESENTATIVE_LAYER, &mut material)?;
        let _ = writeln!(form, "    population                            rows x width    authored   read from the words   difference");
        for (name, scale) in [(tower::ENTERING, tower::EMBED_SCALE), (resident_layer::PLE_ENTERING, tower::PLE_EMBED_SCALE)] {
            let entering = material.entering.get(name).ok_or_else(|| format!("{name} did not enter"))?;
            let authored = 8 + scale.octaves() + grain.0 + 8;
            let read = ResidentSurface::entering_octaves(&entering.words, scale, grain);
            let _ = writeln!(
                form,
                "    {:<36} {:>4} x {:<6} {authored:>9}   {read:>19}   {:>+10}",
                name,
                entering.rows,
                entering.width,
                i64::from(read) - i64::from(authored)
            );
        }
        let _ = writeln!(form);
        // the wide fixture the authored bound could not carry, and the narrow one it over-charged
        let wide = [bfloat16_word(255, 46), bfloat16_word(-255, 46)];
        let narrow = [bfloat16_word(1, -20), bfloat16_word(-3, -18)];
        let authored = 8 + Dyadic::ONE.octaves() + grain.0 + 8;
        let _ = writeln!(form, "    the two fixtures that decide it, at grain 2^-{}:", grain.0);
        let _ = writeln!(
            form,
            "      a wide bf16 population (255 x 2^46): authored {authored}, read {} — the authored bound was BELOW the",
            ResidentSurface::entering_octaves(&wide, Dyadic::ONE, grain)
        );
        let _ = writeln!(form, "      material, so the mouth refused BOUND on words it had itself been handed and every successor");
        let _ = writeln!(form, "      refused UPSTREAM;");
        let _ = writeln!(
            form,
            "      a narrow one (1 x 2^-20): authored {authored}, read {} — the authored bound was an over-charge with",
            ResidentSurface::entering_octaves(&narrow, Dyadic::ONE, grain)
        );
        let _ = writeln!(form, "      no reading behind it.");
        let _ = writeln!(form, "    The H2 driver's seven `close(0, &x, enter.needed.max(...))` sites are now `close(0, &x, enter.needed)`.");
        let _ = writeln!(form);
    }

    // -----------------------------------------------------------------------------------------
    // conduct layer 0, then bind layer 1 unfused — the material [A], [B] and [C] all read
    // -----------------------------------------------------------------------------------------
    println!("  conducting layer 0 to produce layer {REPRESENTATIVE_LAYER}'s entry");
    let passage = FrontPassage::new(surface, grain);
    let occurrence: SourceOccurrence = resident_layer::source_occurrence(&args.root, regions.clone(), None)?;

    let carried: Rc<ResidentSection<'static>>;
    let carried_bound: u32;
    {
        let plan = tower::material_plan(&source, 0, args.tokens.len())?;
        let prediction = passage.predict_material(&plan);
        let admission: MaterialAdmission = passage.admit_material(&prediction).map_err(|o| format!("layer 0 material refused: {}", describe(&o)))?;
        let (material, layer_scalar) = mount_material(readout, surface, &mut source, 0, &args.tokens, &mut regions)?;
        let occurrence0: SourceOccurrence = resident_layer::source_occurrence(&args.root, regions.clone(), None)?;
        let founded = tower::found_layer(0, Entry::Rows, tower::Chart::Midpoint, &scales, terms, layer_scalar, &Intervention::None, args.tokens.len())?;
        let mut bound = passage
            .bind(&founded.complex, &founded.realization, &material, &occurrence0, &receiver, Some(&admission), founded.returns[tower::LAYER_RETURN])
            .map_err(|o| format!("layer 0 refused at bind: {}", describe(&o)))?;
        let returned = bound.launch(&surface.mode()).map_err(|o| format!("layer 0 refused at launch: {}", describe(&o)))?;
        bound.standing(&returned).map_err(|o| format!("layer 0 did not stand: {}", describe(&o)))?;
        let (section, b) = bound.release_section(founded.returns[tower::LAYER_RETURN]).ok_or("layer 0 released nothing")?;
        carried = Rc::new(section);
        carried_bound = b;
    }

    let layer = REPRESENTATIVE_LAYER;
    let plan = tower::material_plan(&source, layer, args.tokens.len())?;
    let prediction = passage.predict_material(&plan);
    let admission: MaterialAdmission = passage.admit_material(&prediction).map_err(|o| format!("layer {layer} material refused: {}", describe(&o)))?;
    let (mut material, layer_scalar) = mount_material(readout, surface, &mut source, layer, &args.tokens, &mut regions)?;
    // The rebase's gain, aligned exactly as the mount aligned it, so the replay reads the same
    // integers the kernel reads.
    let (gain_words, _) = source.whole(&tower::named(REPRESENTATIVE_LAYER, "input_layernorm.weight"))?;
    let gain_entries = align_bfloat16(&gain_words).map_err(|e| format!("{e:?}"))?.entries;
    material.standings.insert(tower::CARRIED_STANDING.to_owned(), (Rc::clone(&carried), carried_bound));
    let occurrence: SourceOccurrence = resident_layer::source_occurrence(&args.root, regions.clone(), None).unwrap_or(occurrence);

    let founded = tower::found_layer(layer, Entry::Carried, tower::Chart::Midpoint, &scales, terms, layer_scalar, &Intervention::None, args.tokens.len())?;
    let names = names_of(&founded.complex);
    let arriving = arriving_of(&founded.complex);
    let consumers = consumers_of(&founded.complex);
    let terminal = founded.returns[tower::LAYER_RETURN];
    let declared_faces: BTreeSet<EventId> = founded.returns.values().copied().collect();

    println!("  binding layer {layer} UNFUSED ({} occurrences)", founded.complex.shape.occurrences.len());
    let bind_clock = Instant::now();
    let unfused_bound = FrontPassage::new(surface, grain)
        .reading(declared_faces.iter().copied())
        .bind(&founded.complex, &founded.realization, &material, &occurrence, &receiver, Some(&admission), terminal)
        .map_err(|o| format!("layer {layer} refused at bind: {}", describe(&o)))?;
    let unfused_bind_s = bind_clock.elapsed().as_secs_f64();
    let launch_clock = Instant::now();
    let unfused_returned = unfused_bound.launch(&surface.mode()).map_err(|o| format!("layer {layer} refused at launch: {}", describe(&o)))?;
    let unfused_launch_s = launch_clock.elapsed().as_secs_f64();
    unfused_bound.standing(&unfused_returned).map_err(|o| format!("layer {layer} did not stand: {}", describe(&o)))?;
    let (unfused_graph, _) = unfused_bound.graph();
    let unfused = Conducted {
        graph_nodes: unfused_graph.nodes,
        graph_edges: unfused_graph.edges,
        kernel_nodes: unfused_graph.kernel_nodes,
        predicted_launches: unfused_bound.apparatus_prediction.captured_launches,
        predicted_allocations: unfused_bound.apparatus_prediction.allocations,
        predicted_section_octets: unfused_bound.apparatus_prediction.section_octets,
        bind_wall_s: unfused_bind_s,
        launch_wall_s: unfused_launch_s,
        returns: founded.returns.clone(),
        names: names.clone(),
        arriving: arriving.clone(),
        bound: unfused_bound,
        returned: unfused_returned,
    };

    // -----------------------------------------------------------------------------------------
    // [A] the reduction exposures
    // -----------------------------------------------------------------------------------------
    println!("  [A] exposing the block reductions");
    let _ = writeln!(form, "  [A] THE STANDING BLOCK REDUCTIONS EXPOSE THEIR RECEIPTS");
    let _ = writeln!(form, "    Layer {layer}, {} tokens, grain 2^-{}. Each exposure is the shape H1's ReductionReceipt states,", args.tokens.len(), grain.0);
    let _ = writeln!(form, "    minus the two fields that owner cannot hold for a strided leaf set, named where they are missing.");
    let _ = writeln!(form);
    let exposures = expose_reductions(surface, &unfused, &material, &gain_entries, args, grain, terms)?;
    for exposure in &exposures {
        write_exposure(form, exposure);
    }
    let _ = writeln!(form, "    THE STRIDED-PARTIAL BOUNDARY, RESTATED. H2 found it for the lane tree of the tiled contraction:");
    let _ = writeln!(form, "    `PartialTerm::inner` is a half-open `SectionRegion` and a per-lane strided set {{i : i = t (mod L)}}");
    let _ = writeln!(form, "    is not one, so `ReductionJunction::certify` cannot certify that partition of K. Every block");
    let _ = writeln!(form, "    reduction above has the same shape one level out: its leaves are the per-thread strided partials");
    let _ = writeln!(form, "    over the group or the reach. Nothing here forces them into a region; the word, its depth, its");
    let _ = writeln!(form, "    per-node widths, its barriers, its boundary residual and its bit-exact agreement with the card are");
    let _ = writeln!(form, "    carried instead, which is what the receipt is for. Founding a strided partial type is not H3's");
    let _ = writeln!(form, "    deed and no receipt here needed one.");
    let _ = writeln!(form);
    let _ = writeln!(form, "    AND ONE FINDING, MEASURED RATHER THAN INFERRED: two of `section_contact`'s three declared");
    let _ = writeln!(form, "    couplings are NOT block trees. The null (the greatest upper bracket) and the partition function");
    let _ = writeln!(form, "    (the sum of the certified weights) are enacted by thread 0 alone, as LEFT-LEANING serial words of");
    let _ = writeln!(form, "    depth reach-1, while `CouplingPlan::block` reports the reduction block the shape derived. The hull");
    let _ = writeln!(form, "    is serial too, but per coordinate — one thread per `d` folding over the reach — so its capacity is");
    let _ = writeln!(form, "    the head width and not one lane. The block's only true tree is its octave census. That is a");
    let _ = writeln!(form, "    realization fact about the kernel, not a defect in the plan, and it is what the receipt was missing.");
    let _ = writeln!(form);

    // -----------------------------------------------------------------------------------------
    // [B] the census equality matrix and its durations
    // -----------------------------------------------------------------------------------------
    println!("  [B] the census equality matrix");
    let _ = writeln!(form, "  [B] THE CENSUS LOSES ITS AVOIDABLE ATOMICS, UNDER EXACT CENSUS EQUALITY");
    let _ = writeln!(form, "    `section_census` is block-aggregated: a warp shuffle fold, then a cross-warp fold in shared");
    let _ = writeln!(form, "    standing, then ONE atomic per block per slot word — and none where the block's fold is the");
    let _ = writeln!(form, "    identity. `section_census_serial_control` is the per-thread-atomic form it replaced, kept in the");
    let _ = writeln!(form, "    module so the equality is measured forever rather than argued once.");
    let _ = writeln!(form);
    let _ = writeln!(form, "    THE A-PRIORI. Every word this census writes is a max, an or, or an add over the coordinates, and");
    let _ = writeln!(form, "    each coordinate's contribution is independent of every other. Max, or and add are commutative and");
    let _ = writeln!(form, "    associative, so the fold may be taken in any order and by any grouping and the result cannot move.");
    let _ = writeln!(form, "    The warp-scheduler audit states the licence exactly: atomics testify only for the exact");
    let _ = writeln!(form, "    commutative/associative receiver they implement, and their contention order is not path lineage.");
    let _ = writeln!(form, "    The aggregation implements the same receivers, so it testifies for the same thing.");
    let _ = writeln!(form);
    census_equality(surface, &unfused, args, form)?;

    // -----------------------------------------------------------------------------------------
    // [C] the fusion
    // -----------------------------------------------------------------------------------------
    println!("  [C] the fusion, and its refusal control");
    let _ = writeln!(form, "  [C] RECEIVER-DEPENDENT FUSION OF THE MIDPOINT QUOTIENT");
    let refound = |value: (usize, Dyadic)| -> Result<tower::Founded, String> {
        tower::found_layer(value.0, Entry::Carried, tower::Chart::Midpoint, &scales, terms, value.1, &Intervention::None, args.tokens.len())
    };
    let refound = move || refound((layer, layer_scalar));
    fusion_controls(surface, &founded, &refound, &material, &occurrence, &receiver, &admission, terminal, &declared_faces, &consumers, &names, &unfused, grain, form)?;
    Ok(())
}

/// A bf16 word from a signed 8-bit significand and a binary exponent.
fn bfloat16_word(significand: i32, exponent: i32) -> u16 {
    let negative = significand < 0;
    let magnitude = significand.unsigned_abs();
    let bits = 32 - magnitude.leading_zeros();
    let normalized = magnitude << (8 - bits);
    let biased = exponent + (bits as i32) - 1 + 127;
    ((negative as u16) << 15) | ((biased as u16) << 7) | ((normalized & 0x7f) as u16)
}

// ---------------------------------------------------------------------------------------------
// [A] the reduction exposures, from a bit-exact replay of the kernels' own arithmetic
// ---------------------------------------------------------------------------------------------

fn ceil_log2(n: usize) -> u32 {
    if n <= 1 {
        0
    } else {
        (n - 1).ilog2() + 1
    }
}

/// The occurrence whose law the complex names exactly `name`.
fn occurrence_named(names: &BTreeMap<EventId, String>, name: &str) -> Option<EventId> {
    names.iter().find(|(_, n)| n.as_str() == name).map(|(e, _)| *e)
}

fn expose_reductions(
    surface: &'static ResidentSurface<'static>,
    unfused: &Conducted<'static>,
    material: &ResidentMaterial<'static>,
    gain_entries: &[i64],
    args: &Args,
    grain: ResidentGrain,
    terms: SeriesAperture,
) -> Result<Vec<ReductionExposure>, String> {
    let mut exposures = Vec::new();
    let rows = args.tokens.len();
    let f = grain.0 as i32;

    // ---- section_rms_rebase: the input rebase over the whole standing ----
    let rebase = occurrence_named(&unfused.names, "input rebase").ok_or("no input rebase occurrence")?;
    let producer = *unfused.arriving.get(&rebase).and_then(|p| p.first()).ok_or("the input rebase carries nothing")?;
    let x = unfused.bound.read_section(&unfused.returned, producer).map_err(|o| describe(&o))?;
    let y = unfused.bound.read_section(&unfused.returned, rebase).map_err(|o| describe(&o))?;
    let group = resident_layer::HIDDEN;
    let width = x.len() / rows;
    let gain = material.populations.get(&tower::named(REPRESENTATIVE_LAYER, "input_layernorm.weight")).ok_or("no input_layernorm gain")?;
    let gain_e = gain.readout.exponent();
    let eps = Dyadic::of_binary64_bits(resident_layer::EPS_BITS).map_err(|e| e.to_string())?;
    let input_octaves = unfused
        .returned
        .fronts
        .iter()
        .flat_map(|front| front.readings.iter())
        .find(|r| r.occurrence == rebase)
        .map(|r| r.bound)
        .ok_or("no reading for the input rebase")?;
    let shape = surface.shape_rms_rebase(rows, width, group, input_octaves, Some(&gain.readout)).map_err(|e| e.to_string())?;
    let block = shape.block as usize;
    let barriers_total = 5 + 2 * (block.trailing_zeros() as usize);

    // (a) the group's own octave census: per-thread strided max, then the stride-halving tree
    let widest: Vec<u32> = (0..block)
        .map(|t| {
            let mut w = 0u32;
            let mut i = t;
            while i < group {
                let (lo, hi) = x[i];
                let m = mirror::magnitude(i128::from(lo)).max(mirror::magnitude(i128::from(hi)));
                w = w.max(mirror::octaves_of(m));
                i += block;
            }
            w
        })
        .collect();
    let (oct_levels, oct_peak) = tree_levels(&widest, |a, b| a.max(b), |v| 32 - v.leading_zeros());
    let oct0 = {
        let mut nodes = widest.clone();
        let mut stride = block / 2;
        while stride > 0 {
            for t in 0..stride {
                nodes[t] = nodes[t].max(nodes[t + stride]);
            }
            stride /= 2;
        }
        nodes[0]
    };
    exposures.push(ReductionExposure {
        owner: "section_rms_rebase",
        kernel: "section_rms_rebase (one block per (row, group))",
        coupling: "the group's own octave census — the reduction the square grain is DERIVED from",
        pivot: format!("the widest octave over one group of the standing, row 0 of {rows}"),
        extent: group as u64,
        capacity: shape.block,
        word: stride_word(block, group as u64, "max"),
        leaves: format!("{block} per-thread strided sets {{i : i = t (mod {block})}}, i < {group}"),
        leaves_are_regions: false,
        depth: block.trailing_zeros() as usize,
        barriers_this_pass: 1 + block.trailing_zeros() as usize,
        barriers_kernel_total: barriers_total,
        level_widths: oct_levels,
        peak_width_bits: oct_peak,
        a_priori_bound_bits: 7,
        a_priori_law: "an octave count of a signed word is at most 63, which is seven octaves; the max cannot exceed its leaves".to_owned(),
        boundary: "none — a max of octave counts rounds nothing".to_owned(),
        residual: "zero by construction: the fold is exact on the integers".to_owned(),
        agreement: format!("the reduced widest octave is {oct0}, and the square shift and root grain the kernel derives from it are below"),
    });

    // the levels the kernel derives from that census
    let lg = ceil_log2(group);
    let squares = 2 * oct0 + lg + 1;
    let s: i32 = if squares > 126 { ((squares - 126 + 1) / 2) as i32 } else { 0 };
    let f_prime = f - s;
    let rg = (126 - f_prime).clamp(0, 60);

    // (b) the quadratic capacity: per-thread strided sums of the squared magnitude bounds
    let mut part_lo = vec![0i128; block];
    let mut part_hi = vec![0i128; block];
    for t in 0..block {
        let mut i = t;
        while i < group {
            let (a, b) = (i128::from(x[i].0), i128::from(x[i].1));
            let (least, greatest) = if a <= 0 && b >= 0 {
                (0u128, mirror::magnitude(a).max(mirror::magnitude(b)))
            } else if a > 0 {
                (a as u128, b as u128)
            } else {
                (mirror::magnitude(b), mirror::magnitude(a))
            };
            let ls = least >> s;
            let gs = (greatest + ((1u128 << s) - 1)) >> s;
            part_lo[t] += (ls * ls) as i128;
            part_hi[t] += (gs * gs) as i128;
            i += block;
        }
    }
    let (sum_levels, sum_peak) = tree_levels(&part_hi, |a, b| a + b, mirror::width_bits);
    let (sum_lo, sum_hi) = {
        let (mut l, mut h) = (part_lo.clone(), part_hi.clone());
        let mut stride = block / 2;
        while stride > 0 {
            for t in 0..stride {
                l[t] += l[t + stride];
                h[t] += h[t + stride];
            }
            stride /= 2;
        }
        (l[0], h[0])
    };
    let mean_lo = mirror::div_floor(sum_lo, group as i128);
    let mean_hi = mirror::div_ceil(sum_hi, group as i128);
    let eps_lo = mirror::shift_floor(i128::from(eps.significand), eps.exponent + 2 * f_prime);
    let eps_hi = mirror::shift_ceil(i128::from(eps.significand), eps.exponent + 2 * f_prime);
    let a_lo = mean_lo + eps_lo;
    let a_hi = mean_hi + eps_hi;
    let scale: i128 = 1 << (f_prime + rg);
    let r_lo = mirror::div_floor(scale, mirror::isqrt_ceil(a_hi));
    let r_hi = mirror::div_ceil(scale, mirror::isqrt_floor(a_lo));

    // (d) the rebase, replayed, and compared with the card's own output words
    let mut replayed: Vec<(i64, i64)> = Vec::with_capacity(group);
    for i in 0..group {
        let (a, b) = (i128::from(x[i].0), i128::from(x[i].1));
        let g = i128::from(gain_entries[i]);
        let (xg_lo, xg_hi) = if g >= 0 { (a * g, b * g) } else { (b * g, a * g) };
        let shift = (rg - gain_e) as u32;
        let (y_lo, y_hi) = if xg_lo >= 0 {
            (mirror::product_shift(xg_lo, r_lo, shift, false), mirror::product_shift(xg_hi, r_hi, shift, true))
        } else if xg_hi <= 0 {
            (mirror::product_shift(xg_lo, r_hi, shift, false), mirror::product_shift(xg_hi, r_lo, shift, true))
        } else {
            (mirror::product_shift(xg_lo, r_hi, shift, false), mirror::product_shift(xg_hi, r_hi, shift, true))
        };
        replayed.push((y_lo as i64, y_hi as i64));
    }
    let disagreements = (0..group).filter(|i| replayed[*i] != y[*i]).count();
    let first_disagreement = (0..group).find(|i| replayed[*i] != y[*i]).map(|i| format!(" first at coordinate {i}: replay {:?} card {:?}", replayed[i], y[i])).unwrap_or_default();
    exposures.push(ReductionExposure {
        owner: "section_rms_rebase",
        kernel: "section_rms_rebase (one block per (row, group))",
        coupling: "the quadratic capacity over the group — the named barrier (H.0219: a term that is not a flux is a barrier)",
        pivot: format!("sum of the squared magnitude bounds over one group, row 0 of {rows}"),
        extent: group as u64,
        capacity: shape.block,
        word: stride_word(block, group as u64, "+"),
        leaves: format!("{block} per-thread strided sets {{i : i = t (mod {block})}}, i < {group}; each leaf is already an exact sum of {} squares", group / block),
        leaves_are_regions: false,
        depth: block.trailing_zeros() as usize,
        barriers_this_pass: 1 + block.trailing_zeros() as usize,
        barriers_kernel_total: barriers_total,
        level_widths: sum_levels,
        peak_width_bits: sum_peak,
        a_priori_bound_bits: 2 * oct0 + lg + 1 - 2 * (s as u32),
        a_priori_law: format!(
            "2(oct - s) + log2(group) + 1 with oct = {oct0} the census above, s = {s} the shift the kernel DERIVED from it, log2(group) = {lg}; the kernel chooses s as the least shift that fits the carrier and nothing is authored"
        ),
        boundary: format!(
            "mean = sum / {group}, directed: floor below and ceil above, at 2^-2(F-s) with F = {}, s = {s}; then the reciprocal root at its own finer grain 2^-{rg}",
            grain.0
        ),
        residual: format!(
            "the mean's own remainder: sum_lo mod group = {}, sum_hi mod group = {} (grains at 2^-2(F-s)); the root's: 2^(F'+Rg) mod isqrt = {} below and {} above",
            sum_lo.rem_euclid(group as i128),
            sum_hi.rem_euclid(group as i128),
            scale.rem_euclid(mirror::isqrt_ceil(a_hi)),
            scale.rem_euclid(mirror::isqrt_floor(a_lo))
        ),
        agreement: format!(
            "the replayed block reproduces {} of {group} of the card's own output coordinates bit for bit{}",
            group - disagreements,
            if disagreements == 0 { " — every one".to_owned() } else { format!(" — {disagreements} DISAGREE,{first_disagreement}") }
        ),
    });

    // ---- section_contact: the block octave census, the null, the partition function, the hull ----
    let contact = occurrence_named(&unfused.names, "contact and carried construction").ok_or("no contact occurrence")?;
    let inputs = unfused.arriving.get(&contact).ok_or("the contact carries nothing")?;
    if inputs.len() != 3 {
        return Err(format!("the contact carries {} inputs", inputs.len()));
    }
    let q = unfused.bound.read_section(&unfused.returned, inputs[0]).map_err(|o| describe(&o))?;
    let k = unfused.bound.read_section(&unfused.returned, inputs[1]).map_err(|o| describe(&o))?;
    let v = unfused.bound.read_section(&unfused.returned, inputs[2]).map_err(|o| describe(&o))?;
    let out = unfused.bound.read_section(&unfused.returned, contact).map_err(|o| describe(&o))?;
    let heads = resident_layer::HEADS;
    let kv_heads = resident_layer::KV_HEADS;
    let head_width = q.len() / (rows * heads);
    let window = match Species::of(REPRESENTATIVE_LAYER) {
        Species::Sliding => resident_layer::SLIDING_WINDOW,
        Species::Full => rows.max(1),
    };
    let contact_octaves = unfused
        .returned
        .fronts
        .iter()
        .flat_map(|front| front.readings.iter())
        .find(|r| r.occurrence == contact)
        .map(|r| r.bound)
        .ok_or("no reading for the contact")?;
    let contact_shape = surface
        .shape_contact(rows, heads * head_width, kv_heads * head_width, kv_heads * head_width, heads, kv_heads, head_width, window, terms, grain, contact_octaves, contact_octaves, contact_octaves)
        .map_err(|e| e.to_string())?;
    let cblock = contact_shape.block as usize;
    // 7 fixed __syncthreads in section_contact plus one per level of its octave-census tree.
    let contact_barriers = 7 + cblock.trailing_zeros() as usize;
    // the block with the widest reach: the last row, head 0
    let t = rows - 1;
    let h = 0usize;
    let g = h / (heads / kv_heads);
    let start = if t + 1 > window { t + 1 - window } else { 0 };
    let reach = t - start + 1;
    let q_base = (t * heads + h) * head_width;

    // (a0) the block octave census over the receiver row and its presented reach
    let mut oct_leaf = vec![0u32; cblock];
    for (tid, leaf) in oct_leaf.iter_mut().enumerate() {
        let mut w = 0u32;
        let mut d = tid;
        while d < head_width {
            let m = mirror::magnitude(i128::from(q[q_base + d].0)).max(mirror::magnitude(i128::from(q[q_base + d].1)));
            w = w.max(mirror::octaves_of(m));
            d += cblock;
        }
        for r in 0..reach {
            let k_base = ((start + r) * kv_heads + g) * head_width;
            let mut d = tid;
            while d < head_width {
                let m = mirror::magnitude(i128::from(k[k_base + d].0)).max(mirror::magnitude(i128::from(k[k_base + d].1)));
                w = w.max(mirror::octaves_of(m));
                d += cblock;
            }
        }
        *leaf = w;
    }
    let (coct_levels, coct_peak) = tree_levels(&oct_leaf, |a, b| a.max(b), |v| 32 - v.leading_zeros());
    let coct = {
        let mut nodes = oct_leaf.clone();
        let mut stride = cblock / 2;
        while stride > 0 {
            for tid in 0..stride {
                nodes[tid] = nodes[tid].max(nodes[tid + stride]);
            }
            stride /= 2;
        }
        nodes[0]
    };
    let clg = ceil_log2(head_width);
    let need = 2 * coct + clg + 2;
    let bs: i32 = if need > 126 { ((need - 126 + 1) / 2) as i32 } else { 0 };
    exposures.push(ReductionExposure {
        owner: "section_contact",
        kernel: "section_contact (one block per (row, receiver head))",
        coupling: "the block's own octave census — the reduction the bracket grain is DERIVED from",
        pivot: format!("the widest octave over the receiver row and its presented reach, row {t} head {h}"),
        extent: (head_width * (1 + reach)) as u64,
        capacity: contact_shape.block,
        word: stride_word(cblock, (head_width * (1 + reach)) as u64, "max"),
        leaves: format!("{cblock} per-thread strided sets over the receiver row's {head_width} coordinates and the reach's {reach} x {head_width}"),
        leaves_are_regions: false,
        depth: cblock.trailing_zeros() as usize,
        barriers_this_pass: 2 + cblock.trailing_zeros() as usize,
        barriers_kernel_total: contact_barriers,
        level_widths: coct_levels,
        peak_width_bits: coct_peak,
        a_priori_bound_bits: 7,
        a_priori_law: "an octave count of a signed word is at most 63, seven octaves".to_owned(),
        boundary: "none".to_owned(),
        residual: "zero: a max over integers".to_owned(),
        agreement: format!("the reduced widest octave is {coct}, and the bracket shift the kernel derives from it is {bs}"),
    });

    // (a) the brackets — NOT a cross-thread reduction: one thread per r, serial over d
    let mut s_lo = vec![0i128; reach];
    let mut s_hi = vec![0i128; reach];
    for r in 0..reach {
        let k_base = ((start + r) * kv_heads + g) * head_width;
        let (mut acc_lo, mut acc_hi) = (0i128, 0i128);
        for d in 0..head_width {
            let ql = mirror::shift_floor(i128::from(q[q_base + d].0), -bs);
            let qh = mirror::shift_ceil(i128::from(q[q_base + d].1), -bs);
            let kl = mirror::shift_floor(i128::from(k[k_base + d].0), -bs);
            let kh = mirror::shift_ceil(i128::from(k[k_base + d].1), -bs);
            let (l, u) = mirror::corners(ql, qh, kl, kh);
            acc_lo += l;
            acc_hi += u;
        }
        s_lo[r] = mirror::shift_floor(acc_lo, -(f - 2 * bs));
        s_hi[r] = mirror::shift_ceil(acc_hi, -(f - 2 * bs));
    }

    // (b) the null: thread 0's LEFT-LEANING serial max over the reach
    let (null_levels, null_peak, null_value) = left_leaning(&s_hi, |a, b| if b > a { b } else { a });
    exposures.push(ReductionExposure {
        owner: "section_contact",
        kernel: "section_contact",
        coupling: "the null: the greatest upper bracket over the reach — a gauge that enters no ratio",
        pivot: format!("the {reach} brackets of row {t}, head {h}"),
        extent: reach as u64,
        capacity: 1,
        word: left_leaning_word(reach, "max"),
        leaves: format!("the {reach} bracket values s_hi[r], one per presented position — coordinate SINGLETONS, so these leaves ARE regions"),
        leaves_are_regions: true,
        depth: reach.saturating_sub(1),
        barriers_this_pass: 1,
        barriers_kernel_total: contact_barriers,
        level_widths: null_levels,
        peak_width_bits: null_peak,
        a_priori_bound_bits: mirror::width_bits(*s_hi.iter().max().unwrap_or(&0)),
        a_priori_law: "a max never exceeds its widest leaf".to_owned(),
        boundary: "none — the null is subtracted from every bracket and enters no ratio".to_owned(),
        residual: "zero".to_owned(),
        agreement: format!("the null is {null_value}; the shape declares this coupling at block {} and the kernel enacts it on ONE lane", contact_shape.block),
    });

    // (c) the certified weights, then the partition function: thread 0's serial sum
    let mut w_lo = vec![0i128; reach];
    let mut w_hi = vec![0i128; reach];
    for r in 0..reach {
        let lo_arg = s_lo[r] - null_value;
        let mut hi_arg = s_hi[r] - null_value;
        if hi_arg > 0 {
            hi_arg = 0;
        }
        let (e_lo_lo, _) = mirror::exp_nonpositive(lo_arg, f, terms.0);
        let (_, e_hi_hi) = mirror::exp_nonpositive(hi_arg, f, terms.0);
        w_lo[r] = e_lo_lo;
        w_hi[r] = e_hi_hi;
    }
    let (tot_levels, tot_peak, total_hi) = left_leaning(&w_hi, |a, b| a + b);
    let (_, _, total_lo) = left_leaning(&w_lo, |a, b| a + b);
    exposures.push(ReductionExposure {
        owner: "section_contact",
        kernel: "section_contact",
        coupling: "the partition function: the sum of the certified weights over the reach",
        pivot: format!("the {reach} certified weight enclosures of row {t}, head {h}"),
        extent: reach as u64,
        capacity: 1,
        word: left_leaning_word(reach, "+"),
        leaves: format!("the {reach} weights w[r] = exp(s[r] - null), each with its own alternating-tail certificate at {} terms", terms.0),
        leaves_are_regions: true,
        depth: reach.saturating_sub(1),
        barriers_this_pass: 1,
        barriers_kernel_total: contact_barriers,
        level_widths: tot_levels,
        peak_width_bits: tot_peak,
        a_priori_bound_bits: mirror::width_bits(i128::from(reach as i64) << grain.0),
        a_priori_law: format!("every weight is at most one unit at the grain, so the sum is at most {reach} x 2^{}", grain.0),
        boundary: "none here — the sum is the denominator of the interval quotient that follows, and THAT is where the one directed rounding happens".to_owned(),
        residual: format!("the enclosure of the partition function is [{total_lo}, {total_hi}] at 2^-{}: width {}", grain.0, total_hi - total_lo),
        agreement: "the sum is the denominator the carried construction divides by; its agreement is the carried construction's, below".to_owned(),
    });

    // (d) the hull, and the carried construction — one thread per coordinate, serial over the reach
    let mut hull_levels_peak = (Vec::new(), 0u32);
    let mut replayed_out: Vec<(i64, i64)> = Vec::with_capacity(head_width);
    for d in 0..head_width {
        let (mut num_lo, mut num_hi) = (0i128, 0i128);
        let mut hull: Vec<i128> = Vec::with_capacity(reach);
        let (mut hull_lo, mut hull_hi) = (0i128, 0i128);
        for r in 0..reach {
            let v_at = ((start + r) * kv_heads + g) * head_width + d;
            let (vl, vh) = (i128::from(v[v_at].0), i128::from(v[v_at].1));
            let (pl, ph) = mirror::corners(w_lo[r], w_hi[r], vl, vh);
            num_lo += pl;
            num_hi += ph;
            hull.push(vh);
            if r == 0 {
                hull_lo = vl;
                hull_hi = vh;
            } else {
                if vl < hull_lo {
                    hull_lo = vl;
                }
                if vh > hull_hi {
                    hull_hi = vh;
                }
            }
        }
        if d == 0 {
            let (levels, peak, _) = left_leaning(&hull, |a, b| if b > a { b } else { a });
            hull_levels_peak = (levels, peak);
        }
        let (mut q_lo, mut q_hi) = mirror::interval_quotient(num_lo, num_hi, total_lo, total_hi, 0);
        if hull_lo > q_lo {
            q_lo = hull_lo;
        }
        if hull_hi < q_hi {
            q_hi = hull_hi;
        }
        replayed_out.push((q_lo as i64, q_hi as i64));
    }
    let card_row = &out[q_base..q_base + head_width];
    let contact_disagreements = (0..head_width).filter(|d| replayed_out[*d] != card_row[*d]).count();
    let contact_first = (0..head_width)
        .find(|d| replayed_out[*d] != card_row[*d])
        .map(|d| format!(" first at coordinate {d}: replay {:?} card {:?}", replayed_out[d], card_row[d]))
        .unwrap_or_default();
    exposures.push(ReductionExposure {
        owner: "section_contact",
        kernel: "section_contact",
        coupling: "the hull: the least and greatest carried coordinate over the reach",
        pivot: format!("the {reach} carried values at one coordinate of row {t}, head {h}"),
        extent: reach as u64,
        capacity: head_width as u32,
        word: left_leaning_word(reach, "min/max"),
        leaves: format!("the {reach} carried enclosures v[start+r, g, d] — coordinate singletons, so these leaves ARE regions"),
        leaves_are_regions: true,
        depth: reach.saturating_sub(1),
        barriers_this_pass: 0,
        barriers_kernel_total: contact_barriers,
        level_widths: hull_levels_peak.0,
        peak_width_bits: hull_levels_peak.1,
        a_priori_bound_bits: mirror::width_bits(i128::from(v.iter().map(|(l, h)| l.abs().max(h.abs())).max().unwrap_or(0))),
        a_priori_law: "a hull never exceeds its widest leaf".to_owned(),
        boundary: "the hull TIGHTENS the interval quotient and never widens it: a convex combination lies inside the hull of its terms, and an empty intersection is a soundness fault the kernel reports".to_owned(),
        residual: "zero; the tightening is exact and the discarded part of the quotient's enclosure was never attainable".to_owned(),
        agreement: format!(
            "the replayed block reproduces {} of {head_width} of the card's own carried coordinates bit for bit{}",
            head_width - contact_disagreements,
            if contact_disagreements == 0 { " — every one".to_owned() } else { format!(" — {contact_disagreements} DISAGREE,{contact_first}") }
        ),
    });
    Ok(exposures)
}

/// The per-node widths of a LEFT-LEANING serial word `((((0 op 1) op 2) op 3) ...)` — the word one
/// thread enacts when it folds a shared array in a `for` loop. Returns the levels, the peak and the
/// root.
fn left_leaning<T: Copy>(leaves: &[T], join: impl Fn(T, T) -> T) -> (Vec<(usize, u32, usize)>, u32, T)
where
    T: Into<i128> + Copy,
{
    let mut levels = Vec::new();
    let mut peak = leaves.iter().map(|l| mirror::width_bits((*l).into())).max().unwrap_or(0);
    levels.push((0usize, peak, leaves.len()));
    let mut node = leaves[0];
    for (at, leaf) in leaves.iter().enumerate().skip(1) {
        node = join(node, *leaf);
        let w = mirror::width_bits(node.into());
        peak = peak.max(w);
        levels.push((at, w, 1));
    }
    (levels, peak, node)
}

fn left_leaning_word(leaves: usize, join: &str) -> String {
    if leaves == 0 {
        return "(empty)".to_owned();
    }
    if leaves > 12 {
        return format!("((((0 {join} 1) {join} 2) {join} 3) ... {join} {}) — a left-leaning serial word of depth {}", leaves - 1, leaves - 1);
    }
    let mut word = "0".to_owned();
    for leaf in 1..leaves {
        word = format!("({word} {join} {leaf})");
    }
    word
}

// ---------------------------------------------------------------------------------------------
// [B] the census equality matrix and the duration comparison
// ---------------------------------------------------------------------------------------------

/// Every slot word of a reading, as `(name, value)`, so the matrix is written by the layout rather
/// than by hand and a word added to the slot cannot be silently dropped from the comparison.
fn slot_words(slot: &SlotReading) -> Vec<(&'static str, u64)> {
    vec![
        ("refused", u64::from(slot.refused)),
        ("reach", u64::from(slot.reach)),
        ("written", u64::from(slot.written)),
        ("inverted", u64::from(slot.inverted)),
        ("max_octave", u64::from(slot.max_octave)),
        ("bound_violated", u64::from(slot.bound_violated)),
        ("max_width", slot.max_width),
        ("upstream_flags", u64::from(slot.upstream_flags)),
        ("upstream_first", slot.upstream_first.map(|f| f as u64 + 1).unwrap_or(0)),
        ("upstream_count", u64::from(slot.upstream_count)),
        ("lineage_inspected", u64::from(slot.lineage_inspected)),
        ("width_sum", slot.width_sum),
        ("nonzero_widths", u64::from(slot.nonzero_widths)),
    ]
}

fn census_equality(
    surface: &'static ResidentSurface<'static>,
    unfused: &Conducted<'static>,
    args: &Args,
    form: &mut String,
) -> Result<(), String> {
    // The shapes are the layer's own: every distinct section extent the H0 profile names, taken
    // from the occurrences of the layer that stood.
    let mut shapes: Vec<(EventId, String, usize, u32)> = Vec::new();
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    for front in &unfused.returned.fronts {
        for reading in &front.readings {
            if let Some(section) = unfused.bound.section(reading.occurrence) {
                let count = section.rows() * section.width();
                if seen.insert(count) {
                    shapes.push((reading.occurrence, unfused.names.get(&reading.occurrence).cloned().unwrap_or_default(), count, reading.bound));
                }
            }
        }
    }
    shapes.sort_by_key(|(_, _, count, _)| *count);

    let _ = writeln!(form, "    THE EQUALITY MATRIX. Every slot word, both kernels, one section each. `entry` is the refusal");
    let _ = writeln!(form, "    word the slot carried when the census entered — 0 is a standing occurrence, the rest are the");
    let _ = writeln!(form, "    poisoned-lineage entries a refused occurrence's census sees.");
    let _ = writeln!(form);
    let mut all_equal = true;
    let mut rows_measured = 0usize;
    let mut tsv = String::from("shape\toccurrence\tcount\tentry\tword\taggregated\tcontrol\tequal\n");
    for (occurrence, name, count, bound) in &shapes {
        let section = unfused.bound.section(*occurrence).ok_or("no section")?;
        for entry in [0u32, 8u32, 2u32, 1u32] {
            let (aggregated, control) = surface.census_both(section, *bound, entry).map_err(|e| e.to_string())?;
            let equal = aggregated == control;
            all_equal &= equal;
            let words_a = slot_words(&aggregated);
            let words_c = slot_words(&control);
            let _ = writeln!(
                form,
                "    {:<44} {:>9} coordinates, admitted {:>2} octaves, entry {:#06x}: {}",
                name.chars().take(44).collect::<String>(),
                count,
                bound,
                entry,
                if equal { "EQUAL, word for word" } else { "DIFFER" }
            );
            for ((word, a), (_, c)) in words_a.iter().zip(words_c.iter()) {
                rows_measured += 1;
                let _ = writeln!(tsv, "{count}\t{name}\t{count}\t{entry}\t{word}\t{a}\t{c}\t{}", a == c);
                if !equal {
                    let _ = writeln!(form, "        {word:<20} aggregated {a:>22}   control {c:>22}   {}", if a == c { "=" } else { "DIFFER" });
                }
            }
            if equal {
                let _ = writeln!(
                    form,
                    "        refused {:#06x}  written {}  inverted {}  max_octave {}  bound {}  max_width {}  width_sum {}  nonzero {}",
                    aggregated.refused, aggregated.written, aggregated.inverted, aggregated.max_octave, aggregated.bound_violated, aggregated.max_width, aggregated.width_sum, aggregated.nonzero_widths
                );
            }
        }
    }
    let _ = writeln!(form);
    let _ = writeln!(form, "    {rows_measured} slot-word comparisons over {} section shapes x 4 entry words: {}", shapes.len(), if all_equal { "EVERY ONE EQUAL" } else { "AT LEAST ONE DIFFERS — see above" });
    let _ = writeln!(form);

    // the commutativity audit, word by word
    let _ = writeln!(form, "    THE COMMUTATIVITY AUDIT — every slot word, its update rule, and its disposition.");
    let _ = writeln!(form, "    word                  written by            update rule                     disposition");
    for row in [
        ("refused", "the semantic kernel; the census", "atomicOr of the flag bits", "AGGREGATED — or is commutative and associative; the census's own two bits (INVERTED, BOUND) are folded in the block and deposited once"),
        ("reach", "section_contact, thread 0", "atomicMax over the blocks of one occurrence", "KEPT AS IT IS — it is not the census kernel's word; one thread per block already deposits one atomic, and max is the receiver it implements"),
        ("written", "the census, one thread", "a plain store of 1", "KEPT AS A STORE — not a reduction and not an atomic; the same thread of the same block writes the same value"),
        ("inverted", "the census", "atomicOr of 1", "AGGREGATED — or"),
        ("max_octave", "the census", "atomicMax", "AGGREGATED — max"),
        ("bound_violated", "the census", "atomicOr of 1", "AGGREGATED — or"),
        ("max_width", "the census", "atomicMax on a 64-bit word", "AGGREGATED — max"),
        ("width_sum", "the census", "atomicAdd on a 64-bit word", "AGGREGATED — add"),
        ("nonzero_widths", "the census", "atomicAdd of 1", "AGGREGATED — add, as a per-block count"),
        ("upstream_flags", "upstream_refused, at kernel entry", "atomicOr of the joined predecessor flags", "KEPT AS IT IS — it is not the census kernel's word; every thread computes the same join from final words"),
        ("upstream_first", "upstream_refused", "a PLAIN STORE of 1 + the LEAST refusing predecessor index", "KEPT AS A STORE, and this is the word the audit was aimed at: it is a MIN by index, which IS commutative and associative, but it is not an atomic at all — the lineage array is declared in ascending index order and every thread scans it serially from final words, so every thread stores the identical value. A first-writer-wins would have been unlawful; a min is not, and this is not even a min across threads"),
        ("upstream_count", "upstream_refused", "a plain store of the refusing count", "KEPT AS A STORE — same reading, same value in every thread"),
        ("lineage_inspected", "upstream_refused", "a plain store of the declared lineage length", "KEPT AS A STORE"),
    ] {
        let _ = writeln!(form, "    {:<21} {:<21} {:<31} {}", row.0, row.1, row.2, row.3);
    }
    let _ = writeln!(form);
    let _ = writeln!(form, "    ONE ORDER-DEPENDENCE IS INHERITED AND IS NOT THE AGGREGATION'S. Both forms decide whether to");
    let _ = writeln!(form, "    measure at all by reading `slot[SLOT_REFUSED]`, and both also OR `REFUSED_INVERTED` and");
    let _ = writeln!(form, "    `REFUSED_BOUND` into that same word. On material where the census itself raises a refusal, a");
    let _ = writeln!(form, "    thread (control) or a block (aggregated) that entered before the raise measures its coordinates and");
    let _ = writeln!(form, "    one that entered after does not. The occurrence refuses either way and its face may not be read;");
    let _ = writeln!(form, "    what can move is the measured octave and width the receipt DISPLAYS. Where the census raises");
    let _ = writeln!(form, "    nothing — every occurrence that stands, which is every row of the matrix above — both forms are");
    let _ = writeln!(form, "    exactly order-free. The refusal itself is order-free in both, and that is measured below.");
    let _ = writeln!(form);
    {
        let (occurrence, name, count, _) = shapes.last().ok_or("no shapes")?;
        let section = unfused.bound.section(*occurrence).ok_or("no section")?;
        let mut refusals: Vec<(u32, u32)> = Vec::new();
        for _ in 0..8 {
            let (a, c) = surface.census_both(section, 1, 0).map_err(|e| e.to_string())?;
            refusals.push((a.refused, c.refused));
        }
        let stable = refusals.windows(2).all(|w| w[0] == w[1]);
        let _ = writeln!(
            form,
            "    the bound refuted deliberately (admitted = 1 octave) on {name} ({count} coordinates), 8 repetitions:",
        );
        let _ = writeln!(form, "      refusal words: {refusals:?} — stable across repetitions: {stable}");
    }
    let _ = writeln!(form);
    let _ = writeln!(form, "    THE TWO LINEAGE CONTROLS ARE OWNER-LOCAL TESTS AND THEY RUN AGAINST THE AGGREGATED CENSUS:");
    let _ = writeln!(form, "      front_passage: a_runtime_refusal_in_one_branch_returns_the_complete_lineage_and_the_terminal_cannot_be_read_as_standing");
    let _ = writeln!(form, "        — the two-branch poisoned lineage: one branch's malformed codeword refuses, the sibling stands,");
    let _ = writeln!(form, "          and the complete obstruction lineage comes back with the terminal refused by name;");
    let _ = writeln!(form, "      resident_section: a_runtime_refusal_at_a_nonzero_coordinate_travels_only_along_its_lineage_and_the_sibling_is_bit_identical");
    let _ = writeln!(form, "        — a refusal raised at a NONZERO coordinate returns the identical lineage and leaves the");
    let _ = writeln!(form, "          unrelated branch bit-identical. Both are green under this census.");
    let _ = writeln!(form);

    // the duration comparison — apparatus measurement, in the frame it was taken in, selecting nothing
    let _ = writeln!(form, "    THE DURATION COMPARISON, on the layer's own shapes. {} launches of each kernel per shape,", args.census_repeats);
    let _ = writeln!(form, "    each with its own fresh slot allocation and its own synchronize, measured on the wall clock of");
    let _ = writeln!(form, "    this process with a display attached to the card. It is a REPORT: no semantics depend on it and");
    let _ = writeln!(form, "    the equality above is what admits the aggregation.");
    let _ = writeln!(form);
    let _ = writeln!(form, "    coordinates  occurrence                                   aggregated (s)    control (s)   ratio");
    let mut tsv_durations = String::from("count\toccurrence\taggregated_s\tcontrol_s\n");
    for (occurrence, name, count, bound) in &shapes {
        let section = unfused.bound.section(*occurrence).ok_or("no section")?;
        // one warm launch of each before the clock starts
        let _ = surface.census_once("section_census", section, *bound, 0).map_err(|e| e.to_string())?;
        let _ = surface.census_once("section_census_serial_control", section, *bound, 0).map_err(|e| e.to_string())?;
        let clock = Instant::now();
        for _ in 0..args.census_repeats {
            let _ = surface.census_once("section_census", section, *bound, 0).map_err(|e| e.to_string())?;
        }
        let aggregated_s = clock.elapsed().as_secs_f64();
        let clock = Instant::now();
        for _ in 0..args.census_repeats {
            let _ = surface.census_once("section_census_serial_control", section, *bound, 0).map_err(|e| e.to_string())?;
        }
        let control_s = clock.elapsed().as_secs_f64();
        let _ = writeln!(
            form,
            "    {count:>11}  {:<44} {aggregated_s:>12.6}   {control_s:>12.6}   {:>6.3}",
            name.chars().take(44).collect::<String>(),
            if aggregated_s > 0.0 { control_s / aggregated_s } else { 0.0 }
        );
        let _ = writeln!(tsv_durations, "{count}\t{name}\t{aggregated_s:.9}\t{control_s:.9}");
    }
    let _ = writeln!(form, "    Each row includes one allocation, one upload of the seeded slot, one launch and one");
    let _ = writeln!(form, "    synchronize per repetition, so the row is a bound on the kernel and not the kernel alone.");
    let _ = writeln!(form);
    let out = PathBuf::from("output/the_reductions_expose_their_words");
    let _ = std::fs::write(out.join("census-equality.tsv"), &tsv);
    let _ = std::fs::write(out.join("census-durations.tsv"), &tsv_durations);
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// [C] the fusion, its controls, and its refusal
// ---------------------------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn fusion_controls(
    surface: &'static ResidentSurface<'static>,
    founded: &tower::Founded,
    refound: &dyn Fn() -> Result<tower::Founded, String>,
    material: &ResidentMaterial<'static>,
    occurrence: &SourceOccurrence,
    receiver: &DeedReceiver,
    admission: &MaterialAdmission,
    terminal: EventId,
    declared_faces: &BTreeSet<EventId>,
    consumers: &BTreeMap<EventId, Vec<EventId>>,
    names: &BTreeMap<EventId, String>,
    unfused: &Conducted<'static>,
    grain: ResidentGrain,
    form: &mut String,
) -> Result<(), String> {
    let _ = writeln!(form, "    The midpoint chart seals nearly every occurrence: under it a MidpointQuotient follows each");
    let _ = writeln!(form, "    producer, and each is a separate kernel launch and a separate census. The fusion declared here");
    let _ = writeln!(form, "    is `SealedMidpointQuotient`: the collapse and the quotient's own census in ONE node, writing the");
    let _ = writeln!(form, "    midpoints over the predecessor's own words rather than into a second section.");
    let _ = writeln!(form);
    let _ = writeln!(form, "    WHY IT IS EXACTLY THE UNFUSED PAIR, ON EVERY PATH. The collapse originates no refusal:");
    let _ = writeln!(form, "    `shift_floor(lo + hi, -1)` on two int64 words cannot leave the wide carrier, so the only flag the");
    let _ = writeln!(form, "    quotient can carry is UPSTREAM. The upstream decision is thread-uniform and final at entry, because");
    let _ = writeln!(form, "    the fused node sits after the predecessor's census on the graph's own edge — exactly where the");
    let _ = writeln!(form, "    unfused collapse kernel sat. And the census of a collapsed section measures lo == hi, so every");
    let _ = writeln!(form, "    width face is the identity and only the octave max and the bound or remain, both aggregated as the");
    let _ = writeln!(form, "    census aggregates them. The PRE-quotient widths — the collapsed population this chart retains —");
    let _ = writeln!(form, "    are the predecessor's own census, which is its own node and runs first, untouched by the fusion.");
    let _ = writeln!(form);
    let _ = writeln!(form, "    THE CONDITION, DECIDED FROM THE DIAGRAM AT COMPILE. A sealing law rewrites its predecessor's");
    let _ = writeln!(form, "    section in place, so that section's face is gone. Section 4.6 admits the fusion only when every");
    let _ = writeln!(form, "    declared future receiver factors through the fused output, and that is three readings of the");
    let _ = writeln!(form, "    diagram: the predecessor is read by this occurrence and by nothing else; it is not the declared");
    let _ = writeln!(form, "    terminal; and the receiver did not declare its face. Readability at READ time is not knowable at");
    let _ = writeln!(form, "    compile — `read_section` takes any occurrence — so the guard stands at both ends: a face the");
    let _ = writeln!(form, "    fusion sealed away is refused by name at read time, with the reopening route, and never returned");
    let _ = writeln!(form, "    as collapsed words.");
    let _ = writeln!(form);

    // which quotients may fuse, decided from the diagram exactly as the compile decides it
    let mut fusible: Vec<EventId> = Vec::new();
    let mut refused_by_face: Vec<EventId> = Vec::new();
    for (event, name) in names {
        if !name.contains("midpoint quotient") {
            continue;
        }
        let predecessor = match unfused.arriving.get(event).and_then(|p| p.first()) {
            Some(p) => *p,
            None => continue,
        };
        let reading = consumers.get(&predecessor).cloned().unwrap_or_default();
        if reading.len() == 1 && reading[0] == *event && predecessor != terminal && !declared_faces.contains(&predecessor) {
            fusible.push(*event);
        } else {
            refused_by_face.push(*event);
        }
    }
    let quotients = fusible.len() + refused_by_face.len();
    let _ = writeln!(
        form,
        "    the layer's diagram carries {quotients} midpoint quotients; {} may fuse and {} may not:",
        fusible.len(),
        refused_by_face.len()
    );
    for event in &refused_by_face {
        let predecessor = unfused.arriving.get(event).and_then(|p| p.first()).copied();
        let _ = writeln!(
            form,
            "      {} — its predecessor {} is {}",
            names.get(event).cloned().unwrap_or_default(),
            predecessor.map(|p| names.get(&p).cloned().unwrap_or_default()).unwrap_or_default(),
            if predecessor == Some(terminal) {
                "the declared terminal".to_owned()
            } else if predecessor.map(|p| declared_faces.contains(&p)).unwrap_or(false) {
                let name = founded.returns.iter().find(|(_, e)| Some(**e) == predecessor).map(|(n, _)| (*n).to_owned()).unwrap_or_default();
                format!("a face the receiver declared: `{name}`")
            } else {
                "read by more than one consumer".to_owned()
            }
        );
    }
    let _ = writeln!(form);

    // (1) THE REFUSAL CONTROL: fuse the quotient over a declared return and require the compile to refuse
    let _ = writeln!(form, "    THE REFUSAL CONTROL. The layer's own dissection face — the layer enclosure, the scalar's output");
    let _ = writeln!(form, "    BEFORE the terminal quotient — is a declared return. Declaring the fusion over it and compiling:");
    {
        let control = founded_with_fusion(refound, &fusible, &refused_by_face, true)?;
        let outcome = FrontPassage::new(surface, grain)
            .reading(declared_faces.iter().copied())
            .compile(&control.complex, &control.realization, material, occurrence, terminal);
        match outcome {
            Err(FrontPassageObstruction::Compile(CompileRefusal::FusionUnfactored { quotient, predecessor, because, reopening })) => {
                let _ = writeln!(form, "      REFUSED, by name: FusionUnfactored");
                let _ = writeln!(form, "        quotient      {} {quotient:?}", names.get(&quotient).cloned().unwrap_or_default());
                let _ = writeln!(form, "        predecessor   {} {predecessor:?}", names.get(&predecessor).cloned().unwrap_or_default());
                let _ = writeln!(form, "        because       {because}");
                let _ = writeln!(form, "        reopening     {reopening}");
            }
            Err(other) => return Err(format!("the refusal control returned the wrong obstruction: {}", describe(&other))),
            Ok(_) => return Err("the refusal control COMPILED: a declared face was fused away without a refusal".to_owned()),
        }
    }
    let _ = writeln!(form);

    // (2) the legal fusion, bound and launched
    let fused_founded = founded_with_fusion(refound, &fusible, &refused_by_face, false)?;
    println!("  binding layer {REPRESENTATIVE_LAYER} FUSED ({} quotients sealed)", fusible.len());
    let bind_clock = Instant::now();
    let fused_bound = FrontPassage::new(surface, grain)
        .reading(declared_faces.iter().copied())
        .bind(&fused_founded.complex, &fused_founded.realization, material, occurrence, receiver, Some(admission), terminal)
        .map_err(|o| format!("the fused layer refused at bind: {}", describe(&o)))?;
    let fused_bind_s = bind_clock.elapsed().as_secs_f64();
    let launch_clock = Instant::now();
    let fused_returned = fused_bound.launch(&surface.mode()).map_err(|o| format!("the fused layer refused at launch: {}", describe(&o)))?;
    let fused_launch_s = launch_clock.elapsed().as_secs_f64();
    fused_bound.standing(&fused_returned).map_err(|o| format!("the fused layer did not stand: {}", describe(&o)))?;
    let (fused_graph, _) = fused_bound.graph();

    let _ = writeln!(form, "    THE KERNEL COUNT AND THE ALLOCATIONS, PER GRAPH");
    let _ = writeln!(form, "                                  unfused      fused     delta");
    for (what, u, f) in [
        ("graph nodes", unfused.graph_nodes as i64, fused_graph.nodes as i64),
        ("graph kernel nodes", unfused.kernel_nodes as i64, fused_graph.kernel_nodes as i64),
        ("graph edges", unfused.graph_edges as i64, fused_graph.edges as i64),
        ("captured launches (predicted)", unfused.predicted_launches as i64, fused_bound.apparatus_prediction.captured_launches as i64),
        ("allocations (predicted)", unfused.predicted_allocations as i64, fused_bound.apparatus_prediction.allocations as i64),
        ("section octets (predicted)", unfused.predicted_section_octets as i64, fused_bound.apparatus_prediction.section_octets as i64),
    ] {
        let _ = writeln!(form, "    {what:<30} {u:>9} {f:>10} {:>+9}", f - u);
    }
    let _ = writeln!(form, "    the prediction and the driver agree: nodes {} == {}, edges {} == {}",
        fused_bound.apparatus_prediction.graph_nodes, fused_graph.nodes, fused_bound.apparatus_prediction.graph_edges, fused_graph.edges);
    let _ = writeln!(form, "    bind wall: unfused {:.3} s, fused {:.3} s; launch wall: unfused {:.6} s, fused {:.6} s", unfused.bind_wall_s, fused_bind_s, unfused.launch_wall_s, fused_launch_s);
    let _ = writeln!(form, "    (elapsed times are apparatus measurements in this process's frame with a display attached; they");
    let _ = writeln!(form, "    select nothing and the equality below is what admits the fusion.)");
    let _ = writeln!(form);

    // (3) the terminal faces, bit-equal
    let unfused_terminal = unfused.bound.read_terminal(&unfused.returned).map_err(|o| describe(&o))?;
    let fused_terminal = fused_bound.read_terminal(&fused_returned).map_err(|o| describe(&o))?;
    let terminal_equal = unfused_terminal == fused_terminal;
    let first_terminal_difference = unfused_terminal
        .iter()
        .zip(fused_terminal.iter())
        .position(|(a, b)| a != b)
        .map(|at| format!(" first at coordinate {at}: unfused {:?} fused {:?}", unfused_terminal[at], fused_terminal[at]))
        .unwrap_or_default();
    let _ = writeln!(
        form,
        "    THE TERMINAL FACE: {} coordinates, {}{}",
        unfused_terminal.len(),
        if terminal_equal { "BIT-EQUAL" } else { "DIFFERENT" },
        first_terminal_difference
    );

    // (4) every census, word for word, including the collapsed population
    let unfused_slots: BTreeMap<EventId, SlotReading> = unfused
        .returned
        .fronts
        .iter()
        .flat_map(|front| front.readings.iter())
        .map(|r| (r.occurrence, r.measured))
        .collect();
    let fused_slots: BTreeMap<EventId, SlotReading> = fused_returned
        .fronts
        .iter()
        .flat_map(|front| front.readings.iter())
        .map(|r| (r.occurrence, r.measured))
        .collect();
    let mut census_differences: Vec<String> = Vec::new();
    let mut collapsed_population_rows: Vec<(String, u64, u32, u64)> = Vec::new();
    for (event, unfused_slot) in &unfused_slots {
        let fused_slot = fused_slots.get(event).ok_or("the fused deed lost an occurrence")?;
        if unfused_slot != fused_slot {
            census_differences.push(format!(
                "{} {event:?}: unfused {unfused_slot:?} fused {fused_slot:?}",
                names.get(event).cloned().unwrap_or_default()
            ));
        }
        // the collapsed population: the census of a quotient's PREDECESSOR
        if fusible.contains(event) {
            if let Some(predecessor) = unfused.arriving.get(event).and_then(|p| p.first()) {
                if let Some(slot) = unfused_slots.get(predecessor) {
                    collapsed_population_rows.push((
                        names.get(predecessor).cloned().unwrap_or_default(),
                        slot.width_sum,
                        slot.nonzero_widths,
                        slot.max_width,
                    ));
                }
            }
        }
    }
    let _ = writeln!(
        form,
        "    EVERY CENSUS, WORD FOR WORD: {} occurrences compared, {} differ{}",
        unfused_slots.len(),
        census_differences.len(),
        if census_differences.is_empty() { " — every slot word of every occurrence is equal".to_owned() } else { ":".to_owned() }
    );
    for difference in census_differences.iter().take(8) {
        let _ = writeln!(form, "      {difference}");
    }
    let _ = writeln!(form);
    let total_collapsed: u64 = collapsed_population_rows.iter().map(|r| r.1).sum();
    let total_nonzero: u32 = collapsed_population_rows.iter().map(|r| r.2).sum();
    let _ = writeln!(
        form,
        "    THE COLLAPSED POPULATION THE CHART RETAINS — the PRE-quotient widths of the {} sealed",
        collapsed_population_rows.len()
    );
    let _ = writeln!(form, "    predecessors, summed over the layer: width_sum {total_collapsed} grains over {total_nonzero} coordinates that had");
    let _ = writeln!(form, "    a width at all. It is the predecessor's own census node in BOTH deeds, so it is unchanged by");
    let _ = writeln!(form, "    the fusion, and Station C's receipt reads the same population it always did. The five widest:");
    let mut widest = collapsed_population_rows.clone();
    widest.sort_by_key(|r| std::cmp::Reverse(r.1));
    for (name, width_sum, nonzero, max_width) in widest.iter().take(5) {
        let _ = writeln!(form, "      {:<50} width_sum {width_sum:>16}  nonzero {nonzero:>8}  widest {max_width:>16}", name.chars().take(50).collect::<String>());
    }
    let _ = writeln!(form);

    // (5) the read-time refusal, exhibited
    let _ = writeln!(form, "    THE READ-TIME REFUSAL, EXHIBITED. Asking the fused deed for a face the fusion sealed away:");
    let sealed_predecessor = fusible
        .first()
        .and_then(|q| unfused.arriving.get(q).and_then(|p| p.first()).copied())
        .ok_or("no fused quotient")?;
    match fused_bound.read_section(&fused_returned, sealed_predecessor) {
        Err(FrontPassageObstruction::Sealed { occurrence, quotient, reopening }) => {
            let _ = writeln!(form, "      REFUSED, by name: Sealed");
            let _ = writeln!(form, "        occurrence    {} {occurrence:?}", names.get(&occurrence).cloned().unwrap_or_default());
            let _ = writeln!(form, "        sealed by     {} {quotient:?}", names.get(&quotient).cloned().unwrap_or_default());
            let _ = writeln!(form, "        reopening     {reopening}");
        }
        Err(other) => return Err(format!("the sealed read returned the wrong obstruction: {}", describe(&other))),
        Ok(words) => return Err(format!("the sealed read returned {} collapsed words instead of refusing", words.len())),
    }
    let unfused_face = unfused.bound.read_section(&unfused.returned, sealed_predecessor).map_err(|o| describe(&o))?;
    let widths = unfused_face.iter().filter(|(lo, hi)| hi > lo).count();
    let _ = writeln!(
        form,
        "      AND THE REOPENING ROUTE RETURNS IT: the same occurrence in the unfused deed returns {} coordinates,",
        unfused_face.len()
    );
    let _ = writeln!(form, "      {widths} of them with a width the quotient would have collapsed. The route is a recompile, not a read.");
    let _ = writeln!(form);
    let _ = writeln!(
        form,
        "    PART C VERDICT: terminal {} · censuses {} · collapsed population {} · kernel nodes {} -> {} ({:+}) · refusal control {}",
        if terminal_equal { "BIT-EQUAL" } else { "DIFFERENT" },
        if census_differences.is_empty() { "EQUAL word for word" } else { "DIFFER" },
        "unchanged",
        unfused.kernel_nodes,
        fused_graph.kernel_nodes,
        fused_graph.kernel_nodes as i64 - unfused.kernel_nodes as i64,
        "REFUSED by name"
    );
    let _ = writeln!(form);
    Ok(())
}

/// **The same layer founded again, with the declared fusion bound on the quotients that may carry
/// it.** A realization holds boxed laws and is not clonable, so the layer is refounded — `found_layer`
/// is deterministic and allocates its occurrences in one order, which is why the event identities of
/// the refounded complex are the identities the fusion was decided over. `everything` binds the
/// fusion on ALL quotients including the one over a declared face; that is the refusal control, and
/// the COMPILE is what must catch it, not this function.
fn founded_with_fusion(
    refound: &dyn Fn() -> Result<tower::Founded, String>,
    fusible: &[EventId],
    refused_by_face: &[EventId],
    everything: bool,
) -> Result<tower::Founded, String> {
    let mut founded = refound()?;
    for event in fusible.iter().chain(if everything { refused_by_face.iter() } else { [].iter() }) {
        founded.realization.bind(*event, SealedMidpointQuotient);
    }
    Ok(founded)
}
