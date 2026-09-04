//! **Deed P1 — the cross-chart lift returns its exact defect, and the mouth returns its fibres.**
//!
//! Three admitted source families are lifted and every lift returns what it owes:
//!
//! 1. **The grouped-sharing quotient.** The source declares `num_attention_heads = 8`,
//!    `num_key_value_heads = 2`, `head_dim = 256`, and `num_key_value_groups =
//!    num_attention_heads // num_key_value_heads`, so **four receiver heads read one key/value
//!    family** — the contract sketch that said eight per family was wrong, and the tree governs.
//!    That sharing is a source-declared quotient `Phi_Y` on the receiver-head chart. `T_gamma` is
//!    the receiver projection over the four sharing heads; `S_gamma` is the presented projection of
//!    the family they share; `Phi_X` is the layer's own input rebase gain, a per-coordinate
//!    invertible chart transition on the hidden chart. `chi_gamma = Phi_Y T_gamma - S_gamma Phi_X`
//!    is computed exactly over the rationals with every face returned.
//! 2. **The bf16 mouth as a lift**, whose fibres are the exact rounding preimages: ties to even on
//!    real ties, asymmetric cells at binade low edges, the subnormal grid, and the two zeros
//!    splitting one magnitude cell. A census over one real map's entries checks the residual against
//!    its own fibre and against its neighbours'.
//! 3. **The recombination**, which composes the first two lifts into a return the source's own
//!    declared operation words do not contain: the exact reconstruction fibre of a grouped family
//!    coordinate. **This is a bounded demonstration of the recombination law and is not a claim that
//!    Phoenix produced a new capability.** It executes CPU-exact over the rationals; no kernel and no
//!    card are involved in it.
//!
//! Everything is exact. `f32` and `f64` appear nowhere: a codeword's meaning is a rational and the
//! rounding law manipulates integers. Every interval endpoint in every artifact is written as an
//! exact `numerator/denominator`.
//!
//! Run:
//! `cargo run --release -p holonic-engine --example the_lift_returns_its_defect_and_the_fibres_are_exact -- --root /home/b/models/gemma-4-E4B-it`

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs::File;
use std::time::Instant;

use holonic_engine::cross_chart::{
    ChartReceipt, CrossChartDefect, PathwiseFibre, PortStep, RoundingFibre, SummedFibre,
    bare_transpose_adjoint_defect, chain_law, chart_receipt, cross_chart_defect, rat_text,
    shortest_reopening_separator,
};
use holonic_engine::embedding_fiber::align_bfloat16;
use holonic_engine::exact_linear::ExactRatMatrix;
use holonic_engine::exact_value::ieee754;
use holonic_engine::foreign_map::{ForeignContainer, manifest_safetensors};
use holonic_engine::receiver_exact_compression::{
    InputId, ItemId, Observation, ObservedSystem, ReceiverId, compress,
};
use num_bigint::BigInt;
use num_traits::{Euclid, One, Signed, Zero};
use relational_geometry::Rat;
use sha2::{Digest, Sha256};

// ---------------------------------------------------------------------------------------------
// the declared apertures, all of them stated and none of them inside an organ
// ---------------------------------------------------------------------------------------------

/// The source's own configuration, read from the committed Station B/C binding site rather than
/// guessed. `resident_layer.rs` carries each of these beside the implementation line that declares
/// it.
const HIDDEN: usize = 2560;
const HEADS: usize = 8;
const KV_HEADS: usize = 2;
const HEAD_WIDTH: usize = 256;
/// `num_key_value_groups = num_attention_heads // num_key_value_heads`. **Four**, not eight.
const SHARED: usize = HEADS / KV_HEADS;

/// APERTURE — the hidden-chart window the exact rational linear algebra is taken over. The source's
/// hidden chart is 2,560 wide; exact reduced row echelon over the rationals on the whole width is a
/// cost, not an obstruction, and this deed declares the window rather than pretending to the width.
const HIDDEN_WINDOW: usize = 64;
/// APERTURE — the head-chart window, of the source's 256-wide head chart.
const HEAD_WINDOW: usize = HIDDEN_WINDOW / SHARED;
/// The key/value family whose four sharing receiver heads are lifted. Station D dissects families
/// `0` and the reuse of `0`; this is the same family.
const FAMILY: usize = 0;
/// APERTURE — the native grain the third port places at. Coarser than bf16 at this material's
/// magnitude, which is why it collapses codewords and has something to say.
const GRAIN: u32 = 8;
/// APERTURE — how many distinct codewords the grain-port receiver compression is run over.
const COMPRESSION_ITEMS: usize = 512;
/// APERTURE — how many doublings the grain-port receiver family may use to separate a pair.
const COMPRESSION_DEPTH: usize = 12;

const LAYER: usize = 0;
const OUT_DIR: &str = ".local/artifacts/the_lift_returns_its_defect";
/// The committed Station B/C deposit the declared source closure is read out of.
const SOURCE_CLOSURE_ARTIFACT: &str =
    ".local/artifacts/the_layer_stays_on_the_card/layer-0-resident-2-tokens-grain-48-terms-14.form";

fn named(suffix: &str) -> String {
    format!("model.language_model.layers.{LAYER}.{suffix}")
}

// ---------------------------------------------------------------------------------------------
// exact helpers — no float arithmetic anywhere
// ---------------------------------------------------------------------------------------------

fn value_of(word: u16) -> Rat {
    ieee754::decode_bfloat16_bits(word)
        .expect("a stored weight is finite")
        .value()
}

fn two() -> Rat {
    Rat::from_integer(BigInt::from(2))
}

fn power_of_two(exponent: i32) -> Rat {
    if exponent >= 0 {
        Rat::from_integer(BigInt::one() << (exponent as usize))
    } else {
        Rat::new(BigInt::one(), BigInt::one() << ((-exponent) as usize))
    }
}

fn digest_of(text: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(text.as_bytes());
    hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>()[..16]
        .to_owned()
}

fn matrix_text(matrix: &ExactRatMatrix) -> String {
    let mut text = String::new();
    for row in 0..matrix.rows() {
        for column in 0..matrix.columns() {
            let _ = write!(
                text,
                "{} ",
                rat_text(matrix.get(row, column).expect("inside"))
            );
        }
        text.push('\n');
    }
    text
}

fn vector_text(vector: &[Rat]) -> String {
    vector.iter().map(rat_text).collect::<Vec<_>>().join(" ")
}

fn is_identity(matrix: &ExactRatMatrix) -> bool {
    matrix.is_square()
        && ExactRatMatrix::identity(matrix.rows()).is_ok_and(|identity| *matrix == identity)
}

// ---------------------------------------------------------------------------------------------
// the grain port: a second rounding law, declared, on a fixed dyadic grid
// ---------------------------------------------------------------------------------------------

/// Round an exact rational onto the resident grain `2^-GRAIN`, round-to-nearest ties-to-even, on
/// integers. This is the third port of the pathway and it is a rounding like the first, on a grid
/// that does not vary with magnitude.
fn place_at_grain(value: &Rat, grain: u32) -> (BigInt, Rat) {
    let scale = power_of_two(grain as i32);
    let scaled = value * &scale;
    let floor = Euclid::div_euclid(scaled.numer(), scaled.denom());
    let remainder = &scaled - Rat::from_integer(floor.clone());
    let half = Rat::new(BigInt::one(), BigInt::from(2));
    let word = match remainder.cmp(&half) {
        std::cmp::Ordering::Less => floor,
        std::cmp::Ordering::Greater => floor + BigInt::one(),
        std::cmp::Ordering::Equal => {
            if (&floor % BigInt::from(2)).is_zero() {
                floor
            } else {
                floor + BigInt::one()
            }
        }
    };
    let placed = Rat::new(word.clone(), BigInt::one() << (grain as usize));
    let residual = value - &placed;
    (word, residual)
}

/// The grain port's own cell, by the same ties-to-even law: both endpoints belong to the even word.
fn grain_cell(word: &BigInt, grain: u32) -> (Rat, Rat, bool) {
    let ulp = power_of_two(-(grain as i32));
    let placed = Rat::new(word.clone(), BigInt::one() << (grain as usize));
    let half = &ulp / two();
    let even = (word % BigInt::from(2)).is_zero();
    (&placed - &half, &placed + &half, even)
}

// ---------------------------------------------------------------------------------------------
// material windows
// ---------------------------------------------------------------------------------------------

struct Material {
    file: File,
    container: ForeignContainer,
}

impl Material {
    fn open(root: &str) -> Result<Self, String> {
        let (file, container) = manifest_safetensors(&format!("{root}/model.safetensors"))
            .map_err(|error| error.to_string())?;
        Ok(Self { file, container })
    }

    fn rows(&mut self, name: &str, from: usize, count: usize) -> Result<(Vec<u16>, usize), String> {
        self.container
            .read_rows_bf16(&mut self.file, name, from, count)
            .map_err(|error| error.to_string())
    }

    fn whole(&mut self, name: &str) -> Result<Vec<u16>, String> {
        self.container
            .read_bf16_whole(&mut self.file, name)
            .map_err(|error| error.to_string())
    }

    fn shape(&self, name: &str) -> Result<Vec<usize>, String> {
        Ok(self
            .container
            .tensor(name)
            .map_err(|e| e.to_string())?
            .shape
            .clone())
    }

    /// A window of a stored rank-2 map: `rows` starting at `from_row`, columns `0..columns`.
    fn window(
        &mut self,
        name: &str,
        from_row: usize,
        row_count: usize,
        columns: usize,
    ) -> Result<Vec<Vec<Rat>>, String> {
        let (words, width) = self.rows(name, from_row, row_count)?;
        Ok(words
            .chunks(width)
            .map(|row| row[..columns].iter().map(|word| value_of(*word)).collect())
            .collect())
    }

    /// The stored codewords of a window, unrounded, for the fibre side.
    fn window_words(
        &mut self,
        name: &str,
        from_row: usize,
        row_count: usize,
        columns: usize,
    ) -> Result<Vec<Vec<u16>>, String> {
        let (words, width) = self.rows(name, from_row, row_count)?;
        Ok(words
            .chunks(width)
            .map(|row| row[..columns].to_vec())
            .collect())
    }
}

// ---------------------------------------------------------------------------------------------
// the grain-port receiver family, for the collapsed-pair reading
// ---------------------------------------------------------------------------------------------

/// Items are stored bf16 codewords. The one shot receiver is the **grain placement** — computed
/// from the material, never declared per item. The one input is *double the value*, which is an
/// exact operation on this chart (the exponent field moves by one) and takes a codeword to another
/// codeword. Two codewords the grain cannot separate may separate after enough doublings, and the
/// shortest such word is how far the reading had to look.
struct GrainReceiver {
    words: Vec<u16>,
    grain: u32,
    depth: usize,
}

impl ObservedSystem for GrainReceiver {
    fn items(&self) -> Vec<ItemId> {
        (0..self.words.len() as u64).map(ItemId).collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        vec![ReceiverId(0)]
    }

    fn inputs(&self) -> Vec<InputId> {
        vec![InputId(0)]
    }

    fn observation(&self, item: ItemId, _receiver: ReceiverId) -> Observation {
        let value = value_of(self.words[item.0 as usize]);
        let (word, _) = place_at_grain(&value, self.grain);
        // The grain word as a label. A label, not a magnitude: it names a block and nothing else.
        let mut hasher = Sha256::new();
        hasher.update(word.to_string().as_bytes());
        let digest = hasher.finalize();
        Observation(u64::from_le_bytes(
            digest[..8].try_into().expect("eight octets"),
        ))
    }

    fn successor(&self, item: ItemId, _input: InputId) -> Option<ItemId> {
        // Double: raise the exponent field by one. Refuses at the top of the format, which is a
        // terminus and therefore itself a distinction.
        let word = self.words[item.0 as usize];
        let exponent = (word >> 7) & 0xff;
        if exponent == 0 || exponent >= 0xfe {
            return None;
        }
        let doubled = (word & 0x807f) | ((exponent + 1) << 7);
        // The successor must be an item of this system, or the transport leaves the declared scope.
        self.words
            .iter()
            .position(|candidate| *candidate == doubled)
            .filter(|_| self.depth > 0)
            .map(|at| ItemId(at as u64))
    }
}

// ---------------------------------------------------------------------------------------------
// the census
// ---------------------------------------------------------------------------------------------

#[derive(Default, Clone)]
struct CensusRow {
    hits: u64,
    ties_held: u64,
    worst_residual: Rat,
}

#[derive(Default)]
struct Census {
    probes: u64,
    residual_law_held: u64,
    inside_own_fibre: u64,
    outside_neighbour_fibres: u64,
    neighbour_checks: u64,
    exact_ties: u64,
    refused: u64,
    by_cell: BTreeMap<&'static str, u64>,
    asymmetric_hits: u64,
    rows: BTreeMap<u16, CensusRow>,
}

impl Census {
    fn absorb(&mut self, other: Census) {
        self.probes += other.probes;
        self.residual_law_held += other.residual_law_held;
        self.inside_own_fibre += other.inside_own_fibre;
        self.outside_neighbour_fibres += other.outside_neighbour_fibres;
        self.neighbour_checks += other.neighbour_checks;
        self.exact_ties += other.exact_ties;
        self.refused += other.refused;
        self.asymmetric_hits += other.asymmetric_hits;
        for (cell, count) in other.by_cell {
            *self.by_cell.entry(cell).or_default() += count;
        }
        for (word, row) in other.rows {
            let slot = self.rows.entry(word).or_default();
            slot.hits += row.hits;
            slot.ties_held += row.ties_held;
            if row.worst_residual.abs() > slot.worst_residual.abs() {
                slot.worst_residual = row.worst_residual;
            }
        }
    }
}

/// One census chunk: the probe is the exact rational **midpoint of two adjacent stored entries**,
/// which is real material and which lands on a tie whenever the two sit in one binade. That is what
/// makes the census able to fail: an exactly representable entry would round to itself with a zero
/// residual and test nothing.
fn census_chunk(words: &[u16], next: &[u16]) -> Census {
    let mut census = Census::default();
    let mut fibres: BTreeMap<u16, RoundingFibre> = BTreeMap::new();
    for (word, following) in words.iter().zip(next) {
        let probe = (value_of(*word) + value_of(*following)) / two();
        census.probes += 1;
        let Ok((emitted, residual)) = ieee754::round_into_bfloat16(&probe) else {
            census.refused += 1;
            continue;
        };
        let fibre = fibres
            .entry(emitted)
            .or_insert_with(|| RoundingFibre::of_bfloat16(emitted).expect("a finite codeword"));
        if &fibre.value + &residual == probe {
            census.residual_law_held += 1;
        }
        if fibre.contains(&probe) {
            census.inside_own_fibre += 1;
        }
        // A TIE is a probe sitting on an endpoint that is not the codeword's own value. The zero
        // cell's lower endpoint IS its value — the sign split puts the origin there — so counting
        // that as a tie would inflate the figure with probes that are exactly zero.
        let held_tie = (probe == fibre.lower || probe == fibre.upper) && probe != fibre.value;
        if held_tie {
            census.exact_ties += 1;
        }
        *census.by_cell.entry(fibre.cell.name()).or_default() += 1;
        if fibre.asymmetric() {
            census.asymmetric_hits += 1;
        }
        let slot = census.rows.entry(emitted).or_default();
        slot.hits += 1;
        if held_tie {
            slot.ties_held += 1;
        }
        if residual.abs() > slot.worst_residual.abs() {
            slot.worst_residual = residual.clone();
        }
        // The falsifier: neither neighbour's cell may contain this probe. If the cells overlapped,
        // the fibre would not be a preimage.
        for neighbour in [emitted.wrapping_sub(1), emitted.wrapping_add(1)] {
            let Ok(other) = RoundingFibre::of_bfloat16(neighbour) else {
                continue;
            };
            census.neighbour_checks += 1;
            if !other.contains(&probe) {
                census.outside_neighbour_fibres += 1;
            }
        }
    }
    census
}

// ---------------------------------------------------------------------------------------------

/// Which reading of the bf16 port the recombination is taken under. `ExactBitPattern` is the
/// ablation of family two: it declares that nothing was deleted at this port, so the cell is a
/// point and the fibre carries no interval.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FibreReading {
    ExactPreimage,
    ExactBitPattern,
}

/// One reading of the recombined return, with the unrelated control recomputed beside it.
struct Recombination {
    summed: usize,
    value: Rat,
    width: Rat,
    interval: String,
    kernel: Vec<Vec<Rat>>,
    kernel_dimension: usize,
    control: CrossChartDefect,
    control_rank: usize,
    control_digest: String,
}

struct Args {
    root: String,
    census_limit: Option<usize>,
    threads: usize,
}

fn parse_args() -> Args {
    let mut args = Args {
        root: "/home/b/models/gemma-4-E4B-it".to_owned(),
        census_limit: None,
        threads: std::thread::available_parallelism()
            .map_or(8, |n| n.get())
            .min(16),
    };
    let raw: Vec<String> = std::env::args().collect();
    let mut at = 1;
    while at < raw.len() {
        match raw[at].as_str() {
            "--root" => {
                args.root = raw[at + 1].clone();
                at += 2;
            }
            "--census-limit" => {
                args.census_limit = Some(raw[at + 1].parse().expect("a count"));
                at += 2;
            }
            "--threads" => {
                args.threads = raw[at + 1].parse().expect("a count");
                at += 2;
            }
            _ => at += 1,
        }
    }
    args
}

fn main() -> Result<(), String> {
    let args = parse_args();
    let started = Instant::now();
    std::fs::create_dir_all(OUT_DIR).map_err(|e| e.to_string())?;
    let mut receipt = String::new();
    let mut chi_rows: Vec<String> = Vec::new();

    let mut material = Material::open(&args.root)?;

    let _ = writeln!(
        receipt,
        "THE LIFT RETURNS ITS DEFECT — Deed P1 · source {} · layer {LAYER}\n\
         Every semantic number below is exact over the rationals. No float arithmetic occurs on any\n\
         semantic path; a codeword's meaning is a rational and both rounding laws run on integers.\n\
         Every interval endpoint is written as an exact numerator/denominator. The only floating\n\
         point in this deed is the wall-clock figures, rendered through Duration::as_secs_f64 — a\n\
         clock here measures and never selects, and no admission, receipt or face depends on one.\n",
        args.root
    );

    // ==========================================================================================
    // the declared charts and their receipts
    // ==========================================================================================
    let _ = writeln!(
        receipt,
        "== 0. THE DECLARED CHARTS, THEIR APERTURES AND THEIR RECEIPTS ==\n"
    );

    let q_shape = material.shape(&named("self_attn.q_proj.weight"))?;
    let k_shape = material.shape(&named("self_attn.k_proj.weight"))?;
    let o_shape = material.shape(&named("self_attn.o_proj.weight"))?;
    let _ = writeln!(
        receipt,
        "source configuration, as the committed binding site carries it: num_attention_heads {HEADS} · \
         num_key_value_heads {KV_HEADS} · head_dim {HEAD_WIDTH} · hidden {HIDDEN}\n\
         num_key_value_groups = {HEADS} // {KV_HEADS} = {SHARED} — **four** receiver heads read one\n\
         key/value family, not eight. The stored shapes agree: q_proj {q_shape:?} = {HEADS} x {HEAD_WIDTH} rows;\n\
         k_proj {k_shape:?} = {KV_HEADS} x {HEAD_WIDTH} rows; o_proj {o_shape:?}.\n\
         APERTURE hidden window {HIDDEN_WINDOW} of {HIDDEN} columns · head window {HEAD_WINDOW} of {HEAD_WIDTH} \
         coordinates · family {FAMILY} of {KV_HEADS} · grain 2^-{GRAIN}\n"
    );

    // Phi_X — the layer's input rebase gain, a source-declared per-coordinate chart transition on
    // the hidden chart. Whether it is a rebase or a quotient is decided by the material, not here.
    let (gain_words, _) = material
        .rows(&named("input_layernorm.weight"), 0, 1)
        .or_else(|_| {
            let words = material.whole(&named("input_layernorm.weight"))?;
            let width = words.len();
            Ok::<_, String>((words, width))
        })?;
    let gains: Vec<Rat> = gain_words[..HIDDEN_WINDOW]
        .iter()
        .map(|w| value_of(*w))
        .collect();
    let zero_gains = gains.iter().filter(|g| g.is_zero()).count();
    let phi_x = ExactRatMatrix::from_diagonal(gains.clone()).map_err(|e| e.to_string())?;
    let phi_x_receipt = chart_receipt(&phi_x).map_err(|e| e.to_string())?;

    // Phi_Z — the layer's post-attention rebase gain, the chart transition on the returning hidden
    // chart. A different real gain, so the chain law is not composed against itself.
    let post_words = material.whole(&named("post_attention_layernorm.weight"))?;
    let post_gains: Vec<Rat> = post_words[..HIDDEN_WINDOW]
        .iter()
        .map(|w| value_of(*w))
        .collect();
    let phi_z = ExactRatMatrix::from_diagonal(post_gains.clone()).map_err(|e| e.to_string())?;
    let phi_z_receipt = chart_receipt(&phi_z).map_err(|e| e.to_string())?;

    // Phi_Y — the grouped-sharing quotient: four receiver-head copies of one head coordinate summed
    // into the family coordinate they share.
    let mut phi_y_rows = vec![vec![Rat::zero(); SHARED * HEAD_WINDOW]; HEAD_WINDOW];
    for (coordinate, row) in phi_y_rows.iter_mut().enumerate() {
        for head in 0..SHARED {
            row[head * HEAD_WINDOW + coordinate] = Rat::one();
        }
    }
    let phi_y = ExactRatMatrix::new(phi_y_rows).map_err(|e| e.to_string())?;
    let phi_y_receipt = chart_receipt(&phi_y).map_err(|e| e.to_string())?;

    for (name, receipt_value, shape) in [
        (
            "Phi_X  input rebase gain (hidden chart)",
            &phi_x_receipt,
            (phi_x.rows(), phi_x.columns()),
        ),
        (
            "Phi_Z  post-attention rebase gain (hidden chart)",
            &phi_z_receipt,
            (phi_z.rows(), phi_z.columns()),
        ),
        (
            "Phi_Y  grouped-sharing quotient (receiver-head chart -> family chart)",
            &phi_y_receipt,
            (phi_y.rows(), phi_y.columns()),
        ),
    ] {
        match receipt_value {
            ChartReceipt::Rebase {
                forward_identity,
                backward_identity,
                inverse,
            } => {
                let _ = writeln!(
                    receipt,
                    "  {name}  [{} x {}]  RECEIPT: rebase.\n    \
                     BOTH identity compositions exhibited: Phi Phi^-1 = I is {} and Phi^-1 Phi = I is {}.\n    \
                     inverse digest {} · first inverse entry {}",
                    shape.0,
                    shape.1,
                    is_identity(forward_identity),
                    is_identity(backward_identity),
                    digest_of(&matrix_text(inverse)),
                    rat_text(inverse.get(0, 0).expect("inside"))
                );
                assert!(is_identity(forward_identity) && is_identity(backward_identity));
            }
            ChartReceipt::Quotient {
                rank,
                kernel,
                cokernel_annihilator,
                refusal,
            } => {
                let _ = writeln!(
                    receipt,
                    "  {name}  [{} x {}]  RECEIPT: quotient. NO INVERSE IS RETURNED — {refusal}\n    \
                     rank {rank} · kernel dimension {} · open exterior {} · first collapsed direction: {}",
                    shape.0,
                    shape.1,
                    kernel.len(),
                    cokernel_annihilator.len(),
                    kernel
                        .first()
                        .map(|direction| {
                            let named: Vec<String> = direction
                                .iter()
                                .enumerate()
                                .filter(|(_, entry)| !entry.is_zero())
                                .map(|(at, entry)| {
                                    format!(
                                        "{}*head[{}].coord[{}]",
                                        rat_text(entry),
                                        at / HEAD_WINDOW,
                                        at % HEAD_WINDOW
                                    )
                                })
                                .collect();
                            named.join(" + ")
                        })
                        .unwrap_or_else(|| "none".to_owned())
                );
            }
        }
    }
    let _ = writeln!(
        receipt,
        "  the input rebase gain has {zero_gains} zero coordinates in the declared window, which is what\n  \
         decides Phi_X's species; the material decided it, not this deed.\n"
    );

    // The bare-transpose control, on a genuinely non-diagonal source-declared invertible chart: the
    // rotate_half signed permutation the source's chronology uses.
    let mut rotate_rows = vec![vec![Rat::zero(); HEAD_WINDOW]; HEAD_WINDOW];
    let half_head = HEAD_WINDOW / 2;
    for at in 0..half_head {
        rotate_rows[at][at + half_head] = -Rat::one();
        rotate_rows[at + half_head][at] = Rat::one();
    }
    let rotate = ExactRatMatrix::new(rotate_rows).map_err(|e| e.to_string())?;
    let rotate_receipt = chart_receipt(&rotate).map_err(|e| e.to_string())?;
    let rotate_squared = rotate.multiply(&rotate).map_err(|e| e.to_string())?;
    let minus_identity = ExactRatMatrix::identity(HEAD_WINDOW)
        .map_err(|e| e.to_string())?
        .scaled(&-Rat::one());
    let identity_head = ExactRatMatrix::identity(HEAD_WINDOW).map_err(|e| e.to_string())?;
    let head_metric =
        ExactRatMatrix::from_diagonal(gains[..HEAD_WINDOW].to_vec()).map_err(|e| e.to_string())?;
    let probe_x: Vec<Rat> = (0..HEAD_WINDOW).map(|at| gains[at].clone()).collect();
    let probe_y: Vec<Rat> = (0..HEAD_WINDOW)
        .map(|at| if at == 0 { Rat::one() } else { Rat::zero() })
        .collect();
    let (bare_euclid, lawful_euclid) =
        bare_transpose_adjoint_defect(&rotate, &identity_head, &identity_head, &probe_x, &probe_y)
            .map_err(|e| e.to_string())?;
    let (bare_weighted, lawful_weighted) =
        bare_transpose_adjoint_defect(&rotate, &head_metric, &identity_head, &probe_x, &probe_y)
            .map_err(|e| e.to_string())?;
    let _ = writeln!(
        receipt,
        "  CONTROL — a bare transpose is not an adjoint under a metric nobody made the identity.\n  \
         the source's `rotate_half` signed permutation on the {HEAD_WINDOW}-wide head chart: receipt {} · \
         J^2 = -I is {}\n    \
         under two IDENTITY metrics:            bare-transpose defect {}   metric-adjoint defect {}\n    \
         under the declared gain metric G_X:    bare-transpose defect {}   metric-adjoint defect {}\n  \
         The bare transpose is the adjoint exactly when the metrics are the identity, which is a\n  \
         declaration. Under the layer's own gain it is a different map and the pairing does not balance.\n",
        rotate_receipt.species(),
        rotate_squared == minus_identity,
        rat_text(&bare_euclid),
        rat_text(&lawful_euclid),
        rat_text(&bare_weighted),
        rat_text(&lawful_weighted)
    );
    assert!(lawful_euclid.is_zero() && lawful_weighted.is_zero());

    // ==========================================================================================
    // FAMILY 1 — the grouped-sharing quotient
    // ==========================================================================================
    let _ = writeln!(
        receipt,
        "== 1. FAMILY ONE — THE GROUPED-SHARING QUOTIENT ==\n"
    );
    let family_one_clock = Instant::now();

    // T_gamma: the receiver projection over the SHARED heads that read family FAMILY.
    let mut t_gamma_rows: Vec<Vec<Rat>> = Vec::with_capacity(SHARED * HEAD_WINDOW);
    for head in 0..SHARED {
        let source_head = FAMILY * SHARED + head;
        let block = material.window(
            &named("self_attn.q_proj.weight"),
            source_head * HEAD_WIDTH,
            HEAD_WINDOW,
            HIDDEN_WINDOW,
        )?;
        t_gamma_rows.extend(block);
    }
    let t_gamma = ExactRatMatrix::new(t_gamma_rows).map_err(|e| e.to_string())?;

    // S_gamma: the presented projection of the family they share.
    let s_gamma_rows = material.window(
        &named("self_attn.k_proj.weight"),
        FAMILY * HEAD_WIDTH,
        HEAD_WINDOW,
        HIDDEN_WINDOW,
    )?;
    let s_gamma = ExactRatMatrix::new(s_gamma_rows).map_err(|e| e.to_string())?;

    let hidden_names: Vec<String> = (0..HIDDEN_WINDOW)
        .map(|at| format!("hidden[{at}]"))
        .collect();
    let chi_gamma = cross_chart_defect(
        "gamma: receiver projection lifted through the grouped-sharing quotient",
        &phi_y,
        &t_gamma,
        &s_gamma,
        &phi_x,
        &hidden_names,
    )
    .map_err(|e| e.to_string())?;
    report_defect(
        &mut receipt,
        &mut chi_rows,
        &chi_gamma,
        "gamma",
        &format!("the hidden chart, {HIDDEN_WINDOW} of {HIDDEN} columns"),
    );

    let separator = shortest_reopening_separator(&phi_y)
        .map_err(|e| e.to_string())?
        .expect("the grouped-sharing quotient collapses something");
    let _ = writeln!(
        receipt,
        "  THE SHORTEST REOPENING SEPARATOR for the grouped-sharing quotient:\n    \
         the pair (0, k) with k the first collapsed direction — both carried to {} by Phi_Y, so the\n    \
         family chart cannot tell them apart. One coordinate of the FINER chart reopens them:\n    \
         coordinate {} = head[{}].coord[{}] reads {} on the left and {} on the right. Word length {}.\n  \
         For a linear quotient the reopening word is always ONE coordinate functional — two distinct\n  \
         vectors differ somewhere and a single coordinate reads the difference. The content is which\n  \
         coordinate and what the two readings were, and both are above. A receiver family with a\n  \
         successor conduct needs receiver_exact_compression, whose words can be longer than one; that\n  \
         reading is taken at the grain port in section 3 where a successor exists.\n",
        vector_text(&separator.identified_image),
        separator.separating_coordinate,
        separator.separating_coordinate / HEAD_WINDOW,
        separator.separating_coordinate % HEAD_WINDOW,
        rat_text(&separator.left_reading),
        rat_text(&separator.right_reading),
        separator.word_length
    );

    // The chain law: eta is the contact's return through o_proj.
    let t_eta_full = material.window(
        &named("self_attn.o_proj.weight"),
        0,
        HIDDEN_WINDOW,
        HEADS * HEAD_WIDTH,
    )?;
    let mut t_eta_rows: Vec<Vec<Rat>> = Vec::with_capacity(HIDDEN_WINDOW);
    let mut s_eta_rows: Vec<Vec<Rat>> = Vec::with_capacity(HIDDEN_WINDOW);
    for row in &t_eta_full {
        let mut carried = Vec::with_capacity(SHARED * HEAD_WINDOW);
        for head in 0..SHARED {
            let source_head = FAMILY * SHARED + head;
            for coordinate in 0..HEAD_WINDOW {
                carried.push(row[source_head * HEAD_WIDTH + coordinate].clone());
            }
        }
        // S_eta reads the family chart: the o_proj columns of the family's first head block.
        let native: Vec<Rat> = (0..HEAD_WINDOW)
            .map(|coordinate| row[FAMILY * SHARED * HEAD_WIDTH + coordinate].clone())
            .collect();
        t_eta_rows.push(carried);
        s_eta_rows.push(native);
    }
    let t_eta = ExactRatMatrix::new(t_eta_rows).map_err(|e| e.to_string())?;
    let s_eta = ExactRatMatrix::new(s_eta_rows).map_err(|e| e.to_string())?;

    // Three real material vectors: rows of the source's own embedding table, windowed.
    let embed_rows = material.window(
        "model.language_model.embed_tokens.weight",
        0,
        3,
        HIDDEN_WINDOW,
    )?;
    let material_vectors: Vec<(String, Vec<Rat>)> = embed_rows
        .into_iter()
        .enumerate()
        .map(|(at, row)| (format!("embed_tokens row {at}"), row))
        .collect();

    let (_, chi_eta, chi_composite, chain) = chain_law(
        &phi_x,
        &phi_y,
        &phi_z,
        &t_gamma,
        &s_gamma,
        &t_eta,
        &s_eta,
        &material_vectors,
    )
    .map_err(|e| e.to_string())?;
    report_defect(
        &mut receipt,
        &mut chi_rows,
        &chi_eta,
        "eta",
        &format!("the receiver-head chart, {SHARED} x {HEAD_WINDOW} coordinates"),
    );
    report_defect(
        &mut receipt,
        &mut chi_rows,
        &chi_composite,
        "eta-after-gamma",
        &format!("the hidden chart, {HIDDEN_WINDOW} of {HIDDEN} columns"),
    );

    let _ = writeln!(
        receipt,
        "  THE SERIAL CHAIN LAW  chi_{{eta gamma}} = chi_eta T_gamma + S_eta chi_gamma\n\n  \
         derivation, one line and the middle terms are what cancel:\n    \
         chi_eta T_gamma + S_eta chi_gamma\n      \
         = (Phi_Z T_eta - S_eta Phi_Y) T_gamma + S_eta (Phi_Y T_gamma - S_gamma Phi_X)\n      \
         = Phi_Z T_eta T_gamma - S_eta Phi_Y T_gamma + S_eta Phi_Y T_gamma - S_eta S_gamma Phi_X\n      \
         = Phi_Z T_{{eta gamma}} - S_{{eta gamma}} Phi_X  =  chi_{{eta gamma}}\n\n  \
         OPERATOR IDENTITY on the real windowed material: residual is the zero {} x {} matrix — {}\n  \
         (the composite defect is itself nonzero, rank {}, so the identity is not vacuous here)",
        chain.residual.rows(),
        chain.residual.columns(),
        chain.operator_identity_holds,
        chi_composite.rank()
    );
    for check in &chain.vector_checks {
        let _ = writeln!(
            receipt,
            "    vector {:<22} holds {} · residual all zero {} · first composed coordinate {}",
            check.name,
            check.holds,
            check.residual.iter().all(num_traits::Zero::is_zero),
            rat_text(&check.composed[0])
        );
    }
    assert!(chain.operator_identity_holds);
    assert!(chain.vector_checks.iter().all(|check| check.holds));
    let _ = writeln!(
        receipt,
        "  family one wall {:.1} s\n",
        family_one_clock.elapsed().as_secs_f64()
    );

    // ==========================================================================================
    // FAMILY 2 — the bf16 mouth as a lift, with exact fibres
    // ==========================================================================================
    let _ = writeln!(
        receipt,
        "== 2. FAMILY TWO — THE BF16 MOUTH, AND ITS FIBRES ARE EXACT ==\n"
    );

    let _ = writeln!(
        receipt,
        "  The forward map is round-to-nearest ties-to-even with an exact rational residual. The\n  \
         FIBRE is the exact preimage: the set of rationals that round to a codeword. The standing\n  \
         enclosure is deliberately OUTWARD — its own text says the true preimage below a binade's low\n  \
         edge is a quarter ulp and it returns a half — so it is an admission test and not a fibre.\n  \
         The membership law, derived from the mouth as written and uniform over every case the format\n  \
         has: BOTH endpoints belong to the codeword whose significand is EVEN. Adjacent codewords\n  \
         always have opposite significand parity, including across a binade re-seat where 255 is\n  \
         followed by 128, so every tie belongs to exactly one side and the cells partition.\n"
    );

    // --- the four exhibits, verbatim ---
    let _ = writeln!(
        receipt,
        "  EXHIBIT 1 — ties to even, on a real tie between two adjacent stored codewords:"
    );
    let (tie_words, tie_probe, tie_emitted, tie_fibre, tie_loser) = {
        let sample = material.window_words(&named("self_attn.q_proj.weight"), 0, 1, 1024)?;
        let row = &sample[0];
        let mut found = None;
        for pair in row.windows(2) {
            let (a, b) = (pair[0], pair[1]);
            if a == b {
                continue;
            }
            let probe = (value_of(a) + value_of(b)) / two();
            let Ok((emitted, _)) = ieee754::round_into_bfloat16(&probe) else {
                continue;
            };
            let Ok(fibre) = RoundingFibre::of_bfloat16(emitted) else {
                continue;
            };
            // A genuine tie: the probe sits exactly on one of the cell's endpoints. The LOSER is
            // the codeword on the other side of that tie — the neighbour whose own cell has this
            // same endpoint — not one of the two summands, which need not be adjacent at all.
            if probe == fibre.lower || probe == fibre.upper {
                let mut loser = None;
                for candidate in [emitted.wrapping_sub(1), emitted.wrapping_add(1)] {
                    let Ok(other) = RoundingFibre::of_bfloat16(candidate) else {
                        continue;
                    };
                    if other.lower == probe || other.upper == probe {
                        loser = Some(candidate);
                        break;
                    }
                }
                let Some(loser) = loser else { continue };
                found = Some(((a, b), probe, emitted, fibre, loser));
                break;
            }
        }
        found.ok_or_else(|| "no real tie in the sampled row".to_owned())?
    };
    let tie_loser_fibre = RoundingFibre::of_bfloat16(tie_loser).map_err(|e| e.to_string())?;
    let _ = writeln!(
        receipt,
        "    stored words {:#06x} and {:#06x}; their exact midpoint is {}\n    \
         the mouth emits {:#06x} (significand even: {}) whose fibre is {}\n    \
         the losing codeword {:#06x} has significand even: {} and fibre {}, which does NOT contain the\n    \
         midpoint. The tie went to the even significand, and the fibre said so before the mouth was asked:\n    \
         fibre.contains(midpoint) = {} for the winner and {} for the loser.\n",
        tie_words.0,
        tie_words.1,
        rat_text(&tie_probe),
        tie_emitted,
        tie_fibre.significand_even,
        tie_fibre.interval_text(),
        tie_loser,
        tie_loser_fibre.significand_even,
        tie_loser_fibre.interval_text(),
        tie_fibre.contains(&tie_probe),
        tie_loser_fibre.contains(&tie_probe)
    );

    let _ = writeln!(
        receipt,
        "  EXHIBIT 2 — an asymmetric cell at a binade's low edge, with its two half-widths UNEQUAL:"
    );
    let asymmetric = RoundingFibre::of_bfloat16(0x3f80).map_err(|e| e.to_string())?;
    let _ = writeln!(
        receipt,
        "    codeword {:#06x} = {} · cell {} · {}\n    \
         lower half-width {} · upper half-width {} · ratio exactly 1:2 — {}\n    \
         The neighbour BELOW sits on the finer grid of the binade underneath, so the cell reaches a\n    \
         quarter ulp down and a half ulp up. The standing outward enclosure returns a half ulp on both\n    \
         sides and therefore over-approximates the preimage by a quarter ulp below the point.\n",
        asymmetric.bits,
        rat_text(&asymmetric.value),
        asymmetric.cell.name(),
        asymmetric.interval_text(),
        rat_text(&asymmetric.lower_half_width),
        rat_text(&asymmetric.upper_half_width),
        &asymmetric.lower_half_width * two() == asymmetric.upper_half_width
    );

    let _ = writeln!(
        receipt,
        "  EXHIBIT 3 — the subnormal grid, and it does NOT change at the normal boundary:"
    );
    for word in [0x0001u16, 0x007f, 0x0080] {
        let fibre = RoundingFibre::of_bfloat16(word).map_err(|e| e.to_string())?;
        let _ = writeln!(
            receipt,
            "    {:#06x} = {} · cell {:<16} · {} · half-widths {} and {} · asymmetric {}",
            word,
            rat_text(&fibre.value),
            fibre.cell.name(),
            fibre.interval_text(),
            rat_text(&fibre.lower_half_width),
            rat_text(&fibre.upper_half_width),
            fibre.asymmetric()
        );
    }
    let largest_subnormal = RoundingFibre::of_bfloat16(0x007f).map_err(|e| e.to_string())?;
    let smallest_normal = RoundingFibre::of_bfloat16(0x0080).map_err(|e| e.to_string())?;
    let _ = writeln!(
        receipt,
        "    the largest subnormal's upper endpoint {} IS the smallest normal's lower endpoint, and\n    \
         exactly one of them holds it: {} and {}. The smallest normal is NOT a binade low edge — its\n    \
         neighbour below shares its ulp — so no asymmetry appears at the subnormal boundary.\n",
        rat_text(&largest_subnormal.upper),
        largest_subnormal.upper_closed,
        smallest_normal.lower_closed
    );

    let _ = writeln!(
        receipt,
        "  EXHIBIT 4 — the two zeros, splitting one magnitude cell:"
    );
    let positive_zero = RoundingFibre::of_bfloat16(0x0000).map_err(|e| e.to_string())?;
    let negative_zero = RoundingFibre::of_bfloat16(0x8000).map_err(|e| e.to_string())?;
    let _ = writeln!(
        receipt,
        "    +0 {:#06x} · cell {} · {}\n    \
         -0 {:#06x} · cell {} · {}\n    \
         The two cells are disjoint and their union is the magnitude cell {}..{}. The ORIGIN belongs to\n    \
         +0, because the emit-side mouth takes the sign from the rational's own sign and an exact zero\n    \
         is not negative. So -0's cell is closed where the tie lands and OPEN at the origin. The mouth\n    \
         agrees: round(the -0 tie) = {:#06x} and round(the +0 tie) = {:#06x}, and round(0) = {:#06x}.\n",
        positive_zero.bits,
        positive_zero.cell.name(),
        positive_zero.interval_text(),
        negative_zero.bits,
        negative_zero.cell.name(),
        negative_zero.interval_text(),
        rat_text(&negative_zero.lower),
        rat_text(&positive_zero.upper),
        ieee754::round_into_bfloat16(&negative_zero.lower)
            .map_err(|e| e.to_string())?
            .0,
        ieee754::round_into_bfloat16(&positive_zero.upper)
            .map_err(|e| e.to_string())?
            .0,
        ieee754::round_into_bfloat16(&Rat::zero())
            .map_err(|e| e.to_string())?
            .0
    );

    // --- the census over one real map ---
    let census_clock = Instant::now();
    let q_words = material.whole(&named("self_attn.q_proj.weight"))?;
    let census_extent = args
        .census_limit
        .unwrap_or(q_words.len())
        .min(q_words.len());
    let slice = &q_words[..census_extent];
    let chunk = census_extent.div_ceil(args.threads.max(1));
    let mut census = Census::default();
    std::thread::scope(|scope| {
        let mut handles = Vec::new();
        for start in (0..census_extent).step_by(chunk.max(1)) {
            let end = (start + chunk).min(census_extent);
            let words = &slice[start..end];
            let next: Vec<u16> = (start..end)
                .map(|at| slice[(at + 1) % census_extent])
                .collect();
            handles.push(scope.spawn(move || census_chunk(words, &next)));
        }
        for handle in handles {
            census.absorb(handle.join().expect("a census chunk"));
        }
    });
    let census_wall = census_clock.elapsed();

    let _ = writeln!(
        receipt,
        "  THE CENSUS — over {} of {} stored entries of {} ({:?})\n  \
         APERTURE: {} · threads {} · wall {:.1} s\n  \
         The probe is the exact rational MIDPOINT of two adjacent stored entries. That is real\n  \
         material and it is what makes the census able to fail: an exactly representable entry rounds\n  \
         to itself with a zero residual and tests nothing, while a midpoint lands on a tie whenever\n  \
         the two entries sit in one binade — so the census exercises ties-to-even at scale.\n\n    \
         probes                                        {}\n    \
         residual law held (probe = value + residual)  {}   ({} failures)\n    \
         probe inside its OWN fibre                    {}   ({} outside)\n    \
         probe outside BOTH neighbour fibres           {} of {} neighbour checks ({} overlaps)\n    \
         exact ties (probe sits on a cell endpoint)    {}\n    \
         refused by the mouth (past the format)        {}\n    \
         distinct codewords the material produced      {}\n    \
         probes landing in an ASYMMETRIC cell          {}\n  \
         Two cell species are asymmetric and for different reasons: a binade low edge, where the grid\n  \
         below is finer, and the zero cells, where the SIGN splits one magnitude cell and the origin\n  \
         goes to the positive side. The by-cell table below separates them.\n",
        census_extent,
        q_words.len(),
        named("self_attn.q_proj.weight"),
        q_shape,
        if args.census_limit.is_some() {
            format!("a declared prefix of {census_extent} entries")
        } else {
            "the WHOLE map, every entry".to_owned()
        },
        args.threads,
        census_wall.as_secs_f64(),
        census.probes,
        census.residual_law_held,
        census.probes - census.residual_law_held - census.refused,
        census.inside_own_fibre,
        census.probes - census.inside_own_fibre - census.refused,
        census.outside_neighbour_fibres,
        census.neighbour_checks,
        census.neighbour_checks - census.outside_neighbour_fibres,
        census.exact_ties,
        census.refused,
        census.rows.len(),
        census.asymmetric_hits
    );
    let _ = writeln!(receipt, "    by cell:");
    for cell in [
        "normal",
        "binade low edge",
        "subnormal",
        "positive zero",
        "negative zero",
    ] {
        match census.by_cell.get(cell) {
            Some(count) => {
                let _ = writeln!(receipt, "      {cell:<18} {count}");
            }
            None => {
                let _ = writeln!(
                    receipt,
                    "      {cell:<18} 0   — this material produced none. A genuine zero: the stored \
                     magnitudes sit far above the subnormal floor 2^-133, and a midpoint of two \
                     same-signed entries is never negative-zero-bound. The cells are exhibited above \
                     from the format directly, and the exhaustive sweep in the owner's tests covers \
                     every pattern the format has."
                );
            }
        }
    }
    assert_eq!(census.residual_law_held + census.refused, census.probes);
    assert_eq!(census.inside_own_fibre + census.refused, census.probes);
    assert_eq!(census.outside_neighbour_fibres, census.neighbour_checks);

    // --- the pathwise composition across three ports ---
    let _ = writeln!(
        receipt,
        "\n  THE PATHWISE COMPOSITION — bf16 -> aligned -> grain, with the lineage carried\n"
    );
    const PATH_WINDOW: usize = 64;
    let path_words = material.window_words(&named("self_attn.q_proj.weight"), 0, 1, PATH_WINDOW)?;
    let path_row = &path_words[0];
    // The exact quantity that ENTERED the mouth is unknown for a stored weight, so the pathway is
    // exhibited on a real quantity this deed itself forms: the midpoint of two adjacent entries.
    let entered_probes: Vec<Rat> = (0..PATH_WINDOW)
        .map(|at| (value_of(path_row[at]) + value_of(path_row[(at + 1) % PATH_WINDOW])) / two())
        .collect();
    let mut emitted_words: Vec<u16> = Vec::with_capacity(PATH_WINDOW);
    let mut bf16_residuals: Vec<Rat> = Vec::with_capacity(PATH_WINDOW);
    for probe in &entered_probes {
        let (emitted, residual) = ieee754::round_into_bfloat16(probe).map_err(|e| e.to_string())?;
        emitted_words.push(emitted);
        bf16_residuals.push(residual);
    }
    // Port two aligns what port one EMITTED. Aligning the stored entries instead would be a second
    // pathway, not this one's next port.
    let aligned = align_bfloat16(&emitted_words).map_err(|e| e.to_string())?;
    let mut grain_classes: BTreeMap<String, Vec<(u16, RoundingFibre)>> = BTreeMap::new();
    for at in 0..PATH_WINDOW {
        let entered = entered_probes[at].clone();
        let emitted = emitted_words[at];
        let bf16_residual = bf16_residuals[at].clone();
        let bf16_fibre = RoundingFibre::of_bfloat16(emitted).map_err(|e| e.to_string())?;

        // Port two: the aligned integer chart. Exact — an integer and a common exponent, zero
        // remainder — so it contributes a point and deletes nothing.
        let aligned_value =
            Rat::from_integer(BigInt::from(aligned.entries[at])) * power_of_two(aligned.exponent);
        let aligned_exact = aligned_value == bf16_fibre.value;

        // Port three: the resident grain, a second rounding on a fixed dyadic grid.
        let (grain_word, grain_residual) = place_at_grain(&bf16_fibre.value, GRAIN);
        let (grain_lower, grain_upper, grain_even) = grain_cell(&grain_word, GRAIN);

        let composed = PathwiseFibre::compose(
            entered.clone(),
            vec![
                PortStep {
                    port: "bf16 round-to-nearest-ties-even".to_owned(),
                    carried: bf16_fibre.value.clone(),
                    lower: bf16_fibre.lower.clone(),
                    upper: bf16_fibre.upper.clone(),
                    lower_closed: bf16_fibre.lower_closed,
                    upper_closed: bf16_fibre.upper_closed,
                    residual: bf16_residual.clone(),
                    exact: false,
                },
                PortStep {
                    port: "aligned integer + common exponent".to_owned(),
                    carried: aligned_value.clone(),
                    lower: bf16_fibre.lower.clone(),
                    upper: bf16_fibre.upper.clone(),
                    lower_closed: bf16_fibre.lower_closed,
                    upper_closed: bf16_fibre.upper_closed,
                    residual: Rat::zero(),
                    exact: true,
                },
                PortStep {
                    port: format!("grain 2^-{GRAIN} round-to-nearest-ties-even"),
                    carried: Rat::new(grain_word.clone(), BigInt::one() << (GRAIN as usize)),
                    lower: grain_lower.clone(),
                    upper: grain_upper.clone(),
                    lower_closed: grain_even,
                    upper_closed: grain_even,
                    residual: grain_residual.clone(),
                    exact: false,
                },
            ],
        );
        assert!(
            aligned_exact,
            "the aligned port must carry the codeword exactly"
        );
        if at < 4 {
            let _ = writeln!(
                receipt,
                "    entry {at}: entered {} \n      \
                 port bf16   -> {:#06x} = {}   residual {}   cell {} {}\n      \
                 port aligned-> integer {} at 2^{}   = {}   exact (zero remainder) {}\n      \
                 port grain  -> word {} at 2^-{GRAIN} = {}   residual {}   cell {}{}, {}{}\n      \
                 COMPOSED preimage (the intersection of the three cells) {}   total deleted {}\n      \
                 what entered lies inside its own composed preimage: {}",
                rat_text(&entered),
                emitted,
                rat_text(&bf16_fibre.value),
                rat_text(&bf16_residual),
                bf16_fibre.cell.name(),
                bf16_fibre.interval_text(),
                aligned.entries[at],
                aligned.exponent,
                rat_text(&aligned_value),
                aligned_exact,
                grain_word,
                rat_text(&Rat::new(
                    grain_word.clone(),
                    BigInt::one() << (GRAIN as usize)
                )),
                rat_text(&grain_residual),
                if grain_even { '[' } else { '(' },
                rat_text(&grain_lower),
                rat_text(&grain_upper),
                if grain_even { ']' } else { ')' },
                composed.interval_text(),
                rat_text(&composed.total_residual),
                composed.entered_inside
            );
        }
        grain_classes
            .entry(grain_word.to_string())
            .or_default()
            .push((emitted, bf16_fibre));
    }
    // Distinct codewords per grain word: one entry producing the same codeword twice is one
    // codeword, not two, and counting occurrences here would count the material rather than the
    // collapse.
    let mut grain_distinct: BTreeMap<String, BTreeMap<u16, RoundingFibre>> = BTreeMap::new();
    for (word, held) in &grain_classes {
        let slot = grain_distinct.entry(word.clone()).or_default();
        for (codeword, fibre) in held {
            slot.entry(*codeword).or_insert_with(|| fibre.clone());
        }
    }
    let collapsing: Vec<_> = grain_distinct
        .iter()
        .filter(|(_, held)| held.len() > 1)
        .collect();
    let _ = writeln!(
        receipt,
        "\n    Note what the intersection did and did not say: at this material's magnitude the bf16 cell\n    \
         is finer than the grain cell, so the composed preimage IS the bf16 cell every time and the\n    \
         grain port contributes nothing to it. The grain port's contribution appears in the other\n    \
         direction — as a COLLAPSE, several bf16 codewords placing at one grain word — and the preimage\n    \
         of a grain word through the pathway is the union of the cells that place there:\n    \
         ({} grain words met by the {PATH_WINDOW}-entry window, {} of them holding more than one codeword)",
        grain_distinct.len(),
        collapsing.len()
    );
    for (word, held) in collapsing.iter().take(3) {
        let mut names = Vec::new();
        let first = held.values().next().expect("nonempty");
        let mut lower = first.lower.clone();
        let mut upper = first.upper.clone();
        for (codeword, fibre) in held.iter() {
            names.push(format!("{codeword:#06x}"));
            if fibre.lower < lower {
                lower = fibre.lower.clone();
            }
            if fibre.upper > upper {
                upper = fibre.upper.clone();
            }
        }
        let _ = writeln!(
            receipt,
            "      grain word {word}: {} distinct codewords {} collapse here; their cells span {} .. {}\n        \
             (the SPAN, i.e. the convex hull; the union itself may have gaps where a codeword between\n        \
             them places at a different grain word)",
            held.len(),
            names.join(", "),
            rat_text(&lower),
            rat_text(&upper)
        );
    }
    if collapsing.is_empty() {
        let _ = writeln!(
            receipt,
            "      no collapse in the exhibited window at grain 2^-{GRAIN}; the receiver compression\n      \
             below takes the reading over a larger declared population."
        );
    }

    // --- the collapsed-pair reading at the grain port ---
    let mut distinct: Vec<u16> = Vec::new();
    let mut seen: BTreeSet<u16> = BTreeSet::new();
    for word in q_words.iter().take(200_000) {
        if seen.insert(*word) {
            distinct.push(*word);
            if distinct.len() >= COMPRESSION_ITEMS {
                break;
            }
        }
    }
    let system = GrainReceiver {
        words: distinct.clone(),
        grain: GRAIN,
        depth: COMPRESSION_DEPTH,
    };
    let compression = compress(&system);
    let _ = writeln!(
        receipt,
        "\n    THE COLLAPSED POPULATION AT THE GRAIN PORT — receiver_exact_compression, where a\n    \
         successor conduct exists and the words can be longer than one.\n    \
         APERTURE: the first {} distinct codewords of the map; the receiver is the grain placement\n    \
         (computed from the material, never declared per item); the one input is DOUBLE, which is\n    \
         exact on this chart. \n      \
         one-shot blocks {} · conduct blocks {} · refinement rounds {} · collapsed pairs {} · memory order {:?}",
        distinct.len(),
        compression.one_shot.len(),
        compression.conduct.len(),
        compression.rounds,
        compression.collapsed.len(),
        compression.memory_order()
    );
    for pair in compression.collapsed.iter().take(4) {
        let left = distinct[pair.left.0 as usize];
        let right = distinct[pair.right.0 as usize];
        let _ = writeln!(
            receipt,
            "      {left:#06x} ({}) and {right:#06x} ({}) are one grain word; separated only after {} doubling(s){}",
            rat_text(&value_of(left)),
            rat_text(&value_of(right)),
            pair.distinguishing_word.len(),
            if pair.separated_by_terminus {
                " (by a terminus)"
            } else {
                ""
            }
        );
    }
    let _ = writeln!(receipt);

    // ==========================================================================================
    // FAMILY 3 — the recombination
    // ==========================================================================================
    let _ = writeln!(
        receipt,
        "== 3. FAMILY THREE — THE RECOMBINATION, A BOUNDED DEMONSTRATION OF THE LAW ==\n"
    );
    let _ = writeln!(
        receipt,
        "  HONESTY BAR, stated before the result: what follows is a bounded demonstration that two\n  \
         lifted families COMPOSE into a return absent from the declared source closure, removed by\n  \
         targeted ablation of either cause. It is NOT a claim that Phoenix produced a new capability,\n  \
         and no capability of the reborn model is graded by it. It runs CPU-exact over the rationals;\n  \
         no kernel and no card are involved.\n"
    );

    // The declared source closure, read from the committed Station B/C deposit.
    let closure_text = std::fs::read_to_string(SOURCE_CLOSURE_ARTIFACT).unwrap_or_default();
    let mut closure_words: Vec<String> = Vec::new();
    for line in closure_text.lines() {
        let trimmed = line.trim_start();
        if let Some(at) = trimmed.find(" [") {
            if trimmed[at..].starts_with(" [") && trimmed.contains("] symbols [") {
                closure_words.push(trimmed[..at].to_owned());
            }
        }
    }
    closure_words.sort();
    closure_words.dedup();
    let forbidden = [
        "preimage",
        "fibre",
        "fiber",
        "reconstruct",
        "inverse",
        "kernel",
        "interval",
    ];
    let closure_hits: Vec<&str> = forbidden
        .iter()
        .copied()
        .filter(|term| {
            closure_words
                .iter()
                .any(|word| word.to_lowercase().contains(term))
        })
        .collect();
    let _ = writeln!(
        receipt,
        "  THE DECLARED SOURCE CLOSURE — the source's own operation words, read from the committed\n  \
         Station B/C deposit {SOURCE_CLOSURE_ARTIFACT}:\n    {} operations: {}\n  \
         Every one is a forward transport or quotient. None of {forbidden:?} occurs in any of them: {}.\n  \
         The source descends; it returns no preimage of anything.\n",
        closure_words.len(),
        closure_words.join(" · "),
        if closure_hits.is_empty() {
            "measured, zero hits"
        } else {
            "HITS FOUND"
        }
    );

    // The recombined native return: the exact reconstruction fibre of one grouped family coordinate.
    //
    // Every reading below — the baseline and both ablations — goes through ONE function that also
    // recomputes the unrelated control from its own charts. The control's digest is therefore a
    // genuine recomputation under each setting and not the same matrix printed three times: a
    // control that did depend on either lift would move, and that is what makes it a control.
    let recombination_column = 0usize;
    let mut summand_words: Vec<u16> = Vec::with_capacity(SHARED);
    for head in 0..SHARED {
        let source_head = FAMILY * SHARED + head;
        let block = material.window_words(
            &named("self_attn.q_proj.weight"),
            source_head * HEAD_WIDTH,
            1,
            HIDDEN_WINDOW,
        )?;
        summand_words.push(block[0][recombination_column]);
    }

    let control_t_rows =
        material.window(&named("mlp.up_proj.weight"), 0, HEAD_WINDOW, HIDDEN_WINDOW)?;
    let control_s_rows = material.window(
        &named("mlp.gate_proj.weight"),
        0,
        HEAD_WINDOW,
        HIDDEN_WINDOW,
    )?;
    let control_t = ExactRatMatrix::new(control_t_rows).map_err(|e| e.to_string())?;
    let control_s = ExactRatMatrix::new(control_s_rows).map_err(|e| e.to_string())?;
    let control_identity_in = ExactRatMatrix::identity(HIDDEN_WINDOW).map_err(|e| e.to_string())?;
    let control_identity_out = ExactRatMatrix::identity(HEAD_WINDOW).map_err(|e| e.to_string())?;

    // The single-head selection that ABLATE A puts in the grouped-sharing quotient's place.
    let mut selection_rows = vec![vec![Rat::zero(); SHARED * HEAD_WINDOW]; HEAD_WINDOW];
    for (coordinate, row) in selection_rows.iter_mut().enumerate() {
        row[coordinate] = Rat::one();
    }
    let phi_y_ablated = ExactRatMatrix::new(selection_rows).map_err(|e| e.to_string())?;

    let recombine = |quotient: &ExactRatMatrix,
                     reading: FibreReading,
                     words: &[u16]|
     -> Result<Recombination, String> {
        // FAMILY ONE's contribution: which summands the quotient actually sums at this coordinate,
        // read off the quotient's own row rather than declared here.
        let summed: Vec<usize> = (0..words.len())
            .filter(|head| {
                !quotient
                    .get(0, head * HEAD_WINDOW)
                    .expect("inside")
                    .is_zero()
            })
            .collect();
        // FAMILY TWO's contribution: each summand's cell, under the declared reading.
        let (value, lower, upper, lower_closed, upper_closed) = match reading {
            FibreReading::ExactPreimage => {
                let fibres: Vec<RoundingFibre> = summed
                    .iter()
                    .map(|head| {
                        RoundingFibre::of_bfloat16(words[*head]).expect("a finite codeword")
                    })
                    .collect();
                let summed_fibre = SummedFibre::of(fibres);
                (
                    summed_fibre.value.clone(),
                    summed_fibre.lower.clone(),
                    summed_fibre.upper.clone(),
                    summed_fibre.lower_closed,
                    summed_fibre.upper_closed,
                )
            }
            // The exact-bit-pattern reading declares that nothing was deleted at this port, so each
            // cell is a point and the sum carries no interval at all.
            FibreReading::ExactBitPattern => {
                let mut value = Rat::zero();
                for head in &summed {
                    value = value + value_of(words[*head]);
                }
                (value.clone(), value.clone(), value, true, true)
            }
        };
        let kernel = quotient.kernel_basis().map_err(|e| e.to_string())?;
        // The unrelated control, RECOMPUTED here from its own charts under this setting.
        let control = cross_chart_defect(
            "unrelated control: the gated passage's two projections, identity charts on both sides",
            &control_identity_out,
            &control_t,
            &control_s,
            &control_identity_in,
            &hidden_names,
        )
        .map_err(|e| e.to_string())?;
        Ok(Recombination {
            summed: summed.len(),
            value,
            width: &upper - &lower,
            interval: format!(
                "{}{}, {}{}",
                if lower_closed { '[' } else { '(' },
                rat_text(&lower),
                rat_text(&upper),
                if upper_closed { ']' } else { ')' }
            ),
            kernel_dimension: kernel.len(),
            kernel,
            control_digest: digest_of(&matrix_text(&control.chi)),
            control_rank: control.rank(),
            control,
        })
    };

    let baseline = recombine(&phi_y, FibreReading::ExactPreimage, &summand_words)?;
    let ablate_a = recombine(&phi_y_ablated, FibreReading::ExactPreimage, &summand_words)?;
    let ablate_b = recombine(&phi_y, FibreReading::ExactBitPattern, &summand_words)?;

    let name_direction = |direction: &[Rat]| -> String {
        direction
            .iter()
            .enumerate()
            .filter(|(_, entry)| !entry.is_zero())
            .map(|(at, entry)| {
                format!(
                    "{}*head[{}].coord[{}]",
                    rat_text(entry),
                    at / HEAD_WINDOW,
                    at % HEAD_WINDOW
                )
            })
            .collect::<Vec<_>>()
            .join(" + ")
    };

    let _ = writeln!(
        receipt,
        "  THE RECOMBINED RETURN — the exact reconstruction fibre of family coordinate 0 at hidden\n  \
         column {recombination_column}, composing the grouped-sharing quotient (family one) with the\n  \
         exact rounding fibre (family two):\n    \
         the four sharing heads store {}\n    \
         the quotient sums {} of them at this coordinate, read off its own row\n    \
         their exact values sum to {}\n    \
         the Minkowski sum of their cells is {}   width {}\n    \
         endpoint membership CONJOINS: a sum reaches its extreme only when every summand does\n    \
         beside it, the {}-dimensional space of receiver-head vectors carried to the SAME family\n    \
         coordinate — ker Phi_Y, exhibited; first direction {}\n  \
         So the return is an exact rational interval TIMES an exhibited affine kernel: which reals\n  \
         could have produced this family coordinate, and which receiver-head vectors are\n  \
         indistinguishable to the family chart. Neither factor is in the source closure above.\n",
        summand_words
            .iter()
            .map(|w| format!("{w:#06x}"))
            .collect::<Vec<_>>()
            .join(", "),
        baseline.summed,
        rat_text(&baseline.value),
        baseline.interval,
        rat_text(&baseline.width),
        baseline.kernel_dimension,
        baseline
            .kernel
            .first()
            .map(|d| name_direction(d))
            .unwrap_or_default()
    );

    report_defect(
        &mut receipt,
        &mut chi_rows,
        &baseline.control,
        "control",
        &format!("the hidden chart, {HIDDEN_WINDOW} of {HIDDEN} columns"),
    );

    // The proper plural diff of the two identified subspaces: their intersection, computed by
    // stacking the two quotients and taking the kernel of the stack.
    let mut stacked_rows = phi_y.to_rows();
    stacked_rows.extend(phi_y_ablated.to_rows());
    let stacked = ExactRatMatrix::new(stacked_rows).map_err(|e| e.to_string())?;
    let shared_kernel = stacked.kernel_basis().map_err(|e| e.to_string())?.len();
    let mut departed_directions = 0usize;
    let mut departed_sample = String::new();
    for direction in &baseline.kernel {
        let image = phi_y_ablated.apply(direction).map_err(|e| e.to_string())?;
        if image.iter().any(|entry| !entry.is_zero()) {
            departed_directions += 1;
            if departed_sample.is_empty() {
                departed_sample = name_direction(direction);
            }
        }
    }

    let _ = writeln!(
        receipt,
        "  THE ABLATION TABLE — each cause removed on its own, plural-diffed\n\n    \
         {:<44} {:<34} {:<12} {:<12} {}\n    \
         {:<44} {:<34} {:<12} {:<12} {}\n    \
         {:<44} {:<34} {:<12} {:<12} {}\n    \
         {:<44} {:<34} {:<12} {:<12} {}\n",
        "reading",
        "interval of admissible sums",
        "width",
        "summands",
        "receiver-head directions identified",
        "BASELINE (both lifts standing)",
        baseline.interval,
        rat_text(&baseline.width),
        baseline.summed,
        format!("{} exhibited", baseline.kernel_dimension),
        "ABLATE A: grouped-sharing lift withdrawn",
        ablate_a.interval,
        rat_text(&ablate_a.width),
        ablate_a.summed,
        format!("{} exhibited", ablate_a.kernel_dimension),
        "ABLATE B: exact-fibre lift withdrawn",
        ablate_b.interval,
        rat_text(&ablate_b.width),
        ablate_b.summed,
        format!("{} exhibited", ablate_b.kernel_dimension)
    );
    let _ = writeln!(
        receipt,
        "    ABLATE A removes the group sum and replaces it with a single-head selection. The summed\n    \
         population drops {} -> {}, so the interval collapses from {} to {}. The kernel DIMENSION is\n    \
         unchanged at {}, and that is precisely why a dimension is not the reading: the kernel is a\n    \
         different SUBSPACE — the two identified spaces intersect in only {} dimensions of {}, and\n    \
         {} of the {} baseline basis directions leave outright, each one a cross-head difference the\n    \
         group sum identified and the selection does not. Plural diff, first departed direction: {}\n    \
         ABLATE B replaces the exact rounding fibre with the exact-bit-pattern reading, which declares\n    \
         that nothing was deleted at this port and therefore returns a point. The interval collapses to\n    \
         width {}; the summed population and the kernel are untouched, {} and {}, identical.\n    \
         So the two causes are separable and neither substitutes for the other: A owns the plural\n    \
         identification and the fourfold width, B owns the interval's existence at all.\n\n    \
         CONTROL — the gated passage's defect, which touches neither lift and is RECOMPUTED from its\n    \
         own charts under each setting: rank {} / {} / {}, digest {} under the baseline, {} under\n    \
         ablation A, {} under ablation B. Bit-identical across all three: {}\n",
        baseline.summed,
        ablate_a.summed,
        rat_text(&baseline.width),
        rat_text(&ablate_a.width),
        ablate_a.kernel_dimension,
        shared_kernel,
        baseline.kernel_dimension,
        departed_directions,
        baseline.kernel_dimension,
        departed_sample,
        rat_text(&ablate_b.width),
        ablate_b.summed,
        ablate_b.kernel_dimension,
        baseline.control_rank,
        ablate_a.control_rank,
        ablate_b.control_rank,
        baseline.control_digest,
        ablate_a.control_digest,
        ablate_b.control_digest,
        baseline.control_digest == ablate_a.control_digest
            && baseline.control_digest == ablate_b.control_digest
    );

    // ==========================================================================================
    // the retained H-era evidence, named for what it is
    // ==========================================================================================
    let _ = writeln!(
        receipt,
        "== 4. THE RETAINED PORT-DEFECT CENSUS — A RECEIVER MISMATCH FACE, NOT THIS STATION'S CHI ==\n\n  \
         The hardware station's per-port inside/outside/gap census stands as evidence and is retained.\n  \
         It compares the source runtime's own emitted values at six ports against the resident interval\n  \
         realization of the same ports, and reports how many coordinates of one sit inside the other.\n  \
         That is a RECEIVER MISMATCH FACE: two realizations of the same declared law read by one\n  \
         receiver, with the disagreement counted. It is not chi_gamma = Phi_Y T_gamma - S_gamma Phi_X,\n  \
         which is an operator between two DECLARED charts with a rank, a kernel, an image and a chain\n  \
         law — none of which an inside/outside count has or could have. The two are kept apart by name\n  \
         here, and the census's own figures are unchanged and uncontested by this deed.\n"
    );

    // ==========================================================================================
    // artifacts
    // ==========================================================================================
    let mut chi_tsv = String::from(
        "family\tchi_rows\tchi_columns\trank\tkernel_dim\timage_dim\tcokernel_dim\tis_zero\tdefect_direction\tfirst_defect_entry\tchi_digest\n",
    );
    for row in &chi_rows {
        chi_tsv.push_str(row);
        chi_tsv.push('\n');
    }
    std::fs::write(format!("{OUT_DIR}/chi-faces.tsv"), &chi_tsv).map_err(|e| e.to_string())?;

    let mut census_tsv = String::from(
        "bits\tcell\tvalue\tlower\tupper\tlower_closed\tupper_closed\tlower_half_width\tupper_half_width\tasymmetric\tsignificand_even\tcensus_hits\tties_held\tworst_residual\n",
    );
    for (word, row) in &census.rows {
        let fibre = RoundingFibre::of_bfloat16(*word).map_err(|e| e.to_string())?;
        let _ = writeln!(
            census_tsv,
            "{:#06x}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            word,
            fibre.cell.name(),
            rat_text(&fibre.value),
            rat_text(&fibre.lower),
            rat_text(&fibre.upper),
            fibre.lower_closed,
            fibre.upper_closed,
            rat_text(&fibre.lower_half_width),
            rat_text(&fibre.upper_half_width),
            fibre.asymmetric(),
            fibre.significand_even,
            row.hits,
            row.ties_held,
            rat_text(&row.worst_residual)
        );
    }
    std::fs::write(format!("{OUT_DIR}/bf16-fibre-census.tsv"), &census_tsv)
        .map_err(|e| e.to_string())?;

    let _ = writeln!(
        receipt,
        "== 5. ARTIFACTS ==\n  {OUT_DIR}/receipt.form\n  {OUT_DIR}/chi-faces.tsv  ({} defect rows)\n  \
         {OUT_DIR}/bf16-fibre-census.tsv  ({} codeword rows, one per codeword the material produced)\n\n\
         total wall {:.1} s",
        chi_rows.len(),
        census.rows.len(),
        started.elapsed().as_secs_f64()
    );

    std::fs::write(format!("{OUT_DIR}/receipt.form"), &receipt).map_err(|e| e.to_string())?;
    println!("{receipt}");
    Ok(())
}

fn report_defect(
    receipt: &mut String,
    rows: &mut Vec<String>,
    defect: &CrossChartDefect,
    tag: &str,
    domain_chart: &str,
) {
    let sample_name = defect
        .sample
        .as_ref()
        .map(|sample| sample.direction_name.clone())
        .unwrap_or_else(|| "none (chi is zero)".to_owned());
    let first_entry = defect
        .sample
        .as_ref()
        .and_then(|sample| sample.defect.iter().find(|entry| !entry.is_zero()))
        .map(rat_text)
        .unwrap_or_else(|| "0".to_owned());
    let full_row_rank = defect.rank() == defect.codomain.min(defect.domain);
    let _ = writeln!(
        receipt,
        "  chi[{tag}] — {}\n    \
         domain: {domain_chart}\n    \
         shape {} x {} · rank {} · kernel (directions the lift AGREES on) {} · image {} · open exterior {}\n    \
         is exactly zero: {}\n    \
         FULL RANK: {}. {}",
        defect.name,
        defect.codomain,
        defect.domain,
        defect.rank(),
        defect.agreeing_dimension(),
        defect.factorization.image.len(),
        defect.open_exterior_dimension(),
        defect.is_zero,
        full_row_rank,
        if full_row_rank {
            "The defect reaches every direction of the codomain, so the agreement dimension above is \
             exactly what the SHAPE forces and carries no information beyond the rank. Stated so it is \
             not read as a discovered structure: the deposited hardware-station measurement already \
             found all 168 inspected circuits of this map full rank, and the plan does not search for \
             a presumed low-rank truncation."
        } else {
            "The defect is rank-deficient: the agreement space is LARGER than the shape forces, and \
             the kernel below is a measured structure rather than a shape consequence."
        }
    );
    if let Some(sample) = &defect.sample {
        let _ = writeln!(
            receipt,
            "    DEFECT BASIS SAMPLE on {} — both sides exhibited:\n      \
             Phi_Y T v  first three coordinates: {}\n      \
             S Phi_X v  first three coordinates: {}\n      \
             chi v      first three coordinates: {}",
            sample.direction_name,
            vector_text(&sample.lifted[..3.min(sample.lifted.len())]),
            vector_text(&sample.native[..3.min(sample.native.len())]),
            vector_text(&sample.defect[..3.min(sample.defect.len())])
        );
        if let Some(direction) = defect.factorization.kernel.first() {
            // The exact kernel coordinates are enormous rationals — the elimination's own growth,
            // which is what exactness costs. Their SIZE is the honest face to print beside the free
            // coordinate; the full vectors live in the matrix the digest covers.
            let free = direction
                .iter()
                .position(|entry| *entry == Rat::one())
                .unwrap_or(0);
            let widest = direction
                .iter()
                .map(|entry| entry.numer().bits().max(entry.denom().bits()))
                .max()
                .unwrap_or(0);
            let _ = writeln!(
                receipt,
                "    a direction the lift AGREES on (in ker chi): free coordinate {free} carries 1; the \
                 widest exact coordinate of this basis vector is {widest} bits (the elimination's own \
                 growth — what exactness costs, printed as a size rather than as ten lines of digits)",
            );
        }
    }
    let _ = writeln!(receipt);
    rows.push(format!(
        "{tag}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
        defect.codomain,
        defect.domain,
        defect.rank(),
        defect.agreeing_dimension(),
        defect.factorization.image.len(),
        defect.open_exterior_dimension(),
        defect.is_zero,
        sample_name,
        first_entry,
        digest_of(&matrix_text(&defect.chi))
    ));
}
