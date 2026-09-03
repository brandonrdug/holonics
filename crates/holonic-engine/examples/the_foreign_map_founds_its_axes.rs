//! The foreign map founds its axes.
//!
//! Record:
//! `research/records/2026-08-13_THE_DEPOSITED_MAP_IS_READ_BY_RATIO_AND_WINDING_THE_ARCHETYPE_IS_A_FINITE_TYPE_WITH_INFINITE_MODULI.md`
//!
//! A pretrained transformer's weight file is MATERIAL, not a port: it answers nothing, so it
//! enters where the declared corpus enters, as bits. This driver carries one head's transport out
//! of a real BF16 weight file, through the declared float mouth, into the body's own exact
//! spectrum owner, and returns the FOUNDED AXES by name.
//!
//! **Nothing here is new.** Every organ it composes already stood:
//!   `exact_value::ieee754::decode_bfloat16_bits` -- the declared boundary; its own header says
//!       "it is the format the material arrives in: a transformer weight file is BF16"
//!   `exact_linear::ExactRatMatrix`               -- the shared dense exact carrier
//!   `lattice_gauge::exact_spectrum`              -- charpoly by Faddeev-LeVerrier, then the
//!       COMPLETE rational-root census, with whatever remains returned as a NAMED unresolved
//!       factor rather than approximated
//!
//! **Why the transport is read receiver-relative rather than whole.** The archetype is a quotient
//! under a declared receiver family, so the object is the transport AS THAT FAMILY SEES IT:
//!
//!     Phi = E_S (W_O W_V diag(g)) E_S^T
//!
//! with `g = input_layernorm.weight`, the gain RMSNorm applies before `v_proj` sees anything -- so
//! this is the operator the model actually applies, not `W_O W_V`, which it never does. Phi is
//! |S| x |S| and exactly gauge-invariant: under the tie's `O(2560)`, `E -> E M^T` and
//! `W -> M W M^T` cancel.
//!
//! **The founding.** An irreducible factor of the characteristic polynomial of degree > 1 founds
//! an algebraic extension -- a new axis, in the sense `RIEMANN_HYPOTHESIS` gives primes founding
//! `sqrt(2), sqrt(3), sqrt(5)`. `exact_spectrum` returns exactly that split: the rational
//! eigenvalues are the directions already placed in the base field, and `unresolved` is the
//! founding, carried by name. Nothing is evaluated and no root is approximated.
//!
//! Bounds: this is the direct path at zero position. RoPE, the attention pattern, the per-layer
//! embedding injection and every prior layer's write are absent by construction.

use std::collections::BTreeMap;
use std::fs::File;
use std::io::{Read, Seek, SeekFrom};

use holonic_engine::cuda_refine::CudaRefineExecutor;
use holonic_engine::exact_linear::ExactRatMatrix;
use holonic_engine::exact_value::ieee754::decode_bfloat16_bits;
use holonic_engine::lattice_gauge::exact_spectrum;
use holonic_engine::receiver_exact_compression::{
    InputId, ItemId, Observation, ObservedSystem, ReceiverId, compress_on_device,
};
use holonic_engine::regime_reading::{Regime, RegimeReading};
use num_bigint::BigInt;
use num_bigint::BigUint;
use num_traits::{One, Signed, Zero};
use relational_geometry::exact::Rat;

const MODEL: &str = "/home/b/models/gemma-4-E4B-it/model.safetensors";

/// **The carrier is chosen by measuring the material, not by assuming.** Measured on this file:
/// no denormal, no inf/nan, exponent field spread <= 33. So a whole tensor aligned to one
/// exponent is 41-bit integers; a product is 82; a 2560-term sum reaches 94. `i128` holds that
/// with 33 bits of headroom, so the hot contraction needs no arbitrary precision at all --
/// exactness is a property of the representation, not of the container. Arbitrary precision is
/// used only for the final 8x8x256 contraction, where the volume is negligible.
///
/// Every accumulation is `checked_*`; an overflow is a typed refusal, never a wrap.
struct Aligned {
    ints: Vec<i64>,
    exponent: i32,
}

/// The declared mouth. Every BF16 word crosses `exact_value::ieee754` and nowhere else.
fn align_words(words: &[u16]) -> Result<Aligned, String> {
    let mut mant = Vec::with_capacity(words.len());
    let mut low = i32::MAX;
    for w in words {
        let datum = decode_bfloat16_bits(*w).map_err(|e| format!("float mouth refused: {e}"))?;
        let significand = u64::try_from(&datum.significand)
            .map_err(|_| "bf16 significand exceeded u64".to_owned())?;
        let signed = if datum.negative {
            -(significand as i64)
        } else {
            significand as i64
        };
        if significand != 0 {
            low = low.min(datum.ulp_exponent);
        }
        mant.push((signed, datum.ulp_exponent));
    }
    if low == i32::MAX {
        low = 0;
    }
    let mut ints = Vec::with_capacity(mant.len());
    for (m, e) in mant {
        if m == 0 {
            ints.push(0);
            continue;
        }
        let shift = (e - low) as u32;
        if shift >= 63 {
            return Err(format!(
                "exponent spread {shift} exceeds the measured carrier"
            ));
        }
        ints.push(m.checked_shl(shift).ok_or("alignment overflowed i64")?);
    }
    Ok(Aligned {
        ints,
        exponent: low,
    })
}

/// An exact dot product in machine integers. This is the whole hot path.
fn dot_i128(a: &Aligned, b: &Aligned) -> Result<(i128, i32), String> {
    let mut acc: i128 = 0;
    for (x, y) in a.ints.iter().zip(b.ints.iter()) {
        if *x != 0 && *y != 0 {
            let p = (*x as i128)
                .checked_mul(*y as i128)
                .ok_or("product overflowed i128")?;
            acc = acc.checked_add(p).ok_or("accumulation overflowed i128")?;
        }
    }
    Ok((acc, a.exponent + b.exponent))
}

fn to_rat(numerator: BigInt, exponent: i32) -> Rat {
    if exponent >= 0 {
        Rat::new(numerator << (exponent as usize), BigInt::one())
    } else {
        Rat::new(numerator, BigInt::one() << ((-exponent) as usize))
    }
}

/// One tensor's declared header row. **`dtype` is retained and checked**, which it was not until
/// 2026-08-13: this reader read `shape` and `data_offsets`, never consulted `dtype`, and assumed a
/// two-octet element unconditionally — so handed an `F32` file it would have returned a plausible
/// population of garbage rather than refusing. That is the shape of defect this project convicts,
/// and it was the weakest of the three safetensors readers in the tree.
struct Entry {
    dtype: String,
    shape: Vec<usize>,
    start: u64,
    end: u64,
}

struct Header {
    map: BTreeMap<String, Entry>,
    base: u64,
}

/// The only element width this reader admits. Named so the refusal can say what it wanted.
const ADMITTED_DTYPE: &str = "BF16";
const ADMITTED_OCTETS: u64 = 2;

fn read_header(path: &str) -> Result<(File, Header), String> {
    let mut f = File::open(path).map_err(|e| format!("open {path}: {e}"))?;
    let mut len = [0u8; 8];
    f.read_exact(&mut len).map_err(|e| e.to_string())?;
    let n = u64::from_le_bytes(len);
    // `n as usize` truncated silently on a 32-bit cpu. Refuse instead.
    let declared = usize::try_from(n)
        .map_err(|_| format!("{path}: declared header length {n} exceeds this cpu's extent"))?;
    let mut raw = vec![0u8; declared];
    f.read_exact(&mut raw).map_err(|e| e.to_string())?;
    let text = String::from_utf8(raw).map_err(|e| e.to_string())?;
    let mut map = BTreeMap::new();
    let mut i = 0usize;
    while let Some(q) = text[i..].find('"') {
        let start = i + q + 1;
        let Some(e) = text[start..].find('"') else {
            break;
        };
        let name = text[start..start + e].to_owned();
        let rest = start + e + 1;
        if !text[rest..].starts_with(':') || !name.contains('.') {
            i = rest;
            continue;
        }
        let seg_end = text[rest..]
            .find('}')
            .map(|z| rest + z)
            .unwrap_or(text.len());
        let seg = &text[rest..seg_end];
        let pull = |key: &str, width: usize| -> Vec<u64> {
            seg.find(key)
                .map(|p| {
                    let s = rest + p + width;
                    let t = text[s..].find(']').map(|z| s + z).unwrap_or(s);
                    text[s..t]
                        .split(',')
                        .filter_map(|x| x.trim().parse::<u64>().ok())
                        .collect()
                })
                .unwrap_or_default()
        };
        // The declared element width, read rather than assumed.
        let dtype = seg
            .find("\"dtype\":\"")
            .map(|p| {
                let s = rest + p + 9;
                let t = text[s..].find('"').map(|z| s + z).unwrap_or(s);
                text[s..t].to_owned()
            })
            .unwrap_or_default();
        let shape: Vec<usize> = pull("\"shape\":[", 9)
            .into_iter()
            .map(|x| x as usize)
            .collect();
        let offs = pull("\"data_offsets\":[", 16);
        if !shape.is_empty() && offs.len() == 2 {
            map.insert(
                name,
                Entry {
                    dtype,
                    shape,
                    start: offs[0],
                    end: offs[1],
                },
            );
        }
        i = seg_end.max(rest + 1);
    }
    Ok((f, Header { map, base: 8 + n }))
}

/// A whole tensor block, read ONCE. Reading a column of a row-major tensor element by element is
/// one syscall per two octets; that is not a cost law, it is a mistake, and it was made twice.
fn block(f: &mut File, h: &Header, name: &str) -> Result<(Vec<u16>, Vec<usize>), String> {
    let entry = h.map.get(name).ok_or_else(|| format!("no tensor {name}"))?;

    // **The declared width is checked by name.** A file that carries anything but the admitted
    // dtype is refused rather than reinterpreted two octets at a time.
    if entry.dtype != ADMITTED_DTYPE {
        return Err(format!(
            "{name}: declared dtype {:?}, and this reader admits only {ADMITTED_DTYPE}. It is \
             refused rather than read at the admitted width, because reinterpreting a wider datum \
             as two octets returns a plausible population that is not the material.",
            entry.dtype
        ));
    }

    // **And the declared shape must account for every octet of the declared span.** Either alone
    // could be right while the pair disagrees, and the disagreement is the whole evidence that the
    // block was located correctly.
    let span = entry
        .end
        .checked_sub(entry.start)
        .ok_or_else(|| format!("{name}: data_offsets are not ascending"))?;
    let members: u64 = entry
        .shape
        .iter()
        .try_fold(1u64, |carried, extent| carried.checked_mul(*extent as u64))
        .ok_or_else(|| format!("{name}: declared shape overflows"))?;
    let owed = members
        .checked_mul(ADMITTED_OCTETS)
        .ok_or_else(|| format!("{name}: declared extent overflows"))?;
    if owed != span {
        return Err(format!(
            "{name}: shape {:?} owes {owed} octets at {ADMITTED_OCTETS} per member, and the \
             declared span carries {span}",
            entry.shape
        ));
    }

    f.seek(SeekFrom::Start(h.base + entry.start))
        .map_err(|e| e.to_string())?;
    let mut raw =
        vec![0u8; usize::try_from(span).map_err(|_| format!("{name}: span exceeds cpu"))?];
    f.read_exact(&mut raw).map_err(|e| e.to_string())?;
    Ok((
        raw.chunks_exact(2)
            .map(|c| u16::from_le_bytes([c[0], c[1]]))
            .collect(),
        entry.shape.clone(),
    ))
}

fn embed_row(f: &mut File, h: &Header, id: usize, bus: usize) -> Result<Vec<u16>, String> {
    const TABLE: &str = "model.language_model.embed_tokens.weight";
    let entry = h
        .map
        .get(TABLE)
        .ok_or_else(|| format!("no tensor {TABLE}"))?;
    // A row is seeked into rather than read whole, so the dtype check `block` performs cannot be
    // inherited and is repeated here. Reinterpreting a wider datum at two octets would return a row
    // of the right length and the wrong material.
    if entry.dtype != ADMITTED_DTYPE {
        return Err(format!(
            "{TABLE}: declared dtype {:?}, and this reader admits only {ADMITTED_DTYPE}",
            entry.dtype
        ));
    }
    let a = entry.start;
    f.seek(SeekFrom::Start(h.base + a + (id * bus) as u64 * 2))
        .map_err(|e| e.to_string())?;
    let mut raw = vec![0u8; bus * 2];
    f.read_exact(&mut raw).map_err(|e| e.to_string())?;
    Ok(raw
        .chunks_exact(2)
        .map(|c| u16::from_le_bytes([c[0], c[1]]))
        .collect())
}

// -------------------------------------------------------------------------------------------------
// The material-scale deed, and it is the card's
// -------------------------------------------------------------------------------------------------

/// One transport read off the map, with faces taken from the **material** and never from the layout.
///
/// `CLAUDE.md` §8's returned-partition rule governs the choice: if two transports landed in one class
/// because this driver handed both the same declared value, the class would restate the declaration
/// table and carry no evidence. So no face below reads a layer index, a head index, a tensor name or
/// a position. Every one is read off the weights.
struct Transport {
    layer: usize,
    /// **A row block of `v_proj`, and NOT a head.** Corrected 2026-08-13 by reading the map: this
    /// map declares `num_key_value_heads = 2`, so `v_proj` is `[2 · 256, 2560]` and an eight-way
    /// row split cuts *inside* a KV head, four blocks to a head. The earlier spelling `head` was a
    /// label the material does not carry, and a collapsed pair reported as "two heads of one layer"
    /// was two row blocks sitting in different KV heads.
    block: usize,
    /// How many rows this block spans. **It is not constant across the sweep**, and that is the
    /// frame: seven of this map's layers carry double-width attention, so a block is 64 rows at 35
    /// layers and 128 at seven. Carried so the two frames are declared rather than silently mixed —
    /// and deliberately **not** a receiver face, since the row width is the layout and a face read
    /// off it would restate this driver's own aperture.
    block_rows: usize,
    /// The regime the entry population reads at — headed, or plane-filling. `regime_reading`'s
    /// verdict, taken on the walk the entries themselves make.
    regime: u64,
    /// How many entries carry a negative hand, **rebased onto a common denominator** so the count
    /// crosses the frame boundary above. A bare count over 163,840 entries and one over 327,680 are
    /// not comparable — the horizon law: magnitudes do not cross, only a `Ratio` does. Each block's
    /// population divides the sweep's common denominator exactly, so this rebase has **zero
    /// remainder**; it is `H.0106`, not a normalisation (id corrected 2026-09-03; `H.0104` is Lambda).
    negatives_rebased: u64,
    /// The octave count of the widest entry — the material's own span in doublings.
    octaves: u64,
}

/// Greatest common divisor, for the exact rebase of the negative-hand counts onto one denominator.
fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// The declared receiver family, and the conduct the residual stream supplies.
struct MapUnderObservation {
    transports: Vec<Transport>,
    /// `(layer, block) -> ordinal`, so a successor can be addressed without the ordinal being a
    /// face.
    located: BTreeMap<(usize, usize), usize>,
}

impl ObservedSystem for MapUnderObservation {
    fn items(&self) -> Vec<ItemId> {
        (0..self.transports.len() as u64).map(ItemId).collect()
    }
    /// Three faces, each read off the material.
    fn receivers(&self) -> Vec<ReceiverId> {
        vec![ReceiverId(0), ReceiverId(1), ReceiverId(2)]
    }
    /// One input: **take the same transport one step along the residual stream.** That is the
    /// causal order the map itself carries — layer `k` writes into the stream layer `k+1` reads —
    /// and it is the only structural fact this system uses, declared here rather than smuggled in
    /// as a face.
    fn inputs(&self) -> Vec<InputId> {
        vec![InputId(0)]
    }
    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let transport = &self.transports[item.0 as usize];
        Observation(match receiver.0 {
            0 => transport.regime,
            1 => transport.negatives_rebased,
            _ => transport.octaves,
        })
    }
    fn successor(&self, item: ItemId, _input: InputId) -> Option<ItemId> {
        let transport = &self.transports[item.0 as usize];
        self.located
            .get(&(transport.layer + 1, transport.block))
            .map(|at| ItemId(*at as u64))
    }
}

/// Read every head of every declared layer, take the three material faces, and **enact the quotient
/// on the card**.
///
/// This is the deed. The single-head spectrum above is one reading of one head at one layer — which
/// is the format — and it mounts nothing. Here the population is the map's own transports and the
/// operation is `receiver_exact_compression`, whose resident path `compress_on_device` enacts the
/// same law through the card's `(current class, exact key)` refinement. What returns is which
/// transports the declared family **cannot tell apart**, each collapsed pair carrying the shortest
/// input word that separates it.
fn sweep_on_the_card(
    f: &mut File,
    h: &Header,
    layers: &[usize],
    blocks: usize,
) -> Result<(), String> {
    println!("\n{}", "=".repeat(96));
    println!("THE MATERIAL-SCALE DEED — the quotient enacted on the resident card");
    println!("{}", "=".repeat(96));

    let started = std::time::Instant::now();
    // Pass one reads the material. The negative-hand counts are held with the population they were
    // taken over, because a count is frame-relative and the frames differ across this map.
    let mut raw: Vec<(Transport, u64, u64)> = Vec::new();
    let mut located = BTreeMap::new();
    let mut layers_read: Vec<usize> = Vec::new();
    let mut layers_absent: Vec<usize> = Vec::new();
    let mut widths: BTreeMap<usize, usize> = BTreeMap::new();
    for layer in layers {
        let name = format!("model.language_model.layers.{layer}.self_attn.v_proj.weight");
        let Ok((words, shape)) = block(f, h, &name) else {
            layers_absent.push(*layer);
            continue;
        };
        if shape.len() != 2 || shape[0] % blocks != 0 {
            layers_absent.push(*layer);
            continue;
        }
        let block_rows = shape[0] / blocks;
        let columns = shape[1];
        layers_read.push(*layer);
        *widths.entry(block_rows).or_default() += 1;
        for index in 0..blocks {
            let from = index * block_rows * columns;
            let to = from + block_rows * columns;
            let aligned = align_words(&words[from..to])?;
            // The walk the entries themselves make. Deviation accumulates; the span is the count.
            let mut deviation = BigInt::zero();
            let mut negatives = 0u64;
            let mut widest = 0u64;
            for value in &aligned.ints {
                deviation += BigInt::from(*value);
                if *value < 0 {
                    negatives += 1;
                }
                widest = widest.max(value.unsigned_abs().max(1).ilog2() as u64 + 1);
            }
            let population = aligned.ints.len() as u64;
            let reading = RegimeReading::read(&deviation, &BigUint::from(population));
            located.insert((*layer, index), raw.len());
            raw.push((
                Transport {
                    layer: *layer,
                    block: index,
                    block_rows,
                    regime: match reading.regime() {
                        Regime::Headed => 1,
                        Regime::PlaneFilling => 2,
                    },
                    // Filled by the rebase below; the raw count and its population travel beside it.
                    negatives_rebased: 0,
                    octaves: widest,
                },
                negatives,
                population,
            ));
        }
    }
    if raw.is_empty() {
        return Err("no transport was read: the declared layers name nothing in this map".into());
    }

    // **The rebase.** Every block's population divides the common denominator exactly, so this
    // carries the negative-hand ratio across the frame boundary with zero remainder.
    let denominator = raw.iter().fold(1u64, |held, (_, _, population)| {
        held / gcd(held, *population) * *population
    });
    let transports: Vec<Transport> = raw
        .into_iter()
        .map(|(mut transport, negatives, population)| {
            transport.negatives_rebased = negatives * (denominator / population);
            transport
        })
        .collect();

    println!(
        "  {} transports read from {} layers x {blocks} row blocks  [{:?}]",
        transports.len(),
        layers_read.len(),
        started.elapsed()
    );
    if !layers_absent.is_empty() {
        println!(
            "  the declared aperture named {} further layers that this map does not carry: {:?} \
             — reported, not dropped",
            layers_absent.len(),
            layers_absent
        );
    }
    println!(
        "  THE FRAMES: block widths {:?} (rows -> layers). A bare negative count is frame-relative, \
         so it is rebased onto the common denominator {denominator} — exact, zero remainder.",
        widths
    );

    let system = MapUnderObservation {
        transports,
        located,
    };

    // **The card.** Refused by name if no device is present, rather than falling back to the cpu
    // and reporting a cpu figure as though the deed had been mounted.
    let mut executor = CudaRefineExecutor::new()
        .map_err(|error| format!("the resident card refused the deed: {error:?}"))?;
    println!("  device: {}", executor.device_name());

    let enacted = std::time::Instant::now();
    let compression = compress_on_device(&system, &mut executor)
        .map_err(|error| format!("the card refused the quotient: {error:?}"))?;
    println!("  quotient enacted on the card  [{:?}]", enacted.elapsed());

    println!(
        "  one-shot classes {} -> conduct classes {} over {} rounds",
        compression.one_shot.len(),
        compression.conduct.len(),
        compression.rounds
    );
    println!(
        "  collapsed pairs: {} — each is a pair the declared family CANNOT tell apart",
        compression.collapsed.len()
    );
    if compression.is_exact() {
        println!(
            "  THE ONE-SHOT READING IS RECEIVER-EXACT on this material: nothing later conduct can \
             see was collapsed. That is a statement about this family, not about the map."
        );
    }
    for pair in compression.collapsed.iter().take(8) {
        let left = &system.transports[pair.left.0 as usize];
        let right = &system.transports[pair.right.0 as usize];
        println!(
            "    L{}b{} ({} rows) ~ L{}b{} ({} rows)   separated after {} step(s) along the \
             residual stream{}",
            left.layer,
            left.block,
            left.block_rows,
            right.layer,
            right.block,
            right.block_rows,
            pair.distinguishing_word.len(),
            if pair.separated_by_terminus {
                ", by a terminus"
            } else {
                ""
            }
        );
    }
    if compression.collapsed.len() > 8 {
        println!("    … {} further pairs", compression.collapsed.len() - 8);
    }
    println!(
        "\n  READ IT AS WHAT IT IS. The faces are three readings of the weights themselves — the \
         regime the entry walk sits at, the population carrying a negative hand, and the octave span \
         — and none of them is a layer index, a head index or a name. So a collapsed pair is a \
         statement about the material and not a restatement of this driver's declaration table."
    );
    Ok(())
}

fn main() -> Result<(), String> {
    let layer: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(13);
    let head: usize = std::env::args()
        .nth(2)
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let started = std::time::Instant::now();
    let (mut f, h) = read_header(MODEL)?;

    let probes: [(&str, usize); 8] = [
        ("two", 13498),
        ("_two", 1156),
        ("_Two", 12481),
        ("_deux", 65332),
        ("four", 19025),
        ("_four", 2390),
        ("_Four", 20358),
        ("_quatre", 100603),
    ];
    let bus = 2560usize;
    let d = if [5, 11, 17, 23, 29, 35, 41].contains(&layer) {
        512
    } else {
        256
    };
    let (nq, nkv) = (8usize, 2usize);
    let group = head / (nq / nkv);
    let n = probes.len();

    println!("layer {layer}, head {head}  (head_dim {d}, bus {bus})");
    println!("receiver family: {n} faces over 2 holons\n");

    let gw = block(
        &mut f,
        &h,
        &format!("model.language_model.layers.{layer}.input_layernorm.weight"),
    )?
    .0;
    let (vw, _) = block(
        &mut f,
        &h,
        &format!("model.language_model.layers.{layer}.self_attn.v_proj.weight"),
    )?;
    let (ow, oshape) = block(
        &mut f,
        &h,
        &format!("model.language_model.layers.{layer}.self_attn.o_proj.weight"),
    )?;
    let o_cols = oshape[1];
    println!(
        "blocks read once: v_proj {} words, o_proj {} words  [{:?}]",
        vw.len(),
        ow.len(),
        started.elapsed()
    );

    let g = align_words(&gw)?;
    let mut e_al = Vec::new();
    let mut eg_al = Vec::new();
    for (_, id) in probes {
        let raw = embed_row(&mut f, &h, id, bus)?;
        let e = align_words(&raw)?;
        // The gain RMSNorm applies before v_proj sees anything: this is the acting operator.
        let mut prod = Vec::with_capacity(bus);
        for i in 0..bus {
            prod.push(
                (e.ints[i] as i128)
                    .checked_mul(g.ints[i] as i128)
                    .ok_or("gain product overflowed")?,
            );
        }
        // The width is read off the material, never authored. An earlier form of this pinned a
        // 40-bit cap here and refused on a 1-bit excess -- an authored level inside the organ,
        // which is the contaminant species `THE_CONTAMINANT_PROTOCOL` names. The only real
        // question is whether the product still fits the carrier exactly.
        for p in &prod {
            i64::try_from(*p).map_err(|_| {
                format!(
                    "gain product needs {} bits, past the i64 carrier",
                    128 - p.unsigned_abs().leading_zeros()
                )
            })?;
        }
        let eg = Aligned {
            ints: prod.iter().map(|p| *p as i64).collect(),
            exponent: e.exponent + g.exponent,
        };
        e_al.push(e);
        eg_al.push(eg);
    }
    println!(
        "faces aligned                                        [{:?}]",
        started.elapsed()
    );

    let mut a: Vec<Vec<(i128, i32)>> = vec![vec![(0, 0); d]; n];
    let mut b: Vec<Vec<(i128, i32)>> = vec![vec![(0, 0); n]; d];
    for k in 0..d {
        let vrow = align_words(&vw[(group * d + k) * bus..(group * d + k + 1) * bus])?;
        let ocol_words: Vec<u16> = (0..bus).map(|i| ow[i * o_cols + head * d + k]).collect();
        let ocol = align_words(&ocol_words)?;
        for s in 0..n {
            a[s][k] = dot_i128(&e_al[s], &ocol)?;
            b[k][s] = dot_i128(&vrow, &eg_al[s])?;
        }
    }
    println!(
        "two contractions over {} x {bus} done                 [{:?}]",
        2 * n * d,
        started.elapsed()
    );

    // Only here does arbitrary precision appear: 8 x 8 x 256 terms, negligible volume.
    let mut phi = vec![vec![Rat::zero(); n]; n];
    for i in 0..n {
        for j in 0..n {
            let mut acc = BigInt::zero();
            let mut exp: Option<i32> = None;
            for k in 0..d {
                let (av, ae) = a[i][k];
                let (bv, be) = b[k][j];
                if av == 0 || bv == 0 {
                    continue;
                }
                let e = ae + be;
                let term = BigInt::from(av) * BigInt::from(bv);
                match exp {
                    None => {
                        acc = term;
                        exp = Some(e);
                    }
                    Some(cur) => {
                        let low = cur.min(e);
                        acc = (acc << ((cur - low) as usize)) + (term << ((e - low) as usize));
                        exp = Some(low);
                    }
                }
            }
            phi[i][j] = to_rat(acc, exp.unwrap_or(0));
        }
    }
    println!(
        "Phi assembled exactly                                [{:?}]\n",
        started.elapsed()
    );

    // THE REBASE, and it is the whole difference between returning and not returning.
    //
    // Every entry of Phi is a dyadic: an integer over a power of two. Handed to the spectrum as
    // independent `Rat`s, each Faddeev-LeVerrier step runs a gcd over numbers that grow, and the
    // root census then bisects to a depth read off a discriminant of enormous coefficients. An
    // earlier form of this driver assembled Phi in 23.8 ms and then did not return from an 8x8
    // spectrum, because the cancellation was thrown away entry by entry.
    //
    // Clearing one common power of two makes the carrier integral:  Phi = 2^-k M.  Then
    //     char_M(t) = 2^(nk) * char_Phi(2^-k t)
    // so every eigenvalue of Phi is one of M's divided by 2^k. Invertible, remainder ZERO -- a
    // rebase (H.0106; citation corrected 2026-09-03, H.0104 is Lambda), not a compression.
    let mut shift = 0i64;
    for r in &phi {
        for e in r {
            shift = shift.max(e.denom().bits() as i64 - 1);
        }
    }
    let scale = BigInt::one() << (shift as usize);
    let mut integral = vec![vec![Rat::zero(); n]; n];
    for i in 0..n {
        for j in 0..n {
            let lifted = &phi[i][j] * Rat::from(scale.clone());
            if !lifted.is_integer() {
                return Err(
                    "rebase did not clear the denominator; the carrier is not dyadic".into(),
                );
            }
            integral[i][j] = Rat::from(lifted.to_integer());
        }
    }
    // **THE REBASE. Removed 2026-08-13 morning and restored the same evening, and the removal was
    // the defect.**
    //
    // The note that stood here said dividing out the integer content "bought nothing", because the
    // projectivised spectrum is scale-invariant and a gcd wants an `abs()` on a carrier whose signs
    // are directions. Half of that is right: a *signed* content would invert the hand of every
    // eigenvalue. The conclusion drawn from it was wrong. A greatest common divisor is **defined**
    // on magnitudes — that is what a common divisor is — and dividing every entry by a **positive**
    // content leaves each entry's own sign exactly where it was. No hand moves.
    //
    // And what it buys is the whole cost of this driver. `c = gcd(entries)` factors out, the
    // eigenvalues of `M` are `c ×` those of `M/c`, so the projectivised spectrum is untouched — but
    // the characteristic polynomial's degree-`k` coefficient carries `c^(8-k)`, so `t^0` alone
    // carries `c^8`. Clearing `2^100` put a large common factor into all 64 entries and then handed
    // the census a constant term inflated by its eighth power. Scale is exactly the species the
    // horizon law says does not cross a frame; carrying it into the charpoly transports a magnitude
    // across a boundary it cannot cross, and the census then pays for it in Sturm sequences.
    fn common_divisor(mut left: BigInt, mut right: BigInt) -> BigInt {
        while !right.is_zero() {
            let carried = left % &right;
            left = right;
            right = carried;
        }
        left
    }
    let mut content = BigInt::zero();
    for entry in integral.iter().flatten() {
        content = common_divisor(content, entry.numer().clone().abs());
    }
    let rebased = !content.is_zero() && !content.is_one();
    if rebased {
        for row in integral.iter_mut() {
            for entry in row.iter_mut() {
                *entry = Rat::from(entry.numer() / &content);
            }
        }
    }
    let widest = integral
        .iter()
        .flatten()
        .map(|e| e.numer().bits())
        .max()
        .unwrap_or(0);
    let negatives = integral
        .iter()
        .flatten()
        .filter(|e| e.is_negative())
        .count();
    println!(
        "rebase: cleared 2^{shift}, divided out content of {} bits; widest entry {widest} bits; \
         {negatives} of {} entries carry a negative hand  [{:?}]",
        content.bits(),
        n * n,
        started.elapsed()
    );

    let operator = ExactRatMatrix::new(integral).map_err(|e| format!("carrier refused: {e:?}"))?;
    let spectrum = exact_spectrum(&operator).map_err(|e| format!("spectrum refused: {e:?}"))?;
    println!(
        "exact_spectrum returned                              [{:?}]",
        started.elapsed()
    );
    println!("eigenvalues below are those of M; Phi's are these over 2^{shift}\n");

    println!("=== THE EXACT SPECTRUM OF THE TRANSPORT, AS THE FAMILY SEES IT ===");
    println!("  extent                     {}", spectrum.extent);
    println!(
        "  characteristic degree      {:?}",
        spectrum.characteristic.degree()
    );
    println!(
        "  rational eigenvalues       {}",
        spectrum.rational_eigenvalues.len()
    );
    for (value, multiplicity) in &spectrum.rational_eigenvalues {
        println!(
            "     {} / {}  (multiplicity {multiplicity})",
            value.numer(),
            value.denom()
        );
    }
    println!(
        "  directions placed exactly  {} of {}",
        spectrum.accounted(),
        spectrum.extent
    );
    println!(
        "  completely rational?       {}",
        spectrum.is_completely_rational()
    );

    println!("\n=== THE FOUNDING -- the unresolved factor, carried by name ===");
    match spectrum.unresolved.degree() {
        None | Some(0) => println!("  none: every direction is already placed in the base field."),
        Some(deg) => {
            println!("  degree {deg}: {deg} directions are NOT in the base field.");
            println!(
                "  This factor founds an algebraic extension -- a new axis, in the sense that a"
            );
            println!("  prime founds sqrt(p). Coefficients ascending, exactly:");
            for (k, c) in spectrum.unresolved.coefficients().iter().enumerate() {
                if !c.is_zero() {
                    println!("     t^{k:<3} {} / {}", c.numer(), c.denom());
                }
            }
            if deg == 2 {
                let c = spectrum.unresolved.coefficients();
                let disc = &c[1] * &c[1] - Rat::from(BigInt::from(4)) * &c[2] * &c[0];
                println!(
                    "  discriminant {} / {} is {} -- the pair is {}",
                    disc.numer(),
                    disc.denom(),
                    if disc.is_negative() {
                        "NEGATIVE"
                    } else {
                        "positive"
                    },
                    if disc.is_negative() {
                        "a TURN (conjugate, carrying a hand)"
                    } else {
                        "two real axes"
                    }
                );
            }
        }
    }
    let layers: Vec<usize> = (0..48).collect();
    if let Err(error) = sweep_on_the_card(&mut f, &h, &layers, nq) {
        println!("\nTHE MATERIAL-SCALE DEED WAS REFUSED: {error}");
    }
    Ok(())
}
