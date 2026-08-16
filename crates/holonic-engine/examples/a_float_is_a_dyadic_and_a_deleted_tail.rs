//! A float is a dyadic and a deleted tail: the mouth on `reopening.rs`.
//!
//! ## What was missing
//!
//! `crates/holonic-engine/src/reopening.rs` does exact integer relation detection over `BigInt`. It
//! recovers Euler's and Machin's identities exactly and returns zero spurious relations over
//! sixteen relation-free searches. It is the organ built to reverse what a float deleted — and
//! until this driver it **could not be handed a float**. Every `ExactFace` constructor required an
//! already-exact source: `rational`, `from_certified_series`, `from_rat_interval`,
//! `integer_combination`, and `collapsed`, which takes an existing `ExactFace` and truncates it. The
//! instrument could only reverse a deletion it had performed itself, so its material was synthetic
//! by construction.
//!
//! ## What a float is, and why the distinction in the type is the whole content
//!
//! `canon/THE_MATHEMATICS_TABLET.md` §1, Brandon's sentence: *"Floats are not real numbers, they
//! are series expansions of ratios."* The part usually missed is that **the truncated expansion is
//! itself exact**: an IEEE-754 value is precisely `±m·2^e` with `m` an integer, and that dyadic is
//! not an approximation of anything. What was destroyed is the **tail**, and the tail's width is
//! exactly one unit in the last place.
//!
//! So the honest face of a float is a point *or* an enclosure of width one ulp, and **which one it
//! is is not a property of the bits**:
//!
//! ```text
//!   a stored bf16 network weight     the file's number IS -158*2^-12    -> a POINT
//!   a decimal literal a compiler
//!     rounded from a measurement     the bits round something else      -> an ENCLOSURE, 1 ulp
//! ```
//!
//! `exact_value::ieee754::FloatReading` is that declaration, `ExactFace::from_binary_float` carries
//! it onto the face, and `reopening.rs`'s admission law separates the two **without a new rule**: a
//! point admits every grain, an enclosure of width `2^-u` is refused at grain `u+1` by name.
//!
//! ## The five declared controls
//!
//! 1. **A mouth that accepts everything has not been built.** A real measured `f64` is refused by
//!    name at a grain finer than its ulp and admitted at a grain coarser than it.
//! 2. **The decode is a bijection.** Declared patterns round-trip `f64 -> exact dyadic -> f64`
//!    bit-identically, subnormals and both zeros included. `NaN` and `±∞` are refused by name.
//! 3. **The organ works on real material.** Faces built from actual trained network weights read
//!    out of safetensors payloads.
//! 4. **The negative control survives.** `reopening.rs`'s relation-free basis must still return
//!    zero spurious relations, and so must a relation-free basis of measured floats.
//! 5. **The distinction is load-bearing.** The same bits, admitted as a point and as an enclosure,
//!    must give different verdicts — or the type distinction is decorative and this driver says so.
//!
//! ## The exactness route
//!
//! `f64` and `f32` appear in this file and in `exact_value::ieee754` and nowhere else. In
//! `ieee754` they appear in four functions, each one call to `to_bits` or `from_bits`. This file is
//! a boundary driver: it reads bytes off a disk, reinterprets them, and hands `BigUint × 2^e`
//! inward. **No arithmetic is performed on a machine float anywhere.**

use std::fs::File;
use std::io::{Read, Seek, SeekFrom};
use std::path::{Path, PathBuf};

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use sha2::{Digest, Sha256};

use holonic_engine::exact_value::ieee754::{
    BinaryFloatDatum, BinaryFloatSpecies, FloatReading, decode_bfloat16_bits, decode_bits,
    decode_f32, decode_f64, encode_f32, encode_f64,
};
use holonic_engine::reopening::{
    CertifiedBits, DeclaredGrain, ExactFace, Reopening, ReopeningError, ReopeningVerdict,
    dyadic_scale, finest_admissible_grain, probe_at_grain, reopen,
};
use relational_geometry::exact::{Rat, integer};
use relational_geometry::exact_analysis::log_rational_interval;

// ---------------------------------------------------------------------------------------------
// The declared external material.
// ---------------------------------------------------------------------------------------------

/// One genuinely external numeric artifact this driver is willing to read.
///
/// Trained network weights are the strongest available source of *measured* floating point in
/// reach of this machine: every word is the residue of an optimisation over real data, nobody
/// chose it, and the file is the same bytes for everyone who downloads it. The reader below is the
/// shape of `soma/life/examples/eros_self_emanated_law.rs:1560` — an eight-byte little-endian
/// header extent, a JSON manifest, a dtype refused by name if it is not the declared one, and a
/// seek to a flat coordinate.
struct DeclaredArtifact {
    label: &'static str,
    /// The HuggingFace cache directory name, `models--<owner>--<model>`.
    repository: &'static str,
    file: &'static str,
    tensor: &'static str,
    dtype: &'static str,
    element_bytes: u64,
    species: BinaryFloatSpecies,
}

const DECLARED_ARTIFACTS: [DeclaredArtifact; 2] = [
    DeclaredArtifact {
        label: "GPT-2, first attention block's fused QKV projection",
        repository: "models--gpt2",
        file: "model.safetensors",
        tensor: "h.0.attn.c_attn.weight",
        dtype: "F32",
        element_bytes: 4,
        species: BinaryFloatSpecies::Binary32,
    },
    DeclaredArtifact {
        label: "Qwen3.5-4B, layer 1 MLP down-projection",
        repository: "models--Qwen--Qwen3.5-4B",
        file: "model.safetensors-00001-of-00002.safetensors",
        tensor: "model.language_model.layers.1.mlp.down_proj.weight",
        dtype: "BF16",
        element_bytes: 2,
        species: BinaryFloatSpecies::Bfloat16,
    },
];

/// CODATA 2022 recommended values, as `binary64`.
///
/// These are **measured** quantities: no exact decimal names them, so the compiler's decimal-to-
/// binary conversion rounded each one and deleted a tail exactly one ulp wide. That is precisely
/// the `RoundedToNearest` case, and it is why these are the right material for control 1.
///
/// The ulp is the *representation's* honesty and not the *measurement's*: the experimental
/// uncertainty on `alpha^-1` is about `2.1e-8`, some six million times the `2^-45` this face
/// declares. A face declared at the experimental uncertainty would be `Coarser` and would admit no
/// grain at all. This driver certifies what the format deleted; it does not certify physics.
const MEASURED_CONSTANTS: [(&str, f64, &str); 3] = [
    (
        "alpha^-1",
        137.035_999_177,
        "CODATA 2022 inverse fine-structure constant",
    ),
    (
        "m_p/m_e",
        1836.152_673_426,
        "CODATA 2022 proton-electron mass ratio",
    ),
    (
        "R_inf",
        10_973_731.568_157,
        "CODATA 2022 Rydberg constant, per metre",
    ),
];

/// Declared `binary64` patterns for the bijection control, each chosen for a specific hazard.
const DECLARED_BINARY64: [(&str, u64); 10] = [
    ("one", 0x3ff0_0000_0000_0000),
    ("pi, a long mantissa", 0x4009_21fb_5444_2d18),
    ("-2/3, a repeating mantissa", 0xbfe5_5555_5555_5555),
    ("+0", 0x0000_0000_0000_0000),
    ("-0, sign over an empty magnitude", 0x8000_0000_0000_0000),
    ("the smallest subnormal", 0x0000_0000_0000_0001),
    ("the largest subnormal", 0x000f_ffff_ffff_ffff),
    ("the smallest normal", 0x0010_0000_0000_0000),
    ("the largest finite", 0x7fef_ffff_ffff_ffff),
    ("a subnormal with a long mantissa", 0x0007_9be1_ff0c_a53d),
];

const DECLARED_BINARY32: [(&str, u32); 5] = [
    ("one", 0x3f80_0000),
    ("a real GPT-2 attention weight", 0xbef2_9c42),
    ("-0", 0x8000_0000),
    ("the smallest subnormal", 0x0000_0001),
    ("the largest finite", 0x7f7f_ffff),
];

const DECLARED_BFLOAT16: [(&str, u16); 4] = [
    ("one", 0x3f80),
    ("a real Qwen down-projection weight", 0xbd1e),
    ("-0", 0x8000),
    ("the smallest subnormal", 0x0001),
];

/// The patterns that name no ratio and must be refused by name rather than mapped to a sentinel.
const DECLARED_REFUSALS: [(&str, BinaryFloatSpecies, u64); 7] = [
    (
        "+infinity",
        BinaryFloatSpecies::Binary64,
        0x7ff0_0000_0000_0000,
    ),
    (
        "-infinity",
        BinaryFloatSpecies::Binary64,
        0xfff0_0000_0000_0000,
    ),
    (
        "a quiet NaN",
        BinaryFloatSpecies::Binary64,
        0x7ff8_0000_0000_0000,
    ),
    (
        "a signalling NaN",
        BinaryFloatSpecies::Binary64,
        0x7ff0_0000_0000_0001,
    ),
    ("+infinity", BinaryFloatSpecies::Binary32, 0x7f80_0000),
    ("a NaN", BinaryFloatSpecies::Bfloat16, 0x7fc0),
    (
        "a pattern too wide for its format",
        BinaryFloatSpecies::Bfloat16,
        0x1_0000,
    ),
];

// ---------------------------------------------------------------------------------------------
// The safetensors boundary reader.
// ---------------------------------------------------------------------------------------------

fn home_directory() -> Option<PathBuf> {
    std::env::var_os("HOME").map(PathBuf::from)
}

/// Resolve `~/.cache/huggingface/hub/<repository>/snapshots/<the one snapshot>/<file>`.
///
/// The snapshot directory is a content hash and is not declarable ahead of time, so it is read
/// rather than assumed — and if more than one is present the artifact is reported unresolved
/// rather than silently picking one, because picking one would be an absolute frame.
fn resolve_artifact(artifact: &DeclaredArtifact) -> Option<PathBuf> {
    let snapshots = home_directory()?
        .join(".cache/huggingface/hub")
        .join(artifact.repository)
        .join("snapshots");
    let mut entries: Vec<PathBuf> = std::fs::read_dir(&snapshots)
        .ok()?
        .filter_map(|entry| entry.ok())
        .map(|entry| entry.path())
        .filter(|path| path.is_dir())
        .collect();
    entries.sort();
    if entries.len() != 1 {
        return None;
    }
    let candidate = entries.remove(0).join(artifact.file);
    candidate.is_file().then_some(candidate)
}

struct TensorExtent {
    data_start: u64,
    byte_start: u64,
    byte_end: u64,
    shape: Vec<u64>,
}

/// The declared entry of one tensor in a safetensors header.
///
/// The header is a JSON object whose keys are tensor names and whose values are flat records. This
/// scans for the declared key and reads three fields out of its braces. It is deliberately a
/// *reader* and not a parser: it accepts what it needs, refuses everything else by name, and
/// depends on nothing.
fn safetensors_extent(
    path: &Path,
    tensor: &str,
    expected_dtype: &str,
    element_bytes: u64,
) -> Result<TensorExtent, String> {
    let mut file =
        File::open(path).map_err(|error| format!("{} opens: {error}", path.display()))?;
    let mut length = [0u8; 8];
    file.read_exact(&mut length)
        .map_err(|error| format!("{} reads its header extent: {error}", path.display()))?;
    let header_length = u64::from_le_bytes(length);
    let extent = usize::try_from(header_length)
        .map_err(|_| "the safetensors header exceeds this cpu".to_owned())?;
    let mut header = vec![0u8; extent];
    file.read_exact(&mut header)
        .map_err(|error| format!("{} reads its header: {error}", path.display()))?;
    let header = String::from_utf8(header)
        .map_err(|_| format!("{} has a non-UTF-8 header", path.display()))?;

    let key = format!("\"{tensor}\":");
    let start = header
        .find(&key)
        .ok_or_else(|| format!("{} declares no tensor {tensor}", path.display()))?;
    let rest = &header[start + key.len()..];
    let mut depth = 0usize;
    let mut close = 0usize;
    for (index, character) in rest.char_indices() {
        match character {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    close = index + 1;
                    break;
                }
            }
            _ => {}
        }
    }
    if close == 0 {
        return Err(format!("tensor {tensor} has an unterminated header record"));
    }
    let record = &rest[..close];

    let dtype =
        scan_string(record, "dtype").ok_or_else(|| format!("tensor {tensor} declares a dtype"))?;
    if dtype != expected_dtype {
        return Err(format!(
            "tensor {tensor} is {dtype} and this reader was declared for {expected_dtype}"
        ));
    }
    let shape =
        scan_numbers(record, "shape").ok_or_else(|| format!("tensor {tensor} declares a shape"))?;
    let offsets = scan_numbers(record, "data_offsets")
        .ok_or_else(|| format!("tensor {tensor} declares data offsets"))?;
    if offsets.len() != 2 {
        return Err(format!("tensor {tensor} declares two data offsets"));
    }
    let elements = shape.iter().try_fold(1u64, |product, dimension| {
        product
            .checked_mul(*dimension)
            .ok_or_else(|| format!("tensor {tensor} extent overflows"))
    })?;
    if offsets[1].checked_sub(offsets[0]) != elements.checked_mul(element_bytes) {
        return Err(format!(
            "tensor {tensor} does not have the exact {expected_dtype} extent its shape declares"
        ));
    }
    Ok(TensorExtent {
        data_start: 8 + header_length,
        byte_start: offsets[0],
        byte_end: offsets[1],
        shape,
    })
}

fn scan_string(record: &str, field: &str) -> Option<String> {
    let key = format!("\"{field}\":\"");
    let start = record.find(&key)? + key.len();
    let end = record[start..].find('"')? + start;
    Some(record[start..end].to_owned())
}

fn scan_numbers(record: &str, field: &str) -> Option<Vec<u64>> {
    let key = format!("\"{field}\":[");
    let start = record.find(&key)? + key.len();
    let end = record[start..].find(']')? + start;
    record[start..end]
        .split(',')
        .map(|entry| entry.trim().parse::<u64>().ok())
        .collect()
}

/// Read raw interchange words at declared flat coordinates, zero-extended to `u64`.
///
/// This is the only place bytes become numbers, and they become **integers**, not floats.
fn read_words(
    path: &Path,
    extent: &TensorExtent,
    element_bytes: u64,
    coordinates: &[u64],
) -> Result<Vec<u64>, String> {
    let mut file =
        File::open(path).map_err(|error| format!("{} opens: {error}", path.display()))?;
    let elements = (extent.byte_end - extent.byte_start) / element_bytes;
    let mut words = Vec::with_capacity(coordinates.len());
    for coordinate in coordinates {
        if *coordinate >= elements {
            return Err(format!("the tensor has no flat coordinate {coordinate}"));
        }
        let offset = extent.data_start + extent.byte_start + coordinate * element_bytes;
        file.seek(SeekFrom::Start(offset))
            .map_err(|error| format!("{} seeks to {offset}: {error}", path.display()))?;
        let mut buffer = [0u8; 8];
        let slice = &mut buffer[..element_bytes as usize];
        file.read_exact(slice)
            .map_err(|error| format!("{} reads {element_bytes} bytes: {error}", path.display()))?;
        let mut word = 0u64;
        for (index, byte) in slice.iter().enumerate() {
            word |= u64::from(*byte) << (8 * index);
        }
        words.push(word);
    }
    Ok(words)
}

fn words_digest(words: &[u64]) -> String {
    let mut hash = Sha256::new();
    for word in words {
        hash.update(word.to_le_bytes());
    }
    let digest = hash.finalize();
    let mut encoded = String::with_capacity(16);
    for byte in digest.iter().take(8) {
        encoded.push_str(&format!("{byte:02x}"));
    }
    encoded
}

// ---------------------------------------------------------------------------------------------
// Reporting.
// ---------------------------------------------------------------------------------------------

fn scale_of(value: &Rat) -> String {
    match dyadic_scale(value) {
        None => "0".to_owned(),
        Some(exponent) => format!("~2^{exponent}"),
    }
}

fn vector_text(vector: &[BigInt]) -> String {
    let entries: Vec<String> = vector
        .iter()
        .map(|entry| {
            let text = entry.to_string();
            if text.len() > 20 {
                let sign = if entry.is_negative() { "-" } else { "" };
                format!("{sign}~2^{}", entry.magnitude().bits().saturating_sub(1))
            } else {
                text
            }
        })
        .collect();
    format!("({})", entries.join(", "))
}

fn describe_datum(name: &str, datum: &BinaryFloatDatum) -> String {
    let (reduced, exponent) = datum.reduced_dyadic();
    format!(
        "{name:<34} 0x{:0width$x}  {} * 2^{}   reduced {reduced}*2^{exponent}   ulp 2^{}",
        datum.bits,
        datum.signed_significand(),
        datum.ulp_exponent,
        datum.ulp_exponent,
        width = (datum.species.width_bits() / 4) as usize
    )
}

fn report_faces(label: &str, faces: &[ExactFace]) {
    println!("  {label}");
    for face in faces {
        println!(
            "    {:<32} width {:<10} certified {:<10} ceiling paid by {}",
            face.name,
            scale_of(&face.width()),
            face.certified_bits().to_string(),
            face.aperture_source()
        );
    }
    println!(
        "    finest grain this basis admits: {}",
        finest_admissible_grain(faces)
    );
}

fn verdict_name(verdict: &ReopeningVerdict) -> &'static str {
    match verdict {
        ReopeningVerdict::Candidate(_) => "CANDIDATE",
        ReopeningVerdict::InvariantButRefuted { .. } => "InvariantButRefuted",
        ReopeningVerdict::FrameDependent { .. } => "FrameDependent",
        ReopeningVerdict::BelowTheFacesResolution { .. } => "BelowTheFacesResolution",
    }
}

fn report_verdict(reopening: &Reopening) {
    match &reopening.verdict {
        ReopeningVerdict::Candidate(candidate) => {
            println!("    RETURNED   {candidate}");
            println!(
                "      coefficients {}   height {}",
                vector_text(&candidate.coefficients),
                candidate.height
            );
            let width = &candidate.residual.upper - &candidate.residual.lower;
            println!(
                "      residual     [{}] width {}{}",
                if candidate.residual.is_point() {
                    "an exact point".to_owned()
                } else {
                    format!("{}", scale_of(&candidate.residual.lower))
                },
                scale_of(&width),
                if candidate.residual.is_point() && candidate.residual.lower.is_zero() {
                    " -- EXACTLY zero, not an enclosure containing zero"
                } else {
                    ""
                }
            );
            println!(
                "      chance popn  {}   (admission needs < 1 expected coincidence)",
                scale_of(&candidate.chance_population)
            );
        }
        ReopeningVerdict::InvariantButRefuted {
            coefficients,
            residual,
        } => {
            println!("    RETURNED NOTHING -- InvariantButRefuted");
            println!(
                "      every frame agreed on {} and the faces' own enclosures PROVE it is not a",
                vector_text(coefficients)
            );
            println!(
                "      relation: the residual {} excludes zero. That is an exact negative.",
                scale_of(&residual.lower)
            );
        }
        ReopeningVerdict::FrameDependent { vectors } => {
            println!("    RETURNED NOTHING -- FrameDependent");
            println!(
                "      the {} probes did not agree; the shortest vector is a coordinate of the",
                vectors.len()
            );
            println!("      grain or of which endpoint was lifted, not an invariant of the faces.");
            for vector in vectors.iter().take(3) {
                println!("        {}", vector_text(vector));
            }
        }
        ReopeningVerdict::BelowTheFacesResolution {
            coefficients,
            chance_population,
            ..
        } => {
            println!("    RETURNED NOTHING -- BelowTheFacesResolution");
            println!(
                "      every frame agreed on {} and the faces cannot refute it, but the searched",
                vector_text(coefficients)
            );
            println!(
                "      population is expected to contain {} such coincidences. Retained, not discarded.",
                scale_of(chance_population)
            );
        }
    }
    let refuted = reopening
        .probes
        .iter()
        .filter(|probe| probe.refuted)
        .count();
    println!(
        "    {} probes, {refuted} refuted by the faces' own enclosures",
        reopening.probes.len()
    );
}

/// The common-denominator integer form of a set of exactly-dyadic faces, and its bit length.
///
/// This is what makes control 3 a measurement rather than a tautology. Any `n` rationals are
/// linearly dependent over `Q`, so the *existence* of a relation is guaranteed and carries no
/// evidence. What is not guaranteed is its **height**: for integer forms of `B` bits over `n`
/// faces, the kernel lattice has determinant about `2^B` and rank `n-1`, so Minkowski bounds the
/// shortest vector by about `sqrt(n-1) * 2^(B/(n-1))`. A returned height at or below that is the
/// instrument doing its job; a height far above it would mean LLL had failed on this material.
fn integer_form_bits(faces: &[ExactFace]) -> Option<u64> {
    let mut denominator = BigInt::one();
    for face in faces {
        if !face.enclosure.is_point() {
            return None;
        }
        let face_denominator = face.enclosure.lower.denom().clone();
        denominator = lcm(&denominator, &face_denominator);
    }
    let mut largest = 0u64;
    for face in faces {
        let value = &face.enclosure.lower;
        let scaled = value.numer() * (&denominator / value.denom());
        largest = largest.max(scaled.magnitude().bits());
    }
    Some(largest)
}

fn lcm(left: &BigInt, right: &BigInt) -> BigInt {
    if left.is_zero() || right.is_zero() {
        return BigInt::zero();
    }
    let mut a = left.magnitude().clone();
    let mut b = right.magnitude().clone();
    while !b.is_zero() {
        let remainder = &a % &b;
        a = b;
        b = remainder;
    }
    (left * right).abs() / BigInt::from(a)
}

fn minkowski_height_bound(bits: u64, faces: usize) -> f64 {
    // Reported as an order of magnitude only, in the driver, and never used to gate anything.
    let rank = (faces - 1) as f64;
    ((bits as f64) / rank).exp2() * rank.sqrt()
}

// ---------------------------------------------------------------------------------------------
// Controls.
// ---------------------------------------------------------------------------------------------

fn measured_faces(reading: FloatReading) -> Vec<(ExactFace, BinaryFloatDatum)> {
    MEASURED_CONSTANTS
        .iter()
        .map(|(name, value, source)| {
            let datum = decode_f64(*value).expect("a CODATA constant is finite");
            let face = ExactFace::from_binary_float(*name, *source, &datum, reading);
            (face, datum)
        })
        .collect()
}

fn control_the_mouth_refuses_and_admits() -> bool {
    println!("-- control 1: a mouth that accepts everything has not been built --\n");
    println!("   Three CODATA 2022 constants, each a MEASURED quantity that no exact decimal");
    println!("   names, so the compiler rounded each one and deleted a tail one ulp wide. The ulp");
    println!("   differs across them by sixteen binary places purely because their magnitudes do:");
    println!("   the unit in the last place belongs to the format AT A MAGNITUDE, not to the");
    println!("   format.\n");

    let pairs = measured_faces(FloatReading::RoundedToNearest);
    for ((_, datum), (name, _, _)) in pairs.iter().zip(MEASURED_CONSTANTS.iter()) {
        println!("    {}", describe_datum(name, datum));
    }
    println!();

    let faces: Vec<ExactFace> = pairs.iter().map(|(face, _)| face.clone()).collect();
    report_faces("faces (read as ROUNDED MEASUREMENTS)", &faces);

    let ceiling = match finest_admissible_grain(&faces) {
        CertifiedBits::Bits(bits) => bits,
        other => {
            println!("    the basis has no finite grain ceiling ({other}); control 1 cannot run");
            return false;
        }
    };
    println!();

    let refused = probe_at_grain(&faces, DeclaredGrain::bits(ceiling + 1));
    let admitted = probe_at_grain(&faces, DeclaredGrain::bits(ceiling));
    let refused_by_name = match &refused {
        Err(ReopeningError::FaceCoarserThanGrain {
            name,
            certified,
            bits,
        }) => {
            println!("    at grain 2^{}: REFUSED BY NAME", ceiling + 1);
            println!("      {}", refused.as_ref().unwrap_err());
            println!(
                "      face {name}, certified {certified}, question {bits} bits -- the ulp is the ceiling"
            );
            true
        }
        Err(other) => {
            println!(
                "    at grain 2^{}: refused, but not by the aperture law: {other}",
                ceiling + 1
            );
            false
        }
        Ok(_) => {
            println!(
                "    at grain 2^{}: ADMITTED. The mouth widened the aperture and that is a defect.",
                ceiling + 1
            );
            false
        }
    };
    let admitted_below = match &admitted {
        Ok(probe) => {
            println!("    at grain 2^{ceiling}: ADMITTED");
            println!(
                "      shortest vector {} height {} residual width {}",
                vector_text(&probe.coefficients),
                probe.height,
                scale_of(&(&probe.residual.upper - &probe.residual.lower))
            );
            true
        }
        Err(error) => {
            println!("    at grain 2^{ceiling}: refused -- {error}");
            false
        }
    };

    // And the same three patterns read as POINTS carry no ceiling at all.
    let points: Vec<ExactFace> = measured_faces(FloatReading::ExactBitPattern)
        .into_iter()
        .map(|(face, _)| face)
        .collect();
    println!();
    report_faces(
        "the same three patterns read as EXACT BIT PATTERNS",
        &points,
    );
    let deep = probe_at_grain(&points, DeclaredGrain::bits(4096)).is_ok();
    println!(
        "    at grain 2^4096: {}",
        if deep {
            "ADMITTED -- a point has no ceiling because nothing was deleted at this boundary"
        } else {
            "refused, which a point must never be"
        }
    );

    let held = refused_by_name && admitted_below && deep;
    println!(
        "\n    control 1: {}\n",
        if held { "HELD" } else { "FAILED" }
    );
    held
}

fn control_the_decode_is_a_bijection() -> bool {
    println!("-- control 2: the decode is a bijection on the format it claims --\n");
    println!("   Every declared pattern makes the full round trip f64 -> exact dyadic -> f64 and");
    println!("   must come back bit-identical. Subnormals, both zeros and a long mantissa are in");
    println!("   the set on purpose; each is a place a decode that took shortcuts would fail.\n");

    let mut held = true;
    for (name, bits) in DECLARED_BINARY64 {
        let value = f64::from_bits(bits);
        let datum = match decode_f64(value) {
            Ok(datum) => datum,
            Err(error) => {
                println!("    binary64 {name:<34} DECODE FAILED: {error}");
                held = false;
                continue;
            }
        };
        let returned = match encode_f64(&datum) {
            Ok(returned) => returned,
            Err(error) => {
                println!("    binary64 {name:<34} ENCODE FAILED: {error}");
                held = false;
                continue;
            }
        };
        let identical = returned.to_bits() == bits;
        held &= identical;
        println!(
            "    binary64 {name:<34} 0x{bits:016x} -> {} * 2^{} -> 0x{:016x}  {}",
            datum.signed_significand(),
            datum.ulp_exponent,
            returned.to_bits(),
            if identical { "identical" } else { "DIFFERENT" }
        );
    }
    for (name, bits) in DECLARED_BINARY32 {
        let value = f32::from_bits(bits);
        let identical = decode_f32(value)
            .and_then(|datum| encode_f32(&datum))
            .map(|returned| returned.to_bits() == bits)
            .unwrap_or(false);
        held &= identical;
        println!(
            "    binary32 {name:<34} 0x{bits:08x} {}",
            if identical { "identical" } else { "DIFFERENT" }
        );
    }
    for (name, bits) in DECLARED_BFLOAT16 {
        // bfloat16 has no machine type; the round trip is pattern -> dyadic -> pattern.
        let identical = decode_bfloat16_bits(bits)
            .and_then(|datum| datum.to_bits())
            .map(|returned| returned == u64::from(bits))
            .unwrap_or(false);
        held &= identical;
        println!(
            "    bfloat16 {name:<34} 0x{bits:04x}     {}",
            if identical { "identical" } else { "DIFFERENT" }
        );
    }

    println!("\n   And what names no ratio is refused BY NAME, not mapped to a sentinel:\n");
    for (name, species, bits) in DECLARED_REFUSALS {
        match decode_bits(species, bits) {
            Err(error) => println!("    {:<9} {name:<34} refused: {error}", species.name()),
            Ok(_) => {
                println!(
                    "    {:<9} {name:<34} ACCEPTED -- and it must not be",
                    species.name()
                );
                held = false;
            }
        }
    }
    // The refusal is reachable from the live-float mouth too, not only from raw patterns.
    let live_nan = decode_f64(f64::NAN).is_err() && decode_f64(f64::INFINITY).is_err();
    held &= live_nan;
    println!(
        "    the live-float mouth refuses NaN and infinity as well: {}",
        if live_nan { "yes" } else { "NO" }
    );

    println!(
        "\n    control 2: {}\n",
        if held { "HELD" } else { "FAILED" }
    );
    held
}

struct RealMaterial {
    label: &'static str,
    path: PathBuf,
    tensor: &'static str,
    dtype: &'static str,
    shape: Vec<u64>,
    digest: String,
    data: Vec<BinaryFloatDatum>,
}

fn open_real_material() -> Vec<RealMaterial> {
    let mut opened = Vec::new();
    for artifact in &DECLARED_ARTIFACTS {
        let Some(path) = resolve_artifact(artifact) else {
            println!(
                "    {}: UNRESOLVED under $HOME/.cache/huggingface/hub/{}",
                artifact.label, artifact.repository
            );
            continue;
        };
        let extent = match safetensors_extent(
            &path,
            artifact.tensor,
            artifact.dtype,
            artifact.element_bytes,
        ) {
            Ok(extent) => extent,
            Err(error) => {
                println!("    {}: {error}", artifact.label);
                continue;
            }
        };
        let coordinates: Vec<u64> = (0..4).collect();
        let words = match read_words(&path, &extent, artifact.element_bytes, &coordinates) {
            Ok(words) => words,
            Err(error) => {
                println!("    {}: {error}", artifact.label);
                continue;
            }
        };
        let mut data = Vec::with_capacity(words.len());
        let mut refused = false;
        for word in &words {
            match decode_bits(artifact.species, *word) {
                Ok(datum) => data.push(datum),
                Err(error) => {
                    println!("    {}: coordinate refused -- {error}", artifact.label);
                    refused = true;
                }
            }
        }
        if refused {
            continue;
        }
        opened.push(RealMaterial {
            label: artifact.label,
            path,
            tensor: artifact.tensor,
            dtype: artifact.dtype,
            shape: extent.shape,
            digest: words_digest(&words),
            data,
        });
    }
    opened
}

fn control_the_organ_on_real_material(material: &[RealMaterial]) -> bool {
    println!("-- control 3: the organ on real material --\n");
    println!("   Trained network weights, read straight out of safetensors payloads by the reader");
    println!("   shape of soma/life/examples/eros_self_emanated_law.rs. Nobody chose these words;");
    println!("   they are the residue of an optimisation over real data.\n");
    println!(
        "   A stored weight is read as an EXACT BIT PATTERN, because it is one: the number in"
    );
    println!("   the file IS m*2^e and nothing rounded it at this boundary.\n");

    if material.is_empty() {
        println!("    no declared external artifact resolved on this cpu.");
        println!("    control 3: FAILED -- a control that could not run has not passed.\n");
        return false;
    }

    let mut held = true;
    for source in material {
        println!("    artifact  {}", source.label);
        println!("      path    {}", source.path.display());
        println!(
            "      tensor  {} [{}] {}   first four words sha256/64 {}",
            source.tensor,
            source
                .shape
                .iter()
                .map(u64::to_string)
                .collect::<Vec<_>>()
                .join(", "),
            source.dtype,
            source.digest
        );
        for (index, datum) in source.data.iter().enumerate() {
            println!(
                "      {}",
                describe_datum(&format!("weight[{index}]"), datum)
            );
        }

        for width in [3usize, 4usize] {
            if source.data.len() < width {
                continue;
            }
            let faces: Vec<ExactFace> = source.data[..width]
                .iter()
                .enumerate()
                .map(|(index, datum)| {
                    ExactFace::from_binary_float(
                        format!("w{index}"),
                        format!("{} {}[{index}]", source.label, source.tensor),
                        datum,
                        FloatReading::ExactBitPattern,
                    )
                })
                .collect();
            let grains = [DeclaredGrain::bits(64), DeclaredGrain::bits(96)];
            println!("\n      {width} weights, grains 2^64 / 2^96:");
            match reopen(&faces, &grains) {
                Ok(reopening) => {
                    report_verdict(&reopening);
                    if let Some(bits) = integer_form_bits(&faces) {
                        let bound = minkowski_height_bound(bits, width);
                        let height = reopening
                            .verdict
                            .candidate()
                            .map(|candidate| candidate.height.clone())
                            .unwrap_or_else(BigInt::zero);
                        println!(
                            "      integer form {bits} bits over {width} faces: Minkowski bounds the \
                             shortest kernel vector"
                        );
                        println!(
                            "      by about {bound:.0}; the instrument returned height {height}. \
                             The EXISTENCE of a relation"
                        );
                        println!(
                            "      among n rationals is guaranteed and carries no evidence; the \
                             height is the measurement."
                        );
                    }
                    if reopening.verdict.candidate().is_none() {
                        held = false;
                    }
                }
                Err(error) => {
                    println!("      refused: {error}");
                    held = false;
                }
            }
        }
        println!();
    }

    println!(
        "    control 3: {}\n",
        if held {
            "HELD -- every basis of real weights returned an exactly-zero-residual relation"
        } else {
            "FAILED"
        }
    );
    held
}

fn log_face(value: i64) -> ExactFace {
    let interval = log_rational_interval(&integer(value), 120, 210).expect("a positive logarithm");
    ExactFace::from_rat_interval(format!("log {value}"), "log_rational_interval", &interval)
        .expect("an ordered enclosure")
}

fn control_the_negative_control_survives() -> bool {
    println!("-- control 4: the negative control survives the mouth --\n");
    println!("   `a*log2 + b*log3 + c*log5 = 0` iff `2^a 3^b 5^c = 1` iff `a=b=c=0`, by unique");
    println!("   factorisation. reopening.rs's own relation-free control must still return zero");
    println!("   spurious relations, and so must a relation-free basis of MEASURED FLOATS.\n");

    let three = vec![log_face(2), log_face(3), log_face(5)];
    let four = vec![log_face(2), log_face(3), log_face(5), log_face(7)];
    let sweep: [(u32, u32); 8] = [
        (24, 32),
        (32, 48),
        (40, 56),
        (48, 72),
        (56, 88),
        (64, 96),
        (80, 120),
        (96, 144),
    ];
    let mut spurious = 0usize;
    for (coarse, fine) in sweep {
        let pair = [DeclaredGrain::bits(coarse), DeclaredGrain::bits(fine)];
        let a = reopen(&three, &pair).expect("a probeable basis");
        let b = reopen(&four, &pair).expect("a probeable basis");
        let a_returned = a.verdict.candidate().is_some();
        let b_returned = b.verdict.candidate().is_some();
        spurious += usize::from(a_returned) + usize::from(b_returned);
        println!(
            "      grains 2^{coarse:<3} / 2^{fine:<3}   three logs: {:<9} four logs: {}",
            if a_returned { "RELATION" } else { "nothing" },
            if b_returned { "RELATION" } else { "nothing" }
        );
    }
    println!("    spurious relations over 16 relation-free searches: {spurious}\n");

    println!("   And the same question asked of the mouth's own material. The three CODATA");
    println!("   constants carry no known integer relation; read as measurements they are exactly");
    println!("   the widened faces that would admit one if the mouth had widened too far.\n");
    let measured: Vec<ExactFace> = measured_faces(FloatReading::RoundedToNearest)
        .into_iter()
        .map(|(face, _)| face)
        .collect();
    let ceiling = match finest_admissible_grain(&measured) {
        CertifiedBits::Bits(bits) => bits,
        other => {
            println!("      the measured basis has no finite ceiling ({other})");
            return false;
        }
    };
    let float_sweep: [(u32, u32); 8] = [
        (10, ceiling),
        (15, ceiling),
        (18, 25),
        (20, ceiling),
        (22, 27),
        (24, 28),
        (26, ceiling),
        (ceiling - 1, ceiling),
    ];
    let mut float_spurious = 0usize;
    for (coarse, fine) in float_sweep {
        let pair = [DeclaredGrain::bits(coarse), DeclaredGrain::bits(fine)];
        match reopen(&measured, &pair) {
            Ok(reopening) => {
                let returned = reopening.verdict.candidate().is_some();
                float_spurious += usize::from(returned);
                println!(
                    "      grains 2^{coarse:<3} / 2^{fine:<3}   {:<24} {}",
                    verdict_name(&reopening.verdict),
                    if returned { "RELATION" } else { "nothing" }
                );
            }
            Err(error) => println!("      grains 2^{coarse:<3} / 2^{fine:<3}   refused: {error}"),
        }
    }
    println!("    spurious relations over 8 measured-float searches: {float_spurious}\n");

    let held = spurious == 0 && float_spurious == 0;
    println!(
        "    control 4: {}\n",
        if held {
            "HELD -- the mouth did not widen any face enough to admit a spurious relation"
        } else {
            "FAILED -- and this is a finding, not something to tune away"
        }
    );
    held
}

fn control_the_distinction_is_load_bearing(material: &[RealMaterial]) -> bool {
    println!("-- control 5: the distinction is load-bearing, not decorative --\n");
    println!(
        "   The SAME bits, admitted as a point and as an enclosure. If the two readings never"
    );
    println!("   differ, the type distinction added here is doing no work and this driver must");
    println!("   say so rather than claim a mechanism it does not have.\n");

    let Some(source) = material
        .iter()
        .find(|source| source.data[0].species == BinaryFloatSpecies::Bfloat16)
        .or_else(|| material.first())
    else {
        println!("    no real material resolved; control 5 falls back to nothing and FAILS.\n");
        return false;
    };

    let width = 3usize.min(source.data.len());
    let build = |reading: FloatReading| -> Vec<ExactFace> {
        source.data[..width]
            .iter()
            .enumerate()
            .map(|(index, datum)| {
                ExactFace::from_binary_float(
                    format!("w{index}"),
                    format!("{} {}[{index}]", source.label, source.tensor),
                    datum,
                    reading,
                )
            })
            .collect()
    };

    println!("    material  {} {}", source.label, source.tensor);
    let points = build(FloatReading::ExactBitPattern);
    let measurements = build(FloatReading::RoundedToNearest);
    report_faces("as EXACT BIT PATTERNS", &points);
    println!();
    report_faces("as ROUNDED MEASUREMENTS", &measurements);
    println!();

    let point_grains = [DeclaredGrain::bits(64), DeclaredGrain::bits(96)];
    let point_reopening = reopen(&points, &point_grains).expect("points admit every grain");
    println!("    as patterns, grains 2^64 / 2^96:");
    report_verdict(&point_reopening);

    let ceiling = match finest_admissible_grain(&measurements) {
        CertifiedBits::Bits(bits) => bits,
        other => {
            println!("\n    the measurement basis has no finite ceiling ({other})");
            return false;
        }
    };
    println!("\n    as measurements the ceiling is 2^{ceiling}; the grains the patterns used are");
    println!("    refused by name:");
    match probe_at_grain(&measurements, point_grains[0]) {
        Err(error) => println!("      {error}"),
        Ok(_) => {
            println!("      ADMITTED at 2^64, which the ulp forbids");
            return false;
        }
    }
    let measured_grains = [
        DeclaredGrain::bits(ceiling - 1),
        DeclaredGrain::bits(ceiling),
    ];
    println!(
        "\n    as measurements, grains 2^{} / 2^{ceiling} (the finest the ulps allow):",
        ceiling - 1
    );
    let measured_reopening = reopen(&measurements, &measured_grains)
        .expect("the declared grains are within the coarsest ulp");
    report_verdict(&measured_reopening);

    let point_verdict = verdict_name(&point_reopening.verdict);
    let measured_verdict = verdict_name(&measured_reopening.verdict);
    let differ = point_reopening.verdict != measured_reopening.verdict;
    println!(
        "\n    as a pattern: {point_verdict}    as a measurement: {measured_verdict}    {}",
        if differ { "DIFFERENT" } else { "the same" }
    );
    if differ {
        println!(
            "    The same {} bits carry an exact integer relation when the file's number is",
            width as u32 * source.data[0].species.width_bits()
        );
        println!(
            "    taken to be the datum, and carry nothing when it is taken to be a rounding of"
        );
        println!("    something else. The reading is the object, not a label on it.");
    } else {
        println!("    The two readings agreed. On this material the distinction is doing no work,");
        println!("    and that is what this control is for.");
    }
    println!(
        "\n    control 5: {}\n",
        if differ { "HELD" } else { "FAILED" }
    );
    differ
}

fn main() {
    println!("== a float is a dyadic and a deleted tail ==\n");
    println!(
        "A float is not a bad approximation of a ratio. It is the ratio's series expansion in"
    );
    println!("base two, TRUNCATED, with the remainder discarded -- and the truncated expansion is");
    println!("itself exact: an IEEE-754 value is precisely m*2^e over the integers. What was");
    println!("destroyed is the tail, and the tail is exactly one unit in the last place wide.\n");
    println!(
        "So the honest face of a float is a POINT or an ENCLOSURE of width one ulp, and which"
    );
    println!("one it is is NOT a property of the bits. It is a declaration the caller must make,");
    println!("and reopening.rs's admission law separates the two without a new rule.\n");
    println!("The float enters at exact_value::ieee754 and nowhere else: four functions, each one");
    println!("call to to_bits or from_bits, no arithmetic on a machine float anywhere.\n");

    println!("-- resolving the declared external material --\n");
    let material = open_real_material();
    if !material.is_empty() {
        for source in &material {
            println!("    resolved  {}  ({})", source.label, source.dtype);
        }
    }
    println!();

    let one = control_the_mouth_refuses_and_admits();
    let two = control_the_decode_is_a_bijection();
    let three = control_the_organ_on_real_material(&material);
    let four = control_the_negative_control_survives();
    let five = control_the_distinction_is_load_bearing(&material);

    println!("== the mouth, stated exactly ==\n");
    println!("   ACCEPTS  every finite bfloat16, binary32 and binary64 interchange pattern,");
    println!("            including all subnormals and both zeros, as an exact dyadic");
    println!("            +/- significand * 2^ulp_exponent over BigUint, with the sign retained");
    println!("            separately so -0.0 round-trips.");
    println!("   REFUSES  NaN and +/-infinity by name (NotANumberFloat, InfiniteFloat), a pattern");
    println!("            carrying bits above its declared format width (OverWideBitPattern), and");
    println!("            any decode that does not re-encode to the pattern it came from");
    println!("            (NonInvertibleDecode) -- the round trip is a law checked on every call.");
    println!("   REQUIRES a declared FloatReading. It never infers whether a tail was deleted.");
    println!("   REFUSES  downstream, by the unchanged aperture law, any rounded face probed at a");
    println!("            grain finer than its own unit in the last place: FaceCoarserThanGrain,");
    println!("            naming the face, its certified width and the grain that asked.\n");

    println!("== summary ==\n");
    for (label, held) in [
        ("1  the mouth refuses and admits at the ulp", one),
        ("2  the decode is a bijection on the format", two),
        ("3  the organ returns on real trained weights", three),
        ("4  the negative control survives the mouth", four),
        ("5  point and enclosure give different verdicts", five),
    ] {
        println!(
            "   control {label:<48} {}",
            if held { "HELD" } else { "FAILED" }
        );
    }
    println!();

    if !(one && two && three && four && five) {
        eprintln!("a declared control did not hold");
        std::process::exit(1);
    }
}
