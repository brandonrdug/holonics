//! **The exact bracket becomes a face that crosses a horizon, on real map material.**
//!
//! Station three of
//! `archive/plans/THE_MAP_IS_MATERIAL_THE_HEAD_IS_A_CONTACT_AND_THE_INSTANCE_RESUMES.md`. The chain that
//! blueprint carries listed steps four and five — `cos² = <a|b>²/(<a|a><b|b>)` with the powers of
//! two cancelling, and ordering without division — as **IN NUMPY ONLY**. This driver takes both into
//! the body, through the library intake rather than a sixth private parser.
//!
//! **What is claimed.** A bracket is a magnitude and does not cross a frame boundary. The squared
//! cosine does, and not by declaration: where the material enters through the dyadic mouth as exact
//! integers over a common power of two, the numerator carries `2^{2(e_a+e_b)}` and the denominator
//! carries `2^{2e_a}·2^{2e_b}`, which are the same integer. This run computes that difference on
//! every contact rather than asserting it, and `crates/holonic-engine/src/exact_contact.rs` refuses
//! a contact whose frames did not cancel to exactly zero.
//!
//! **The control is a gauge, and it is the point.** The dyadic exponent is a frame. Re-aligning the
//! same rows onto a deliberately different exponent must move every bracket and move no face. If the
//! faces move, the frame did not cancel and the reading is a coordinate presented as an invariant.
//! If the brackets do NOT move, the control gauged nothing and this run says so.
//!
//! **Nothing here selects.** No maximum, no ranking, no threshold. The population is returned whole
//! and ordered by cross-multiplication with no division anywhere.
//!
//! **The model is not run and nothing is resident**: one contiguous row band of one tensor is read
//! by offset, which is the residency constraint Brandon set on 2026-08-13 — *"running the actual
//! models is off of the table"* — and it is untouched by his 2026-08-16 ruling that the mathematics
//! of inference is the instrument.

use std::collections::BTreeMap;

use holonic_engine::clifford::Aim;
use holonic_engine::embedding_fiber::{AlignedMaterial, align_bfloat16, safetensors};
use holonic_engine::exact_contact::{ContactError, ExactContact, RatioFace};
use holonic_engine::exact_value::ExactOrdering;
use num_bigint::BigInt;
use num_traits::Zero;

const MAP: &str = "/home/b/models/gemma-4-E4B-it/model.safetensors";
const READOUT: &str = "model.language_model.embed_tokens.weight";

/// The declared row band. **This caller's aperture, against this caller's memory**, and what it
/// excludes is reported rather than dropped: the tensor's full row count is printed beside it.
const BAND: usize = 24;

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

/// The exact integer bracket `<a|b>` over two aligned rows. `BigInt` because the product of two
/// aligned significands summed across the full width has no bound a fixed carrier could promise.
fn bracket(left: &[i64], right: &[i64]) -> BigInt {
    let mut carried = BigInt::from(0);
    for (a, b) in left.iter().zip(right.iter()) {
        carried += BigInt::from(*a) * BigInt::from(*b);
    }
    carried
}

/// Re-align a row onto a **deliberately different** dyadic frame by shifting every entry left and
/// lowering the exponent to match. This is the gauge: the value is untouched and the coordinates
/// move.
fn regauged(material: &AlignedMaterial, octaves: u32) -> Option<AlignedMaterial> {
    let mut entries = Vec::with_capacity(material.entries.len());
    for entry in &material.entries {
        entries.push(entry.checked_mul(1i64.checked_shl(octaves)?)?);
    }
    Some(AlignedMaterial {
        entries,
        exponent: material.exponent - i32::try_from(octaves).ok()?,
        entry_octaves: material.entry_octaves + octaves,
        negatives: material.negatives,
    })
}

fn run() -> Result<(), String> {
    let (mut file, header) = safetensors::read_header(MAP)?;
    let entry = header.entry(READOUT)?;
    let rows_declared = entry.shape[0];
    let dim = entry.shape[1];
    println!("THE MAP");
    println!("  container      {MAP}");
    println!("  tensor         {READOUT}");
    println!(
        "  declared       {rows_declared} rows x {dim}, dtype {}",
        entry.dtype
    );
    println!("  read           rows 0..{BAND}  (aperture declared by this caller)");
    println!(
        "  excluded       {} rows, reported not dropped",
        rows_declared - BAND
    );

    let (words, width) = safetensors::read_rows(&mut file, &header, READOUT, 0, BAND)?;
    if width != dim {
        return Err(format!(
            "the intake returned width {width} against a declared {dim}"
        ));
    }

    // Each row is aligned onto ITS OWN exponent. That is what makes the cancellation a theorem
    // rather than an artefact of a shared frame.
    let mut aligned = Vec::with_capacity(BAND);
    let mut refused_alignment = Vec::new();
    for row in 0..BAND {
        let slice = &words[row * dim..(row + 1) * dim];
        match align_bfloat16(slice) {
            Ok(material) => aligned.push((row, material)),
            Err(error) => refused_alignment.push((row, format!("{error}"))),
        }
    }
    println!();
    println!("THE DYADIC MOUTH");
    println!("  rows aligned   {}", aligned.len());
    println!("  rows refused   {}", refused_alignment.len());
    for (row, reason) in &refused_alignment {
        println!("    row {row:<6} {reason}");
    }
    if aligned.len() < 2 {
        return Err("fewer than two rows crossed the mouth; no contact is posed".to_owned());
    }
    let exponents: Vec<i32> = aligned.iter().map(|(_, m)| m.exponent).collect();
    let lowest = exponents.iter().copied().min().unwrap_or(0);
    let highest = exponents.iter().copied().max().unwrap_or(0);
    println!("  exponents      {lowest} .. {highest}   (each row on its OWN frame)");

    // ---- the contact population, whole ----
    let mut contacts: Vec<((usize, usize), ExactContact)> = Vec::new();
    let mut null_traversals: Vec<((usize, usize), String)> = Vec::new();
    for i in 0..aligned.len() {
        for j in (i + 1)..aligned.len() {
            let (row_a, a) = &aligned[i];
            let (row_b, b) = &aligned[j];
            let aim = bracket(&a.entries, &b.entries);
            let left_span = bracket(&a.entries, &a.entries);
            let right_span = bracket(&b.entries, &b.entries);
            match ExactContact::of_brackets(aim, left_span, right_span, a.exponent, b.exponent) {
                Ok(contact) => contacts.push(((*row_a, *row_b), contact)),
                Err(error) => null_traversals.push(((*row_a, *row_b), format!("{error}"))),
            }
        }
    }

    println!();
    println!("THE CONTACT POPULATION");
    println!("  contacts       {}", contacts.len());
    println!("  refused        {}", null_traversals.len());
    for (pair, reason) in null_traversals.iter().take(4) {
        println!("    {pair:?}  {reason}");
    }

    // ---- what a face carries, exhibited whole on the first contacts ----
    println!();
    println!("THE FACE, UNDIVIDED  (first four contacts, carried as pairs)");
    for ((row_a, row_b), contact) in contacts.iter().take(4) {
        let cohere = contact.cohere_square();
        let turn = contact.turn_square();
        let (num_frame, den_frame) = contact.cancelled_frame();
        println!("  rows {row_a} / {row_b}");
        println!("    aim            {}", contact.aim());
        println!(
            "    hand           {:?}   (what the square deleted)",
            contact.hand()
        );
        println!(
            "    cos^2          {} / {}",
            cohere.numerator, cohere.denominator
        );
        println!(
            "    sin^2          {} / {}",
            turn.numerator, turn.denominator
        );
        println!(
            "    frame          2^{num_frame} over 2^{den_frame}   residual {}",
            num_frame - den_frame
        );
    }

    // ---- the two checks, on every contact ----
    let mut frame_residuals: BTreeMap<i64, usize> = BTreeMap::new();
    let mut closures_failed = 0usize;
    for (_, contact) in &contacts {
        let (num, den) = contact.cancelled_frame();
        *frame_residuals.entry(num - den).or_default() += 1;
        if !contact.closes() {
            closures_failed += 1;
        }
    }
    println!();
    println!("THE HORIZON");
    println!("  frame residual census (octaves -> contacts)");
    for (residual, count) in &frame_residuals {
        println!("    2^{residual:<4}  {count}");
    }
    println!(
        "  cos^2 + sin^2 = 1 exactly on {} of {} contacts; {closures_failed} failed",
        contacts.len() - closures_failed,
        contacts.len()
    );

    // ---- the hand census: what the squared face erased ----
    let mut hands: BTreeMap<String, usize> = BTreeMap::new();
    for (_, contact) in &contacts {
        let name = match contact.hand() {
            Aim::Cohere => "Cohere",
            Aim::Anti => "Anti",
            Aim::Ortho => "Ortho  (the founding hand)",
        };
        *hands.entry(name.to_owned()).or_default() += 1;
    }
    println!();
    println!("THE HAND THE SQUARE DELETED");
    for (hand, count) in &hands {
        println!("  {hand:<28} {count}");
    }

    // ---- the gauge control ----
    println!();
    println!("THE GAUGE CONTROL  (re-align every row onto a different dyadic frame)");
    let mut regauge_refused = 0usize;
    let mut regauged_rows = Vec::with_capacity(aligned.len());
    for (row, material) in &aligned {
        match regauged(material, 5) {
            Some(moved) => regauged_rows.push((*row, moved)),
            None => regauge_refused += 1,
        }
    }
    if regauge_refused > 0 {
        println!("  {regauge_refused} rows could not be regauged inside the signed carrier");
    }
    let mut brackets_moved = 0usize;
    let mut brackets_still = 0usize;
    let mut faces_moved: Vec<((usize, usize), RatioFace, RatioFace)> = Vec::new();
    let mut representation_moved = 0usize;
    let mut common_factors: Vec<((usize, usize), BigInt, BigInt)> = Vec::new();
    let mut compared = 0usize;
    for i in 0..regauged_rows.len() {
        for j in (i + 1)..regauged_rows.len() {
            let (row_a, a) = &regauged_rows[i];
            let (row_b, b) = &regauged_rows[j];
            let aim = bracket(&a.entries, &b.entries);
            let left_span = bracket(&a.entries, &a.entries);
            let right_span = bracket(&b.entries, &b.entries);
            let Ok(moved) =
                ExactContact::of_brackets(aim, left_span, right_span, a.exponent, b.exponent)
            else {
                continue;
            };
            let Some((_, original)) = contacts.iter().find(|((x, y), _)| x == row_a && y == row_b)
            else {
                continue;
            };
            compared += 1;
            if moved.aim() == original.aim() {
                brackets_still += 1;
            } else {
                brackets_moved += 1;
            }
            // **Compare the VALUE, not the representation.** A pair carries its own gauge -- a
            // common factor multiplies numerator and denominator alike -- so a bitwise comparison
            // of pairs reads a coordinate and calls it the invariant, which is the exact defect
            // this whole line exists to remove. Cross-multiplication reads the value.
            if moved.cohere_square().compare(&original.cohere_square()) != ExactOrdering::Equal {
                faces_moved.push((
                    (*row_a, *row_b),
                    original.cohere_square(),
                    moved.cohere_square(),
                ));
            } else if moved.cohere_square() != original.cohere_square() {
                representation_moved += 1;
                if common_factors.len() < 3 {
                    let before = original.cohere_square();
                    let after = moved.cohere_square();
                    if !before.numerator.is_zero() {
                        common_factors.push((
                            (*row_a, *row_b),
                            &after.numerator / &before.numerator,
                            &after.denominator / &before.denominator,
                        ));
                    }
                }
            }
        }
    }
    println!("  contacts compared          {compared}");
    println!(
        "  brackets that MOVED        {brackets_moved}   (the gauge must move the coordinate)"
    );
    println!("  brackets that stood        {brackets_still}");
    println!(
        "  face VALUES that moved     {}   (the gauge must not move the invariant)",
        faces_moved.len()
    );
    for (pair, before, after) in faces_moved.iter().take(3) {
        println!(
            "    {pair:?}  {} / {}   ->   {} / {}",
            before.numerator, before.denominator, after.numerator, after.denominator
        );
    }
    println!(
        "  face PAIRS that moved      {representation_moved}   (the pair carries its own gauge: a"
    );
    println!("                                 common factor is a representation, not a value)");
    for (pair, numerator_factor, denominator_factor) in &common_factors {
        println!("    {pair:?}  numerator x{numerator_factor}  denominator x{denominator_factor}");
    }
    if brackets_moved == 0 {
        println!("  VACUOUS: the gauge moved no bracket, so it gauged nothing and this control is");
        println!("           evidence of nothing. Reported rather than presented as agreement.");
    }

    // ---- ordering, by cross-multiplication, with no division ----
    println!();
    println!("THE ORDERING  (cross-multiplication; no division anywhere)");
    let mut orderings: BTreeMap<String, usize> = BTreeMap::new();
    let mut checked = 0usize;
    for i in 0..contacts.len() {
        for j in (i + 1)..contacts.len() {
            let reading = contacts[i].1.compare_cohere(&contacts[j].1);
            let name = match reading {
                ExactOrdering::Less => "Less",
                ExactOrdering::Equal => "Equal",
                ExactOrdering::Greater => "Greater",
                ExactOrdering::Open => "Open",
            };
            *orderings.entry(name.to_owned()).or_default() += 1;
            checked += 1;
        }
    }
    println!("  contact pairs compared     {checked}");
    for (reading, count) in &orderings {
        println!("  {reading:<26} {count}");
    }
    println!();
    println!("  No maximum was taken. No contact was discarded. The population is the return.");

    // ---- what this run does NOT establish ----
    println!();
    println!("WHAT THIS DOES NOT ESTABLISH");
    println!("  The rows are addressed by index and no token surface is decoded here, so nothing");
    println!(
        "  above is a claim about what any row MEANS. That is station four's material, and it"
    );
    println!("  needs the bound tokenizer octets rather than an authored decoder.");
    println!("  The signature is the container's own chart read as declared-orthonormal by this");
    println!("  caller. A different declared metric moves every span and is a different reading.");

    if closures_failed > 0 {
        return Err(format!(
            "{closures_failed} contacts did not close: Lagrange's identity failed on real material"
        ));
    }
    if frame_residuals.keys().any(|residual| *residual != 0) {
        return Err("a dyadic frame survived the face: the horizon was not crossed".to_owned());
    }
    Ok(())
}

/// Kept so a reader can see the refusal type is consumed rather than stringified away.
#[allow(dead_code)]
fn names_the_refusal(error: &ContactError) -> &'static str {
    match error {
        ContactError::NullTraversal { .. } => "a traversal that returns nothing",
        ContactError::FrameSurvived { .. } => "a frame that did not cancel",
        ContactError::NotIntegral { .. } => "a span that is not integral",
    }
}
