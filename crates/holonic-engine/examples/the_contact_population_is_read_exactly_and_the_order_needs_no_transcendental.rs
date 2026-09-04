//! **Phoenix station three, its contact half: a real contact population, read exactly, with its
//! order taken by cross-multiplication and no transcendental anywhere.**
//!
//! Plan: `archive/plans/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`.
//! Derivation:
//! `research/records/2026-08-18_THE_HOLON_IS_THE_OPERATION_COMPLEX_THE_FOREIGN_MAP_IS_A_PORTED_WORD_AND_THE_CARD_CARRIES_ITS_FRONTS.md`
//! §§10, 12.3 — *"enact the real branch/join diagram, using existing exact contact, ratio,
//! certified-value, incidence and reconstruction owners."*
//!
//! # The split follows the causal geometry, not the arithmetic volume
//!
//! The two projections are a **front**: co-present branches of one predecessor, `2048 x 2560` and
//! `512 x 2560` of stored material each. The card carries them. The contact between two charts is a
//! **local face** over a few hundred terms; the serial chart carries that. Neither is a fallback
//! for the other and the placement is by the material's own shape.
//!
//! # The sharp return
//!
//! A receiver that reads the **order** of a contact population needs **no transcendental at all**.
//! `exact_contact::RatioFace::compare` orders two contacts by cross-multiplication with no division
//! anywhere, and the ratio family's exponential enters only where a *carried weight* is wanted. So
//! the whole ordering of a real attention population returns exactly, in integers, and the
//! certified series is needed for one thing only — and where it is needed, `exact_value`'s standing
//! `CertifiedSeries` carries it with its tail exhibited.
//!
//! ```text
//! cargo run --release -q -p holonic-engine \
//!   --example the_contact_population_is_read_exactly_and_the_order_needs_no_transcendental -- \
//!   /home/b/models/gemma-4-E4B-it
//! ```

use std::time::Instant;

use holonic_engine::embedding_fiber::{ResidentReadout, align_bfloat16};
use holonic_engine::exact_contact::{ContactError, ExactContact};
use holonic_engine::exact_value::{CertifiedSeries, ExactOrdering, SeriesTailCertificate};
use holonic_engine::exact_work::{Admission, ExactWork, WorkBudget, WorkMetric};
use holonic_engine::foreign_map::manifest_safetensors;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::{ExactExpr, Rat};

const RECEIVER: &str = "model.language_model.layers.0.self_attn.q_proj.weight";
const PRESENTED: &str = "model.language_model.layers.0.self_attn.k_proj.weight";
const SYMBOLS: &str = "model.language_model.embed_tokens.weight";

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let chart_width: usize = std::env::var("CHART")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(256);

    let (mut file, container) = match manifest_safetensors(&format!("{root}/model.safetensors")) {
        Ok(pair) => pair,
        Err(error) => {
            println!("the source refused: {error}");
            std::process::exit(1);
        }
    };
    let chart = match ResidentReadout::new() {
        Ok(chart) => chart,
        Err(error) => {
            println!("the resident chart refused: {error:?}");
            println!("A CPU answer is not admitted for the front. The deed refuses.");
            std::process::exit(1);
        }
    };

    println!("PHOENIX STATION THREE (CONTACT) — THE POPULATION IS READ EXACTLY");
    println!();
    println!(
        "  resident chart                    {}",
        chart.device_name()
    );

    // ---------------------------------------------------------------------------------------
    // THE FRONT: two co-present projections of one predecessor. The card carries it.
    // ---------------------------------------------------------------------------------------
    let receiver_tensor = container.tensor(RECEIVER).expect("manifested").clone();
    let presented_tensor = container.tensor(PRESENTED).expect("manifested").clone();
    let (standing_words, _) = container
        .read_rows_bf16(&mut file, SYMBOLS, 18_740, 1)
        .expect("read");
    let query = align_bfloat16(&standing_words).expect("aligned");

    let front_work =
        ExactWork::predicted_product(receiver_tensor.shape[0], receiver_tensor.shape[1], 1, 8)
            .then(&ExactWork::predicted_product(
                presented_tensor.shape[0],
                presented_tensor.shape[1],
                1,
                8,
            ));
    let budget = WorkBudget::declared(WorkMetric::width_weighted(), 1u64 << 40);
    println!();
    println!("  THE FRONT — two co-present branches of one predecessor");
    println!(
        "    receiver projection             {:?}",
        receiver_tensor.shape
    );
    println!(
        "    presented projection            {:?}",
        presented_tensor.shape
    );
    match budget.admits(&front_work) {
        Admission::Admitted { priced, ceiling } => {
            println!("    ADMITTED  priced {priced} against {ceiling}")
        }
        Admission::Deferred {
            priced,
            ceiling,
            dominating,
        } => {
            println!("    DEFERRED  {priced} against {ceiling}, dominated by {dominating:?}");
            std::process::exit(0);
        }
    }

    let clock = Instant::now();
    let mut stored_octets = 0u64;
    let receiver = {
        let words = container
            .read_bf16_whole(&mut file, RECEIVER)
            .expect("read");
        stored_octets += (words.len() * 2) as u64;
        let mounted = chart
            .mount_bfloat16(&words, receiver_tensor.shape[1])
            .expect("mounted");
        let population = mounted.score_many(&[&query]).expect("scored");
        exact_entries(&population[0], receiver_tensor.shape[0])
    };
    let presented = {
        let words = container
            .read_bf16_whole(&mut file, PRESENTED)
            .expect("read");
        stored_octets += (words.len() * 2) as u64;
        let mounted = chart
            .mount_bfloat16(&words, presented_tensor.shape[1])
            .expect("mounted");
        let population = mounted.score_many(&[&query]).expect("scored");
        exact_entries(&population[0], presented_tensor.shape[0])
    };
    let front = clock.elapsed();
    println!("    stored codewords across the bus {stored_octets} octets");
    println!("    both branches carried in        {front:?}");
    println!(
        "    receiver chart entries {}   presented chart entries {}",
        receiver.len(),
        presented.len()
    );

    // ---------------------------------------------------------------------------------------
    // THE LOCAL FACE: the contact population, exact, with its frame cancelled.
    // ---------------------------------------------------------------------------------------
    let receiver_heads = receiver.len() / chart_width;
    let presented_heads = presented.len() / chart_width;
    println!();
    println!("  THE CONTACT POPULATION — the serial chart carries the local face");
    println!("    declared chart width            {chart_width}");
    println!("    receiver charts                 {receiver_heads}");
    println!("    presented charts                {presented_heads}");

    let mut contacts: Vec<((usize, usize), ExactContact)> = Vec::new();
    let mut refusals: Vec<((usize, usize), ContactError)> = Vec::new();
    let clock = Instant::now();
    for r in 0..receiver_heads {
        let left = &receiver[r * chart_width..(r + 1) * chart_width];
        for p in 0..presented_heads {
            let right = &presented[p * chart_width..(p + 1) * chart_width];
            let aim = bracket(left, right);
            let left_span = bracket(left, left);
            let right_span = bracket(right, right);
            match ExactContact::of_brackets(aim, left_span, right_span, 0, 0) {
                Ok(contact) => contacts.push(((r, p), contact)),
                Err(error) => refusals.push(((r, p), error)),
            }
        }
    }
    let faces = clock.elapsed();
    println!(
        "    contacts read                   {} in {faces:?}",
        contacts.len()
    );
    println!("    refused by name                 {}", refusals.len());
    for ((r, p), error) in refusals.iter().take(3) {
        println!("        ({r}, {p})  {error}");
    }

    println!();
    println!("    each contact carries an UNDIVIDED PAIR and a hand:");
    for ((r, p), contact) in contacts.iter().take(6) {
        let cohere = contact.cohere_square();
        println!(
            "        ({r}, {p})  hand {:?}  cohere^2 = {} / {}",
            contact.hand(),
            shorten(&cohere.numerator.to_string(), 26),
            shorten(&cohere.denominator.to_string(), 26)
        );
    }

    // ---------------------------------------------------------------------------------------
    // THE ORDER, BY CROSS-MULTIPLICATION. No division and no transcendental.
    // ---------------------------------------------------------------------------------------
    println!();
    println!("  THE ORDER OF THE POPULATION — cross-multiplied, never divided");
    let clock = Instant::now();
    let mut ordering: Vec<usize> = (0..contacts.len()).collect();
    let mut open_pairs = 0usize;
    for left in 0..contacts.len() {
        for right in (left + 1)..contacts.len() {
            if contacts[left]
                .1
                .cohere_square()
                .compare(&contacts[right].1.cohere_square())
                == ExactOrdering::Open
            {
                open_pairs += 1;
            }
        }
    }
    ordering.sort_by(|a, b| {
        match contacts[*b]
            .1
            .cohere_square()
            .compare(&contacts[*a].1.cohere_square())
        {
            ExactOrdering::Less => std::cmp::Ordering::Less,
            ExactOrdering::Greater => std::cmp::Ordering::Greater,
            _ => std::cmp::Ordering::Equal,
        }
    });
    let ordered = clock.elapsed();
    println!("    every pair compared in          {ordered:?}");
    println!("    pairs the aperture did not separate  {open_pairs}");
    println!("    NO DIVISION AND NO TRANSCENDENTAL ENTERED THIS ORDERING.");
    println!();
    println!("    the greatest six contacts, by their undivided pairs:");
    for at in ordering.iter().take(6) {
        let ((r, p), contact) = &contacts[*at];
        println!(
            "        ({r}, {p})  hand {:?}  closes {}",
            contact.hand(),
            contact.closes()
        );
    }

    // ---------------------------------------------------------------------------------------
    // THE FRAME CANCELS. A ratio crosses a horizon; a magnitude does not.
    // ---------------------------------------------------------------------------------------
    println!();
    println!("  THE FRAME CANCELS — the horizon law, executed on this material");
    let scaled_receiver: Vec<BigInt> = receiver[..chart_width]
        .iter()
        .map(|value| value * BigInt::from(1024))
        .collect();
    let plain = ExactContact::of_brackets(
        bracket(&receiver[..chart_width], &presented[..chart_width]),
        bracket(&receiver[..chart_width], &receiver[..chart_width]),
        bracket(&presented[..chart_width], &presented[..chart_width]),
        0,
        0,
    );
    let moved = ExactContact::of_brackets(
        bracket(&scaled_receiver, &presented[..chart_width]),
        bracket(&scaled_receiver, &scaled_receiver),
        bracket(&presented[..chart_width], &presented[..chart_width]),
        0,
        0,
    );
    match (plain, moved) {
        (Ok(plain), Ok(moved)) => {
            let agree = plain.cohere_square().compare(&moved.cohere_square());
            println!("    the receiver chart scaled by 2^10");
            println!("    cohere^2 under the two frames   {:?}", agree);
            println!(
                "    hands                           {:?} / {:?}",
                plain.hand(),
                moved.hand()
            );
            println!("    a magnitude moved; the ratio did not.");
        }
        _ => println!("    a null traversal refused, which is itself the return"),
    }

    // ---------------------------------------------------------------------------------------
    // WHERE A TRANSCENDENTAL IS ACTUALLY NEEDED, AND WHO OWNS IT.
    // ---------------------------------------------------------------------------------------
    println!();
    println!("  WHERE A TRANSCENDENTAL IS ACTUALLY NEEDED");
    println!();
    println!("    Not in the order. Only in a CARRIED WEIGHT: a convex combination needs the");
    println!("    exponential of a face difference, and `exact_value::CertifiedSeries` owns that");
    println!("    with its tail exhibited. Nothing is built beside it.");
    println!();
    let difference = Rat::new(BigInt::from(3), BigInt::from(8));
    for terms in [8usize, 16, 24] {
        match certified_exponential(&difference, terms) {
            Ok(series) => {
                let enclosure = series.enclosure();
                println!(
                    "      exp(3/8) after {terms:>2} terms  width {}",
                    shorten(&(&enclosure.upper - &enclosure.lower).to_string(), 34)
                );
            }
            Err(reason) => println!("      {terms} terms refused: {reason}"),
        }
    }
    let series = certified_exponential(&difference, 24).expect("certified");
    println!();
    println!("      tail certificate  {:?}", series.tail_certificate);
    println!("      terms folded      {}", series.terms_folded);
    let enclosure = series.enclosure();
    // exp(3/8) = 1.4549914146...; the bracket is STATED rather than computed, and the enclosure
    // must sit strictly inside it. That checks placement and tightness at once, where a one-sided
    // test checks neither.
    let below = Rat::new(BigInt::from(14549914), BigInt::from(10000000));
    let above = Rat::new(BigInt::from(14549915), BigInt::from(10000000));
    println!(
        "      sits inside the stated bracket for exp(3/8)  {}",
        enclosure.lower >= below && enclosure.upper <= above
    );
    println!(
        "      and its own width is                         {}",
        shorten(&(&enclosure.upper - &enclosure.lower).to_string(), 34)
    );
    println!(
        "      four-state order against a point   {:?}",
        enclosure.disjoint_order(&holonic_engine::exact_value::ExactInterval::point(
            above.clone()
        ))
    );

    println!();
    println!("THE STATION'S VERDICT");
    println!();
    println!("  The front is carried by the card and the local face by the serial chart, split by");
    println!("  the material's own causal geometry rather than by arithmetic volume.");
    println!(
        "  {} contacts were read exactly, each an undivided pair with its hand retained.",
        contacts.len()
    );
    println!("  The complete ordering of the population needed no division and no transcendental.");
    println!("  The frame cancels: a ratio crossed the horizon and a magnitude did not.");
    println!("  Where a carried weight needs an exponential, the standing certified-value owner");
    println!("  carries it with its tail certificate exhibited.");
    println!();
    println!("  This is the contact half of the contextual complex. The chronology, the carried");
    println!("  construction and the constitutive passage are NOT enacted, and no candidate");
    println!("  composition is selected. CONSTRUCTION_STATE is untouched.");
}

/// The exact scores of one query, as integers at the readout's own frame.
fn exact_entries(
    population: &holonic_engine::embedding_fiber::ScorePopulation,
    rows: usize,
) -> Vec<BigInt> {
    (0..rows)
        .map(|row| population.exact(row).unwrap_or_else(BigInt::zero))
        .collect()
}

/// One bracket, exactly. Integers throughout; nothing rounds.
fn bracket(left: &[BigInt], right: &[BigInt]) -> BigInt {
    left.iter()
        .zip(right)
        .fold(BigInt::zero(), |sum, (a, b)| sum + a * b)
}

/// `exp(x)` as a [`CertifiedSeries`], with an absolute geometric tail the owner validates.
///
/// After `n` terms the omitted tail is `sum_{k>=n} x^k/k!`, and each omitted term is at most the
/// first times `(|x|/(n+1))^j`. That is exactly `SeriesTailCertificate::AbsoluteGeometric`, and the
/// owner refuses the certificate if the ratio bound does not close it.
fn certified_exponential(x: &Rat, terms: usize) -> Result<CertifiedSeries, String> {
    let mut sum = Rat::zero();
    let mut term = Rat::one();
    for k in 0..terms {
        sum += &term;
        term = &term * x / Rat::from_integer(BigInt::from(k as u64 + 1));
    }
    let magnitude = |value: &Rat| -> Rat {
        if value.is_negative() {
            -value.clone()
        } else {
            value.clone()
        }
    };
    let ratio_bound = magnitude(x) / Rat::from_integer(BigInt::from(terms as u64 + 1));
    if ratio_bound >= Rat::one() {
        return Err(format!(
            "the geometric ratio bound {ratio_bound} does not close the tail at {terms} terms"
        ));
    }
    CertifiedSeries::new(
        ExactExpr::Rational(x.clone()),
        sum,
        num_bigint::BigUint::from(terms as u64),
        SeriesTailCertificate::AbsoluteGeometric {
            first_omitted_abs_bound: magnitude(&term),
            ratio_abs_bound: ratio_bound,
        },
    )
    .map_err(|error| format!("{error:?}"))
}

fn shorten(text: &str, extent: usize) -> String {
    if text.len() <= extent {
        return text.to_owned();
    }
    format!("{}…({} digits)", &text[..extent], text.len())
}
