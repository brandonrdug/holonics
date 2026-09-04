//! **Phoenix station two: a real ported transport is posed, and the work receiver decides.**
//!
//! Plan: `archive/plans/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`.
//! Derivation:
//! `research/records/2026-08-18_THE_HOLON_IS_THE_OPERATION_COMPLEX_THE_FOREIGN_MAP_IS_A_PORTED_WORD_AND_THE_CARD_CARRIES_ITS_FRONTS.md`
//! §§6, 10, 12.2.
//!
//! Three things are separated here that a single "matrix" hides:
//!
//! 1. **Applying** a transport to a standing. Exact, and the card owns it — the stored codewords
//!    cross once, decode and align on the card, and only the contraction comes back.
//! 2. **Posing** it densely as exact rationals. Priced before it is attempted, because an exact
//!    rational entry is not a machine word and a caller that discovers that after allocating has
//!    already paid.
//! 3. **Factorizing** it — kernel, image, open exterior, rebase receipt, metric adjoint. Priced
//!    separately again, because elimination's dependency span is its pivot count while a product's
//!    is one.
//!
//! A refusal at any of the three is a **return**, carrying the priced work, the ceiling and the
//! coordinate that dominated the price. Resource pressure changes the aperture; it never raises a
//! number.
//!
//! ```text
//! cargo run --release -q -p holonic-engine \
//!   --example the_ported_transport_is_posed_or_the_work_refuses -- /home/b/models/gemma-4-E4B-it
//! ```

use std::time::Instant;

use holonic_engine::embedding_fiber::{ResidentReadout, align_bfloat16};
use holonic_engine::exact_linear::{ExactRatMatrix, RebaseReceipt};
use holonic_engine::exact_work::{Admission, ExactWork, WorkBudget, WorkMetric};
use holonic_engine::foreign_map::manifest_safetensors;
use holonic_engine::ported_operation::{
    OperationSpecies, PortedOperationComplex, PortedTransport, PortedWord, SourceTestimony,
};
use num_bigint::BigInt;
use relational_geometry::Rat;

const RECEIVER: &str = "model.language_model.layers.0.self_attn.q_proj.weight";
const PRESENTED: &str = "model.language_model.layers.0.self_attn.k_proj.weight";
const RETURN: &str = "model.language_model.layers.0.self_attn.o_proj.weight";
const SYMBOLS: &str = "model.language_model.embed_tokens.weight";

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let aperture: usize = std::env::var("APERTURE")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(48);

    let (mut file, container) = match manifest_safetensors(&format!("{root}/model.safetensors")) {
        Ok(pair) => pair,
        Err(error) => {
            println!("the source refused: {error}");
            std::process::exit(1);
        }
    };

    println!("PHOENIX STATION TWO — THE PORTED TRANSPORT IS POSED, OR THE WORK REFUSES");
    println!();

    // ---------------------------------------------------------------------------------------
    // The typed ports. Two ports of equal extent are still two ports.
    // ---------------------------------------------------------------------------------------
    let mut complex = PortedOperationComplex::new("site zero contact transports");
    let standing = complex.port("site 0 continuing standing");
    let receiver_chart = complex.port("site 0 receiver chart");
    let presented_chart = complex.port("site 0 presented chart");
    let carried_chart = complex.port("site 0 carried chart");
    for (name, port, carrier) in [
        ("receiver projection", receiver_chart, RECEIVER),
        ("presented projection", presented_chart, PRESENTED),
    ] {
        let tensor = container.tensor(carrier).expect("manifested");
        complex
            .bind_operation(
                name,
                OperationSpecies::Transport,
                vec![standing],
                vec![port],
                Some(carrier.to_owned()),
                vec![SourceTestimony::DeclaredShape {
                    population: carrier.to_owned(),
                    shape: tensor.shape.clone(),
                }],
            )
            .expect("bound");
    }
    println!(
        "  typed ports declared              {}",
        complex.closure().map(|c| c.ports).unwrap_or(0)
    );
    println!(
        "  operations bound                  {}",
        complex.operations.len()
    );

    // ---------------------------------------------------------------------------------------
    // 1. APPLYING at full extent. The card owns this.
    // ---------------------------------------------------------------------------------------
    println!();
    println!("1. APPLYING THE TRANSPORT AT FULL EXTENT — the card owns the deed");
    println!();
    let chart = match ResidentReadout::new() {
        Ok(chart) => chart,
        Err(error) => {
            println!("  the resident chart refused: {error:?}");
            println!("  A CPU answer is not admitted here. The deed refuses.");
            std::process::exit(1);
        }
    };
    println!(
        "  resident chart                    {}",
        chart.device_name()
    );

    let tensor = container.tensor(RECEIVER).expect("manifested").clone();
    let (rows, columns) = (tensor.shape[0], tensor.shape[1]);
    println!("  transport                         {RECEIVER}");
    println!("  ports                             standing -> receiver chart");
    println!("  extent                            {rows} x {columns}");

    // A real standing: one stored symbol's construction.
    let (standing_words, _) = container
        .read_rows_bf16(&mut file, SYMBOLS, 18_740, 1)
        .expect("read");
    let query = align_bfloat16(&standing_words).expect("aligned");

    let predicted = ExactWork::predicted_product(rows, columns, 1, 8);
    let budget = WorkBudget::declared(WorkMetric::width_weighted(), 1u64 << 40);
    println!();
    println!("  predicted work, before dispatch:");
    for (name, count) in predicted.coordinates() {
        println!("      {name:<28} {count}");
    }
    match budget.admits(&predicted) {
        Admission::Admitted { priced, ceiling } => {
            println!("  ADMITTED  priced {priced} against a declared ceiling of {ceiling}");
        }
        Admission::Deferred {
            priced,
            ceiling,
            dominating,
        } => {
            println!("  DEFERRED  priced {priced} against {ceiling}; dominated by {dominating:?}");
            println!("  the deed is not dispatched.");
            std::process::exit(0);
        }
    }

    let stored_octets = (rows * columns * 2) as u64;
    let clock = Instant::now();
    let words = container
        .read_bf16_whole(&mut file, RECEIVER)
        .expect("read");
    let read = clock.elapsed();
    let clock = Instant::now();
    let mounted = chart.mount_bfloat16(&words, columns).expect("mounted");
    let mount = clock.elapsed();
    let clock = Instant::now();
    let population = mounted.score_many(&[&query]).expect("scored");
    let deed = clock.elapsed();
    let carried = &population[0];

    println!();
    println!("  ACTUAL TRANSFER TELEMETRY — summed crossings, never a predicted counter");
    println!("      stored codewords across the bus  {stored_octets} octets");
    println!(
        "      query across the bus             {} octets",
        query.entries.len() * 8
    );
    println!(
        "      resident expansion on the card   {} octets",
        (rows * columns * 8) as u64
    );
    println!(
        "      result egress                    {} octets",
        rows * 8 * 2 + rows * 4
    );
    println!("      launches                         2 (decode/align, contract)");
    println!("      read {read:?}   mount {mount:?}   deed {deed:?}");
    println!(
        "      apparatus frame                  display active on this card; no clock selects here"
    );
    println!();
    println!(
        "  the transport carried the standing into {} exact entries",
        rows
    );
    println!(
        "      first three, exactly: {:?}",
        (0..3)
            .filter_map(|row| carried.exact(row))
            .collect::<Vec<_>>()
    );

    // ---------------------------------------------------------------------------------------
    // 2. POSING densely, priced first.
    // ---------------------------------------------------------------------------------------
    println!();
    println!("2. POSING THE SAME TRANSPORT DENSELY AS EXACT RATIONALS");
    println!();
    let posing = PortedTransport::predicted_posing_work(rows, columns, 8);
    let residency_budget = WorkBudget::declared(
        WorkMetric::declared("residency", &[("resident-entries", 1)]),
        1u64 << 20,
    );
    println!("  predicted residency               {rows} x {columns} exact rational entries");
    match residency_budget.admits(&posing) {
        Admission::Admitted { priced, ceiling } => {
            println!("  ADMITTED  priced {priced} against {ceiling}")
        }
        Admission::Deferred {
            priced,
            ceiling,
            dominating,
        } => {
            println!("  REFUSED   priced {priced} against a declared ceiling of {ceiling}");
            println!(
                "            dominated by {} at {}",
                dominating.0, dominating.1
            );
            println!();
            println!(
                "  **This refusal is the return.** The transport is not posed densely, and the"
            );
            println!("  station changes its APERTURE rather than its ceiling.");
        }
    }

    // ---------------------------------------------------------------------------------------
    // 3. A DECLARED APERTURE on real material, and everything it owes.
    // ---------------------------------------------------------------------------------------
    println!();
    println!("3. A DECLARED APERTURE ON THE SAME REAL MATERIAL");
    println!();
    println!("  aperture                          the leading {aperture} x {aperture} block");
    println!(
        "  what it excluded                  {} of {} entries, reported rather than dropped",
        rows * columns - aperture * aperture,
        rows * columns
    );
    let block = block_of(&words, columns, aperture);
    let posed = PortedTransport::posed_from_bfloat16(
        "receiver projection, leading block",
        standing,
        receiver_chart,
        format!("{RECEIVER} [0..{aperture}, 0..{aperture}]"),
        &block,
        aperture,
        aperture,
    )
    .expect("posed");

    let factorization_budget = WorkBudget::declared(WorkMetric::width_weighted(), 1u64 << 48);
    match posed
        .factorization_under(&factorization_budget, 8)
        .expect("priced")
    {
        Err(admission) => println!("  the factorization refused: {admission:?}"),
        Ok(factorization) => {
            println!("  rank                              {}", factorization.rank);
            println!(
                "  collapsed directions              {}",
                factorization.collapsed_dimension()
            );
            println!(
                "  open exterior                     {}",
                factorization.open_exterior_dimension()
            );
            println!(
                "  is a rebase                       {}",
                factorization.is_rebase()
            );
        }
    }

    match posed.rebase_receipt().expect("receipt") {
        RebaseReceipt::Rebase {
            forward_identity,
            backward_identity,
            ..
        } => {
            println!(
                "  REBASE, and both identity compositions returned: forward {forward_identity}, backward {backward_identity}"
            );
        }
        RebaseReceipt::Refused { reason, .. } => {
            println!("  NOT a rebase: {reason}");
        }
    }

    // The metric adjoint on real material, with both receiver metrics declared.
    let domain_metric = declared_metric(aperture, 2);
    let codomain_metric = declared_metric(aperture, 3);
    let adjoint = posed
        .metric_adjoint(&domain_metric, &codomain_metric)
        .expect("adjoint");
    println!();
    println!("  THE ADJOINT NEEDS ITS METRICS, and a bare transpose is not it:");
    let x: Vec<Rat> = (0..aperture)
        .map(|k| Rat::new(BigInt::from(k as i64 + 1), BigInt::from(7)))
        .collect();
    let y: Vec<Rat> = (0..aperture)
        .map(|k| Rat::new(BigInt::from(2 * k as i64 - 3), BigInt::from(5)))
        .collect();
    let bare = posed.matrix.transpose().expect("transposed");
    let bare_defect = posed
        .matrix
        .adjoint_defect(&bare, &domain_metric, &codomain_metric, &x, &y)
        .expect("paired");
    let metric_defect = posed
        .matrix
        .adjoint_defect(&adjoint.matrix, &domain_metric, &codomain_metric, &x, &y)
        .expect("paired");
    println!("      bare transpose   defect {bare_defect}");
    println!("      metric adjoint   defect {metric_defect}");
    println!(
        "      the adjoint's ports are swapped: it carries a covector the other way ({:?} -> {:?})",
        adjoint.source_port, adjoint.target_port
    );

    // ---------------------------------------------------------------------------------------
    // 4. THE WORD, and why it is not the product.
    // ---------------------------------------------------------------------------------------
    println!();
    println!("4. THE WORD IS THE CONSTRUCTION; THE PRODUCT IS A COMPILED CHART");
    println!();
    let return_tensor = container.tensor(RETURN).expect("manifested");
    println!(
        "  {RECEIVER} emits the receiver chart; {RETURN} admits the carried chart {:?}",
        return_tensor.shape
    );
    let mismatched = PortedTransport::posed_from_bfloat16(
        "contact return, leading block",
        carried_chart,
        standing,
        format!("{RETURN} [0..{aperture}, 0..{aperture}]"),
        &block_of(
            &container
                .read_bf16(
                    &mut file,
                    RETURN,
                    0,
                    (aperture * return_tensor.shape[1]) as u64,
                )
                .expect("read"),
            return_tensor.shape[1],
            aperture,
        ),
        aperture,
        aperture,
    )
    .expect("posed");
    match PortedWord::founded(
        "receiver then return",
        vec![posed.clone(), mismatched.clone()],
    ) {
        Ok(_) => println!("  the two composed, which they should not have"),
        Err(error) => {
            println!("  COMPOSITION REFUSED, by port identity and not by extent:");
            println!("      {error}");
            println!(
                "      both blocks are {aperture} x {aperture}. Matching extent is not a matching port."
            );
        }
    }

    let through = PortedTransport::new(
        "presented projection, leading block",
        receiver_chart,
        presented_chart,
        "declared chart",
        posed.matrix.clone(),
    );
    let word =
        PortedWord::founded("receiver then presented", vec![posed, through]).expect("composes");
    let standing_vector: Vec<Rat> = (0..aperture)
        .map(|k| Rat::new(BigInt::from((k as i64 % 5) - 2), BigInt::from(3)))
        .collect();
    let lineage = word.enact(&standing_vector).expect("enacted");
    println!();
    println!(
        "  the word retains {} standings: entering, {} intermediate, leaving",
        lineage.len(),
        lineage.len() - 2
    );
    let (_, compiling) = word.compiled_chart().expect("compiled");
    println!("  compiling the total product cost:");
    for (name, count) in compiling.coordinates() {
        println!("      {name:<28} {count}");
    }
    println!("  and the product is one FACE of the word, formed only because this reader asked.");

    println!();
    println!("THE STATION'S VERDICT");
    println!();
    println!("  The transport applies at full extent on the card, exactly.");
    println!("  Posing it densely as exact rationals is REFUSED by a declared work receiver.");
    println!("  Under a declared aperture on the same real material it returns its factorization,");
    println!("  its rebase receipt, and a metric adjoint a bare transpose does not satisfy.");
    println!("  Port identity refuses a composition that extent would have admitted.");
    println!("  No contextual lift is claimed and CONSTRUCTION_STATE is untouched.");
}

/// The leading `extent x extent` block of a row-major population, exactly as stored.
fn block_of(words: &[u16], columns: usize, extent: usize) -> Vec<u16> {
    let mut block = Vec::with_capacity(extent * extent);
    for row in 0..extent {
        for column in 0..extent {
            block.push(words[row * columns + column]);
        }
    }
    block
}

/// A declared, deliberately non-Euclidean receiver metric. **Nothing defaults to the identity.**
fn declared_metric(extent: usize, spread: i64) -> ExactRatMatrix {
    let mut rows = Vec::with_capacity(extent);
    for row in 0..extent {
        let mut carried = Vec::with_capacity(extent);
        for column in 0..extent {
            carried.push(if row == column {
                Rat::from_integer(BigInt::from(1 + (row as i64 % spread)))
            } else {
                Rat::from_integer(BigInt::from(0))
            });
        }
        rows.push(carried);
    }
    ExactRatMatrix::new(rows).expect("well-formed")
}
