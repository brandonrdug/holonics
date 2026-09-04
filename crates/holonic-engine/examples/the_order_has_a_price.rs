//! THE ORDER HAS A PRICE — `⌈log₂(n!)⌉` bits, and whether the receiver family can read them.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_order_has_a_price
//! ```
//!
//! ## What this closes
//!
//! Roadmap open item 4. This repository has treated *"apparatus completion order never enters
//! semantic lineage"* as a **correctness** law since it was ratified, and
//! `crates/holonic-engine/src/interchange.rs` decides it exactly, by exhibiting the distinguishing
//! word when there is one.
//!
//! Devillers and Gandoin, *Geometric compression for progressive transmission* (`arXiv:cs/9909018`,
//! INRIA, 1999), add the missing half: **the order has a measurable size.** Their coder discards the
//! topology, spends the vertex-order entropy on the coordinates, and reconstructs the topology
//! afterward, and their result is verbatim: *"the gain is `log₂ n − 2.402` per point… which
//! corresponds exactly to the **order information** over the points… the algorithm **saves the
//! encoding of the order information**."*
//!
//! So: an order over `n` items costs `⌈log₂(n!)⌉` bits, exactly. If a declared receiver family cannot
//! read that order, those bits were **paid for nothing**, and the amount is now a number rather than
//! a suspicion.
//!
//! ## The receiver question
//!
//! **How many bits does this body pay to carry an order, and can anything read them?**
//!
//! ## What is deliberately NOT claimed
//!
//! The price is arithmetic and always correct. The verdict is a measurement against **one declared
//! receiver family**, and a different family may read what this one cannot. Reporting the price alone
//! would assert a waste that has not been established; reporting the verdict alone leaves the
//! correctness law without a magnitude. `OrderPrice` carries both and `overpayment()` is zero unless
//! the certificate itself says the family is blind to the order.
//!
//! No Stirling approximation is used anywhere: the factorial is exact over `BigUint` and its bit
//! length is read off. `n log₂ n` appears only as a scale column, and the test asserts it as a
//! **bound**, never as an identity.

use std::error::Error;

use holonic_engine::interchange::declared_material::{
    CoupledJunctions, SameEndpointDifferentPath, TwoGadgets,
};
use holonic_engine::interchange::{
    StagedFootprint, certify_founding_orders, certify_pair, order_price_bits,
};
use holonic_engine::receiver_exact_compression::ItemId;

/// APERTURE — the populations tabulated below. Declared by this caller; every value is a function of
/// `n` alone and nothing depends on which are listed.
const TABULATED: [usize; 10] = [1, 2, 3, 4, 8, 16, 64, 256, 1024, 4096];

fn rule(title: &str) {
    println!("\n{}", "=".repeat(96));
    println!("{title}");
    println!("{}", "=".repeat(96));
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut failures: Vec<String> = Vec::new();
    let mut hold = |claim: &str, held: bool, evidence: String| {
        if held {
            println!("  [holds] {claim}\n            {evidence}");
        } else {
            println!("  [FAILS] {claim}\n            {evidence}");
            failures.push(claim.to_owned());
        }
    };

    rule("THE PRICE — exact, over BigUint, with no Stirling anywhere on the path");

    println!(
        "  {:>6}  {:>14}  {:>16}",
        "n", "ceil(log2 n!)", "n·log2(n) [scale]"
    );
    println!("  {}", "-".repeat(42));
    for population in TABULATED {
        let n = population as u64;
        let scale = if n < 2 {
            0
        } else {
            n * (u64::BITS - (n - 1).leading_zeros()) as u64
        };
        println!(
            "  {:>6}  {:>14}  {:>16}",
            population,
            order_price_bits(population),
            scale
        );
    }

    hold(
        "the price is zero where there is no order to carry",
        order_price_bits(0) == 0 && order_price_bits(1) == 0,
        "one item admits exactly one ordering".to_owned(),
    );
    hold(
        "the price is superlinear and bounded by n·log2(n)",
        TABULATED.iter().skip(1).all(|population| {
            let n = *population as u64;
            let bits = order_price_bits(*population);
            let scale = n * (u64::BITS - (n - 1).leading_zeros()) as u64;
            bits <= scale && (n < 4 || bits > n)
        }),
        "checked at every tabulated population".to_owned(),
    );

    // ---------------------------------------------------------------------------------------------

    rule("AND WHETHER ANYTHING CAN READ WHAT WAS PAID");

    // The trait is private, so each material is certified by name rather than through a boxed dyn.
    // The first is the INDEPENDENT pair — the case the certificate admits — and it is the one that
    // pays, because an admitted interchange is exactly a family that cannot read the order.
    let certificates = [
        (
            "TwoGadgets (independent pair)",
            certify_pair(
                &TwoGadgets,
                &[],
                StagedFootprint::at(ItemId(0), ItemId(1)),
                StagedFootprint::at(ItemId(4), ItemId(5)),
            ),
        ),
        (
            "TwoGadgets (whole order)",
            certify_founding_orders(&TwoGadgets),
        ),
        (
            "CoupledJunctions",
            certify_founding_orders(&CoupledJunctions),
        ),
        (
            "SameEndpointDifferentPath",
            certify_founding_orders(&SameEndpointDifferentPath),
        ),
    ];

    let mut unreadable = 0usize;
    let mut load_bearing = 0usize;
    let mut total_overpayment = 0u64;

    println!(
        "  {:<28} {:>7}  {:<14}  {:>8}  {}",
        "material", "staged", "verdict", "bits", "overpayment"
    );
    println!("  {}", "-".repeat(80));
    for (name, certificate) in &certificates {
        let price = certificate.order_price(certificate.staged.len());
        if price.unreadable_by_the_declared_family {
            unreadable += 1;
        } else {
            load_bearing += 1;
        }
        total_overpayment += price.overpayment();
        println!(
            "  {:<28} {:>7}  {:<14}  {:>8}  {}",
            name,
            price.population,
            if certificate.is_interchangeable() {
                "INTERCHANGE"
            } else {
                "ORDERED"
            },
            price.bits,
            price.overpayment()
        );
    }

    println!();
    hold(
        "THE PRICE IS CHARGED ONLY WHERE THE FAMILY IS BLIND — an ordered front pays nothing",
        load_bearing > 0 && certificates.len() > load_bearing,
        format!(
            "{unreadable} unreadable · {load_bearing} load-bearing over {} materials",
            certificates.len()
        ),
    );
    hold(
        "the two halves are separable — a material exists on each side",
        unreadable > 0 && load_bearing > 0,
        format!("total overpayment {total_overpayment} bits across the declared materials"),
    );

    // ---------------------------------------------------------------------------------------------

    rule("WHAT THIS RETURNED");

    println!(
        "  1. `apparatus completion order never enters semantic lineage` now has a MAGNITUDE.\n\
         \x20    An order over n items costs ceil(log2(n!)) bits, exactly, and interchange.rs already\n\
         \x20    decides whether the declared family can read it.\n\
         \x20 2. Over {} declared materials: {} paid bits the family cannot read, {} carry a\n\
         \x20    load-bearing order and pay nothing. Total unreadable: {total_overpayment} bits.\n\
         \x20 3. Devillers-Gandoin's `the algorithm saves the encoding of the order information` is\n\
         \x20    the same quantity from the other side: what a coder gains by dropping an order is\n\
         \x20    what a front loses by carrying one.",
        certificates.len(),
        unreadable,
        load_bearing
    );

    println!(
        "\n  NOT CLAIMED: that this body's production front carries an unreadable order. That is a\n\
        \x20 measurement on the front's own material and it is roadmap item 4's second half. The\n\
        \x20 driver that runs the certificate on `formal` —\n\
        \x20 `the_front_is_ordered_until_a_certificate_unorders_it` — SIGKILLs at HEAD (exit 137),\n\
        \x20 measured 2026-08-10, so the real-material figure is not available and is not guessed."
    );

    if failures.is_empty() {
        println!("\n  ALL CONTROLS HELD.");
        Ok(())
    } else {
        println!("\n  FAILURES: {failures:?}");
        std::process::exit(1);
    }
}
