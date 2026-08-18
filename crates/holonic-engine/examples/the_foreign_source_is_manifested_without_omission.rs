//! **Source-mouth checkpoint: every declared population is manifested and a bounded population is
//! decoded exactly.**
//!
//! Plan: `blueprint/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`.
//!
//! Enumeration is not admission and admission is not a transport lift. This driver enumerates
//! every entry the container declares —
//! **including rank 0, which the prior reader dropped without a refusal** — founds the coverage
//! ledger over the whole population, and reports the three axes that disagree.
//!
//! Run:
//! ```text
//! cargo run -q -p holonic-engine --example the_foreign_source_is_manifested_without_omission -- \
//!     /home/b/models/gemma-4-E4B-it/model.safetensors
//! ```

use std::collections::BTreeMap;

use holonic_engine::foreign_map::{AdmissionClass, ForeignDtype, manifest_safetensors};

fn main() {
    let address = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it/model.safetensors".to_owned());
    let frame = std::env::args().any(|argument| argument == "--declare-frame");

    let (mut file, container) = match manifest_safetensors(&address) {
        Ok(pair) => pair,
        Err(error) => {
            println!("REFUSED: {error}");
            std::process::exit(1);
        }
    };

    println!("THE SOURCE IS MANIFESTED WITHOUT OMISSION");
    println!();
    println!(
        "  address (apparatus, never identity)  {}",
        container.address
    );
    println!(
        "  container species                    {:?}",
        container.species
    );
    println!(
        "  file octets                          {}",
        container.file_octets
    );
    println!(
        "  payload octets                       {}",
        container.payload_octets
    );
    println!(
        "  container metadata                   {:?}",
        container.container_metadata
    );
    println!(
        "  declared populations                 {}",
        container.tensors.len() + container.refused.len()
    );
    println!(
        "  structurally readable tensors        {}",
        container.tensors.len()
    );
    println!(
        "  refused by name                      {}",
        container.refused.len()
    );
    for (name, why) in container.refused.iter().take(8) {
        println!("      {name}  {why:?}");
    }
    let overlaps = container.overlaps();
    println!("  entries claiming the same octets     {}", overlaps.len());
    for (left, right) in overlaps.iter().take(4) {
        println!("      {left} <-> {right}");
    }
    if let Err(error) = container.validate_no_overlaps() {
        println!("REFUSED: {error}");
        std::process::exit(1);
    }

    println!();
    println!("THE THREE AXES, AND TWO OF THEM DISAGREE");
    println!();
    let census = container.rank_census();
    let total_octets: u64 = census.values().map(|(_, octets)| *octets).sum();
    let total_count: usize = census.values().map(|(count, _)| *count).sum();
    println!("    rank    entries              octets     share of octets");
    for (rank, (count, octets)) in &census {
        let per_ten_thousand = if total_octets == 0 {
            0
        } else {
            octets * 10_000 / total_octets
        };
        println!(
            "      {rank:>2}    {count:>7}  {octets:>18}     {}.{:02} in 100",
            per_ten_thousand / 100,
            per_ten_thousand % 100
        );
    }
    println!("    total   {total_count:>7}  {total_octets:>18}");

    let mut dtypes: BTreeMap<String, usize> = BTreeMap::new();
    for tensor in container.tensors.values() {
        *dtypes
            .entry(tensor.dtype.declared().to_owned())
            .or_insert(0) += 1;
    }
    println!();
    println!("  declared element species             {dtypes:?}");
    let exact = container
        .tensors
        .values()
        .filter(|tensor| tensor.dtype.exactly_decodable())
        .count();
    println!(
        "  exactly decodable at their own grain {exact} of {}",
        container.tensors.len()
    );
    println!("  (the pre-quantization preimage of a stored codeword remains an unresolved fibre)");

    println!();
    println!("THE TWO COVERAGE AXES, FOUNDED OVER THE WHOLE POPULATION");
    println!();
    let mut ledger = container.found_ledger();
    println!("  every readable entry starts manifested-only and transport-unposed");
    for (class, count) in ledger.admission_census() {
        println!("      admission {:<22} {count}", class.name());
    }
    for (class, count) in ledger.transport_census() {
        println!("      transport {:<22} {count}", class.name());
    }

    // Decode every rank-0 and rank-1 population exactly. These are 1,485 of 2,130 entries and
    // 0.009% of the octets. Which are load-bearing belongs to the actual operator diagram, not to
    // their rank or source name, so this mouth does not declare that axis.
    println!();
    println!("SOURCE VALUES DECODED EXACTLY — the populations a byte census calls negligible");
    println!();
    let mut small: Vec<&str> = container
        .tensors
        .values()
        .filter(|tensor| tensor.rank() <= 1 && tensor.dtype == ForeignDtype::Bf16)
        .map(|tensor| tensor.name.as_str())
        .collect();
    small.sort_unstable();
    let mut decoded = 0usize;
    let mut octets = 0u64;
    let mut refused = Vec::new();
    for name in &small {
        let elements = container
            .tensor(name)
            .expect("manifested")
            .elements()
            .expect("manifested extent was validated");
        match container.decode_bf16(&mut file, name, 0, elements) {
            Ok(data) => {
                decoded += 1;
                octets += elements * 2;
                debug_assert_eq!(data.len() as u64, elements);
                ledger.place_admission(name, AdmissionClass::DecodedExact);
            }
            Err(error) => refused.push((*name, error.to_string())),
        }
    }
    println!("  rank 0 and rank 1 BF16 populations    {}", small.len());
    println!("  decoded exactly, no remainder         {decoded}");
    println!("  octets they occupy                    {octets}");
    println!("  refused                               {}", refused.len());
    for (name, why) in refused.iter().take(4) {
        println!("      {name}  {why}");
    }

    // Exhibit a handful so the decode is inspectable rather than asserted.
    println!();
    println!("  a sample, as exact rationals — the codeword IS the value, not an approximation:");
    for name in small.iter().take(3) {
        let data = container
            .decode_bf16(&mut file, name, 0, 1)
            .expect("decoded above");
        let datum = &data[0];
        println!(
            "      {name}\n          significand {} x 2^{}  -> {}",
            datum.significand,
            datum.ulp_exponent,
            datum.value()
        );
    }

    println!();
    println!("THE BOUND, RETURNED RATHER THAN PROMOTED");
    println!();
    println!("  decoded populations are not thereby transports; every transport remains unposed");
    println!(
        "  ledger declares {} of {} declared populations",
        ledger.declared(),
        container.tensors.len() + container.refused.len()
    );
    for (class, count) in ledger.admission_census() {
        println!("      admission {:<22} {count}", class.name());
    }
    for (class, count) in ledger.transport_census() {
        println!("      transport {:<22} {count}", class.name());
    }

    if frame {
        println!();
        println!("THE APPARATUS FRAME — a digest declares which byte occurrence was read");
        match container.declare_source_frame(&mut file) {
            Ok(digest) => println!("  sha256  {digest}"),
            Err(error) => println!("  REFUSED  {error}"),
        }
        println!("  this is a frame declaration and never an identity; nothing is keyed by it");
    }
}
