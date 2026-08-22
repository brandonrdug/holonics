//! **Deed H1: the partition is typed and the reduction is a junction.**
//!
//! Plan: `blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md` §2
//! (existing owners composed), §3.2 `TilingReceipt`, §3.3 `ReductionReceipt`, §3.4
//! `PressureReceipt`, §4.3, §8 Deed H1, §11. Audit: the warp-scheduler record's §6 and §8.
//!
//! # What runs here, and what does not
//!
//! Everything is **CPU-side exact**: `Rat`, `BigInt`, `BigUint`, `i64` alignments. **No device is
//! mounted**, so the cover is `HardwareCover::cpu_only()`, the device chart's lane faces are
//! *unknown* rather than zero, and every apparatus capacity below is a **declared** aperture rather
//! than a measurement. H2 enacts this on the card; H1 owes the receipts.
//!
//! The Gemma shapes are real and are read from the source's own header. One real `bf16` slice of
//! each of two populations is read through the existing mouth — `foreign_map::manifest_safetensors`
//! then `ForeignContainer::read_rows_bf16` then `embedding_fiber::align_bfloat16` — so the reduction
//! equality is shown on real words and not on a fixture.
//!
//! ```text
//! cargo run --release -q -p holonic-engine \
//!   --example the_partition_is_typed_and_the_reduction_is_a_junction -- \
//!   /home/b/models/gemma-4-E4B-it
//! ```

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs;

use holonic_engine::embedding_fiber::align_bfloat16;
use holonic_engine::exact_linear::ExactRatMatrix;
use holonic_engine::foreign_map::manifest_safetensors;
use holonic_engine::hardware_cover::HardwareCover;
use holonic_engine::reduction_junction::{
    DirectedRounding, PartialTerm, ReductionDefect, ReductionJunction, ReductionReceipt,
    ReductionWord, RoundingPolicy,
};
use holonic_engine::section_partition::{
    DeclaredSpecies, DemandFace, PartialAddress, PartitionDefect, ReadRegion, ResourceDeclaration,
    SectionCell, SectionLineage, SectionPartition, SectionRegion, SectionShape, TilingReceipt,
};
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;
use relational_geometry::Rat;

const OUTPUT: &str = "output/the_partition_is_typed_and_the_reduction_is_a_junction";
const LAYER: usize = 0;

/// The receiver's declared boundary grain, `2^-BOUNDARY`. A **declaration of this driver**, like the
/// ceiling in a `WorkBudget`; nothing measured it.
const DECLARED_BOUNDARY_EXPONENT: u32 = 24;
/// The declared width of the accumulator H2 will carry, in bits. A declaration, not a measurement.
const DECLARED_OVERFLOW_APERTURE: u64 = 256;
/// The greatest fan-out this reading founds inside `receiver_current`. Above it the enacted current
/// face is `BeyondAperture` — unknown, never zero.
const DECLARED_ENACTMENT_APERTURE: u64 = 4096;
/// A declared transfer unit: how many section entries one boundary sector carries. **Declared by
/// this driver**; no device was consulted in H1.
const DECLARED_SECTOR_ENTRIES: u64 = 16;
/// Which row of the embedding population the reduction contracts against. **The first row the
/// header offers** — a choice made by the source's own layout rather than by this driver. It read
/// `18_740` until 2026-08-19, which was a token ordinal carried over from another driver and had no
/// occasion here.
const SOURCE_ROW: usize = 0;

struct Control {
    number: usize,
    name: &'static str,
    perturbation: &'static str,
    verdict: &'static str,
    control_says: String,
    perturbed_says: String,
}

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let mut form = String::new();
    let mut controls: Vec<Control> = Vec::new();

    let (mut file, container) = match manifest_safetensors(&format!("{root}/model.safetensors")) {
        Ok(pair) => pair,
        Err(error) => {
            println!("the source refused: {error}");
            std::process::exit(1);
        }
    };

    let cover = HardwareCover::cpu_only();
    let lanes = cover.cpu().resident_lanes().max(1);

    line(
        &mut form,
        "DEED H1 — THE PARTITION IS TYPED AND THE REDUCTION IS A JUNCTION",
    );
    line(&mut form, "");
    line(
        &mut form,
        "the section partition carries coordinate regions with completeness and disjointness COMPUTED;",
    );
    line(
        &mut form,
        "the shared-output junction carries the fixed word, the per-node width, one directed",
    );
    line(
        &mut form,
        "outward rounding at the declared boundary, and the adjoint return into every partial chart.",
    );
    line(&mut form, "");
    line(&mut form, "APPARATUS FRAME");
    line(
        &mut form,
        &format!("  source                            {root}"),
    );
    line(
        &mut form,
        "  cover                             HardwareCover::cpu_only() — NO DEVICE IS MOUNTED IN H1",
    );
    line(
        &mut form,
        &format!(
            "  cpu declaration, resident lanes   {lanes}   (std::thread::available_parallelism)"
        ),
    );
    line(
        &mut form,
        "  device chart lane faces           UNKNOWN — not consulted, and not zero",
    );
    line(
        &mut form,
        "  arithmetic                        exact: Rat / BigInt / BigUint / aligned i64. No float.",
    );
    line(
        &mut form,
        &format!("  declared boundary grain           2^-{DECLARED_BOUNDARY_EXPONENT}"),
    );
    line(
        &mut form,
        &format!("  declared overflow aperture        {DECLARED_OVERFLOW_APERTURE} bits"),
    );
    line(
        &mut form,
        &format!(
            "  declared enactment aperture       {DECLARED_ENACTMENT_APERTURE} passages per site"
        ),
    );
    line(
        &mut form,
        &format!("  declared transfer sector          {DECLARED_SECTOR_ENTRIES} section entries"),
    );
    line(
        &mut form,
        "  declared characteristic delays    1 / 2 / 3 chronology steps for the three species below.",
    );
    line(
        &mut form,
        "                                    DECLARED by this driver, in the order the species are named;",
    );
    line(
        &mut form,
        "                                    no apparatus was measured for any of them.",
    );
    line(
        &mut form,
        "  declared species capacities       every C is the caller's DeclaredSpecies field. The owner never",
    );
    line(
        &mut form,
        "                                    reads the cover; this driver couples C to the cpu's own lane count",
    );
    line(
        &mut form,
        "                                    BY HAND, and that coupling is the driver's and not the owner's.",
    );
    line(
        &mut form,
        &format!(
            "  source row for the reduction      row {SOURCE_ROW} of the embedding population — the FIRST row"
        ),
    );
    line(
        &mut form,
        "                                    the header offers, so the choice is the header's and not this driver's.",
    );
    line(&mut form, "");

    // -------------------------------------------------------------------------------------------
    // 1. The real Gemma shapes, read from the source's own header.
    // -------------------------------------------------------------------------------------------
    let maps = [
        (
            "q_proj",
            format!("model.language_model.layers.{LAYER}.self_attn.q_proj.weight"),
        ),
        (
            "o_proj",
            format!("model.language_model.layers.{LAYER}.self_attn.o_proj.weight"),
        ),
        (
            "gate_proj",
            format!("model.language_model.layers.{LAYER}.mlp.gate_proj.weight"),
        ),
        (
            "down_proj",
            format!("model.language_model.layers.{LAYER}.mlp.down_proj.weight"),
        ),
    ];
    let mut shapes: Vec<(&str, String, usize, usize)> = Vec::new();
    line(&mut form, "THE REAL SHAPES, FROM THE SOURCE HEADER");
    for (short, name) in &maps {
        match container.tensor(name) {
            Ok(tensor) if tensor.shape.len() == 2 => {
                line(
                    &mut form,
                    &format!(
                        "  {short:<12} {name}\n                 shape {:?}  dtype {:?}",
                        tensor.shape, tensor.dtype
                    ),
                );
                shapes.push((short, name.clone(), tensor.shape[0], tensor.shape[1]));
            }
            Ok(tensor) => line(
                &mut form,
                &format!(
                    "  {short:<12} OPEN — rank {} is not a map",
                    tensor.shape.len()
                ),
            ),
            Err(error) => line(&mut form, &format!("  {short:<12} OPEN — {error}")),
        }
    }
    line(&mut form, "");

    // -------------------------------------------------------------------------------------------
    // 2. The tiling receipt on every shape at T in {1, 5, 16}.
    // -------------------------------------------------------------------------------------------
    line(
        &mut form,
        "TILING RECEIPTS — the disjoint output partition (H.5), one cell per resident lane",
    );
    line(
        &mut form,
        "  cells are column bands of the output section; the last band is a NONMULTIPLE TAIL.",
    );
    line(
        &mut form,
        "  every cell reads the same token rows: one shared immutable standing, computed.",
    );
    line(&mut form, "");
    let mut first_receipt: Option<TilingReceipt> = None;
    for (short, _, out_features, in_features) in &shapes {
        for tokens in [1usize, 5, 16] {
            let partition = output_band_partition(*out_features, *in_features, tokens, lanes);
            let resources = declared_resources(lanes);
            match partition.certify(&cover, &[], &resources, "h1_section_partition") {
                Ok(receipt) => {
                    let idle: BigUint = receipt
                        .cover
                        .work
                        .iter()
                        .map(|work| work.idle_lanes.clone())
                        .sum();
                    let occupied: BigUint = receipt
                        .cover
                        .work
                        .iter()
                        .map(|work| work.occupied_lanes.clone())
                        .sum();
                    line(
                        &mut form,
                        &format!(
                            "  {short:<10} T={tokens:<3} section {} x {}  cells {:<4} \
                             complete {}  disjoint {}  pairs {}  interchange {}",
                            receipt.shape.rows,
                            receipt.shape.width,
                            receipt.cells.len(),
                            receipt.completeness.complete,
                            receipt.disjointness.disjoint,
                            receipt.disjointness.pairs_checked,
                            if receipt.is_interchangeable() {
                                "INTERCHANGEABLE"
                            } else {
                                "ORDERED"
                            },
                        ),
                    );
                    let tail = receipt.cells.last().map(|cell| cell.write);
                    line(
                        &mut form,
                        &format!(
                            "                  covered {}/{} entries · shared reads {} \
                             (immutable {}) · pairwise halo entries {} · tail {}",
                            receipt.completeness.covered_extent,
                            receipt.completeness.section_extent,
                            receipt.shared_reads.len(),
                            receipt
                                .shared_reads
                                .iter()
                                .filter(|shared| shared.immutable)
                                .count(),
                            receipt
                                .halo
                                .iter()
                                .map(|(_, _, region)| region.extent())
                                .sum::<u64>(),
                            tail.map(|region| region.to_string()).unwrap_or_default(),
                        ),
                    );
                    line(
                        &mut form,
                        &format!(
                            "                  cover: occupied {:?} · members {} · occupied lanes {} \
                             · idle lanes {} · barriers {}",
                            receipt.cover.occupied,
                            receipt
                                .cover
                                .work
                                .iter()
                                .map(|work| work.members.clone())
                                .sum::<BigUint>(),
                            occupied,
                            idle,
                            receipt.cover.barriers.len(),
                        ),
                    );
                    if first_receipt.is_none() {
                        first_receipt = Some(receipt);
                    }
                }
                Err(defects) => {
                    line(&mut form, &format!("  {short:<10} T={tokens:<3} REFUSED"));
                    for defect in defects.iter().take(4) {
                        line(&mut form, &format!("                  {defect}"));
                    }
                }
            }
        }
    }
    line(&mut form, "");

    // -------------------------------------------------------------------------------------------
    // 3. The pressure receipt, one covector per species, on one real shape.
    // -------------------------------------------------------------------------------------------
    if let Some(receipt) = &first_receipt {
        line(
            &mut form,
            "PRESSURE — one covector coordinate per resource species, per cell. NEVER SUMMED.",
        );
        line(
            &mut form,
            "  R = ceil(N/C) is receiver_current's own service dilation, taken from a founded and",
        );
        line(
            &mut form,
            "  radiated ExactReceiverCurrentLaw wherever the demand is inside the declared aperture.",
        );
        for cell in receipt.pressure.iter().take(2) {
            line(&mut form, &format!("  cell {}", cell.cell));
            for species in &cell.species {
                line(
                    &mut form,
                    &format!(
                        "    {:<28} N {:<10} C {:<8} R {:<6} boundary residual {:<8} reflected {:<10} {}",
                        species.species,
                        species.incoming,
                        species.capacity,
                        species.service_rounds,
                        species.boundary_residual,
                        species.reflected,
                        enacted_face(&species.enacted),
                    ),
                );
            }
        }
        line(&mut form, "");
    }

    // -------------------------------------------------------------------------------------------
    // 4. The reduction junction on REAL WORDS: the inner/K partition of one output coordinate.
    // -------------------------------------------------------------------------------------------
    line(
        &mut form,
        "REDUCTION JUNCTION ON REAL WORDS — the inner/K partition (H.6)",
    );
    let map_name = format!("model.language_model.layers.{LAYER}.self_attn.q_proj.weight");
    let row_name = "model.language_model.embed_tokens.weight".to_owned();
    let mut real_receipt: Option<(ReductionReceipt, ReductionJunction)> = None;
    match build_real_junction(&mut file, &container, &map_name, &row_name, lanes) {
        Ok((junction, bands, refused)) => {
            line(
                &mut form,
                &format!(
                    "  map    {map_name}\n  rows   {row_name}\n  \
                     inner axis K = {}  partials {}  bands refused by the mouth {}",
                    junction.inner_shape.width,
                    junction.partials.len(),
                    refused
                ),
            );
            line(
                &mut form,
                &format!(
                    "  carrier grain 2^-{}  boundary grain 2^-{}  aperture {} bits  word {}",
                    junction.carrier_exponent,
                    junction.boundary_exponent,
                    junction.overflow_aperture,
                    junction.word.written().chars().take(48).collect::<String>()
                ),
            );
            line(
                &mut form,
                &format!("  band width {bands} columns, last band is the nonmultiple tail"),
            );
            match junction.certify() {
                Ok(receipt) => {
                    line(&mut form, "");
                    line(
                        &mut form,
                        &format!(
                            "  declared word   peak width {:>5} bits · span {:>3} · nodes {:>4} · roundings {}",
                            receipt.declared.peak_width_bits,
                            receipt.declared.dependency_span,
                            receipt.declared.nodes.len(),
                            receipt.declared.roundings
                        ),
                    );
                    line(
                        &mut form,
                        &format!(
                            "  reversed control peak width {:>4} bits · span {:>3} · nodes {:>4} · roundings {}",
                            receipt.reversed.peak_width_bits,
                            receipt.reversed.dependency_span,
                            receipt.reversed.nodes.len(),
                            receipt.reversed.roundings
                        ),
                    );
                    let differing_nodes = receipt
                        .declared
                        .nodes
                        .iter()
                        .zip(&receipt.reversed.nodes)
                        .filter(|(left, right)| left.width_bits != right.width_bits)
                        .count();
                    line(
                        &mut form,
                        &format!("  words agree on the value        {}", receipt.words_agree),
                    );
                    line(
                        &mut form,
                        &format!(
                            "  nodes standing at DIFFERENT widths between the two words   {} of {}",
                            differing_nodes,
                            receipt.declared.nodes.len()
                        ),
                    );
                    line(
                        &mut form,
                        &format!(
                            "  exact value before rounding    {}",
                            short_rat(&receipt.declared.value[0])
                        ),
                    );
                    line(
                        &mut form,
                        &format!(
                            "  boundary value (2^-{})        {}",
                            receipt.boundary_exponent, receipt.boundary_value[0]
                        ),
                    );
                    line(
                        &mut form,
                        &format!(
                            "  boundary residual              {}",
                            short_rat(&receipt.boundary_residual[0])
                        ),
                    );
                    line(
                        &mut form,
                        &format!(
                            "  roundings                      {} — COUNTED round_outward invocations on the certified",
                            receipt.roundings
                        ),
                    );
                    line(
                        &mut form,
                        "                                 path: one per output coordinate, at the declared boundary, and",
                    );
                    line(
                        &mut form,
                        "                                 none inside the tree. It was the literal 1 until 2026-08-19.",
                    );
                    line(
                        &mut form,
                        &format!(
                            "  inner partition: uncovered {} · overlaps {}",
                            receipt.inner_uncovered.len(),
                            receipt.inner_overlaps.len()
                        ),
                    );
                    line(
                        &mut form,
                        "  the first four nodes of each word, with the width they stood at:",
                    );
                    for (which, reading) in [
                        ("declared", &receipt.declared),
                        ("reversed", &receipt.reversed),
                    ] {
                        for node in reading
                            .nodes
                            .iter()
                            .filter(|node| node.leaves.len() > 1)
                            .take(3)
                        {
                            line(
                                &mut form,
                                &format!(
                                    "    {which:<9} leaves {:>3}..{:<3} depth {:<3} width {:>5} bits",
                                    node.leaves.first().copied().unwrap_or(0),
                                    node.leaves.last().copied().unwrap_or(0),
                                    node.depth,
                                    node.width_bits
                                ),
                            );
                        }
                    }
                    line(
                        &mut form,
                        "  the adjoint return into every partial chart, under the DECLARED metrics:",
                    );
                    line(
                        &mut form,
                        &format!(
                            "    partials reached               {} of {}",
                            receipt.adjoints.len(),
                            receipt.partials.len()
                        ),
                    );
                    line(
                        &mut form,
                        &format!(
                            "    every adjoint defect zero      {}",
                            receipt
                                .adjoints
                                .iter()
                                .all(|adjoint| adjoint.defect.is_zero())
                        ),
                    );
                    line(
                        &mut form,
                        &format!(
                            "    bare-transpose defects nonzero {} of {}",
                            receipt
                                .adjoints
                                .iter()
                                .filter(|adjoint| !adjoint.bare_transpose_defect.is_zero())
                                .count(),
                            receipt.adjoints.len()
                        ),
                    );
                    line(
                        &mut form,
                        &format!(
                            "    exact work: additions {} · multiplications {} · entries {} · peak bits {} · span {}",
                            receipt.work.additions,
                            receipt.work.multiplications,
                            receipt.work.entries_written,
                            receipt.work.peak_bits,
                            receipt.work.dependency_span
                        ),
                    );
                    real_receipt = Some((receipt, junction));
                }
                Err(defects) => {
                    line(&mut form, "  REFUSED");
                    for defect in defects.iter().take(6) {
                        line(&mut form, &format!("    {defect}"));
                    }
                }
            }
        }
        Err(reason) => line(&mut form, &format!("  OPEN — the mouth refused: {reason}")),
    }
    line(&mut form, "");

    // -------------------------------------------------------------------------------------------
    // 5. The seven controls, each with the perturbation that makes it fail.
    // -------------------------------------------------------------------------------------------
    // A failed header read REFUSES the controls; it does not run them on authored shapes. The
    // `.unwrap_or((2048, 2560))` that stood here would have reported seven verdicts about a section
    // no source declared.
    let Some((out_features, in_features)) = shapes
        .first()
        .map(|(_, _, rows, columns)| (*rows, *columns))
    else {
        println!(
            "the source declared none of the four maps, so the controls have no material and are \
             not run. This is a refusal, not a zero."
        );
        std::process::exit(1);
    };
    let tokens = 5usize;
    let resources = declared_resources(lanes);

    // --- control 1 --------------------------------------------------------------------------
    {
        let base = output_band_partition(out_features, in_features, tokens, lanes);
        let control = base.certify(&cover, &[], &resources, "h1_control_one");
        let mut perturbed = base.clone();
        let victim = perturbed.cells[1].write;
        perturbed
            .populations
            .insert("section".to_owned(), perturbed.shape);
        perturbed.cells[0].reads.push(ReadRegion {
            population: "section".to_owned(),
            region: victim,
        });
        let perturbed = perturbed.certify(&cover, &[], &resources, "h1_control_one");
        controls.push(Control {
            number: 1,
            name: "disjoint outputs certify",
            perturbation: "cell 0 additionally READS the output region cell 1 writes",
            verdict: verdict(control.is_ok() && perturbed.is_err()),
            control_says: match &control {
                Ok(receipt) => format!(
                    "{} cells, {} pairs checked, verdict {:?}, complete {}",
                    receipt.cells.len(),
                    receipt.disjointness.pairs_checked,
                    receipt.certificate.verdict,
                    receipt.completeness.complete
                ),
                Err(defects) => format!("REFUSED: {}", first_partition_defect(defects)),
            },
            perturbed_says: match &perturbed {
                Ok(_) => "certified — the control is vacuous".to_owned(),
                Err(defects) => first_partition_defect(defects),
            },
        });
    }

    // --- control 2 --------------------------------------------------------------------------
    {
        let base = output_band_partition(out_features, in_features, tokens, lanes);
        let control = base.certify(&cover, &[], &resources, "h1_control_two");
        let mut perturbed = base.clone();
        perturbed
            .populations
            .insert("section".to_owned(), perturbed.shape);
        for cell in &mut perturbed.cells {
            cell.reads.push(ReadRegion {
                population: "section".to_owned(),
                region: perturbed_shape_region(perturbed.shape),
            });
        }
        let perturbed = perturbed.certify(&cover, &[], &resources, "h1_control_two");
        controls.push(Control {
            number: 2,
            name: "shared immutable input certifies",
            perturbation:
                "the shared read moves into the section's own population, which the cells write",
            verdict: verdict(control.is_ok() && perturbed.is_err()),
            control_says: match &control {
                Ok(receipt) => format!(
                    "{} pairwise shared read regions, {} of them immutable; the whole {} x {} token \
                     standing is read by every cell",
                    receipt.shared_reads.len(),
                    receipt
                        .shared_reads
                        .iter()
                        .filter(|shared| shared.immutable)
                        .count(),
                    tokens,
                    in_features
                ),
                Err(defects) => format!("REFUSED: {}", first_partition_defect(defects)),
            },
            perturbed_says: match &perturbed {
                Ok(_) => "certified — the control is vacuous".to_owned(),
                Err(defects) => defects
                    .iter()
                    .find_map(|defect| match defect {
                        PartitionDefect::SharedReadIsWritten { .. } => Some(defect.to_string()),
                        _ => None,
                    })
                    .unwrap_or_else(|| first_partition_defect(defects)),
            },
        });
    }

    // --- control 3 --------------------------------------------------------------------------
    {
        let shape = SectionShape::of(tokens, out_features, 0);
        let whole = shape.whole();
        let lineage = SectionLineage {
            source: "shared-output".to_owned(),
            population: "section".to_owned(),
            body: "h1".to_owned(),
        };
        let without = SectionPartition {
            lineage: lineage.clone(),
            shape,
            populations: BTreeMap::new(),
            cells: vec![
                SectionCell {
                    index: 0,
                    write: whole,
                    reads: Vec::new(),
                    partial_of: None,
                },
                SectionCell {
                    index: 1,
                    write: whole,
                    reads: Vec::new(),
                    partial_of: None,
                },
            ],
        }
        .certify(&cover, &[], &resources, "h1_control_three");
        let junction = shared_output_junction(whole);
        let with = SectionPartition {
            lineage,
            shape,
            populations: BTreeMap::new(),
            cells: vec![
                SectionCell {
                    index: 0,
                    write: whole,
                    reads: Vec::new(),
                    partial_of: Some(PartialAddress {
                        junction: 0,
                        partial: 0,
                    }),
                },
                SectionCell {
                    index: 1,
                    write: whole,
                    reads: Vec::new(),
                    partial_of: Some(PartialAddress {
                        junction: 0,
                        partial: 1,
                    }),
                },
            ],
        }
        .certify(
            &cover,
            &[junction.output_face()],
            &resources,
            "h1_control_three",
        );
        controls.push(Control {
            number: 3,
            name: "a shared output refuses without a ReductionReceipt and certifies with one",
            perturbation: "the SAME two cells, with and without the declared junction",
            verdict: verdict(without.is_err() && with.is_ok()),
            control_says: match &with {
                Ok(receipt) => format!(
                    "WITH the junction: complete {} · disjoint {} · verdict {:?} · the junction owns {}",
                    receipt.completeness.complete,
                    receipt.disjointness.disjoint,
                    receipt.certificate.verdict,
                    whole
                ),
                Err(defects) => format!("REFUSED: {}", first_partition_defect(defects)),
            },
            perturbed_says: match &without {
                Ok(_) => "certified — the control is vacuous".to_owned(),
                Err(defects) => defects
                    .iter()
                    .find_map(|defect| match defect {
                        PartitionDefect::RegionsOverlap { .. } => Some(defect.to_string()),
                        _ => None,
                    })
                    .map(|overlap| {
                        let footprint = defects
                            .iter()
                            .find_map(|defect| match defect {
                                PartitionDefect::FootprintRefused { region: Some(region), .. } => {
                                    Some(region.to_string())
                                }
                                _ => None,
                            })
                            .unwrap_or_else(|| "-".to_owned());
                        format!("{overlap}; the footprint certificate meets first at {footprint}")
                    })
                    .unwrap_or_else(|| first_partition_defect(defects)),
            },
        });
    }

    // --- control 4 --------------------------------------------------------------------------
    {
        let base = output_band_partition(out_features, in_features, tokens, lanes);
        let control = base.certify(&cover, &[], &resources, "h1_control_four");
        let mut incomplete = base.clone();
        incomplete.cells.pop();
        let incomplete = incomplete.certify(&cover, &[], &resources, "h1_control_four");
        let mut overlapping = base.clone();
        overlapping.cells[1].write.column_from = overlapping.cells[0].write.column_from;
        let overlapping = overlapping.certify(&cover, &[], &resources, "h1_control_four");
        let mut foreign = base.clone();
        if let Some(cell) = foreign.cells.last_mut() {
            cell.write.column_to += 1;
        }
        let foreign = foreign.certify(&cover, &[], &resources, "h1_control_four");
        controls.push(Control {
            number: 4,
            name: "an incomplete, an overlapping and a foreign tile each refuse by name",
            perturbation:
                "(a) the last cell is dropped; (b) cell 1's band is widened onto cell 0's; (c) the \
                 last cell's band runs one column past the section",
            verdict: verdict(
                control.is_ok() && incomplete.is_err() && overlapping.is_err() && foreign.is_err(),
            ),
            control_says: match &control {
                Ok(receipt) => format!(
                    "the exact partition covers {}/{} entries with {} overlaps",
                    receipt.completeness.covered_extent,
                    receipt.completeness.section_extent,
                    receipt.disjointness.overlaps.len()
                ),
                Err(defects) => format!("REFUSED: {}", first_partition_defect(defects)),
            },
            perturbed_says: format!(
                "(a) {}\n                     (b) {}\n                     (c) {}",
                named_defect(&incomplete, |defect| matches!(
                    defect,
                    PartitionDefect::RegionUncovered { .. }
                )),
                named_defect(&overlapping, |defect| matches!(
                    defect,
                    PartitionDefect::RegionsOverlap { .. }
                )),
                named_defect(&foreign, |defect| matches!(
                    defect,
                    PartitionDefect::RegionOutsideSection { .. }
                )),
            ),
        });
    }

    // --- controls 5 and 6, on the real words where they were built --------------------------
    match &real_receipt {
        Some((receipt, junction)) => {
            let mut narrow = junction.clone();
            narrow.overflow_aperture = receipt.declared.peak_width_bits.saturating_sub(1);
            let narrowed = narrow.certify();
            let mut per_node = junction.clone();
            per_node.policy = RoundingPolicy::AtEveryNode;
            let per_node_refusal = per_node.certify();
            let carried: Vec<Vec<Rat>> = junction
                .partials
                .iter()
                .map(|partial| partial.carried.clone())
                .collect();
            let mut ignored = Vec::new();
            let forward = per_node.read_word(
                &per_node.word,
                &carried,
                RoundingPolicy::AtEveryNode,
                &mut ignored,
            );
            let backward = per_node.read_word(
                &per_node.word.reversed(per_node.partials.len()),
                &carried,
                RoundingPolicy::AtEveryNode,
                &mut ignored,
            );
            controls.push(Control {
                number: 5,
                name: "the fixed word and its reversed control agree on the value; both carry every node's width",
                perturbation:
                    "(a) the overflow aperture is set one bit below the widest node; (b) the rounding \
                     policy moves from the boundary to every node",
                // The verdict rests on what does NOT depend on the fixture: the words agree, a
                // narrow aperture refuses, and `certify` refuses the per-node policy. Whether the
                // two words also DISAGREE in value under that policy is a property of the material
                // — on symmetric material they agree — so it is reported below as a reading and is
                // no longer a clause of the verdict. It was one until 2026-08-19, which made a
                // verdict about a law depend on which row of the source was read.
                verdict: verdict(
                    receipt.words_agree && narrowed.is_err() && per_node_refusal.is_err(),
                ),
                control_says: format!(
                    "value agrees; declared peak {} bits over {} nodes, reversed peak {} bits over {} \
                     nodes, and {} nodes stand at DIFFERENT widths between the two words; one \
                     outward rounding, residual {}",
                    receipt.declared.peak_width_bits,
                    receipt.declared.nodes.len(),
                    receipt.reversed.peak_width_bits,
                    receipt.reversed.nodes.len(),
                    receipt
                        .declared
                        .nodes
                        .iter()
                        .zip(&receipt.reversed.nodes)
                        .filter(|(left, right)| left.width_bits != right.width_bits)
                        .count(),
                    short_rat(&receipt.boundary_residual[0]),
                ),
                perturbed_says: format!(
                    "(a) {}\n                     (b) {}\n                     reading, not a \
                     verdict clause: under that policy the two words return different values on \
                     THIS material = {} (on symmetric material they agree, so the separation is a \
                     property of the material and not of the policy)",
                    named_reduction_defect(&narrowed, |defect| matches!(
                        defect,
                        ReductionDefect::WidthExceedsAperture { .. }
                    )),
                    named_reduction_defect(&per_node_refusal, |defect| matches!(
                        defect,
                        ReductionDefect::RoundingNotAtBoundary { .. }
                    )),
                    forward.value != backward.value,
                ),
            });

            let bare = receipt
                .adjoints
                .iter()
                .filter(|adjoint| !adjoint.bare_transpose_defect.is_zero())
                .count();
            controls.push(Control {
                number: 6,
                name: "the adjoint return reaches every partial chart under a declared metric",
                perturbation: "the bare transpose is claimed as the adjoint under the declared G_Y",
                verdict: verdict(
                    receipt.adjoints.len() == receipt.partials.len()
                        && receipt
                            .adjoints
                            .iter()
                            .all(|adjoint| adjoint.defect.is_zero())
                        && bare == receipt.adjoints.len(),
                ),
                control_says: format!(
                    "T_a* = G_X^-1 T_a^T G_Y reached {} of {} partial charts; every \
                     exact_linear::adjoint_defect is 0",
                    receipt.adjoints.len(),
                    receipt.partials.len()
                ),
                perturbed_says: format!(
                    "{bare} of {} bare transposes exhibit a NONZERO defect under the declared \
                     non-identity G_Y; first is {}",
                    receipt.adjoints.len(),
                    receipt
                        .adjoints
                        .first()
                        .map(|adjoint| short_rat(&adjoint.bare_transpose_defect))
                        .unwrap_or_default()
                ),
            });
        }
        None => {
            controls.push(Control {
                number: 5,
                name: "the fixed word and its reversed control agree on the value",
                perturbation: "not reached",
                verdict: "OPEN",
                control_says: "the real-words junction was not built".to_owned(),
                perturbed_says: "-".to_owned(),
            });
            controls.push(Control {
                number: 6,
                name: "the adjoint return reaches every partial chart",
                perturbation: "not reached",
                verdict: "OPEN",
                control_says: "the real-words junction was not built".to_owned(),
                perturbed_says: "-".to_owned(),
            });
        }
    }

    // --- control 7 --------------------------------------------------------------------------
    {
        let base = output_band_partition(out_features, in_features, tokens, lanes);
        // Two species over the SAME face at different units, and the same two with the units
        // exchanged. The cross-species sums are then equal by construction and the per-species
        // splits are not: `(N, N/2)` against `(N/2, N)`. Anything that combined the species would
        // identify these two declarations.
        let paired = |first: u64, second: u64| ResourceDeclaration {
            species: vec![
                DeclaredSpecies {
                    name: "written-lanes".to_owned(),
                    unit: first,
                    face: DemandFace::Written,
                    capacity: BigUint::from(lanes),
                    characteristic_delay: 1,
                    sink_capacity: BigUint::from(1u32),
                },
                DeclaredSpecies {
                    name: "written-sectors".to_owned(),
                    unit: second,
                    face: DemandFace::Written,
                    capacity: BigUint::from(lanes),
                    characteristic_delay: 1,
                    sink_capacity: BigUint::from(1u32),
                },
            ],
            enactment_aperture: DECLARED_ENACTMENT_APERTURE,
        };
        let declared = paired(1, 2);
        let moved = paired(2, 1);
        let left = base.certify(&cover, &[], &declared, "h1_control_seven");
        let right = base.certify(&cover, &[], &moved, "h1_control_seven");
        let split = |receipt: &Result<TilingReceipt, Vec<PartitionDefect>>| -> Vec<String> {
            match receipt {
                Ok(receipt) => receipt.pressure[0]
                    .species
                    .iter()
                    .map(|species| format!("{}={}", species.species, species.incoming))
                    .collect(),
                Err(_) => Vec::new(),
            }
        };
        let combined = |receipt: &Result<TilingReceipt, Vec<PartitionDefect>>| -> BigUint {
            match receipt {
                Ok(receipt) => receipt.pressure[0]
                    .species
                    .iter()
                    .map(|species| species.incoming.clone())
                    .sum(),
                Err(_) => BigUint::zero(),
            }
        };
        let names: Vec<String> = match &left {
            Ok(receipt) => receipt.pressure[0]
                .coordinates()
                .iter()
                .map(|(name, _)| (*name).to_owned())
                .collect(),
            Err(_) => Vec::new(),
        };
        let separated = split(&left) != split(&right);
        controls.push(Control {
            number: 7,
            name: "pressure stays a local product: one covector per species, per cell, never summed",
            perturbation:
                "the two species' declared units are exchanged, so the CROSS-SPECIES SUM is \
                 unchanged and only the per-species split moves",
            verdict: verdict(
                left.is_ok()
                    && right.is_ok()
                    && separated
                    && combined(&left) == combined(&right)
                    && !combined(&left).is_zero(),
            ),
            control_says: format!(
                "the receipt's coordinates are exactly the declared species {names:?}. The absence \
                 of a combined coordinate is a fact about the TYPE and is read off its own field \
                 names by the unit test that does so; the split comparison below is the weaker \
                 half and a receipt carrying an extra `total` would pass it"
            ),
            perturbed_says: format!(
                "split {:?} against {:?}; the sum a COMBINING receipt would return is the SAME \
                 ({} = {}), and the two receipts still differ ({separated}) — so the per-species \
                 coordinates are not collapsed INTO one. That no combined coordinate stands BESIDE \
                 them is the field-name reading, not this one",
                split(&left),
                split(&right),
                combined(&left),
                combined(&right),
            ),
        });
    }

    // -------------------------------------------------------------------------------------------
    // 6. Report.
    // -------------------------------------------------------------------------------------------
    line(
        &mut form,
        "THE SEVEN CONTROLS — each is a test that FAILS under its perturbation",
    );
    line(&mut form, "");
    controls.sort_by_key(|control| control.number);
    for control in &controls {
        line(
            &mut form,
            &format!(
                "  [{}] {}  — {}",
                control.number, control.verdict, control.name
            ),
        );
        line(
            &mut form,
            &format!("      control      {}", control.control_says),
        );
        line(
            &mut form,
            &format!("      perturbation {}", control.perturbation),
        );
        line(
            &mut form,
            &format!("      perturbed    {}", control.perturbed_says),
        );
        line(&mut form, "");
    }

    line(&mut form, "WHAT THIS DEED DOES NOT CLAIM");
    line(
        &mut form,
        "  - no device was mounted; every apparatus capacity above is a DECLARATION, and every",
    );
    line(
        &mut form,
        "    device-chart face is unknown rather than zero;",
    );
    line(
        &mut form,
        "  - value agreement between the word and its reversed control is FORCED by exactness. The",
    );
    line(
        &mut form,
        "    evidence is the per-node width, which differs, and the aperture refusal, which does not;",
    );
    line(
        &mut form,
        "  - whether the two words DISAGREE under a per-node rounding is a property of the MATERIAL and",
    );
    line(
        &mut form,
        "    not of the policy — on symmetric material they agree — so it decides no verdict here;",
    );
    line(
        &mut form,
        "  - a partition is a decomposition and never a schedule, and tiling is not compression;",
    );
    line(
        &mut form,
        "  - CompiledPlan::occurrence_work was added as a read-only accessor and is NOT exercised",
    );
    line(
        &mut form,
        "    here: it needs a compiled plan, which needs the card.",
    );

    let form_text = form;
    print!("{form_text}");
    if let Err(error) = fs::create_dir_all(OUTPUT) {
        println!("the output directory refused: {error}");
        return;
    }
    match fs::write(format!("{OUTPUT}/receipt.form"), &form_text) {
        Ok(()) => println!("\nwritten: {OUTPUT}/receipt.form"),
        Err(error) => println!("\nthe receipt refused: {error}"),
    }
}

// -------------------------------------------------------------------------------------------------
// construction
// -------------------------------------------------------------------------------------------------

fn line(form: &mut String, text: &str) {
    let _ = writeln!(form, "{text}");
}

fn verdict(passed: bool) -> &'static str {
    if passed { "PASS" } else { "OPEN" }
}

fn short_rat(value: &Rat) -> String {
    let text = value.to_string();
    if text.len() <= 72 {
        return text;
    }
    format!(
        "{}…{}  [{} numerator bits / {} denominator bits]",
        &text[..40],
        &text[text.len() - 16..],
        value.numer().bits(),
        value.denom().bits()
    )
}

fn enacted_face(enacted: &holonic_engine::section_partition::EnactedCurrent) -> String {
    use holonic_engine::section_partition::EnactedCurrent;
    match enacted {
        EnactedCurrent::Radiated {
            co_present_branch_population,
            passage_delay,
            arrival_chronology,
            deferred_arrivals,
            ..
        } => format!(
            "RADIATED co-present {co_present_branch_population} · delay {passage_delay} · arrival \
             {arrival_chronology} · deferred arrivals {deferred_arrivals}"
        ),
        EnactedCurrent::BeyondAperture { demand, aperture } => {
            format!("UNKNOWN — demand {demand} exceeds the declared enactment aperture {aperture}")
        }
        EnactedCurrent::NoDemand { face } => {
            format!(
                "NO DEMAND — the {face:?} face carries no material here. A zero, not an unknown"
            )
        }
    }
}

fn first_partition_defect(defects: &[PartitionDefect]) -> String {
    defects
        .first()
        .map(PartitionDefect::to_string)
        .unwrap_or_else(|| "no defect".to_owned())
}

fn named_defect(
    outcome: &Result<TilingReceipt, Vec<PartitionDefect>>,
    wanted: impl Fn(&PartitionDefect) -> bool,
) -> String {
    match outcome {
        Ok(_) => "certified — the perturbation did not bite".to_owned(),
        Err(defects) => defects
            .iter()
            .find(|defect| wanted(defect))
            .map(PartitionDefect::to_string)
            .unwrap_or_else(|| first_partition_defect(defects)),
    }
}

fn named_reduction_defect(
    outcome: &Result<ReductionReceipt, Vec<ReductionDefect>>,
    wanted: impl Fn(&ReductionDefect) -> bool,
) -> String {
    match outcome {
        Ok(_) => "certified — the perturbation did not bite".to_owned(),
        Err(defects) => defects
            .iter()
            .find(|defect| wanted(defect))
            .map(ReductionDefect::to_string)
            .unwrap_or_else(|| {
                defects
                    .first()
                    .map(ReductionDefect::to_string)
                    .unwrap_or_else(|| "no defect".to_owned())
            }),
    }
}

fn perturbed_shape_region(shape: SectionShape) -> SectionRegion {
    shape.whole()
}

/// **The disjoint output partition (H.5): one cell per resident lane of the declared cover.**
///
/// The band width is `ceil(out_features / lanes)`, so the last band is a nonmultiple tail whenever
/// the lanes do not divide the output. Nothing here is authored: the lane count is the cover's own
/// answer about itself and the section's extent is the source header's.
fn output_band_partition(
    out_features: usize,
    in_features: usize,
    tokens: usize,
    lanes: u64,
) -> SectionPartition {
    let shape = SectionShape::of(tokens, out_features, 0);
    let band = out_features.div_ceil(lanes as usize).max(1);
    let mut cells: Vec<SectionCell> = Vec::new();
    let mut column = 0usize;
    while column < out_features {
        let end = (column + band).min(out_features);
        let write = SectionRegion::new(0, tokens, column, end).expect("a nonempty band");
        cells.push(SectionCell {
            index: cells.len(),
            write,
            reads: vec![
                // The map slab this band needs: its own output rows, all inner columns.
                ReadRegion {
                    population: "map".to_owned(),
                    region: SectionRegion::new(column, end, 0, in_features).expect("a slab"),
                },
                // The token rows: ONE shared immutable standing that every cell reads.
                ReadRegion {
                    population: "tokens".to_owned(),
                    region: SectionRegion::new(0, tokens, 0, in_features).expect("the rows"),
                },
            ],
            partial_of: None,
        });
        column = end;
    }
    let mut populations = BTreeMap::new();
    populations.insert(
        "map".to_owned(),
        SectionShape::of(out_features, in_features, 0),
    );
    populations.insert(
        "tokens".to_owned(),
        SectionShape::of(tokens, in_features, 0),
    );
    SectionPartition {
        lineage: SectionLineage {
            source: "gemma".to_owned(),
            population: "section".to_owned(),
            body: "h1".to_owned(),
        },
        shape,
        populations,
        cells,
    }
}

/// The declared resource species.
///
/// **`C` is a caller declaration per species and the owner never reads the cover.** This driver
/// couples the two by hand — it passes the cpu chart's own lane count into every `capacity` — and
/// that coupling is the driver's doing. Two different covers return byte-identical pressure from
/// the owner, which is the honest reading and is why the earlier phrasing here ("every capacity is
/// the cover's own answer") was wrong: it credited the owner with a coupling this function makes.
///
/// The units, the faces, the characteristic delays and the sink capacities are declarations of this
/// driver outright; nothing measured them. The three species are different covectors and are never
/// added.
fn declared_resources(lanes: u64) -> ResourceDeclaration {
    ResourceDeclaration {
        species: vec![
            DeclaredSpecies {
                name: "resident-lanes".to_owned(),
                unit: 1,
                face: DemandFace::Written,
                capacity: BigUint::from(lanes),
                characteristic_delay: 1,
                sink_capacity: BigUint::from(1u32),
            },
            DeclaredSpecies {
                name: "map-ingress-words".to_owned(),
                unit: 1,
                face: DemandFace::Read,
                capacity: BigUint::from(lanes),
                characteristic_delay: 2,
                sink_capacity: BigUint::from(1u32),
            },
            DeclaredSpecies {
                name: "boundary-transfer-sectors".to_owned(),
                unit: DECLARED_SECTOR_ENTRIES,
                face: DemandFace::Touched,
                capacity: BigUint::from(lanes),
                characteristic_delay: 3,
                sink_capacity: BigUint::from(1u32),
            },
        ],
        enactment_aperture: DECLARED_ENACTMENT_APERTURE,
    }
}

/// A two-partial junction over a declared output region, used by the shared-output control.
fn shared_output_junction(output: SectionRegion) -> ReductionJunction {
    let partials: Vec<PartialTerm> = (0..2usize)
        .map(|index| PartialTerm {
            index,
            inner: SectionRegion::new(0, 1, index, index + 1).expect("a region"),
            carried: vec![Rat::from(BigInt::from(index as i64 + 1))],
            enclosure: vec![(
                Rat::from(BigInt::from(index as i64 + 1)),
                Rat::from(BigInt::from(index as i64 + 1)),
            )],
            chart: ExactRatMatrix::identity(1).expect("identity"),
            domain_metric: ExactRatMatrix::identity(1).expect("identity"),
        })
        .collect();
    ReductionJunction {
        owner: "h1::shared-output".to_owned(),
        output,
        output_dimension: 1,
        inner_shape: SectionShape::of(1, 2, 0),
        word: ReductionWord::balanced(2).expect("a word"),
        partials,
        overflow_aperture: DECLARED_OVERFLOW_APERTURE,
        carrier_exponent: 0,
        boundary_exponent: 0,
        rounding: DirectedRounding::Outward,
        policy: RoundingPolicy::OnceAtBoundary,
        codomain_metric: ExactRatMatrix::identity(1).expect("identity"),
        returned_covector: vec![Rat::from(BigInt::from(1))],
    }
}

/// **Build the real-words junction**: one output coordinate of `y = W x`, its inner axis partitioned
/// into bands, each partial an exact integer contraction of REAL `bf16` words read through the
/// existing mouth.
///
/// Each band is aligned in its own chart, so a band's alignment spread never has to cover the whole
/// row and each partial stands exactly in its own carrier. `T_a` is the identity embedding and is
/// **written down**; `G_Y` is declared NON-identity, so the adjoint is not a transpose.
fn build_real_junction(
    file: &mut std::fs::File,
    container: &holonic_engine::foreign_map::ForeignContainer,
    map: &str,
    rows: &str,
    lanes: u64,
) -> Result<(ReductionJunction, usize, usize), String> {
    let map_shape = container
        .tensor(map)
        .map_err(|error| error.to_string())?
        .shape
        .clone();
    let inner = *map_shape.get(1).ok_or("the map is not a matrix")?;
    let (map_words, _) = container
        .read_rows_bf16(file, map, 0, 1)
        .map_err(|error| error.to_string())?;
    let (row_words, _) = container
        .read_rows_bf16(file, rows, SOURCE_ROW, 1)
        .map_err(|error| error.to_string())?;
    if map_words.len() < inner || row_words.len() < inner {
        return Err("the mouth returned fewer words than the header declares".to_owned());
    }
    let band = inner.div_ceil(lanes as usize).max(1);
    let mut partials: Vec<PartialTerm> = Vec::new();
    let mut refused = 0usize;
    let mut carrier_exponent = 0u32;
    let mut column = 0usize;
    while column < inner {
        let end = (column + band).min(inner);
        let left = align_bfloat16(&map_words[column..end]);
        let right = align_bfloat16(&row_words[column..end]);
        match (left, right) {
            (Ok(left), Ok(right)) => {
                let mut accumulated = BigInt::from(0);
                for (a, b) in left.entries.iter().zip(&right.entries) {
                    accumulated += BigInt::from(*a) * BigInt::from(*b);
                }
                let exponent = left.exponent + right.exponent;
                let value = if exponent >= 0 {
                    Rat::from(accumulated * (BigInt::from(1) << (exponent as u32)))
                } else {
                    let scale = BigInt::from(1) << ((-exponent) as u32);
                    carrier_exponent = carrier_exponent.max((-exponent) as u32);
                    Rat::new(accumulated, scale)
                };
                partials.push(PartialTerm {
                    index: partials.len(),
                    inner: SectionRegion::new(0, 1, column, end).expect("a band"),
                    carried: vec![value.clone()],
                    enclosure: vec![(value.clone(), value)],
                    // The identity embedding, DECLARED.
                    chart: ExactRatMatrix::identity(1).expect("identity"),
                    domain_metric: ExactRatMatrix::identity(1).expect("identity"),
                });
            }
            _ => {
                refused += 1;
                // A band the mouth refused is retained as a partial of exact zero with its region
                // named, so K stays covered and the refusal is visible rather than deleted.
                partials.push(PartialTerm {
                    index: partials.len(),
                    inner: SectionRegion::new(0, 1, column, end).expect("a band"),
                    carried: vec![Rat::from(BigInt::from(0))],
                    enclosure: vec![(Rat::from(BigInt::from(0)), Rat::from(BigInt::from(0)))],
                    chart: ExactRatMatrix::identity(1).expect("identity"),
                    domain_metric: ExactRatMatrix::identity(1).expect("identity"),
                });
            }
        }
        column = end;
    }
    let word = ReductionWord::balanced(partials.len()).ok_or("no partials")?;
    let junction = ReductionJunction {
        owner: "h1::q_proj-row-0".to_owned(),
        output: SectionRegion::new(0, 1, 0, 1).expect("one output coordinate"),
        output_dimension: 1,
        inner_shape: SectionShape::of(1, inner, carrier_exponent),
        word,
        partials,
        overflow_aperture: DECLARED_OVERFLOW_APERTURE,
        carrier_exponent,
        boundary_exponent: DECLARED_BOUNDARY_EXPONENT.min(carrier_exponent),
        rounding: DirectedRounding::Outward,
        policy: RoundingPolicy::OnceAtBoundary,
        // DECLARED non-identity: the receiver weights the one output coordinate by three, so the
        // adjoint is G_X^-1 T^T G_Y = 3 and a bare transpose is refuted.
        codomain_metric: ExactRatMatrix::new(vec![vec![Rat::from(BigInt::from(3))]])
            .expect("a metric"),
        returned_covector: vec![Rat::from(BigInt::from(1))],
    };
    Ok((junction, band, refused))
}
