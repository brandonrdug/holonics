//! Complete framed episodes and conditional joint samples at the existing native boundary.
//! These are exterior workloads. Record cuts never reset a native moment or force a tick.

use super::*;
use holonics::hnn::reference::observed::{HostObservedEpochExecution, ObservedEpochExecution};
use std::collections::BTreeMap;

#[path = "complete_language/continuation.rs"]
mod continuation;

#[cfg(test)]
#[path = "complete_language/code_parallel_controls.rs"]
mod code_parallel_controls;

const READ_BUDGET: u64 = 64 * 1024 * 1024;
const READING_BITS: u32 = holonics::ratio::exponentiated::READING_BITS;

fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    Ok(())
}

fn pinned_read(path: &str, expected: &str, maximum: usize) -> Result<Vec<u8>> {
    let file = std::fs::File::open(path)?;
    if file.metadata()?.len() > maximum as u64 {
        return Err("declared input extent exceeded".into());
    }
    let mut bytes = Vec::new();
    file.take(maximum as u64 + 1).read_to_end(&mut bytes)?;
    if bytes.len() > maximum || sha256(&bytes)? != expected {
        return Err("input SHA256 or extent mismatch".into());
    }
    Ok(bytes)
}

fn parse_cuts(bytes: &[u8], cells: usize) -> Result<BTreeMap<usize, String>> {
    let mut cuts = BTreeMap::new();
    for line in std::str::from_utf8(bytes)?.lines() {
        let (at, label) = line.split_once('\t').ok_or("cut requires cell and label")?;
        let at: usize = at.parse()?;
        if at > cells || label.is_empty() || cuts.insert(at, label.to_owned()).is_some() {
            return Err("duplicate or invalid causal cut".into());
        }
    }
    Ok(cuts)
}

fn fresh_checkpoint(population: u64) -> Result<Checkpoint> {
    fresh_checkpoint_at_law(
        population,
        holonics::hnn::receiving::ReceivingLaw::CoarseGrainV1,
    )
}

fn fresh_checkpoint_at_law(
    population: u64,
    law: holonics::hnn::receiving::ReceivingLaw,
) -> Result<Checkpoint> {
    let (field, initial, pairing) = declaration(population)?;
    let reference = port();
    let mut resident = reference.mount_with(&field, &Current::at_rest(&field), initial)?;
    resident.select_receiving_law(law)?;
    let boundary = PairedObservation::admit(&field, resident.constitution(), &pairing)?;
    reference.ingest(&mut resident, None, &boundary.encode(&[])?)?;
    Ok(Checkpoint {
        population,
        stream: ObservedStream::new(
            resident,
            ObservedCrib::new(0),
            ObservedEpochDepositionScope::NormalMaps,
        )?,
        provenance: "complete episodes; fresh native initializer; explicit exterior framing".into(),
    })
}

/// A structural witness, independent of subject bytes. These advance operands are the native
/// lock route: every class advances ring0 once, with no own advance on rings1/2. Periods5,2
/// therefore give the actual receiver tick every10 source arrivals, including whole carries.
fn clock_contract(checkpoint: &Checkpoint) -> Result<String> {
    let field = checkpoint.stream.resident().field();
    if field.rings().len() != 3
        || field.rings()[0].period() != 5
        || field.rings()[1].period() != 2
        || field.rings()[2].period() != 3
        || checkpoint.stream.epoch_bound() != 10
    {
        return Err("unexpected native clock declaration".into());
    }
    let mut advances = Vec::new();
    for ring in 0..3 {
        let row = (0..4)
            .map(|class| field.class_advance(ring, class))
            .collect::<std::result::Result<Vec<_>, _>>()?;
        if row != vec![u64::from(ring == 0); 4] {
            return Err("actual class advances do not establish ten-cell closure".into());
        }
        advances.push(row);
    }
    Ok(object(&[
        (
            "actual_rayon_workers",
            rayon::current_num_threads().to_string(),
        ),
        ("periods", "[5,2,3]".into()),
        ("native_class_advances", exact(&advances)),
        ("finite_bound", "10".into()),
        ("closure_cells", "10".into()),
        ("source_horizon", checkpoint.population.to_string()),
        ("lattices", exact(field.lattices())),
        ("field_declaration", exact(field.declaration())),
        (
            "paired_initial_constitution_sha256",
            quoted(&material_hash(checkpoint.stream.resident())?),
        ),
        ("terminal_flush", "false".into()),
        (
            "law",
            quoted(
                "ring0 every arrival; ring1 only carry each5; receiver2 only carry each10; whole carry preserves lift",
            ),
        ),
    ]))
}

fn code_of_mass(mass: &ExactInterval) -> Result<ExactInterval> {
    let log = holonics::ratio::algebraic::log2_of_enclosure_at(mass, READING_BITS)?;
    Ok(ExactInterval::new(-log.upper, -log.lower)?)
}

/// Read a requested accepted-prefix cut on a disposable native query fork. Pending classes
/// advance by query_fork's genuine fixed-medium owner; they are never deposited or flushed.
fn causal_cut(checkpoint: &Checkpoint, next_class: Option<usize>, label: &str) -> Result<String> {
    let before = checkpoint.bytes()?;
    let reference = port();
    let (_, founding, pairing) = declaration(checkpoint.population)?;
    let (mut resident, crib) = checkpoint.stream.query_fork(&reference, &pairing)?;
    let moment_id = resident.continuing().ok_or("cut requires native moment")?.0;
    let moment = exact(resident.moment(&moment_id).ok_or("cut moment missing")?);
    let current = exact(resident.current());
    let state = resident.continuing_state(0)?.to_text();
    let phases = resident
        .admitted()
        .first()
        .ok_or("cut receiving phase missing")?
        .clone();
    let control = founding
        .receiving_law(phases.ring())
        .ok_or("founding map missing")?
        .map()
        .clone();
    let receiver = holonics::hnn::receiving::RetainedFibreReceiver::declare(phases.grain())?;
    let (pending, _) = reference.refine(&mut resident, &moment_id, &phases)?;
    let coarse = reference.diagnose_pending_readout(&resident, &pending, &control, READING_BITS)?;
    let fine = reference.diagnose_pending_readout_at_receiver(
        &resident,
        &pending,
        &control,
        &receiver,
        READING_BITS,
    )?;
    let codes = if let Some(class) = next_class {
        let old = holonics::hnn::receiving::cells::diagnostic::compare_readout_class_codes_at(
            &coarse.scored_face,
            &coarse.tree,
            &coarse.readout.feature,
            &coarse.native_map,
            &coarse.readout.native_wave_logits,
            &control,
            class,
            READING_BITS,
        )?;
        object(&[
            ("supervised_next_class", class.to_string()),
            ("actual_coarse_code", interval(&old.native_code)),
            ("tree_code", interval(&old.tree_code)),
            (
                "fine_code",
                interval(&code_of_mass(&fine.native.native_masses[class])?),
            ),
            (
                "fine_founding_R_code",
                interval(&code_of_mass(&fine.control.native_masses[class])?),
            ),
        ])
    } else {
        "null".into()
    };
    reference.discard(&mut resident, Handle::Pending(pending))?;
    if checkpoint.bytes()? != before {
        return Err("causal cut changed training body".into());
    }
    Ok(object(&[
        ("label", quoted(label)),
        (
            "accepted_cells",
            checkpoint.stream.accepted_cells()?.to_string(),
        ),
        (
            "published_cells",
            total(checkpoint.stream.resident())?.to_string(),
        ),
        (
            "unpublished_cells",
            checkpoint.stream.pending_classes().len().to_string(),
        ),
        ("retained_moment", moment),
        ("actual_current", current),
        ("retained_state_sha256", quoted(&sha256(state.as_bytes())?)),
        ("crib", exact(&crib)),
        ("coarse_producing_read", exact(&coarse)),
        ("fine_matched_read", exact(&fine)),
        ("code_readings", codes),
        (
            "cut_scope",
            quoted(
                "actual accepted-prefix view on fixed committed medium; no deposit; fine objective is diagnostic only",
            ),
        ),
    ]))
}

/// Reusable native training entry. Data are already framed and pinned by the exterior plan.
/// Backend injection changes only the existing forward/reverse executor, not the epoch law.
#[allow(clippy::too_many_arguments)]
fn train(
    args: &[String],
    execution: &dyn ObservedEpochExecution,
    law: holonics::hnn::receiving::ReceivingLaw,
) -> Result<()> {
    if args.len() != 10 {
        return Err("train BACKEND CORPUS SHA CUTS CUTSHA POPULATION CELLS EPOCHS OUT".into());
    }
    let backend = &args[1];
    if backend != "host-reference" {
        return Err("this CLI adapter implements host-reference; CUDA executor adapter/parity remains unrun; no fallback".into());
    }
    let data = pinned_read(&args[2], &args[3], 1 << 20)?;
    let cells = digits(&data);
    let expected_cells: usize = args[7].parse()?;
    let expected_epochs: usize = args[8].parse()?;
    if cells.len() != expected_cells
        || expected_cells != expected_epochs.checked_mul(10).ok_or("count overflow")?
    {
        return Err("declared framed arrival/epoch counts mismatch".into());
    }
    let cuts = parse_cuts(&pinned_read(&args[4], &args[5], 1 << 20)?, expected_cells)?;
    let population: u64 = args[6].parse()?;
    if expected_cells as u64 + (QUERY_BYTE_BUDGET as u64 * 4) + 128 > population {
        return Err("declared horizon cannot contain training and longest continuation".into());
    }
    let out = Path::new(&args[9]);
    std::fs::create_dir(out)?;
    let started = Instant::now();
    let mut checkpoint = if law == holonics::hnn::receiving::ReceivingLaw::CoarseGrainV1 {
        fresh_checkpoint(population)?
    } else {
        fresh_checkpoint_at_law(population, law)?
    };
    checkpoint.provenance = format!(
        "complete Q+LF+A+LF; corpus SHA256 {}; backend {backend}; no record-boundary resets",
        args[3]
    );
    write_new(
        &out.join("CLOCK_CONTRACT.json"),
        clock_contract(&checkpoint)?.as_bytes(),
    )?;
    checkpoint.publish(out.join("fresh.state").to_str().ok_or("UTF8 path")?)?;
    let reference = port();
    let pairing = declaration(population)?.2;
    let mut epoch_log = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(out.join("epochs.jsonl"))?;
    let mut at = 0usize;
    let mut epochs = 0usize;
    loop {
        if let Some(label) = cuts.get(&at) {
            write_new(
                &out.join(format!("cut-{at:05}.json")),
                causal_cut(&checkpoint, cells.get(at).copied(), label)?.as_bytes(),
            )?;
            checkpoint.publish(
                out.join(format!("cut-{at:05}.state"))
                    .to_str()
                    .ok_or("UTF8 path")?,
            )?;
        }
        if at == cells.len() {
            break;
        }
        let next_cut = cuts
            .range((at + 1)..)
            .next()
            .map_or(cells.len(), |(&n, _)| n);
        let remaining = checkpoint
            .stream
            .epoch_bound()
            .checked_sub(checkpoint.stream.pending_classes().len())
            .ok_or("invalid pending bound")?;
        let end = next_cut
            .min(at.checked_add(remaining).ok_or("count overflow")?)
            .min(cells.len());
        let receipt = checkpoint.stream.receive_diagnosed_with_execution(
            &reference,
            &pairing,
            &cells[at..end],
            execution,
            &mut |attempt, refusal| {
                eprintln!(
                    "complete-language stage_refusal {}",
                    object(&[("attempt", exact(&attempt)), ("refusal", exact(refusal))])
                )
            },
        )?;
        at = end;
        for epoch in receipt.epochs {
            if epoch.consumed != 10
                || !epoch.closed_section
                || epoch.terminal_partial
                || epoch.reads.len() != 10
            {
                checkpoint.publish(
                    out.join(format!("closure-mismatch-{at}.state"))
                        .to_str()
                        .ok_or("UTF8 path")?,
                )?;
                return Err("actual epoch/closure count contradicts declared ten-cell law; no flush or retry".into());
            }
            epochs += 1;
            let coarse = epoch
                .reads
                .iter()
                .fold(ExactInterval::point(integer(0)), |sum, read| {
                    ExactInterval {
                        lower: sum.lower + &read.code.lower,
                        upper: sum.upper + &read.code.upper,
                    }
                });
            let record = object(&[
                ("epoch", epochs.to_string()),
                ("source_cells", epoch.cells.to_string()),
                ("consumed", epoch.consumed.to_string()),
                ("closed_section", epoch.closed_section.to_string()),
                ("carry_out", epoch.carry_out.to_string()),
                ("commit", epoch.deposit.commit.to_string()),
                ("outcome", exact(&epoch.outcome)),
                (
                    if law == holonics::hnn::receiving::ReceivingLaw::CoarseGrainV1 {
                        "actual_coarse_prequential_code_sum"
                    } else {
                        "actual_retained_prequential_code_sum"
                    },
                    interval(&coarse),
                ),
                ("receiving_law", quoted(law.as_str())),
                (
                    "prequential_readings",
                    format!(
                        "[{}]",
                        epoch
                            .reads
                            .iter()
                            .enumerate()
                            .map(|(offset, read)| object(&[
                                (
                                    "source_cell",
                                    (epoch.cells - epoch.consumed as u64 + offset as u64)
                                        .to_string()
                                ),
                                (
                                    if law == holonics::hnn::receiving::ReceivingLaw::CoarseGrainV1
                                    {
                                        "actual_coarse_code"
                                    } else {
                                        "actual_retained_code"
                                    },
                                    interval(&read.code)
                                ),
                                (
                                    "tree_code",
                                    read.tree.as_ref().map_or_else(|| "null".into(), interval)
                                ),
                            ]))
                            .collect::<Vec<_>>()
                            .join(",")
                    ),
                ),
                ("actual_normal_comparison", exact(&epoch.comparison)),
                ("actual_joint_comparison", exact(&epoch.joint_comparison)),
                (
                    "actual_receiving_only_comparison",
                    exact(&epoch.receiving_only_comparison),
                ),
                (
                    "retained_section_return",
                    exact(&epoch.retained_section_return),
                ),
                ("whole_refusal", exact(&epoch.whole_stage_refusal)),
                ("joint_refusal", exact(&epoch.joint_stage_refusal)),
                ("wall", exact(&epoch.wall)),
                ("backend", quoted(backend)),
            ]);
            writeln!(epoch_log, "{record}")?;
            epoch_log.flush()?;
            eprintln!(
                "complete-language epoch={epochs} cells={} elapsed_ns={} backend={backend}",
                epoch.cells,
                started.elapsed().as_nanos()
            );
        }
    }
    if at != expected_cells
        || epochs != expected_epochs
        || !checkpoint.stream.pending_classes().is_empty()
        || total(checkpoint.stream.resident())? != expected_cells
        || checkpoint.stream.accepted_cells()? != expected_cells as u64
    {
        return Err("actual complete-episode totals differ; no terminal flush".into());
    }
    let path = out.join("trained.state");
    let (bytes, hash) = checkpoint.publish(path.to_str().ok_or("UTF8 path")?)?;
    let (cold, cold_hash) = Checkpoint::load(path.to_str().ok_or("UTF8 path")?, READ_BUDGET)?;
    if hash != cold_hash || checkpoint.bytes()? != cold.bytes()? {
        return Err("trained cold restore differs".into());
    }
    write_new(
        &out.join("TRAINING_COMPLETE.json"),
        object(&[
            ("backend", quoted(backend)),
            (
                "actual_rayon_workers",
                rayon::current_num_threads().to_string(),
            ),
            (
                "receiving_law",
                quoted(checkpoint.stream.resident().receiving_law().as_str()),
            ),
            ("accepted_cells", at.to_string()),
            (
                "published_cells",
                total(checkpoint.stream.resident())?.to_string(),
            ),
            ("actual_epochs", epochs.to_string()),
            ("final_pending_cells", "0".into()),
            ("checkpoint_bytes", bytes.to_string()),
            ("checkpoint_sha256", quoted(&hash)),
            ("cold_exact", "true".into()),
            ("terminal_flush", "false".into()),
            ("elapsed_ns", started.elapsed().as_nanos().to_string()),
        ])
        .as_bytes(),
    )?;
    Ok(())
}

fn sample(args: &[String]) -> Result<()> {
    // Targets are intentionally absent from this command's interface.
    if args.len() != 10 {
        return Err(
            "sample BACKEND CHECKPOINT PROMPT SHA KEYS KEYSHA POLICY COLD_CHECK OUT".into(),
        );
    }
    if args[1] != "host-reference" {
        return Err(
            "full-fibre prefix/diagnostic consumer is host-reference; no CUDA fallback".into(),
        );
    }
    let (checkpoint, _) = Checkpoint::load(&args[2], READ_BUDGET)?;
    if args[7] == "fresh-native" && checkpoint.stream.accepted_cells()? != 0 {
        return Err(
            "fresh-native requires the selected run's saved pre-arrival fresh checkpoint".into(),
        );
    }

    let prompt = pinned_read(&args[3], &args[4], QUERY_BYTE_BUDGET)?;
    let keys = pinned_read(&args[5], &args[6], 1024)?;
    let policy = match args[7].as_str() {
        "native" | "fresh-native" => continuation::SamplingPolicy::NativeFullFibre,
        "founding-R" => continuation::SamplingPolicy::FoundingRAtSameHistory,
        "tree" => continuation::SamplingPolicy::Tree,
        _ => return Err("unknown explicitly selected conditional sampling policy".into()),
    };
    let cold = match args[8].as_str() {
        "cold-replay" => Some(64),
        "no-replay" => None,
        _ => return Err("invalid cold replay declaration".into()),
    };
    let out = Path::new(&args[9]);
    std::fs::create_dir(out)?;
    let receipt = continuation::sample_continuing(
        &checkpoint,
        &prompt,
        policy,
        &keys,
        128,
        &[0, 1, 4, 16, 64, 128],
        cold,
        out,
    )?;
    write_new(&out.join("OUTPUT.bin"), &receipt.raw_bytes)?;
    write_new(
        &out.join("OUTPUT.json"),
        object(&[
            ("backend", quoted(&args[1])),
            (
                "actual_rayon_workers",
                rayon::current_num_threads().to_string(),
            ),
            (
                "receiving_law",
                quoted(checkpoint.stream.resident().receiving_law().as_str()),
            ),
            (
                "opening_accepted_cells",
                checkpoint.stream.accepted_cells()?.to_string(),
            ),
            ("policy", quoted(&args[7])),
            ("prompt_sha256", quoted(&receipt.prompt_sha256)),
            ("key_schedule_sha256", quoted(&receipt.key_schedule_sha256)),
            (
                "output_cells_requested",
                receipt.output_cells_requested.to_string(),
            ),
            ("classes", exact_classes(&receipt.classes)),
            ("raw_bytes", format!("{:?}", receipt.raw_bytes)),
            ("unfinished_cells", exact_classes(&receipt.unfinished_cells)),
            (
                "strict_utf8",
                receipt
                    .strict_utf8
                    .as_deref()
                    .map_or_else(|| "null".into(), quoted),
            ),
            ("utf8_boundary", quoted(&receipt.utf8_boundary)),
            ("stop", quoted(&receipt.stop)),
            ("final_state_sha256", quoted(&receipt.final_state_sha256)),
            ("final_crib_sha256", quoted(&receipt.final_crib_sha256)),
            ("cold_continuation", exact(&receipt.cold_continuation)),
            ("cut_receipts", exact(&receipt.cuts)),
        ])
        .as_bytes(),
    )?;
    Ok(())
}

fn exact_classes(classes: &[usize]) -> String {
    format!("{classes:?}")
}

pub(super) fn run(args: &[String]) -> Result<()> {
    match args.first().map(String::as_str) {
        Some("train") => train(args, &HostObservedEpochExecution,holonics::hnn::receiving::ReceivingLaw::CoarseGrainV1),
        Some("train-retained-fibre-v1") => train(args,&HostObservedEpochExecution,holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1),
        Some("sample") => sample(args),
        _ => Err(
            "complete-language requires train, explicit train-retained-fibre-v1, or sample; no default backend/model action".into(),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn complete_language_cut_parser_refuses_duplicate_or_out_of_horizon() {
        assert!(parse_cuts(b"0\topening\n20\tend\n", 20).is_ok());
        assert!(parse_cuts(b"0\ta\n0\tb\n", 20).is_err());
        assert!(parse_cuts(b"21\ta\n", 20).is_err());
    }
    #[test]
    fn complete_language_native_clock_contract_has_no_subject_dependent_advance() {
        let checkpoint = fresh_checkpoint(16384).unwrap();
        let smaller = fresh_checkpoint(4096).unwrap();
        assert_eq!(checkpoint.stream.epoch_bound(), 10);
        assert!(clock_contract(&checkpoint).unwrap().contains("16384"));
        assert_eq!(checkpoint.stream.accepted_cells().unwrap(), 0);
        assert_eq!(
            checkpoint.stream.resident().field().declaration().lattice
                [&holonics::hnn::constitution::Locus::SourcePort(0)],
            17
        );
        assert_eq!(
            smaller.stream.resident().field().declaration().lattice
                [&holonics::hnn::constitution::Locus::SourcePort(0)],
            15
        );
        for (locus, lattice) in checkpoint.stream.resident().field().lattices() {
            if *locus != holonics::hnn::constitution::Locus::SourcePort(0) {
                assert_eq!(
                    Some(lattice),
                    smaller.stream.resident().field().lattices().get(locus)
                );
            }
        }
        assert_eq!(
            checkpoint.stream.resident().admitted(),
            smaller.stream.resident().admitted()
        );
        println!(
            "V91_DECLARATION_RECEIPT {}",
            clock_contract(&checkpoint).unwrap()
        );
    }
    #[test]
    fn complete_language_synthetic_conditional_sample_restores_and_continues_cold() {
        let checkpoint = fresh_checkpoint(16384).unwrap();
        let before = checkpoint.bytes().unwrap();
        let out =
            std::env::temp_dir().join(format!("holonics-v91-synthetic-{}", std::process::id()));
        std::fs::create_dir(&out).unwrap();
        // Synthetic law fixture: no corpus or natural-language model data.
        let keys = vec![0x55u8; 64];
        let receipt = continuation::sample_continuing(
            &checkpoint,
            &[],
            continuation::SamplingPolicy::NativeFullFibre,
            &keys,
            8,
            &[0, 4, 8],
            Some(4),
            &out,
        )
        .unwrap();
        assert_eq!(receipt.classes.len(), 8);
        assert_eq!(receipt.raw_bytes.len(), 2);
        assert_eq!(receipt.stop, "DeclaredLength");
        assert!(
            receipt
                .cold_continuation
                .unwrap()
                .matched_warm_state_and_crib
        );
        assert_eq!(checkpoint.bytes().unwrap(), before);
        // Remove only this test's newly created private fixtures.
        for entry in std::fs::read_dir(&out).unwrap() {
            std::fs::remove_file(entry.unwrap().path()).unwrap();
        }
        std::fs::remove_dir(out).unwrap();
    }
}
