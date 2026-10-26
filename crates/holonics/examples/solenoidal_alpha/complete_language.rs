//! Complete framed episodes and conditional joint samples at the existing native boundary.
//! These are exterior workloads. Record cuts never reset a native moment or force a tick.

use super::*;
use holonics::hnn::reference::observed::{HostObservedEpochExecution, ObservedEpochExecution};
use std::collections::BTreeMap;

#[path = "complete_language/continuation.rs"]
mod continuation;
#[path="complete_language/stage.rs"]
mod stage;
#[path = "complete_language/native_train.rs"]
mod native_train;
#[path = "complete_language/modes_train.rs"]
mod modes_train;
#[path = "complete_language/tower_train.rs"]
mod tower_train;
#[path = "complete_language/tower_situated.rs"]
mod tower_situated;
#[path = "complete_language/tower_ring.rs"]
mod tower_ring;
#[path = "complete_language/tower_classes.rs"]
mod tower_classes;
#[path = "complete_language/tower_bank.rs"]
mod tower_bank;
#[path = "complete_language/duplex_train.rs"]
mod duplex_train;
#[path = "complete_language/unit_copy.rs"]
mod unit_copy;

#[cfg(test)]
#[path = "complete_language/code_parallel_controls.rs"]
mod code_parallel_controls;

#[cfg(test)]
#[path = "complete_language/prepared_controls.rs"]
mod prepared_controls;
#[cfg(test)]
#[path = "complete_language/native_context_controls.rs"]
pub(crate) mod native_context_controls;

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
    fresh_checkpoint_at_law_and_scope(population, law, ObservedEpochDepositionScope::NormalMaps)
}

fn fresh_checkpoint_at_law_and_scope(
    population: u64,
    law: holonics::hnn::receiving::ReceivingLaw,
    scope: ObservedEpochDepositionScope,
) -> Result<Checkpoint> {
    fresh_checkpoint_at_context(population,law,scope,false)
}
fn fresh_checkpoint_at_context(population:u64,law:holonics::hnn::receiving::ReceivingLaw,scope:ObservedEpochDepositionScope,framed:bool)->Result<Checkpoint>{fresh_checkpoint_at_input_context(population,law,scope,framed,false)}
fn fresh_checkpoint_at_input_context(population:u64,law:holonics::hnn::receiving::ReceivingLaw,scope:ObservedEpochDepositionScope,framed:bool,arrival:bool)->Result<Checkpoint>{
    let (field, initial, pairing) = declaration_with_input_context(population,framed,arrival)?;
    let reference = port();
    let mut resident = reference.mount_declared_receiving_law(&field, &Current::at_rest(&field), initial,law)?;
    let boundary = PairedObservation::admit(&field, resident.constitution(), &pairing)?;
    reference.ingest(&mut resident, None, &boundary.encode(&[])?)?;
    Ok(Checkpoint {
        population,
        stream: ObservedStream::new(resident, ObservedCrib::new(0), scope)?,
        provenance: "complete episodes; fresh native initializer; explicit exterior framing".into(),
    })
}

// Scalar exterior evidence from the already-produced representation receipt;
// compact rows do not reread the normal, Word, target or certificate.
fn representation_evidence(r:&holonics::hnn::constitution::EpochReceivingRepresentationReading)->String {
    object(&[("before",r.before.to_string()),("proposed",r.proposed.to_string()),("ceiling",r.ceiling.to_string()),
        ("minimum_nonzero",r.minimum_nonzero.map_or_else(||"null".into(),|v|v.to_string())),
        ("disposition",exact(&r.disposition)),
        ("predicted_whole_bits",r.predicted_whole_bits.map_or_else(||"null".into(),|v|v.to_string()))])
}
fn fresh_family_local_checkpoint(population:u64,scope:ObservedEpochDepositionScope)->Result<Checkpoint> {fresh_family_local_checkpoint_at_representation(population,scope,false)}
fn fresh_family_local_checkpoint_at_representation(population:u64,scope:ObservedEpochDepositionScope,adaptive:bool)->Result<Checkpoint> { Ok({
        let (field,mut initial,pairing)=declaration_with_input_context(population,true,true)?;
        initial.bind_family_local_receiving_return(2)?;
        if adaptive {initial.bind_bounded_receiving_representation(2)?;}
        let reference=port();
        let mut resident=reference.mount_declared_receiving_law(&field,&Current::at_rest(&field),initial,holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1)?;
        let boundary=PairedObservation::admit(&field,resident.constitution(),&pairing)?;
        reference.ingest(&mut resident,None,&boundary.encode(&[])?)?;
        Checkpoint {population, stream:ObservedStream::new(resident,ObservedCrib::new(0),scope)?,provenance:if adaptive {"fresh FamilyLocalRetainedReturnV1 + BoundedSubquantum20V1 representation; no previous moments migrated".into()} else {"fresh FamilyLocalRetainedReturnV1; unchanged RetainedFibreV1 release/history; framed paired source".into()}}

    }) }

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
    let (_, founding, pairing) = checkpoint.declaration()?;
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
        .receiving_map(phases.ring())
        .ok_or("founding map missing")?
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
fn e_scope(scope: ObservedEpochDepositionScope, prepared: bool) -> &'static str {
    if prepared {
        return "class-coordinate contextual M plus local R/tree/population; native E/C/K/D held; general contextual E/family producer is a separate owner";
    }
    if scope.is_local_receiving() {
        "R/tree/population only; bounded addressed JointFamily E response is a separate API, not automatically produced or invoked"
    } else {
        "preserved legacy normal-map reference; no generic contextual JointFamily producer"
    }
}

fn train(
    args: &[String],
    execution: &dyn ObservedEpochExecution,
    law: holonics::hnn::receiving::ReceivingLaw,
    selected_backend: CompleteLanguageTrainingBackend,
    scope: ObservedEpochDepositionScope,
) -> Result<()> {
    let staged=args.first().is_some_and(|s|s==stage::COMMAND);
    if args.len()!=if staged{12}else{10} {
        return Err("train BACKEND CORPUS SHA CUTS CUTSHA POPULATION CELLS EPOCHS OUT [STAGE_MANIFEST SHA]".into());
    }
    let adaptive=staged || args[0]=="train-adaptive-family-local-arrival-held-v1";
    let family_local=adaptive || args[0]=="train-family-local-arrival-context-held-v1";
    let arrival=family_local || args[0]=="train-source-framing-arrival-context-held-v1";
    let framed=arrival || args[0]=="train-source-framing-retained-held-v1";
    let prepared_input = framed || matches!(args[0].as_str(), "train-prepared-local-retained-fibre-v1" | "train-prepared-local-retained-held-v1");
    if prepared_input {
        execution.admit_prepared_input()?;
    }
    let backend = selected_backend.as_str();
    if args[1] != backend {
        return Err(
            "training backend does not match the explicitly injected executor; no fallback".into(),
        );
    }
    if selected_backend == CompleteLanguageTrainingBackend::CudaObservedEpochDevice0
        && law != holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1
    {
        return Err("CUDA complete-language training requires explicit RetainedFibreV1".into());
    }
    let started=Instant::now();
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
    let mut stage=if staged{Some(stage::Stage::open(args,&data,&cells,backend,scope)?)}else{None};
    let out = Path::new(&args[9]);
    std::fs::create_dir(out)?;
    write_new(&out.join("EXECUTION_CONTRACT.json"), object(&[
        ("backend", quoted(backend)),
        ("command",quoted(&args[0])),
        ("input_preparation_law",if prepared_input {quoted(if framed{holonics::hnn::reference::prepared_input::SOURCE_FRAMING_LAW}else{holonics::hnn::reference::prepared_input::LAW})}else{"null".into()}),
        ("deposition_scope",exact(&scope)),
        ("receiving_representation_policy",quoted(if adaptive {"bounded-subquantum20-v1"} else {"fixed-lattice-v1"})),
        ("constitutive_return_policy",quoted(if family_local {"family-local-retained-return-v1"} else {"population-mixture-section-return-v1"})),
        ("receiving_layout",quoted(if arrival{"ArrivalContext-source6/context6"}else{"Single6"})),
        ("additional_whole_section_monotone_policy_requested",(!scope.is_local_receiving()).to_string()),
        ("e_scope",quoted(e_scope(scope,prepared_input))),
        ("training_executor_injected", "true".into()),
        ("device_ordinal", if selected_backend == CompleteLanguageTrainingBackend::CudaObservedEpochDevice0 { "0".into() } else { "null".into() }),
        ("host_owned", quoted("source/clock/normal law; scalar face/root/normalization/scoring/certification; causal cuts; prefix diagnostics; exact decode; independent output forks")),
        ("host_fallback", "false".into()),
        ("evidence_policy",quoted("local: compact outcome/actual-code/wall; full return+energy at predeclared cut crossings or Held; all stage failures retained")),
    ]).as_bytes())?;
    let resumed=stage.as_ref().is_some_and(|s|s.checkpoint.is_some());
    let mut checkpoint = if let Some(cp)=stage.as_mut().and_then(|s|s.checkpoint.take()){cp}else if family_local {fresh_family_local_checkpoint_at_representation(population,scope,adaptive)?    } else {fresh_checkpoint_at_input_context(population, law, scope,framed,arrival)?};
    if prepared_input && !resumed {
        let pairing=declaration_with_source_framing(population,framed)?.2;
        if framed {checkpoint.stream.select_source_framing_prepared_input(&pairing)?;}else{checkpoint.stream.select_prepared_input(&pairing)?;}
    }
    if !resumed {
        checkpoint.provenance = format!(
            "complete Q+LF+A+LF; corpus SHA256 {}; backend {backend}; command {}; scope {scope:?}; no record-boundary resets",
            args[3], args[0]
        );
    }
    if let Some(s)=&stage{s.append_provenance(&mut checkpoint);}
    write_new(
        &out.join("CLOCK_CONTRACT.json"),
        clock_contract(&checkpoint)?.as_bytes(),
    )?;
    checkpoint.publish(out.join(if resumed{"resumed-opening.state"}else{"fresh.state"}).to_str().ok_or("UTF8 path")?)?;
    let reference = port();
    let pairing = declaration(population)?.2;
    let mut epoch_log = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(out.join("epochs.jsonl"))?;
    let mut at=stage.as_ref().map_or(0,|s|s.accepted);
    let mut epochs=stage.as_ref().map_or(0,|s|s.epoch_start);
    loop {
        if at<cells.len() {
            if let Some(s)=&stage {
                if let Some(reason)=s.stop_reason(at,started.elapsed()) {
                    s.seal(&checkpoint,out,backend,at,epochs,started.elapsed(),reason,false)?;
                    return Ok(());
                }
            }
        }
        if let Some(s)=&stage{s.snapshot(&checkpoint,out,at)?;}
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
        let mut end = next_cut.min(at.checked_add(remaining).ok_or("count overflow")?).min(cells.len());
        if let Some(s)=&stage {
            end=s.next_boundary(at,end);
            if let Some(reason)=s.stop_reason(at,started.elapsed()) {
                s.seal(&checkpoint,out,backend,at,epochs,started.elapsed(),reason,false)?;return Ok(());
            }
        }
        if end<=at{return Err("strict forward-only accepted source cursor".into());}
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
            if epoch.deposition_scope != scope || checkpoint.stream.scope() != scope {
                return Err(
                    "actual training scope differs from explicitly declared command".into(),
                );
            }
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
            if staged && epoch.cells!=epochs as u64*10{return Err("global native epoch lineage cannot reset on stage continuation".into());}
            let coarse = epoch
                .reads
                .iter()
                .fold(ExactInterval::point(integer(0)), |sum, read| {
                    ExactInterval {
                        lower: sum.lower + &read.code.lower,
                        upper: sum.upper + &read.code.upper,
                    }
                });
            // Compact authentic evidence; full actual return/energy only at declared cut crossings
            // or a held publication. This changes no target/model code or native operation.
            let full_evidence = !scope.is_local_receiving()
                || cuts.range((epoch.cells as usize - epoch.consumed)..=epoch.cells as usize).next().is_some()
                || epoch.deposit.epoch.as_ref().is_some_and(|e|e.held_receiving.is_some());
            let record = object(&[
                ("epoch", epochs.to_string()),
                ("source_cells", epoch.cells.to_string()),
                ("consumed", epoch.consumed.to_string()),
                ("closed_section", epoch.closed_section.to_string()),
                ("carry_out", epoch.carry_out.to_string()),
                ("commit", epoch.deposit.commit.to_string()),
                ("outcome", exact(&epoch.outcome)),
                ("deposition_scope", exact(&epoch.deposition_scope)),
                ("paired_receiving",epoch.deposit.epoch.as_ref().and_then(|e|e.paired_receiving.as_ref()).map_or_else(||"null".into(),|p|if full_evidence { exact(p) } else {object(&[
                    ("representation_policy",exact(&p.representation_policy)),
                    ("source_width",p.source_width.to_string()),
                    ("fresh_physical_alignment",quoted(&p.fresh_physical_alignment.to_string())),
                    ("fresh_return_error",quoted(&p.fresh_return_error.to_string())),
                    ("actual_alignment",p.actual_alignment.as_ref().map_or_else(||"null".into(),|v|quoted(&v.to_string()))),
                    ("blocks",format!("[{}]",p.blocks.iter().map(|b|object(&[("index",b.index.to_string()),("representation",b.representation.as_ref().map_or_else(||"null".into(),representation_evidence)),("crossings_before",b.crossings_before.to_string()),("crossings_after",b.crossings_after.to_string()),("gamma",quoted(&b.gamma.to_string())),("eta",quoted(&b.eta.to_string())),("normal_fall",quoted(&b.normal_fall.to_string()))])).collect::<Vec<_>>().join(","))),
                    ("full_evidence_deferred", "true".into()),
                ])})),
                ("held_receiving", epoch.deposit.epoch.as_ref().and_then(|e| e.held_receiving.as_ref()).map_or_else(|| "null".into(), |h| object(&[
                    ("paired_representative_block",epoch.deposit.epoch.as_ref().and_then(|e|e.paired_receiving.as_ref()).and_then(|p|p.held_representative_block).map_or_else(||"null".into(),|i|i.to_string())),
                    ("original_decline", exact(&h.original_decline)), ("gamma", quoted(&h.gamma.to_string())),
                    ("crossings_before",h.crossings_before.to_string()), ("crossings_after",h.crossings_after.to_string()),
                    ("gram_update",exact(&h.gram_update)), ("fresh_covector",exact(&h.fresh_covector)),
                    ("news_before",exact(&h.news_before)), ("news_after",exact(&h.news_after)),
                ]))),
                ("probe_state", exact(&epoch.probe_state)),
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
                    if full_evidence { exact(&epoch.retained_section_return) } else { "null".into() },
                ),
                ("whole_refusal", exact(&epoch.whole_stage_refusal)),
                ("joint_refusal", exact(&epoch.joint_stage_refusal)),
                ("wall", exact(&epoch.wall)),
                ("full_evidence_requested",full_evidence.to_string()),
                ("coarse_diagnostics",quoted(if scope.is_local_receiving(){"deferred; authentic raw retained source kept"}else{"observed"})),
                ("energy_closes",epoch.energy.closes().to_string()),
                ("actual_preparation_and_energy", if full_evidence {exact(&epoch.energy)} else {"null".into()}),
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
            ("command", quoted(&args[0])),
            ("receiving_representation_policy",exact(&checkpoint.stream.resident().constitution().receiving_representation_policy(2))),
            ("constitutive_return_policy",quoted(checkpoint.stream.resident().constitution().receiving_return_policy(2).ok_or("receiving return owner")?.tag())),
            ("deposition_scope", exact(&checkpoint.stream.scope())),
            (
                "input_preparation_law",
                checkpoint
                    .stream
                    .resident()
                    .prepared_input()
                    .map_or("null".into(), |p| quoted(p.law())),
            ),
            (
                "prepared_input_state",
                exact(&checkpoint.stream.resident().prepared_input()),
            ),
            ("e_scope", quoted(e_scope(scope, prepared_input))),
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
    if let Some(s)=&stage{s.seal(&checkpoint,out,backend,at,epochs,started.elapsed(),"full_source_complete",true)?;}
    Ok(())
}

fn sampling_policy(label: &str, prepared: bool) -> Result<continuation::SamplingPolicy> {
    match label {
        "native" | "fresh-native" => Ok(continuation::SamplingPolicy::NativeFullFibre),
        "native-zero-M" if prepared => Ok(continuation::SamplingPolicy::NativeZeroMControl),
        "native-context-zero" if prepared => Ok(continuation::SamplingPolicy::NativeContextZeroReadout),
        "combined-family" if prepared => Ok(continuation::SamplingPolicy::CombinedFamilyAblation),
        "combined-family-zero-M" if prepared => Ok(continuation::SamplingPolicy::CombinedFamilyZeroMControl),
        "founding-R" => Ok(continuation::SamplingPolicy::FoundingRAtSameHistory),
        "tree" => Ok(continuation::SamplingPolicy::Tree),
        _ => Err("unknown explicitly selected conditional sampling policy".into()),
    }
}

fn sample(args: &[String]) -> Result<()> {
    let started = Instant::now();
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
    let full_question = args[0] == "sample-prepared-retained-full-question-v1";
    let prompt_bound = if full_question { 512 } else { QUERY_BYTE_BUDGET };
    let long = full_question || args[0] == "sample-prepared-retained-512-v1";
    let cells = if long { 512 } else { 128 };
    let prepared = long || args[0] == "sample-prepared-retained-fibre-v1";
    if prepared != checkpoint.stream.resident().prepared_input().is_some() {
        return Err(
            "sample command and checkpoint input preparation law must match explicitly".into(),
        );
    }
    if args[7] == "fresh-native" && checkpoint.stream.accepted_cells()? != 0 {
        return Err(
            "fresh-native requires the selected run's saved pre-arrival fresh checkpoint".into(),
        );
    }

    let prompt = pinned_read(&args[3], &args[4], prompt_bound)?;
    let keys = pinned_read(&args[5], &args[6], cells * 8)?;
    let policy = sampling_policy(&args[7], prepared)?;
    let cold = match args[8].as_str() {
        "cold-replay" => Some(if long { 1 } else { 64 }),
        "no-replay" => None,
        _ => return Err("invalid cold replay declaration".into()),
    };
    let out = Path::new(&args[9]);
    std::fs::create_dir(out)?;
    let sample = if full_question { continuation::sample_full_question } else { continuation::sample_continuing };
    let receipt = sample(
        &checkpoint,
        &prompt,
        policy,
        &keys,
        cells,
        if long {
            &[0, 1, 4, 16, 64, 128, 256, 512]
        } else {
            &[0, 1, 4, 16, 64, 128]
        },
        cold,
        out,
    )?;
    write_new(&out.join("OUTPUT.bin"), &receipt.raw_bytes)?;
    write_new(
        &out.join("OUTPUT.json"),
        object(&[
            ("backend", quoted(&args[1])),
            ("command", quoted(&args[0])),
            ("prompt_byte_bound", prompt_bound.to_string()),
            ("prompt_bytes", prompt.len().to_string()),
            ("elapsed_ns", started.elapsed().as_nanos().to_string()),
            (
                "input_control",
                quoted(
                    if policy == continuation::SamplingPolicy::NativeZeroMControl {
                        "u=0 from first conditioning; learned M retained"
                    } else {
                        "learned u=eta_M"
                    },
                ),
            ),
            (
                "input_preparation_law",
                checkpoint
                    .stream
                    .resident()
                    .prepared_input()
                    .map_or("null".into(), |p| quoted(p.law())),
            ),
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

pub(super) fn run_with_execution(
    args: &[String],
    execution: &dyn ObservedEpochExecution,
    backend: CompleteLanguageTrainingBackend,
) -> Result<()> {
    match args.first().map(String::as_str) {
        Some("train") => train(args, execution, holonics::hnn::receiving::ReceivingLaw::CoarseGrainV1, backend,ObservedEpochDepositionScope::NormalMaps),
        Some("train-retained-fibre-v1") => train(args, execution, holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1, backend,ObservedEpochDepositionScope::NormalMaps),
        Some("train-local-retained-fibre-v1") => train(args,execution,holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1,backend,ObservedEpochDepositionScope::LocalReceivingReturn),
        Some("train-prepared-local-retained-fibre-v1") => train(args,execution,holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1,backend,ObservedEpochDepositionScope::LocalReceivingReturn),
        Some(stage::COMMAND) | Some("train-adaptive-family-local-arrival-held-v1") | Some("train-family-local-arrival-context-held-v1") | Some("train-source-framing-arrival-context-held-v1") | Some("train-source-framing-retained-held-v1") => train(args,execution,holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1,backend,ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap),
        Some("train-prepared-local-retained-held-v1") => train(args,execution,holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1,backend,ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap),
        Some("train-native") if backend == CompleteLanguageTrainingBackend::HostReference => native_train::train(args),
        Some("sample-native") if backend == CompleteLanguageTrainingBackend::HostReference => native_train::sample(args),
        Some("train-modes") if backend == CompleteLanguageTrainingBackend::HostReference => modes_train::train(args),
        Some("sample-modes") if backend == CompleteLanguageTrainingBackend::HostReference => modes_train::sample(args),
        Some("read-modes") if backend == CompleteLanguageTrainingBackend::HostReference => modes_train::read_text(args),
        Some("train-tower") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::train(args, false, false, false, false, holonics::hnn::tower::ContactLaw::Rectifying),
        Some("train-gated-tower") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::train(args, true, false, false, false, holonics::hnn::tower::ContactLaw::Rectifying),
        Some("train-turned-tower") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::train(args, true, true, false, false, holonics::hnn::tower::ContactLaw::Rectifying),
        Some("train-pumped-tower") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::train(args, true, true, true, false, holonics::hnn::tower::ContactLaw::Rectifying),
        Some("train-looking-gated-tower") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::train_looking(args, true, false, false),
        Some("train-looking-turned-tower") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::train_looking(args, true, true, false),
        Some("train-looking-pumped-tower") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::train_looking(args, true, true, true),
        Some("train-pair-pumped-tower") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::train(args, true, true, true, false, holonics::hnn::tower::ContactLaw::Pair),
        Some("train-pair-linear-pumped-tower") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::train(args, true, true, true, false, holonics::hnn::tower::ContactLaw::PairLinear),
        Some("train-credited-tower") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::train(args, true, false, false, true, holonics::hnn::tower::ContactLaw::Rectifying),
        Some("found-units") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::found_units(args),
        Some("train-unit-tower") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::train_units(args),
        Some("sample-unit-tower") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::sample_units(args),
        Some("read-unit-copy") if backend == CompleteLanguageTrainingBackend::HostReference => unit_copy::read(args),
        Some("sample-unit-copy") if backend == CompleteLanguageTrainingBackend::HostReference => unit_copy::sample(args),
        Some("read-joined") if backend == CompleteLanguageTrainingBackend::HostReference => modes_train::read_joined(args),
        Some("sample-joined") if backend == CompleteLanguageTrainingBackend::HostReference => modes_train::sample_joined(args),
        Some("sample-tower") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::sample(args),
        Some("read-lines") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_lines(args, false, tower_train::Look::Once, false),
        Some("read-lines-stream") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_lines(args, true, tower_train::Look::Once, false),
        Some("read-lines-again") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_lines(args, true, tower_train::Look::Again, false),
        Some("read-lines-redraw") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_lines(args, true, tower_train::Look::Redraw, false),
        Some("read-lines-carried") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_lines(args, true, tower_train::Look::Carried, false),
        Some("read-lines-own") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_lines(args, true, tower_train::Look::Own, false),
        Some("read-lines-located") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_lines(args, true, tower_train::Look::Again, true),
        Some("read-tower-pair") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_tower_pair(args),
        Some("read-tower-held") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_tower_held(args),
        Some("read-tower-held-cells") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_tower_held_cells(args),
        Some("read-tower-bank-trace") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_tower_bank_trace(args),
        Some("read-tower-faces") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_tower_faces(args),
        Some("read-tower-circuit") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_tower_circuit(args),
        Some("read-tower-modes") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_tower_modes(args),
        Some("read-tower-tension") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_tower_tension(args),
        Some("read-tower-floor") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_tower_floor(args),
        Some("found-tower-pair") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::found_tower_pair(args),
        Some("found-tower-situated") if backend == CompleteLanguageTrainingBackend::HostReference => tower_situated::found_tower_situated(args),
        Some("train-gated-tower-classes") if backend == CompleteLanguageTrainingBackend::HostReference => tower_classes::train(args, false, false, false, holonics::hnn::tower::TurnLadder::Fixed),
        Some("train-credited-tower-classes") if backend == CompleteLanguageTrainingBackend::HostReference => tower_classes::train(args, true, false, false, holonics::hnn::tower::TurnLadder::Fixed),
        Some("train-target-tower-classes") if backend == CompleteLanguageTrainingBackend::HostReference => tower_classes::train(args, true, true, false, holonics::hnn::tower::TurnLadder::Fixed),
        Some("train-turned-tower-classes") if backend == CompleteLanguageTrainingBackend::HostReference => tower_classes::train(args, false, false, true, holonics::hnn::tower::TurnLadder::Fixed),
        Some("train-scaled-tower-classes") if backend == CompleteLanguageTrainingBackend::HostReference => tower_classes::train(args, false, false, false, holonics::hnn::tower::TurnLadder::Scaled),
        Some("train-two-ladder-tower-classes") if backend == CompleteLanguageTrainingBackend::HostReference => tower_classes::train(args, false, false, false, holonics::hnn::tower::TurnLadder::Both),
        Some("read-tower-classes") if backend == CompleteLanguageTrainingBackend::HostReference => tower_classes::read(args),
        Some("found-tower-classes") if backend == CompleteLanguageTrainingBackend::HostReference => tower_bank::found(args),
        Some("join-tower-bank") if backend == CompleteLanguageTrainingBackend::HostReference => tower_bank::join(args),
        Some("found-tower-clock") if backend == CompleteLanguageTrainingBackend::HostReference => tower_bank::found_clock(args),
        Some("read-tower-clock-cells") if backend == CompleteLanguageTrainingBackend::HostReference => tower_bank::read_clock_cells(args),
        Some("train-sections-tower-classes") if backend == CompleteLanguageTrainingBackend::HostReference => tower_bank::train(args),
        Some("read-tower-classes-at") if backend == CompleteLanguageTrainingBackend::HostReference => tower_classes::read_at(args),
        Some("release-tower-classes") if backend == CompleteLanguageTrainingBackend::HostReference => tower_classes::release(args),
        Some("found-tower-ring") if backend == CompleteLanguageTrainingBackend::HostReference => tower_ring::found_tower_ring(args),
        Some("join-tower-ring") if backend == CompleteLanguageTrainingBackend::HostReference => tower_ring::join_tower_ring(args),
        Some("read-tower-at") if backend == CompleteLanguageTrainingBackend::HostReference => tower_ring::read_tower_at(args),
        Some("read-tower-cells") if backend == CompleteLanguageTrainingBackend::HostReference => tower_ring::read_tower_cells(args),
        Some("found-ring-readout") if backend == CompleteLanguageTrainingBackend::HostReference => tower_ring::found_ring_readout(args),
        Some("pass-ring-held") if backend == CompleteLanguageTrainingBackend::HostReference => tower_ring::pass_ring_held(args),
        Some("read-tower-situated-moments") if backend == CompleteLanguageTrainingBackend::HostReference => tower_situated::read_tower_situated_moments(args),
        Some("read-tower-situated") if backend == CompleteLanguageTrainingBackend::HostReference => tower_situated::read_tower_situated(args),
        Some("read-tower-input-covectors") if backend == CompleteLanguageTrainingBackend::HostReference => tower_situated::read_tower_input_covectors(args),
        Some("found-tower-pair-block") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::found_tower_pair_block(args),
        Some("install-tower-pair-block") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::install_tower_pair_block(args),
        Some("sample-tower-block") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::sample_tower_block(args),
        Some("join-tower-pair-face") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::join_tower_pair_face(args),
        Some("read-tower-pair-cells") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_tower_pair_cells(args),
        Some("read-tower-pair-leverage") if backend == CompleteLanguageTrainingBackend::HostReference => tower_train::read_tower_pair_leverage(args),
        Some("train-duplex") if backend == CompleteLanguageTrainingBackend::HostReference => duplex_train::train(args),
        Some("read-lines-duplex") if backend == CompleteLanguageTrainingBackend::HostReference => duplex_train::read_lines(args),
        Some("train-native" | "sample-native") => Err("the native route's commands are host-owned; no CUDA fallback".into()),
        Some("sample" | "sample-prepared-retained-fibre-v1" | "sample-prepared-retained-512-v1" | "sample-prepared-retained-full-question-v1") if backend == CompleteLanguageTrainingBackend::HostReference => sample(args),
        Some("sample" | "sample-prepared-retained-fibre-v1" | "sample-prepared-retained-512-v1" | "sample-prepared-retained-full-question-v1") => Err("complete-language continuation remains explicitly host-owned; no CUDA fallback".into()),
        _ => Err("complete-language requires train, explicit train-retained-fibre-v1 (reference), train-local-retained-fibre-v1 (R/tree/population only), train-prepared-local-retained-fibre-v1 (host prepared input + local R), train-prepared-local-retained-held-v1 (explicit held-map continuation), train-source-framing-retained-held-v1 (explicit known byte-position context), sample, or sample-prepared-retained-fibre-v1; no default backend/model action".into()),
    }
}
/// The class-passage tower commands with each section's forward and reverse through a declared
/// realization (`hnn::tower::realization`; `holonics-cuda`'s `tower_pass` example passes the card).
pub(super) fn run_tower_classes_realized(args: &[String], realization: &mut dyn holonics::hnn::tower::realization::PassRealization) -> Result<()> {
    use holonics::hnn::tower::TurnLadder;
    match args.first().map(String::as_str) {
        Some("train-gated-tower-classes") => tower_classes::train_realized(args, false, false, false, TurnLadder::Fixed, realization),
        Some("train-scaled-tower-classes") => tower_classes::train_realized(args, false, false, false, TurnLadder::Scaled, realization),
        Some("train-two-ladder-tower-classes") => tower_classes::train_realized(args, false, false, false, TurnLadder::Both, realization),
        _ => Err("a realized route trains the gated tower on a class passage: train-gated-tower-classes, train-scaled-tower-classes or train-two-ladder-tower-classes".into()),
    }
}

pub(super) fn run(args: &[String]) -> Result<()> {
    run_with_execution(
        args,
        &HostObservedEpochExecution,
        CompleteLanguageTrainingBackend::HostReference,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn receiver_ablation_cli_is_explicit_and_requires_prepared_state() {
        assert_eq!(sampling_policy("combined-family",true).unwrap(),continuation::SamplingPolicy::CombinedFamilyAblation);
        assert_eq!(sampling_policy("combined-family-zero-M",true).unwrap(),continuation::SamplingPolicy::CombinedFamilyZeroMControl);
        assert!(sampling_policy("combined-family",false).is_err());
        assert!(sampling_policy("combined-family-zero-M",false).is_err());
        assert_eq!(sampling_policy("native",true).unwrap(),continuation::SamplingPolicy::NativeFullFibre);
        assert_eq!(sampling_policy("native-zero-M",true).unwrap(),continuation::SamplingPolicy::NativeZeroMControl);
        assert!(sampling_policy("combined-family-rho-one",true).is_err());
    }
    #[test]
    #[ignore = "bounded CODE control requires the explicitly pinned existing synthetic checkpoint"]
    fn receiver_ablation_synthetic_prepared_cold_and_frozen_owner() {
        let path=std::env::var("A18_SYNTHETIC_CHECKPOINT").expect("explicit synthetic fixture");
        let expected=std::env::var("A18_SYNTHETIC_SHA256").expect("fixture hash");
        assert_eq!(sha256(&std::fs::read(&path).unwrap()).unwrap(),expected);
        let (checkpoint,_)=Checkpoint::load(&path,READ_BUDGET).unwrap();
        let before=checkpoint.bytes().unwrap();
        assert_eq!(checkpoint.stream.accepted_cells().unwrap(),40);
        for policy in [continuation::SamplingPolicy::NativeFullFibre,
            continuation::SamplingPolicy::CombinedFamilyAblation,
            continuation::SamplingPolicy::CombinedFamilyZeroMControl] {
            let out=std::path::Path::new(&std::env::var("A18_CODE_OUTPUT").unwrap()).join(policy.label());
            std::fs::create_dir(&out).unwrap();
            let result=continuation::sample_continuing(&checkpoint,b"A",policy,&[0x55;64],8,
                &[0,1,4,8],Some(1),&out).unwrap();
            assert_eq!(result.classes.len(),8);
            assert_eq!(result.raw_bytes,Base4Bytes::decode(&result.classes,8).unwrap().bytes);
            assert!(result.cold_continuation.unwrap().matched_warm_state_and_crib);
            assert_eq!(checkpoint.bytes().unwrap(),before);
            let freeze=std::fs::read_to_string(out.join("FROZEN_MATERIAL.json")).unwrap();
            assert!(freeze.contains("\"native_laws_unchanged\":true"));
            assert!(freeze.contains("\"empirical_material_unchanged\":true"));
            let progress=std::fs::read_to_string(out.join("classes.jsonl")).unwrap();
            assert!(progress.lines().all(|r|r.contains("\"selected_receiver\"")&&r.contains("\"selected_masses\"")&&r.contains("\"combined_masses\"")));
            if policy==continuation::SamplingPolicy::CombinedFamilyZeroMControl {
                let first=std::fs::read_to_string(out.join("CONDITIONING_FIRST.json")).unwrap();
                assert!(first.contains("ForecastZeroControl"));
                assert!(first.contains("\"added_and_work_zero\":true"));
            }
            println!("A18_SYNTHETIC_CONTROL policy={} output_classes=8 prompt_classes=4 cold_replayed_classes=4 frozen=true",policy.label());
        }
    }
    #[test]
    fn local_cli_constructor_cold_and_continuation_scope_are_explicit() {
        let local = fresh_checkpoint_at_law_and_scope(
            16384,
            holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1,
            ObservedEpochDepositionScope::LocalReceivingReturn,
        )
        .unwrap();
        let old = fresh_checkpoint_at_law(
            16384,
            holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1,
        )
        .unwrap();
        assert_eq!(old.stream.scope(), ObservedEpochDepositionScope::NormalMaps);
        assert_eq!(
            local.stream.scope(),
            ObservedEpochDepositionScope::LocalReceivingReturn
        );
        assert_eq!(local.stream.accepted_cells().unwrap(), 0);
        assert!(
            fresh_checkpoint_at_law_and_scope(
                16384,
                holonics::hnn::receiving::ReceivingLaw::CoarseGrainV1,
                ObservedEpochDepositionScope::LocalReceivingReturn
            )
            .is_err()
        );
        let reference = port();
        let fork = continuation::code_scope_preserving_checkpoint(&local, &reference).unwrap();
        assert_eq!(
            fork.stream.scope(),
            ObservedEpochDepositionScope::LocalReceivingReturn
        );
        assert_eq!(
            fork.stream.resident().continuing_state(0).unwrap(),
            local.stream.resident().continuing_state(0).unwrap()
        );
    }
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
        let decisions = std::fs::read_to_string(out.join("classes.jsonl")).unwrap();
        assert_eq!(decisions.lines().count(), 8);
        for line in decisions.lines() {
            for key in [
                "certified_draw",
                "certified_key_margin_lower",
                "native_masses",
                "founding_R_masses",
                "tree_masses",
                "native_minus_tree",
                "native_minus_founding_R",
            ] {
                assert!(line.contains(key));
            }
            assert!(line.contains("\"extra_word_score_root_calls_for_receipt\":0"));
        }

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

#[cfg(test)]
pub(super) fn code_prepared_late_rollback(
    execution: &dyn ObservedEpochExecution,
) -> Result<String> { code_prepared_late_rollback_at_scope(execution, ObservedEpochDepositionScope::LocalReceivingReturn,false) }
#[cfg(test)]
pub(super) fn code_held_prepared_late_rollback(
    execution: &dyn ObservedEpochExecution,
) -> Result<String> { code_prepared_late_rollback_at_scope(execution, ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap,false) }
#[cfg(test)]
pub(super) fn code_framed_prepared_late_rollback(execution:&dyn ObservedEpochExecution)->Result<String>{code_prepared_late_rollback_at_scope(execution,ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap,true)}
#[cfg(test)]
fn code_prepared_late_rollback_at_scope(
    execution: &dyn ObservedEpochExecution, scope: ObservedEpochDepositionScope, framed:bool,
) -> Result<String> {
    code_prepared_late_rollback_at_input_context(execution,scope,framed,false)
}
#[cfg(test)]
pub(super) fn code_paired_prepared_late_rollback(execution:&dyn ObservedEpochExecution)->Result<String>{
    code_prepared_late_rollback_at_input_context(execution,ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap,true,true)
}
#[cfg(test)]
fn code_prepared_late_rollback_at_input_context(execution:&dyn ObservedEpochExecution,scope:ObservedEpochDepositionScope,framed:bool,arrival:bool)->Result<String>{
    let mut checkpoint = fresh_checkpoint_at_input_context(
        16384, holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1,
        scope, framed, arrival,
    )?;
    let pairing = checkpoint.declaration()?.2;
    if framed {checkpoint.stream.select_source_framing_prepared_input(&pairing)?;}else{checkpoint.stream.select_prepared_input(&pairing)?;}
    let before = checkpoint.bytes()?;
    let err = checkpoint
        .stream
        .receive_with_execution(&port(), &pairing, &digits(&[0x1b; 3])[..10], execution)
        .unwrap_err();
    if checkpoint.bytes()? != before {
        return Err("late card refusal must preserve native/M/pending/carry exactly".into());
    }
    Ok(err.to_string())
}

#[cfg(test)]
pub(super) fn code_prepared_arrival_context(
    execution: &dyn ObservedEpochExecution,
) -> Result<(String, String, String)> {
    let (field, mut initial, pairing) = declaration(16384)?;
    initial.bind_arrival_context_receiving(2)?;
    let opening = initial.clone();
    let reference = port();
    let mut resident = reference.mount_declared_receiving_law(
        &field,
        &Current::at_rest(&field),
        initial,
        holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1,
    )?;
    let boundary = PairedObservation::admit(&field, resident.constitution(), &pairing)?;
    reference.ingest(&mut resident, None, &boundary.encode(&[])?)?;
    let mut stream = ObservedStream::new(
        resident,
        ObservedCrib::new(0),
        ObservedEpochDepositionScope::LocalReceivingReturn,
    )?;
    stream.select_prepared_input(&pairing)?;
    let before = stream.resident().continuing_state(0)?;
    let refusal = stream
        .receive_with_execution(&reference, &pairing, &digits(&[0x1b; 3])[..10], execution)
        .unwrap_err();
    assert!(
        refusal
            .to_string()
            .contains("an epoch normal locus must exist as one declared linear law")
    );
    assert_eq!(
        stream.resident().continuing_state(0)?,
        before,
        "unsupported paired local normal publication is atomic"
    );
    let cold = reference.mount_continued(&field, &Current::at_rest(&field), opening, &before)?;
    assert_eq!(cold.continuing_state(0)?, before);
    Ok((
        before.to_text(),
        refusal.to_string(),
        "paired local R publication UNJOINED; actual prepared words/returns compared by executor"
            .into(),
    ))
}

#[cfg(test)]
pub(super) fn code_family_local_late_rollback(execution:&dyn ObservedEpochExecution)->Result<String>{code_receiving_late_rollback(execution,false)}
#[cfg(test)]
pub(super) fn code_adaptive_receiving_late_rollback(execution:&dyn ObservedEpochExecution)->Result<String>{code_receiving_late_rollback(execution,true)}
#[cfg(test)]
fn code_receiving_late_rollback(execution:&dyn ObservedEpochExecution,adaptive:bool)->Result<String>{
    let mut checkpoint=fresh_family_local_checkpoint_at_representation(16384,ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap,adaptive)?;
    let pairing=checkpoint.declaration()?.2;
    checkpoint.stream.select_source_framing_prepared_input(&pairing)?;
    let before=checkpoint.bytes()?;
    let error=checkpoint.stream.receive_with_execution(&port(),&pairing,&digits(&[0x1b;3])[..10],execution).unwrap_err();
    if checkpoint.bytes()?!=before {return Err("family-local late aggregate refusal changed native/M/crib/pending".into());}
    Ok(error.to_string())
}

#[cfg(test)]
pub(super) fn code_durable_continuation(execution:&dyn ObservedEpochExecution,backend:CompleteLanguageTrainingBackend,path:&Path)->Result<(Vec<u8>,String)>{stage::exercise(execution,backend,path)}
