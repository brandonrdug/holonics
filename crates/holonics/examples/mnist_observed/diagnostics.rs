//! Read-only, reset-address probes and exact gradient activity reports.
//! These measurements never supply labels to inference and never deposit probe results.
use super::*;
use holonics::hnn::field::ConstitutionRead;
use holonics::hnn::port::{Deposit, Pullback};
use holonics::ratio::Rat;

fn nonzero<'a>(values: impl IntoIterator<Item = &'a Rat>) -> usize {
    values.into_iter().filter(|x| **x != integer(0)).count()
}

pub(super) fn gradient_report(image: usize, pullback: &Pullback, deposit: &Deposit) {
    println!(
        "gradient_activity image={image} receiving_ring={} receiving_nonzero={} receiving_entries={} landmark_steps={} population_steps={}",
        pullback.receiving.0,
        nonzero(pullback.receiving.1.entries()),
        pullback.receiving.1.entries().len(),
        deposit.landmarks().len(),
        deposit.receiving().len()
    );
    for ring in &pullback.rings {
        if let Some(source) = &ring.source {
            println!(
                "gradient_activity image={image} source_ring={} source_nonzero={} source_entries={}",
                ring.ring,
                nonzero(source.entries()),
                source.entries().len()
            );
        }
        for (offset, parts) in &ring.pair {
            println!(
                "gradient_activity image={image} source_ring={} offset={offset} pair_output_nonzero={} pair_current_nonzero={} pair_earlier_nonzero={}",
                ring.ring,
                nonzero(parts[0].iter().flatten()),
                nonzero(parts[1].iter().flatten()),
                nonzero(parts[2].iter().flatten())
            );
        }
    }
    for step in deposit.linear() {
        println!(
            "linear_activity image={image} locus={:?} samples={} feature_nonzero={} covector_nonzero={}",
            step.locus,
            step.samples.len(),
            nonzero(step.samples.iter().flat_map(|s| &s.feature)),
            nonzero(step.samples.iter().flat_map(|s| &s.covector))
        );
    }
}

pub(super) fn material_report(
    image: usize,
    field: &Field,
    before: &Constitution,
    after: &Constitution,
) {
    for ring in 0..field.rings().len() {
        if before.receiving_map(ring).is_some() {
            println!(
                "material_activity image={image} receiving_ring={ring} receiving_changed={}",
                before.receiving_map(ring) != after.receiving_map(ring)
            );
        }
    }
    for &ring in field.sources() {
        println!(
            "material_activity image={image} source_ring={ring} source_changed={}",
            before.source_port(ring) != after.source_port(ring)
        );
        for &offset in field.offsets() {
            println!(
                "material_activity image={image} source_ring={ring} offset={offset} pair_changed={}",
                before.pair_port(ring, offset) != after.pair_port(ring, offset)
            );
        }
    }
}

pub(super) fn fixed_state<P, Mount>(
    port: &P,
    mount: &Mount,
    field: &Field,
    chart: InputChart,
    periods: [u64; 3],
    mode_view: &holonics::hnn::ring::modes::ModeView,
    pairing: &PairingDeclaration,
    frozen: &Constitution,
    current: &Current,
    original: &Raster,
) -> Result<()>
where
    P: ExecutionPort,
    P::Resident: ExposedResident,
    Mount: Fn(&Field, &Current, Constitution) -> std::result::Result<P::Resident, HnnError>,
{
    let boundary = PairedObservation::admit(field, frozen, pairing)?;
    let blank = Raster::new(original.grid(), vec![0; original.samples().len()])?;
    // Fixed reversal preserves the exact pixel histogram at every raster extent.
    let permuted = Raster::new(
        original.grid(),
        original.samples().iter().rev().copied().collect(),
    )?;
    let mut baseline: Option<ObservationRead> = None;
    let mut baseline_moment = None;
    let mut baseline_storage = None;
    for (name, raster) in [
        ("original", original.clone()),
        ("blank", blank),
        ("reverse_pixel_permutation", permuted),
    ] {
        let mut resident = mount(field, current, frozen.clone())?;
        if resident.current() != current {
            return Err("probe mount changed the requested opening current".into());
        }
        if resident.constitution() != frozen {
            return Err("probe mount changed the requested frozen material".into());
        }
        let (read, _timing) = predict(
            port,
            &mut resident,
            field,
            chart,
            periods,
            mode_view,
            None,
            false,
            None,
            &boundary,
            raster,
            StageProgress {
                role: "fixed_state_probe",
                image: 0,
                enabled: false,
            },
            ClassGrain::Off,
        )?;
        if resident.constitution() != frozen {
            return Err("a fixed-state probe changed material".into());
        }
        let moment = resident
            .moment(&read.moment)
            .ok_or("probe moment missing")?;
        let storage = moment.open_storage(field, frozen, resident.current())?;
        // Independent host execution of the same producing operands. This is a parity/causality
        // reading, not a second learner; a fresh probe has the rest reception opening.
        let phases = resident
            .admitted()
            .first()
            .ok_or("probe receiver missing")?;
        let mut word = holonics::hnn::word::Word::open(field, frozen, resident.current(), moment)?;
        let anchors = word.forward(phases)?;
        let host_reads = anchors
            .iter()
            .map(|anchor| phases.read(field, frozen, anchor))
            .collect::<std::result::Result<Vec<_>, _>>()?;
        let host_faces = Faces::of_reads(&host_reads, phases.grain())?;
        let map = frozen
            .receiving_map(phases.ring())
            .ok_or("probe receiving map missing")?;
        let law = frozen
            .receiving_law(phases.ring())
            .ok_or("probe receiving law missing")?;
        let remainder = law.map_remainder();
        println!(
            "fixed_state_receiving_law variant={name} prior_scale={} founding_prior={:?} published_map_nonzero={} map_remainder_nonzero={} published_map={:?} map_remainder={:?}",
            law.prior_scale(),
            law.receiving_prior(),
            nonzero(map.entries()),
            nonzero(remainder.entries()),
            map.entries(),
            remainder.entries()
        );

        println!(
            "fixed_state_receiver variant={name} receiver_ring={} junction_steps={} host_anchors={anchors:?} map_nonzero={} map_entries={} host_logits={:?} executed_logits_match_host={}",
            phases.ring(),
            phases.junction_steps(),
            nonzero(map.entries()),
            map.entries().len(),
            host_faces.logits,
            host_faces.logits == read.faces.logits
        );

        println!(
            "fixed_state_source variant={name} retained_moment_changed={:?} source_storage_changed={:?} source_storage={storage:?}",
            baseline_moment.as_ref().map(|base| base != moment),
            baseline_storage.as_ref().map(|base| base != &storage)
        );
        for &ring in field.sources() {
            use holonics::hnn::ring::modes::{decompose, reconstruct};
            let modes = decompose(field.ring(ring), &storage[ring])?;
            if reconstruct(&modes)? != storage[ring] {
                return Err("cyclic modes did not reconstruct actual source storage".into());
            }
            let previous = baseline_storage
                .as_ref()
                .map(|base: &Vec<Vec<Rat>>| decompose(field.ring(ring), &base[ring]))
                .transpose()?;
            for (index, mode) in modes.iter().enumerate() {
                println!(
                    "fixed_state_cyclic_mode variant={name} source_ring={ring} primitive_period={} coordinates={:?} changed_from_original={:?} reconstruction_exact=true interpretation=transport_subspace",
                    mode.period,
                    mode.coordinates,
                    previous
                        .as_ref()
                        .map(|base| base[index].coordinates != mode.coordinates)
                );
            }
        }
        if baseline_moment.is_none() {
            baseline_moment = Some(moment.clone());
            baseline_storage = Some(storage);
        }

        println!(
            "fixed_state_probe variant={name} same_material=true same_opening_current=true reset_address=true labels_used=false raw_logits={:?} raw_cells={:?} raw_phases={:?} raw_codes={:?} release_codes={:?}",
            read.faces.logits,
            read.faces.faces[0].cells(),
            read.faces.faces[0].phases(),
            read.pre_release.code_lengths,
            read.released.as_ref().map(|x| &x.code_lengths)
        );
        if let Some(base) = &baseline {
            println!(
                "fixed_state_difference variant={name} raw_logits_changed={} raw_grain_cells_changed={} raw_codes_changed={} released_codes_changed={}",
                base.faces.logits != read.faces.logits,
                base.faces.faces[0].cells() != read.faces.faces[0].cells(),
                base.pre_release.code_lengths != read.pre_release.code_lengths,
                base.released.as_ref().map(|x| &x.code_lengths)
                    != read.released.as_ref().map(|x| &x.code_lengths)
            );
        }
        // The local resident is dropped with its read-only handles; no continuation is asserted.
        if baseline.is_none() {
            baseline = Some(read);
        }
    }
    Ok(())
}

/// Actual staged receiver-return seeds and the declared first split, before any material update.
pub(super) fn return_precision_report(
    image: usize,
    field: &Field,
    material: &Constitution,
    deposit: &Deposit,
    receipt: &holonics::hnn::port::PortReceipt,
) -> Result<()> {
    use holonics::hnn::chart::Remainders;
    use holonics::hnn::constitution::LinearLocus;
    let lattice = field.word_lattice().map(|word| word.transient());
    for step in deposit.linear() {
        if let LinearLocus::Receiving(ring) = step.locus {
            let transpose = material
                .receiving_map(ring)
                .ok_or("missing receiving map")?
                .transpose()?;
            for (sample_index, sample) in step.samples.iter().enumerate() {
                let gradient = sample.covector.iter().map(|x| -x).collect::<Vec<_>>();
                let seed = transpose.apply(&gradient)?;
                let mut remainder = vec![integer(0); seed.len()];
                let carried = match &lattice {
                    Some(at) => holonics::hnn::chart::carry(at, &seed, &mut remainder),
                    None => seed.clone(),
                };
                println!(
                    "return_seed image={image} ring={ring} sample={sample_index} unrotated_R_transpose_g={seed:?} seed_nonzero={} declared_transient_exponent={:?} zero_opening_declared_first_split_nonzero={} declared_first_split_remainder={:?} rotation_preserves_lattice_split_counts=true",
                    nonzero(&seed),
                    lattice.as_ref().map(|x| x.exponent()),
                    nonzero(&carried),
                    Remainders::of(&remainder)
                );
            }
        }
    }
    if let holonics::hnn::port::ReceiptDetail::Compare {
        released,
        return_precision,
        ..
    } = &receipt.detail
    {
        println!(
            "return_released image={image} actual_same_return_aggregate={released:?} precision={return_precision:?} aggregate_has_no_signed_coordinate_reconstruction=true"
        );
    }
    Ok(())
}

/// Counterfactual reads of one already-ingested native passage. The live production resident
/// is untouched. Each alternative restores its own exact carry/address/charts; these extra
/// traversals are diagnostics, not an attention policy or additional label observations.
/// The pilot host witness uses the declared Carry(Nothing) reception (or AtRest).
pub(super) fn continued_views<P: ExecutionPort>(
    port: &P,
    field: &Field,
    opening: &Constitution,
    state: &ContinuingState,
    views: &[(&str, ModeView)],
    grains: &[u64],
) -> Result<()>
where
    P::Resident: ExposedResident,
{
    use holonics::hnn::pending::PendingRatio;
    use holonics::hnn::receiving::{ReceivingRead, faces_of_splits, window_splits};
    use holonics::hnn::retention::Opens;
    use holonics::hnn::word::{Absorption, Word, WordOpening};
    let passage = state
        .resident_passage(field, opening)?
        .ok_or("view probe needs full passage")?;
    let parts = passage.parts();
    let (id, moment) = parts
        .moment
        .as_ref()
        .ok_or("view probe needs an ingested moment")?;
    let phases = parts
        .admitted
        .first()
        .ok_or("view probe needs admitted receiver")?;
    let material = opening.clone().continued_on(field, state)?;
    let word_opening = match (parts.opens, state.carry()) {
        (Opens::OnMotion, Some(carry)) => WordOpening::Received {
            carry: carry.clone(),
            absorption: Absorption::Nothing,
        },
        _ => WordOpening::Rest,
    };
    let storage = moment.open_storage(field, &material, &parts.current)?;
    let addresses = phases.addresses(&parts.address, &[])?;
    let tree = material
        .landmarks(phases.ring())
        .ok_or("view probe tree missing")?;
    let splits = if phases.observation_partition().is_none() {
        Some(window_splits(tree, &addresses, &[])?)
    } else {
        None
    };
    println!(
        "continued_view_context current={:?} address_letters={:?} reader={:?} addresses={addresses:?} tree_splits={splits:?} carry_present={} grain={} labels_used=false diagnostic_counterfactual=true",
        parts.current,
        parts.address.letters(),
        parts.address.reader(),
        state.carry().is_some(),
        phases.grain()
    );
    let mut baseline: Option<(Vec<Vec<Rat>>, Vec<Vec<Rat>>, Vec<Vec<Rat>>)> = None;
    for (name, view) in views {
        let started = Instant::now();
        let mut resident = port.mount_continued(field, &parts.current, opening.clone(), state)?;
        if resident.current() != &parts.current
            || resident.constitution() != &material
            || resident.carried() != state.carry()
        {
            return Err("view probe restore changed producing state".into());
        }
        let projected = view.apply(field, &storage)?;
        let mut charts = parts.charts.clone();
        let mut word = Word::open_received_view(
            field,
            &material,
            &parts.current,
            moment,
            &mut charts,
            &word_opening,
            view,
        )?;
        let anchors = word.forward(phases)?;
        let reads = anchors
            .iter()
            .map(|a| phases.read(field, &material, a))
            .collect::<std::result::Result<Vec<_>, _>>()?;
        let host_faces = Faces::of_reads(&reads, phases.grain())?;
        let (pending, refined) = match port.refine_view(&mut resident, id, phases, view) {
            Ok(value) => value,
            Err(error) => {
                println!(
                    "continued_view_refused name={name} error={error:?} elapsed_ns={} host_witness_traversals=1 labels_compared=0",
                    started.elapsed().as_nanos()
                );
                continue;
            }
        };
        let actual = refined
            .forward
            .present()
            .ok_or("view probe returned no wave face")?;
        if actual != &host_faces {
            return Err("same-passage host/device view mismatch".into());
        }
        let mut ratio = PendingRatio::produce(
            &parts.current,
            moment,
            &parts.address,
            phases,
            material.commit(),
        )?
        .with_view(field, view)?;
        ratio.admit_observed_read(field, &anchors, actual)?;
        let view_splits = if let Some(observed) = ratio.observed_addresses(&[])? {
            let window = tree.window_observed(&observed, &[])?;
            (0..window.phases())
                .map(|j| window.splits(j))
                .collect::<Vec<_>>()
        } else {
            splits.clone().ok_or("causal tree splits missing")?
        };
        println!(
            "continued_view_observation name={name} observation_bits={:?} tree_splits={view_splits:?}",
            ratio.observation_bits()
        );
        let combined = ratio.against(&material, actual, &[])?.faces;
        println!(
            "continued_view name={name} selection={:?} source={projected:?} anchors={anchors:?} raw_logits={:?} source_changed={:?} anchor_changed={:?} logits_changed={:?} exact_host_parity=true",
            view.selections(),
            actual.logits,
            baseline.as_ref().map(|b| b.0 != projected),
            baseline.as_ref().map(|b| b.1 != anchors),
            baseline.as_ref().map(|b| b.2 != actual.logits)
        );
        for (station, (wave, total)) in actual.faces.iter().zip(&combined.faces).enumerate() {
            println!(
                "continued_view_face name={name} station={station} grain={} raw_cells={:?} raw_phase_turns={:?} raw_maxima={:?} combined_cells={:?} combined_phase_turns={:?} combined_maxima={:?}",
                phases.grain(),
                wave.cells(),
                wave.phases(),
                wave.maximal_mass_classes(),
                total.cells(),
                total.phases(),
                total.maximal_mass_classes()
            );
        }
        // Re-exponentiate sparse retained tree splits and raw wave reads only. This does not
        // authorize a production receiver rechart, change declared phases, or teach a target.
        for &grain in grains {
            if grain == 0 {
                return Err("diagnostic receiver grain must be positive".into());
            }
            let trees = faces_of_splits(tree.declaration(), &view_splits, grain)?;
            for (station, (logits, tree_face)) in actual.logits.iter().zip(&trees).enumerate() {
                let raw = Face::of_read(&ReceivingRead::of_logits(logits.clone(), grain), grain)?;
                let total = Face::of_read(
                    &ReceivingRead::combined(logits.clone(), tree_face, grain)?,
                    grain,
                )?;
                println!(
                    "continued_view_resolution name={name} station={station} diagnostic_grain={grain} raw_cells={:?} raw_maxima={:?} combined_cells={:?} combined_maxima={:?} production_grain_unchanged=true",
                    raw.cells(),
                    raw.maximal_mass_classes(),
                    total.cells(),
                    total.maximal_mass_classes()
                );
            }
        }
        let rule = DecisionRule::new(
            "same-state diagnostic release",
            WithinTolerance::Release,
            BeyondTolerance::Hold,
        );
        let released = port.release(&mut resident, &pending, &rule)?;
        println!(
            "continued_view_execution name={name} refine_work={:?} release_work={:?} released={} elapsed_ns={} host_witness_traversals=1 state_advancing_clone_traversals=1 labels_compared=0",
            refined.receipt.work,
            released.receipt.work,
            released.forward.present().is_some(),
            started.elapsed().as_nanos()
        );
        port.discard(&mut resident, Handle::Pending(pending))?;
        port.discard(&mut resident, Handle::Moment(*id))?;
        if baseline.is_none() {
            baseline = Some((projected, anchors, actual.logits.clone()));
        }
    }
    Ok(())
}
