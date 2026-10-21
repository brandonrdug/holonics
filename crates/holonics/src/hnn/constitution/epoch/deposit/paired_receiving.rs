//! Local retained publication for two independently charted receiving normals.
//! Only the joined PHYSICAL ray is certified. No joined normal law is retained.
use super::*;

pub(super) struct Prepared {
    owner: ReceivingMaterial,
    samples: Vec<Sample>,
    laws: [Option<EpochLaw>; 2],
    flows: [Option<EpochFlow>; 2],
    aggregation_scales: [Rat; 2],
    face: EpochCertificateFace,
    certificate: EpochReceivingCertificate,
    certified: BTreeMap<(Locus, Family), StepReading>,
    fresh_joint: Option<JointReading>,
    envelope: Reach,
    reaches: Vec<Reach>,
    series: EpochReceivingSeries,
    population: Vec<crate::hnn::receiving::ReceivingStep>,
    reached: BTreeSet<Locus>,
    landmarks: u64,
    grain: u32,
}

fn joined(left: &ExactRatMatrix, right: &ExactRatMatrix) -> Result<ExactRatMatrix, HnnError> {
    if left.rows() != right.rows() {
        return Err(refused("joined physical block rows agree"));
    }
    Ok(ExactRatMatrix::new(
        left.to_rows()
            .into_iter()
            .zip(right.to_rows())
            .map(|(mut a, b)| {
                a.extend(b);
                a
            })
            .collect(),
    )?)
}
/// Preserve the original declared odd phase divisor; no approximation is made.
fn physical_array(m: &ExactRatMatrix, period: u64) -> Result<EpochArray, HnnError> {
    let mut rows = m.to_rows();
    for row in rows.iter_mut().skip(1).step_by(2) {
        for x in row {
            *x *= Rat::from_integer(period.into());
        }
    }
    let a = EpochArray::from_dyadic_matrix(&rows_matrix(&rows))?;
    EpochArray::with_row_divisors(
        a.rows,
        a.columns,
        a.exponent,
        a.values,
        (0..m.rows())
            .map(|r| if r % 2 == 1 { period } else { 1 })
            .collect(),
    )
}
fn face(
    direction: &EpochArray,
    c: &EpochReceivingCertificate,
    covector: Rat,
) -> Result<EpochCertificateFace, HnnError> {
    let (n, d) = direction.integral_chart()?;
    let unit = IntegralMatrix::from_grouped(direction.rows, direction.columns, n, d)?;
    let unit_norms = unit.schur_norms();
    Ok(EpochCertificateFace {
        unit,
        alignment: (&c.alignment - &c.return_error).max(Rat::zero()),
        moves: c.moves.clone(),
        covector: covector.max(c.oscillation.clone()).max(Rat::one()),
        unit_norms,
        norm: EpochSpectral::grouped_frobenius(direction),
    })
}

/// Exact temporary transport scale only. Frozen operand charts, H/G and their units
/// are restored after the selected executor's guarded unit-feature aggregation.
fn block_flow(
    stage: &ObservedNormalEpochStage<'_>,
    law: &EpochLaw,
    samples: &[Sample],
    grain: u32,
    trace: &mut EpochStageTrace,
) -> Result<(EpochFlow, Rat), HnnError> {
    let max = samples
        .iter()
        .flat_map(|s| &s.feature)
        .map(Signed::abs)
        .max()
        .unwrap_or_default();
    let mut scale = Rat::one();
    while scale < max {
        scale *= Rat::from_integer(2.into());
    }
    let mut transport = samples.to_vec();
    for s in &mut transport {
        for f in &mut s.feature {
            *f /= &scale;
        }
    }
    let rows: Vec<_> = (1..law.map.rows).step_by(2).collect();
    let mut flow = executed_epoch_flow(
        LinearLocus::Receiving(stage.receiver),
        law,
        &transport,
        &rows,
        stage.receiving_period,
        grain,
        stage.epoch_cells,
        stage.epoch_index,
        stage.heard_cells,
        stage.execution,
        &mut trace.evidence,
    )?;
    flow.gram = flow
        .gram
        .scalar_product(&EpochArray::from_dyadic_scalar(&(&scale * &scale))?)?;
    flow.covector = flow
        .covector
        .scalar_product(&EpochArray::from_dyadic_scalar(&scale)?)?;
    Ok((flow, scale))
}

fn prepare(
    stage: &ObservedNormalEpochStage<'_>,
    observe: &mut dyn FnMut(EpochDepositPhase),
    trace: &mut EpochStageTrace,
) -> Result<Prepared, HnnError> {
    let opening = stage.opening;
    let receiver = stage.receiver;
    let kind = LinearLocus::Receiving(receiver);
    trace.at(
        "paired_receiving_admission",
        Some(kind.locus()),
        Some(Family::Map),
    );
    let mut owner = opening
        .rings
        .get(receiver)
        .and_then(|r| r.receiving.clone())
        .ok_or(HnnError::MissingReceivingMap { ring: receiver })?;
    owner.validate()?;
    if owner.blocks().is_none()
        || stage.heard_cells == 0
        || stage.heard_cells > stage.epoch_cells
        || stage.receiving_period <= 1
        || stage.receiving_period % 2 == 0
        || partition_exponent(
            opening.observed_epoch_grain(receiver)?,
            stage.epoch_cells,
            stage.epoch_index,
        )? != stage.exponent
    {
        return Err(refused(
            "paired local epoch keeps its actual owner and receiver partition",
        ));
    }
    let mut samples = Vec::new();
    let mut population = Vec::new();
    let mut reaches = Vec::new();
    let mut reached = BTreeSet::new();
    let mut landmarks = 0u64;
    for d in stage.deposits {
        if d.commit() != opening.commit() {
            return Err(HnnError::StaleDeposit {
                staged: d.commit(),
                published: opening.commit(),
            });
        }
        let reach = d.reach().ok_or(HnnError::MissingReach)?;
        if reach.receiver != receiver {
            return Err(refused("paired epoch keeps producing receiver"));
        }
        reaches.push(reach.clone());
        if !d.factors().is_empty() || d.linear().iter().any(|s| s.locus != kind) {
            return Err(refused(
                "paired local publication holds all upstream families",
            ));
        }
        for s in d.linear() {
            samples.extend(s.samples.iter().cloned());
        }
        for p in d.receiving() {
            if p.ring != receiver {
                return Err(refused(
                    "paired chronological population has actual receiver",
                ));
            }
            population.push(p.clone());
        }
        reached.extend(d.loci());
        landmarks = landmarks
            .checked_add(d.landmarks().len() as u64)
            .ok_or_else(extent)?;
    }
    if samples.len() != stage.receiving_parts.len() || samples.is_empty() {
        return Err(refused(
            "paired epoch retains one full-output return per actual station",
        ));
    }
    if reached.iter().any(|l| opening.released.contains(l)) {
        return Err(HnnError::ReleasedLocus {
            locus: *reached
                .iter()
                .find(|l| opening.released.contains(l))
                .unwrap(),
        });
    }
    for p in stage.receiving_parts {
        p.law.admit_policy(owner.return_policy())?;
        p.law.admit_owner(receiver, opening.commit(), owner.map())?;
        if p.law.retained_origin().is_none() {
            return Err(refused("paired local epoch uses retained full-section law"));
        }
    }
    for s in &samples {
        if s.weight != Rat::one() {
            return Err(refused("paired native samples keep unit multiplicity"));
        }
        owner.found_operand_charts(&s.feature)?;
    }
    observe(EpochDepositPhase::GroupedInputs);
    let grain = opening.observed_epoch_grain(receiver)?;
    let mut laws: [Option<EpochLaw>; 2] = [None, None];
    let mut flows: [Option<EpochFlow>; 2] = [None, None];
    let mut scales = [Rat::one(), Rat::one()];
    let mut directions = Vec::new();
    let width = owner.blocks().unwrap()[0].width();
    let rows = owner.map().rows();
    for i in 0..2 {
        let block = &owner.blocks().unwrap()[i];
        if block.chart().is_none() {
            directions.push(ExactRatMatrix::zero(rows, width)?);
            continue;
        }
        let mut law = match block.law().epoch_law() {
            Some(l) => l.clone(),
            None => EpochLaw::from_normal(block.law(), grain)?.with_phase_rows(
                &(1..rows).step_by(2).collect::<Vec<_>>(),
                stage.receiving_period,
            )?,
        };
        law.receiving_refinement = owner.representation_policy().ceiling();
        if law.receiving_refinement.is_some_and(|cap|law.map_lattice > cap) {
            return Err(refused("the initial receiving lattice exceeds the explicit representation ceiling"));
        }
        let local = owner.block_samples(i, &samples)?;
        trace.at("paired_normal_flow", Some(kind.locus()), Some(Family::Map));
        let (flow, scale) = block_flow(stage, &law, &local, grain, trace)?;
        let fresh = law.fresh(&flow)?;
        directions.push(block.physical_direction(&fresh.direction.to_matrix()?)?);
        laws[i] = Some(law);
        flows[i] = Some(flow);
        scales[i] = scale;
        observe(EpochDepositPhase::Flow(kind));
    }
    let direction = physical_array(
        &joined(&directions[0], &directions[1])?,
        stage.receiving_period,
    )?;
    let certificate = receiving_epoch_certificate(
        &samples,
        stage.receiving_parts,
        &direction.to_rows(),
        stage.exponent,
    )?;
    let raw: Rat = laws
        .iter()
        .zip(&flows)
        .filter_map(|(l, f)| l.as_ref().zip(f.as_ref()))
        .map(|(l, f)| l.fresh(f).and_then(|x| x.alignment.scalar_ratio()))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .sum();
    if raw != certificate.alignment {
        return Err(refused(
            "joined physical fresh alignment equals both actual block pairings",
        ));
    }
    let covector = samples
        .iter()
        .flat_map(|s| &s.covector)
        .map(Signed::abs)
        .max()
        .unwrap_or_default();
    let face = face(&direction, &certificate, covector)?;
    let envelope = Reach {
        receiver,
        stations: vec![
            reaches
                .iter()
                .flat_map(|r| r.stations.iter().copied())
                .max()
                .unwrap_or(0),
        ],
        entries: Vec::new(),
        phases: reaches.iter().map(|r| r.phases).max().unwrap_or(0),
        loci: reaches
            .iter()
            .flat_map(|r| r.loci.iter().copied())
            .collect(),
        passages: Vec::new(),
    };
    let bound =
        EpochSpectral::grouped_frobenius(&physical_array(owner.map(), stage.receiving_period)?);
    trace.at("fresh_joint_certificate", None, None);
    let (certified, fresh_joint, _, _) = opening
        .certify_steps_with_epoch_evidence(
            Some(&envelope),
            &[(kind.locus(), kind, face.direction())],
            &[],
            None,
            StepSource::Certified,
            Some(&bound),
            Some(&reaches),
            &mut trace.evidence,
        )?
        .map_err(|_| refused("paired fresh physical receiving certificate refused"))?;
    observe(EpochDepositPhase::JointCertificate);
    let (p, f, h) = receiving_series_for(
        &samples,
        stage.receiving_parts,
        rows,
        width * 2,
        stage.receiving_period,
    )?;
    Ok(Prepared {
        owner,
        samples,
        laws,
        flows,
        aggregation_scales: scales,
        face,
        certificate,
        certified,
        fresh_joint,
        envelope,
        series: EpochReceivingSeries {
            positive: EpochSeriesReading::of(&p),
            foil: EpochSeriesReading::of(&f),
            phase: EpochSeriesReading::of(&h),
        },
        population,
        reached,
        landmarks,
        grain,
        reaches,
    })
}

fn decline(error: &HnnError, e: &EpochStageRefusal, receiver: usize) -> bool {
    e.locus == Some(Locus::ReceivingMap(receiver))
        && e.family == Some(Family::Map)
        && !e.seal_formed
        && !e.finite_probe_executed
        && e.participating_families.is_empty()
        && matches!(
            (error, e.phase, e.condition),
            (
                HnnError::Unadmitted {
                    reason: "a moving actual epoch ray must descend its contemporary comparison"
                },
                "actual_ray",
                EpochStageCondition::ActualRayAlignment
            ) | (
                HnnError::Unadmitted {
                    reason: "the actual epoch ray violates its own curvature bound"
                },
                "actual_certificate",
                EpochStageCondition::ActualRayCurvature
            )
        )
}

fn publish(
    stage: &ObservedNormalEpochStage<'_>,
    p: &Prepared,
    held: Option<&EpochStageRefusal>,
    observe: &mut dyn FnMut(EpochDepositPhase),
    trace: &mut EpochStageTrace,
) -> Result<StagedEpochCandidate, HnnError> {
    let kind = LinearLocus::Receiving(stage.receiver);
    let gamma = p
        .certified
        .get(&(kind.locus(), Family::Map))
        .map(|r| r.step.step.clone())
        .unwrap_or_default();
    if held.is_some() && !gamma.is_positive() {
        return Err(refused(
            "paired hold requires its actual positive fresh gain",
        ));
    }
    let gain = EpochArray::from_dyadic_scalar(&gamma)?;
    let mut candidates: [Option<EpochDeposit>; 2] = [None, None];
    let mut normal_laws = std::array::from_fn(|i| p.owner.blocks().unwrap()[i].law().clone());
    let mut steps = Vec::new();
    let mut block_readings = Vec::new();
    // The second block must reserve the first block's proposed growth too. These
    // conservative transient reservations never become normal state or new budget.
    let mut occupied = stage.opening.bits_within(stage.retained);
    for i in 0..2 {
        if let (Some(law), Some(flow)) = (&p.laws[i], &p.flows[i]) {
            let d = if held.is_some() {
                law.deposited_at(flow, &gain, BigInt::zero(), BigInt::one())?
            } else if p.owner.representation_policy() == ReceivingRepresentationPolicy::BoundedSubquantumV1 {
                let scale = p.owner.blocks().unwrap()[i].chart().expect("reached chart").scale();
                law.deposit_receiving(flow,&gain,stage.opening.budget,occupied,bits(scale))?
            } else {
                law.deposit(flow, &gain)?
            };
            if let Some(r) = &d.receiving_representation {
                if r.disposition==ReceivingRepresentationDisposition::Refined {occupied=r.predicted_whole_bits.expect("preflight admitted");}
                trace.receiving_representations.push(r.clone());
            }
            steps.push(p.owner.blocks().unwrap()[i].physical_direction(&d.step.to_matrix()?)?);
            candidates[i] = Some(d);
        } else {
            steps.push(ExactRatMatrix::zero(
                p.owner.map().rows(),
                p.owner.blocks().unwrap()[i].width(),
            )?);
        }
    }
    let physical_step = physical_array(&joined(&steps[0], &steps[1])?, stage.receiving_period)?;
    let mut actual_alignment = None;
    let mut actual_moves = None;
    let mut actual_certified = BTreeMap::new();
    let mut joint = None;
    let mut pumped = None;
    let mut loaded = None;
    if !physical_step.is_zero() {
        trace.at("actual_ray", Some(kind.locus()), Some(Family::Map));
        let actual = actual_epoch_face(
            kind,
            &physical_step,
            &p.samples,
            stage.receiving_parts,
            stage.exponent,
            &gamma * &p.face.covector,
            &mut trace.evidence,
        )?;
        actual_alignment = Some(actual.alignment.clone());
        actual_moves = Some(actual.moves.clone());
        let mut declared = DeclaredExponents {
            steps: BTreeMap::new(),
        };
        declared.steps.insert(
            (kind.locus(), Family::Map),
            DeclaredExponent {
                exponent: 0,
                reach: None,
            },
        );
        trace.at("actual_joint_certificate", None, None);
        let bound = EpochSpectral::grouped_frobenius(&physical_array(
            p.owner.map(),
            stage.receiving_period,
        )?);
        let result = stage
            .opening
            .certify_steps_with_epoch_evidence(
                Some(&p.envelope),
                &[(kind.locus(), kind, actual.direction())],
                &[],
                None,
                StepSource::Actual(&declared),
                Some(&bound),
                Some(&p.reaches),
                &mut trace.evidence,
            )
            .map_err(|error| {
                if let Some(e) = &mut trace.evidence {
                    if !e
                        .readings
                        .iter()
                        .any(|r| r.name == "actual_receiving_ray_operands")
                    {
                        attach_receiving_ray_packet(
                            e,
                            &p.samples,
                            stage.receiving_parts,
                            &physical_step.to_rows(),
                            stage.exponent,
                        );
                    }
                }
                error
            })?
            .map_err(|_| refused("the fixed actual epoch rays were not all admitted"))?;
        (actual_certified, joint, pumped, loaded) = result;
    }
    let mut certified = p.certified.clone();
    let (lobe, lock) =
        stage
            .opening
            .lobe(Some(&p.envelope), stage.retained, &[], &mut certified)?;
    let mut owner = p.owner.clone();
    let mut normalized = owner.block_samples(0, &p.samples)?;
    let right = owner.block_samples(1, &p.samples)?;
    for (a, b) in normalized.iter_mut().zip(right) {
        a.feature.extend(b.feature);
    }
    let internal_map = joined(
        p.owner.blocks().unwrap()[0].law().map(),
        p.owner.blocks().unwrap()[1].law().map(),
    )?;
    if let ReceivingMaterial::ArrivalContext { shared_phase, .. } = &mut owner {
        absorb_receiving_phase(
            shared_phase,
            &internal_map,
            &normalized,
            stage.receiving_parts,
        )?;
    }
    let mut held_reading = None;
    let mut representative = None;
    let mut moved = 0u64;
    for i in 0..2 {
        if let (Some(d), Some(law), Some(flow)) = (candidates[i].take(), &p.laws[i], &p.flows[i]) {
            moved = moved
                .checked_add(d.step.values.iter().filter(|v| !v.is_zero()).count() as u64)
                .ok_or_else(extent)?;
            if let Some(original) = held {
                if held_reading.is_none() {
                    representative = Some(i);
                    held_reading = Some(EpochHeldReceivingReading {
                        original_decline: Box::new(original.clone()),
                        gamma: gamma.clone(),
                        crossings_before: law.crossings,
                        crossings_after: d.successor.crossings,
                        gram_update: EpochSeriesReading::of(&flow.gram),
                        fresh_covector: EpochSeriesReading::of(&flow.covector),
                        news_before: EpochSeriesReading::of(&law.news),
                        news_after: EpochSeriesReading::of(&d.successor.news),
                    });
                }
            }
            block_readings.push(EpochPairedReceivingBlockReading {
                representation: d.receiving_representation.clone(),
                index: i,
                operand_scale: p.owner.blocks().unwrap()[i]
                    .chart()
                    .unwrap()
                    .scale()
                    .clone(),
                aggregation_scale: p.aggregation_scales[i].clone(),
                crossings_before: law.crossings,
                crossings_after: d.successor.crossings,
                gamma: gamma.clone(),
                eta: Rat::new(d.eta_numerator.clone(), d.eta_denominator.clone()),
                normal_fall: d.fall.scalar_ratio()?,
                gram_update: EpochSeriesReading::of(&flow.gram),
                fresh_covector: EpochSeriesReading::of(&flow.covector),
                news_before: EpochSeriesReading::of(&law.news),
                news_after: EpochSeriesReading::of(&d.successor.news),
                represented_step_internal: EpochSeriesReading::of(&d.step),
            });
            normal_laws[i].publish_epoch(d.successor)?;
        }
    }
    owner = owner.with_block_laws(normal_laws)?;
    let mut next = stage.opening.clone();
    if owner.representation_policy() == ReceivingRepresentationPolicy::BoundedSubquantumV1 {
        let finer = owner.laws().iter().filter_map(|l|l.epoch_law().map(|e|e.map_lattice)).max()
            .unwrap_or(stage.opening.lattice(kind.locus())?.exponent());
        if finer > stage.opening.lattice(kind.locus())?.exponent() {
            admit_refined_receiving_carries(kind.locus(),finer,&next.carries,&mut trace.evidence)?;
            next.lattices.insert(kind.locus(),Lattice::new(finer));
        }
    }
    next.rings[stage.receiver].receiving = Some(owner);
    next.rings[stage.receiver].tree = Some(stage.tree.clone());
    for step in &p.population {
        next.rings[stage.receiver]
            .population
            .as_mut()
            .ok_or(HnnError::MissingReceivingMap {
                ring: stage.receiver,
            })?
            .receive(&step.faces())
            .map_err(crate::hnn::receiving::population_refusal)?;
    }
    for (r, m) in next.rings.iter().enumerate() {
        if let (Some(resonator), Some(hop)) = (&m.resonator, &m.resonator_step) {
            resonator.certify(r, hop)?;
        }
    }
    next.commit = next.commit.checked_add(1).ok_or_else(extent)?;
    let storage_growth =
        certify_storage_growth(&stage.opening.storage_forms()?, &next.storage_forms()?)?
            .ok_or(HnnError::UncertifiedStorage)?;
    next.storage_product = &stage.opening.storage_product * (Rat::one() + &storage_growth);
    let bits = next.bits_within(stage.retained);
    if bits > stage.opening.budget {
        return Err(HnnError::ConstitutionBudget {
            bits,
            budget: stage.opening.budget,
            commit: stage.opening.commit,
            loci: p.reached.iter().copied().collect(),
        });
    }
    let paired = EpochPairedReceivingReading {
        representation_policy: p.owner.representation_policy(),
        source_width: p.owner.blocks().unwrap()[0].width(),
        fresh_physical_alignment: p.certificate.alignment.clone(),
        fresh_return_error: p.certificate.return_error.clone(),
        fresh_moves: p.certificate.moves.clone(),
        actual_alignment,
        actual_moves,
        actual_physical_step: EpochSeriesReading::of(&physical_step),
        held_original_decline: held.cloned().map(Box::new),
        held_representative_block: representative,
        blocks: block_readings,
    };
    let reading = DepositReading {
        epoch: Some(EpochDepositReading {
            paired_receiving: Some(paired),
            channel_endpoints: Vec::new(),
            channel_grain: None,
            channel_grain_deferred: None,
            channel_grain_restaged: None,
            quantum_projection: None,
            held_receiving: held_reading,
            actual_receiving_ingress: stage.epoch_index,
            heard_cells: stage.heard_cells,
            declared_cells: stage.epoch_cells,
            receiver_partition_bits: p.grain,
            partition_exponent: stage.exponent,
            loci: Vec::new(),
            fresh_joint: p.fresh_joint.clone(),
            fresh_steps: p
                .certified
                .iter()
                .map(|((l, _), r)| (*l, r.clone()))
                .collect(),
            receiving: p.series.clone(),
        }),
        storage_growth,
        storage_product: next.storage_product.clone(),
        unresolved_contact_material: Vec::new(),
        steps: actual_certified
            .into_iter()
            .map(|((l, _), r)| (l, r))
            .collect(),
        joint,
        amplitude: next.amplitude()?,
        commit: next.commit,
        bits: next.exact_bits(),
        budget: next.budget,
        loci: p.reached.iter().copied().collect(),
        released_bits: 0,
        released: Vec::new(),
        stepped: moved,
        vanished: Vec::new(),
        charts: Vec::new(),
        landmarks: p.landmarks,
        backtracks: Vec::new(),
        lobe,
        lock,
        pumped,
        loaded,
    };
    observe(EpochDepositPhase::CandidateStaged);
    Ok(StagedEpochCandidate {
        material: next,
        reading,
        upstream: false,
        physical_motion: !physical_step.is_zero(),
    })
}

pub(super) fn stage(
    stage: &mut ObservedNormalEpochStage<'_>,
    observe: &mut dyn FnMut(EpochDepositPhase),
) -> Result<StagedEpochCandidate, EpochStageFailure> {
    let mut trace = EpochStageTrace::default();
    if stage.paired_prepared.is_none() {
        stage.paired_prepared =
            Some(prepare(stage, observe, &mut trace).map_err(|e| trace.failed(e))?);
    }
    let prepared = stage.paired_prepared.as_ref().unwrap();
    let mut trace = EpochStageTrace::default();
    match publish(stage, prepared, None, observe, &mut trace) {
        Ok(c) => Ok(c),
        Err(error) => {
            let failure = trace.failed(error);
            let gamma = prepared
                .certified
                .get(&(Locus::ReceivingMap(stage.receiver), Family::Map))
                .map(|r| &r.step.step);
            if !gamma.is_some_and(Signed::is_positive)
                || !decline(&failure.error, &failure.evidence, stage.receiver)
            {
                return Err(failure);
            }
            // Private same-owner operands/gamma remain borrowed and unchanged; only the
            // two zero-applied-motion successors are independently staged and published.
            let mut trace = EpochStageTrace::default();
            publish(
                stage,
                prepared,
                Some(&failure.evidence),
                observe,
                &mut trace,
            )
            .map_err(|e| {
                let mut f = trace.failed(e);
                f.evidence.readings.push(EpochStageReading {
                    name: "original_local_ray_decline",
                    value: EpochStageValue::ReceivingDecline(Box::new(failure.evidence.clone())),
                });
                f
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::reference::observed::HostObservedEpochExecution;
    #[test]
    fn paired_context_hold_keeps_both_normals_once_and_cold() {
        for (scale,family_local) in [(-64,false),(64,false),(-64,true),(64,true)] {
            let (field, material, deposit, parts, exponent) =
                super::super::tests::held_retained_fixture_policy(scale,true,family_local);
            let expected=if family_local {crate::hnn::receiving::RetainedReturnPolicy::FamilyLocalRetainedReturnV1}else{crate::hnn::receiving::RetainedReturnPolicy::PopulationMixtureSectionV1};
            for part in &parts {part.law.admit_policy(expected).unwrap(); let other=if family_local {crate::hnn::receiving::RetainedReturnPolicy::PopulationMixtureSectionV1}else{crate::hnn::receiving::RetainedReturnPolicy::FamilyLocalRetainedReturnV1};assert!(part.law.admit_policy(other).is_err());}
            let receiver = field.receivers()[0].ring;
            let retained = crate::hnn::retention::loci(&field).into_iter().collect();
            let deposits = [deposit];
            let pair_speed = |_, _, _: &PairPort, _: [&[Vec<Rat>]; 3]| panic!("no pair factor");
            let mut stage = ObservedNormalEpochStage::new(
                &material,
                &deposits,
                receiver,
                field.ring(receiver).period(),
                1,
                1,
                0,
                exponent,
                &retained,
                material.landmarks(receiver).unwrap().clone(),
                &pair_speed,
                &parts,
                &HostObservedEpochExecution,
                false,
            )
            .unwrap()
            .for_local_receiving_hold()
            .unwrap();
            let mut trace = EpochStageTrace::default();
            let prepared = prepare(&stage, &mut |_| {}, &mut trace).unwrap();
            let gamma = prepared.certified[&(Locus::ReceivingMap(receiver), Family::Map)]
                .step
                .step
                .clone();
            assert!(gamma.is_positive());
            let mut trace = EpochStageTrace::default();
            let error = publish(&stage, &prepared, None, &mut |_| {}, &mut trace).unwrap_err();
            let refusal = trace.failed(error);
            assert!(
                decline(&refusal.error, &refusal.evidence, receiver),
                "{refusal:?}"
            );
            assert!(!decline(
                &HnnError::CountOverflow,
                &refusal.evidence,
                receiver
            ));
            assert!(!decline(
                &HnnError::ConstitutionBudget {
                    bits: 2,
                    budget: 1,
                    commit: material.commit(),
                    loci: vec![]
                },
                &refusal.evidence,
                receiver
            ));
            let original = material.continuing_state(0).unwrap();
            let mut trace = EpochStageTrace::default();
            let candidate = publish(
                &stage,
                &prepared,
                Some(&refusal.evidence),
                &mut |_| {},
                &mut trace,
            )
            .unwrap();
            assert!(candidate.held_receiving() && !candidate.has_physical_motion());
            let (next, reading) = candidate.admit_receiving().unwrap();
            let p = reading
                .epoch
                .as_ref()
                .unwrap()
                .paired_receiving
                .as_ref()
                .unwrap();
            assert_eq!(p.blocks.len(), 2);
            for i in 0..2 {
                let before = prepared.laws[i].as_ref().unwrap();
                let flow = prepared.flows[i].as_ref().unwrap();
                let after = next.receiving_blocks(receiver).unwrap()[i]
                    .law()
                    .epoch_law()
                    .unwrap();
                assert_eq!(after.map, before.map);
                assert_eq!(after.gram, before.gram.add(&flow.gram).unwrap());
                assert_eq!(
                    after.news,
                    before
                        .news
                        .add(
                            &flow
                                .covector
                                .scalar_product(&EpochArray::from_dyadic_scalar(&gamma).unwrap())
                                .unwrap()
                        )
                        .unwrap()
                );
                assert_eq!(after.crossings, before.crossings + 1);
                assert!(p.blocks[i].eta.is_zero() && p.blocks[i].normal_fall.is_zero());
            }
            let state = ContinuingState::from_text(
                &next.continuing_state(0).unwrap().to_text(),
                next.budget(),
            )
            .unwrap();
            let mut cold_opening = Constitution::initial(&field, next.budget()).unwrap();
            cold_opening.bind_arrival_context_receiving(receiver).unwrap();
            if family_local {cold_opening.bind_family_local_receiving_return(receiver).unwrap();}
            let cold = cold_opening.continued_on(&field, &state).unwrap();
            assert_eq!(next.receiving_phase_statistics(receiver).unwrap().cells(),
                &(material.receiving_phase_statistics(receiver).unwrap().cells()+Rat::one()),
                "one actual observed class increments shared phase once");
            assert_eq!(
                cold.continuing_state(0).unwrap(),
                next.continuing_state(0).unwrap()
            );
            assert_eq!(material.continuing_state(0).unwrap(), original);
            // Install the prepared capability, as the actual public stage does once.
            stage.paired_prepared=Some(prepared);
            // Held restaging uses that same cached flow, never re-observes a Word.
            let full = stage.stage_local_receiving_with_hold(&mut |_| {}).unwrap();
            assert!(full.held_receiving());
            println!(
                "PAIRED_CONTEXT_HELD scale={scale} cause={:?} gamma={gamma} blocks=2 crossings_once=true cold_exact=true",
                refusal.evidence.condition
            );
            let mut limited = material.clone();
            limited.budget = 1;
            let mut late = ObservedNormalEpochStage::new(
                &limited,
                &deposits,
                receiver,
                field.ring(receiver).period(),
                1,
                1,
                0,
                exponent,
                &retained,
                limited.landmarks(receiver).unwrap().clone(),
                &pair_speed,
                &parts,
                &HostObservedEpochExecution,
                false,
            )
            .unwrap()
            .for_local_receiving_hold()
            .unwrap();
            let before = limited.clone();
            let failure = late
                .stage_local_receiving_with_hold(&mut |_| {})
                .unwrap_err();
            assert!(
                matches!(failure.error, HnnError::ConstitutionBudget { .. }),
                "{failure:?}"
            );
            assert_eq!(limited, before);
        }
    }
    #[test]
    fn paired_context_aggregate_transport_restores_exact_units() {
        let (field, material, deposit, parts, exponent) =
            super::super::tests::held_retained_fixture_at(0, true);
        let receiver = field.receivers()[0].ring;
        let retained = crate::hnn::retention::loci(&field).into_iter().collect();
        let deposits = [deposit];
        let pair_speed = |_, _, _: &PairPort, _: [&[Vec<Rat>]; 3]| panic!("no pair factor");
        let stage = ObservedNormalEpochStage::new(
            &material,
            &deposits,
            receiver,
            field.ring(receiver).period(),
            1,
            1,
            0,
            exponent,
            &retained,
            material.landmarks(receiver).unwrap().clone(),
            &pair_speed,
            &parts,
            &HostObservedEpochExecution,
            false,
        )
        .unwrap();
        let law = material.receiving_blocks(receiver).unwrap()[0]
            .law()
            .epoch_law()
            .unwrap();
        let mut sample = deposits[0].linear()[0].samples[0].clone();
        sample.feature = vec![Rat::zero(); law.map.columns];
        sample.feature[0] = Rat::from_integer(3.into());
        sample.feature[1] = -Rat::new(5.into(), 2.into());
        let mut trace = EpochStageTrace::default();
        let (flow, scale) = block_flow(
            &stage,
            law,
            std::slice::from_ref(&sample),
            material.observed_epoch_grain(receiver).unwrap(),
            &mut trace,
        )
        .unwrap();
        assert_eq!(scale, Rat::from_integer(4.into()));
        let gram = flow.gram.to_matrix().unwrap();
        let cov = flow.covector.to_matrix().unwrap();
        for i in 0..sample.feature.len() {
            for j in 0..sample.feature.len() {
                assert_eq!(
                    gram.get(i, j).unwrap(),
                    &(&sample.feature[i] * &sample.feature[j])
                );
            }
        }
        for i in 0..sample.covector.len() {
            for j in 0..sample.feature.len() {
                assert_eq!(
                    cov.get(i, j).unwrap(),
                    &(&sample.covector[i] * &sample.feature[j])
                );
            }
        }
    }
}

#[cfg(test)]
mod representation_controls {
    use super::*;
    use crate::hnn::reference::observed::HostObservedEpochExecution;
    #[test]
    fn bounded_receiving_representation_native_cold() {
        for scale in [0,-64] {
            let start=std::time::Instant::now();
            let (field,material,deposit,parts,exponent)=super::super::tests::held_retained_fixture_representation(scale,true,true,true);
            let receiver=field.receivers()[0].ring;
            let retained=crate::hnn::retention::loci(&field).into_iter().collect();
            let deposits=[deposit];
            let pair_speed=|_,_,_:&PairPort,_:[&[Vec<Rat>];3]|panic!("no pair factor");
            let mut stage=ObservedNormalEpochStage::new(&material,&deposits,receiver,field.ring(receiver).period(),1,1,0,exponent,&retained,
                material.landmarks(receiver).unwrap().clone(),&pair_speed,&parts,&HostObservedEpochExecution,false).unwrap().for_local_receiving_hold().unwrap();
            let mut trace=EpochStageTrace::default();
            let p=prepare(&stage,&mut |_|{},&mut trace).unwrap();
            let gamma=p.certified[&(Locus::ReceivingMap(receiver),Family::Map)].step.step.clone();
            let gain=EpochArray::from_dyadic_scalar(&gamma).unwrap();
            for i in 0..2 {
                let law=p.laws[i].as_ref().unwrap();let flow=p.flows[i].as_ref().unwrap();
                let old=law.deposit(flow,&gain).unwrap();
                if scale==0 {assert!(old.step.is_zero());assert!(!old.direction.is_zero());}
            }
            let before=material.continuing_state(0).unwrap();
            stage.paired_prepared=Some(p);
            let candidate=stage.stage_local_receiving_with_hold(&mut |_|{}).unwrap();
            let (next,reading)=candidate.admit_receiving().unwrap();
            let paired=reading.epoch.as_ref().unwrap().paired_receiving.as_ref().unwrap();
            if scale==0 {
                assert!(paired.blocks.iter().any(|b|b.representation.as_ref().is_some_and(|r|r.disposition==ReceivingRepresentationDisposition::Refined)),"{paired:?}");
                assert_ne!(next.receiving_map(receiver),material.receiving_map(receiver));
                assert!(paired.actual_alignment.as_ref().is_some_and(Signed::is_positive));
                assert!(paired.held_original_decline.is_none());
            } else {assert!(paired.held_original_decline.is_some()); assert_eq!(next.receiving_map(receiver),material.receiving_map(receiver));}
            for block in &paired.blocks {
                let old=material.receiving_blocks(receiver).unwrap()[block.index].law().epoch_law().unwrap();
                let new=next.receiving_blocks(receiver).unwrap()[block.index].law().epoch_law().unwrap();
                assert_eq!(new.crossings,old.crossings+1);
                assert_eq!(new.receiving_refinement,Some(20));
                assert!(new.map_lattice<=20 && !new.source_refinement);
            }
            let state=ContinuingState::from_text(&next.continuing_state(0).unwrap().to_text(),next.budget()).unwrap();
            let mut declaration=Constitution::initial(&field,next.budget()).unwrap();
            declaration.bind_arrival_context_receiving(receiver).unwrap();
            declaration.bind_family_local_receiving_return(receiver).unwrap();
            assert!(declaration.clone().continued_on(&field,&state).is_err(),"old policy cannot silently consume a finer state");
            declaration.bind_bounded_receiving_representation(receiver).unwrap();
            let cold=declaration.continued_on(&field,&state).unwrap();
            assert_eq!(cold.continuing_state(0).unwrap(),next.continuing_state(0).unwrap());
            assert_eq!(material.continuing_state(0).unwrap(),before);
            println!("BOUNDED_REPRESENTATION_NATIVE scale={scale} elapsed_ns={} gamma={gamma} map_changed={} cold_exact=true reading={paired:?}",start.elapsed().as_nanos(),next.receiving_map(receiver)!=material.receiving_map(receiver));
        }
    }
}
