//! Native epoch publication: one canonical grouped normal law per locus, with
//! independent word reaches admitted by the existing joint certificate.
use super::*;

/// The receiving face's three exact series, produced from the heard class and
/// its one retained RHS. These operands never stand in for an upstream split.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EpochReceivingRecord {
    pub(crate) feature: Vec<Rat>,
    pub(crate) positive: Vec<Rat>,
    pub(crate) foil: Vec<Rat>,
    pub(crate) phase: Vec<Rat>,
}

/// Exterior observation boundaries only; these events carry no timing or numerical state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EpochDepositPhase {
    GroupedInputs,
    Flow(LinearLocus),
    Certificate(LinearLocus),
    PairDirections,
    RegionPreparation,
    JointCertificate,
    Publication,
}

/// [proved-derived; agent-inferred] An enclosure of the existing receiving
/// certificate, at the epoch's declared grain `u = 2^(-2L)`. Each sample's
/// exact Fisher move, odometer defect and signed partition contribution is
/// read before its own normalizer leaves scope. Only integer numerators on
/// this common grid are summed: no epoch-wide LCM of sample normalizers.
///
/// For every rational `x`, `x <= ceil(x/u) u < x+u`, including negative x.
/// Thus `M_hat >= M`, `O_hat >= O`, `P_hat >= P`, each with excess `< n u`.
/// The consumer keeps the exact fresh alignment a and oscillation, and reads
/// `a_hat = max(0, a - O_hat - max(0, P_hat)) <= a_cert` from the same
/// certificate. Increasing its nonnegative curvature and decreasing its
/// alignment preserves the existing joint inequality for every eta >= 0.
/// These are transient enclosures, never replacement producing face masses.
///
/// The denominator is at most `2^(2L)` regardless of the number or coprimality
/// of sample normalizers. Numerator size still follows the actual local move
/// magnitudes and sample count; this is no cap on unrelated downstream gains.
/// Existing Fisher/soft-target proof obligations remain #62; the directed
/// integer enclosure and its consumer composition also remain to be formalized.
struct EpochReceivingCertificate {
    moves: Rat,
    oscillation: Rat,
    alignment: Rat,
    odometer: Rat,
    partition: Rat,
}

fn upper_grid_numerator(value: &Rat, denominator: &BigInt) -> BigInt {
    let scaled = value.numer() * denominator;
    let quotient = &scaled / value.denom();
    // BigInt division truncates towards zero, already the ceiling below zero.
    // A positive remainder alone requires the next grid point.
    if (&scaled % value.denom()).is_positive() {
        quotient + BigInt::one()
    } else {
        quotient
    }
}

fn receiving_epoch_certificate(
    samples: &[Sample],
    parts: &[EpochReceivingRecord],
    direction: &[Vec<Rat>],
    partition_bits: u32,
) -> Result<EpochReceivingCertificate, HnnError> {
    if samples.len() != parts.len() {
        return Err(refused(
            "an epoch certificate needs every producing receiving split",
        ));
    }
    let bits = partition_bits.checked_mul(2).ok_or_else(extent)?;
    let denominator = BigInt::one() << bits as usize;
    let (mut moves, mut odometer, mut partition) = (BigInt::zero(), BigInt::zero(), BigInt::zero());
    let (mut oscillation, mut alignment) = (Rat::zero(), Rat::zero());
    for (sample, part) in samples.iter().zip(parts) {
        let local = std::slice::from_ref(sample);
        let (local_moves, local_oscillation, local_alignment) =
            receiving_fisher_face(local, direction).ok_or_else(|| {
                refused("the receiving epoch Fisher certificate requires its actual normalized producing masses")
            })?;
        let local_odometer = odometer_alignment_defect(local, direction).ok_or_else(|| {
            refused("the receiving epoch needs its producing odometer alignment defect")
        })?;
        moves += upper_grid_numerator(&local_moves, &denominator);
        odometer += upper_grid_numerator(&local_odometer, &denominator);
        oscillation = oscillation.max(local_oscillation);
        // Only the admitted covector/feature/direction enter this exact sum;
        // no raw producing mass or its odd normalizer enters the alignment.
        alignment += local_alignment;
        let masses = face_masses(sample).ok_or_else(|| {
            refused("a receiving partition keeps its producing normalized masses")
        })?;
        let mut local_partition = Rat::zero();
        for (class, mass) in masses.iter().enumerate() {
            let delta: Rat = direction[2 * class]
                .iter()
                .zip(&sample.feature)
                .map(|(d, f)| d * f)
                .sum();
            // Preserve the existing partition certificate's operands exactly.
            // In particular, its signed contribution is clipped only AFTER
            // summing, never per sample, and is not multiplied by sample.weight.
            local_partition += (mass - &part.foil[2 * class]) * delta;
        }
        partition += upper_grid_numerator(&local_partition, &denominator);
    }
    Ok(EpochReceivingCertificate {
        moves: Rat::new(moves, denominator.clone()),
        oscillation,
        alignment,
        odometer: Rat::new(odometer, denominator.clone()),
        partition: Rat::new(partition, denominator),
    })
}

impl Constitution {
    fn epoch_normal(&self, kind: LinearLocus) -> Result<&NormalLaw, HnnError> {
        match kind {
            LinearLocus::SourcePort(ring) => self.rings.get(ring).and_then(|m| m.source.as_ref()),
            LinearLocus::Contrast(ring) => self.rings.get(ring).map(|m| &m.contrast),
            LinearLocus::Receiving(ring) => self
                .rings
                .get(ring)
                .and_then(|m| m.receiving.as_ref())
                .and_then(ReceivingMaterial::single),
        }
        .ok_or_else(|| refused("an epoch normal locus must exist as one declared linear law"))
    }

    fn epoch_normal_mut(&mut self, kind: LinearLocus) -> Result<&mut NormalLaw, HnnError> {
        match kind {
            LinearLocus::SourcePort(ring) => {
                self.rings.get_mut(ring).and_then(|m| m.source.as_mut())
            }
            LinearLocus::Contrast(ring) => self.rings.get_mut(ring).map(|m| &mut m.contrast),
            LinearLocus::Receiving(ring) => self
                .rings
                .get_mut(ring)
                .and_then(|m| m.receiving.as_mut())
                .and_then(ReceivingMaterial::single_mut),
        }
        .ok_or_else(|| refused("an epoch normal locus must exist as one declared linear law"))
    }

    /// Absorption count only. The resident's actual receiving ingress count
    /// remains the authority for c and for terminal partial closure.
    pub(crate) fn observed_epoch_index(&self, receiver: usize) -> u64 {
        self.receiving_law(receiver)
            .and_then(NormalLaw::epoch_law)
            .map_or(0, |law| law.crossings)
    }
    pub(crate) fn observed_epoch_grain(&self, _receiver: usize) -> Result<u32, HnnError> {
        Ok(lattice_exponent(self.grain, 1))
    }

    /// A transient fork view: physical laws, carry and material commit are the
    /// opening's; only the receiver's actual prefix tree/population clocks move.
    pub(crate) fn observed_epoch_prefix(
        &self,
        receiver: usize,
        tree: Landmarks,
        receiving: &[ReceivingStep],
    ) -> Result<Self, HnnError> {
        let mut next = self.clone();
        let material = next
            .rings
            .get_mut(receiver)
            .ok_or(HnnError::MissingReceivingMap { ring: receiver })?;
        material.tree = Some(tree);
        for step in receiving {
            if step.ring != receiver {
                return Err(refused(
                    "an epoch prefix keeps its declared receiving population",
                ));
            }
            material
                .population
                .as_mut()
                .ok_or(HnnError::MissingReceivingMap { ring: receiver })?
                .receive(&step.faces())
                .map_err(crate::hnn::receiving::population_refusal)?;
        }
        Ok(next)
    }

    /// Every comparison was produced at this opening. Fresh grouped directions
    /// are certified jointly before R is read; eta is fixed to one by each
    /// normal law's majorizer. Publication happens once, on the complete clone.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn deposit_observed_epoch(
        &self,
        deposits: &[Deposit],
        receiver: usize,
        receiving_period: u64,
        heard_cells: u64,
        epoch_cells: u64,
        epoch_index: u64,
        exponent: u32,
        retained: &BTreeSet<Locus>,
        tree: Landmarks,
        pair_speed: &dyn Fn(
            usize,
            usize,
            &PairPort,
            [&[Vec<Rat>]; 3],
        ) -> Result<[Rat; 2], HnnError>,
        receiving_parts: &[EpochReceivingRecord],
        observe: &mut dyn FnMut(EpochDepositPhase),
    ) -> Result<(Self, DepositReading), HnnError> {
        self.deposit_observed_epoch_with_execution(
            deposits,
            receiver,
            receiving_period,
            heard_cells,
            epoch_cells,
            epoch_index,
            exponent,
            retained,
            tree,
            pair_speed,
            receiving_parts,
            observe,
            &crate::hnn::reference::observed::HostObservedEpochExecution,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn deposit_observed_epoch_with_execution(
        &self,
        deposits: &[Deposit],
        receiver: usize,
        receiving_period: u64,
        heard_cells: u64,
        epoch_cells: u64,
        epoch_index: u64,
        exponent: u32,
        retained: &BTreeSet<Locus>,
        tree: Landmarks,
        pair_speed: &dyn Fn(
            usize,
            usize,
            &PairPort,
            [&[Vec<Rat>]; 3],
        ) -> Result<[Rat; 2], HnnError>,
        receiving_parts: &[EpochReceivingRecord],
        observe: &mut dyn FnMut(EpochDepositPhase),
        execution: &dyn crate::hnn::reference::observed::ObservedEpochExecution,
    ) -> Result<(Self, DepositReading), HnnError> {
        let grain = self.observed_epoch_grain(receiver)?;
        if heard_cells == 0
            || heard_cells > epoch_cells
            || receiving_period <= 1
            || receiving_period % 2 == 0
            || partition_exponent(grain, epoch_cells, epoch_index)? != exponent
        {
            return Err(refused(
                "an epoch close must retain its actual heard count, field period, c and receiver partition",
            ));
        }
        let mut samples: BTreeMap<LinearLocus, Vec<Sample>> = BTreeMap::new();
        let mut factors: BTreeMap<(Locus, Family), FactorStep> = BTreeMap::new();
        let mut reaches = Vec::new();
        let mut population = Vec::new();
        let mut reached = BTreeSet::new();
        let mut landmarks = 0u64;
        for deposit in deposits {
            if deposit.commit() != self.commit {
                return Err(HnnError::StaleDeposit {
                    staged: deposit.commit(),
                    published: self.commit,
                });
            }
            if let Some(reach) = deposit.reach() {
                if reach.receiver != receiver {
                    return Err(refused("epoch returns must keep their declared receiver"));
                }
                reaches.push(reach.clone());
            } else if !deposit.linear().is_empty() || !deposit.factors().is_empty() {
                return Err(HnnError::MissingReach);
            }
            for linear in deposit.linear() {
                samples
                    .entry(linear.locus)
                    .or_default()
                    .extend(linear.samples.iter().cloned());
            }
            for factor in deposit.factors() {
                let key = (factor.gradient.locus(), factor.gradient.family());
                if let Some(existing) = factors.get_mut(&key) {
                    add_factor(existing, factor)?;
                } else {
                    factors.insert(key, factor.clone());
                }
            }
            reached.extend(deposit.loci());
            population.extend_from_slice(deposit.receiving());
            landmarks = landmarks
                .checked_add(deposit.landmarks().len() as u64)
                .ok_or_else(extent)?;
        }
        if reached.iter().any(|l| self.released.contains(l)) {
            return Err(HnnError::ReleasedLocus {
                locus: *reached
                    .iter()
                    .find(|l| self.released.contains(l))
                    .expect("found above"),
            });
        }
        // All extant normal loci share the crossing clock, including a locus
        // with zero records. Record multiplicity is never a heard-cell count.
        let mut kinds = Vec::new();
        for (ring, material) in self.rings.iter().enumerate() {
            if material.source.is_some() && !self.released.contains(&Locus::SourcePort(ring)) {
                kinds.push(LinearLocus::SourcePort(ring));
            }
            if !self.released.contains(&Locus::Element(ring)) {
                kinds.push(LinearLocus::Contrast(ring));
            }
        }
        kinds.push(LinearLocus::Receiving(receiver));
        observe(EpochDepositPhase::GroupedInputs);
        let mut laws = BTreeMap::new();
        let mut flows = BTreeMap::new();
        let mut faces = Vec::new();
        let mut receiving_series = None;
        let mut raw_covector_scales = BTreeMap::new();
        let mut raw_alignments = BTreeMap::new();
        let mut alignment_defects = BTreeMap::new();
        for kind in &kinds {
            let normal = self.epoch_normal(*kind)?;
            let law = if let Some(law) = normal.epoch_law() {
                law.clone()
            } else {
                let law = EpochLaw::from_normal(normal, grain)?;
                if matches!(kind, LinearLocus::Receiving(_)) {
                    let phase_rows: Vec<_> = (1..law.map.rows).step_by(2).collect();
                    law.with_phase_rows(&phase_rows, receiving_period)?
                } else {
                    law
                }
            };
            let phase_rows: Vec<_> = if matches!(kind, LinearLocus::Receiving(_)) {
                (1..law.map.rows).step_by(2).collect()
            } else {
                Vec::new()
            };
            let locus_samples = samples.get(kind).map(Vec::as_slice).unwrap_or(&[]);
            let records =
                super::device::epoch_record_operands(locus_samples, &phase_rows, receiving_period)?;
            // Admission reads the actual reached operands before any selected
            // executor runs. No host aggregation is performed on this route.
            let partition_exponent = super::device::epoch_record_flow_admit(
                law.map.rows,
                law.map.columns,
                grain,
                epoch_cells,
                epoch_index,
                heard_cells,
                &records,
            )?;
            let reading =
                super::device::epoch_record_flow_canonicalize(execution.aggregate_records(
                    *kind,
                    law.map.rows,
                    law.map.columns,
                    grain,
                    epoch_cells,
                    epoch_index,
                    heard_cells,
                    &records,
                )?)?;
            let records_count = u64::try_from(records.len()).map_err(|_| extent())?;
            let support: Vec<_> = (0..law.map.columns)
                .filter(|&column| {
                    records
                        .iter()
                        .any(|record| !record.feature.numerators[column].is_zero())
                })
                .collect();
            if reading.gram.rows != law.map.columns
                || reading.gram.columns != law.map.columns
                || reading.covector.rows != law.map.rows
                || reading.covector.columns != law.map.columns
                || reading.records != records_count
                || reading.heard_cells != heard_cells
                || reading.declared_cells != epoch_cells
                || reading.partition_exponent != partition_exponent
                || reading.support != support
            {
                return Err(refused(
                    "an executed epoch flow must retain its actual locus, support, producer count and receiving partition",
                ));
            }
            let array = |series: &EpochSeriesReading| {
                EpochArray::with_row_divisors(
                    series.rows,
                    series.columns,
                    series.exponent,
                    series.numerators.clone(),
                    series.row_odd_divisors.clone(),
                )
            };
            let flow = EpochFlow {
                gram: array(&reading.gram)?,
                covector: array(&reading.covector)?,
                support: reading.support,
                partitions: Vec::new(),
                cells: heard_cells,
                partition_cells: epoch_cells,
                records: records_count,
                partition_exponent,
                receiver_grain: grain,
                epoch: epoch_index,
            };
            let fresh = law.fresh(&flow)?;
            observe(EpochDepositPhase::Flow(*kind));
            let c = locus_samples
                .iter()
                .flat_map(|s| s.covector.iter().map(|v| v.abs()))
                .max()
                .unwrap_or_else(Rat::zero);
            raw_covector_scales.insert(*kind, c.clone());
            raw_alignments.insert(*kind, fresh.alignment.scalar_ratio()?);
            alignment_defects.insert(*kind, (Rat::zero(), Rat::zero()));
            let mut face = fresh.certificate_face(&EpochSeries {
                rows: 1,
                columns: 1,
                numerators: vec![c.numer().clone()],
                denominator: c.denom().clone(),
            })?;
            if matches!(kind, LinearLocus::Receiving(_)) {
                let (positive, foil, phase) = receiving_series_for(
                    locus_samples,
                    receiving_parts,
                    law.map.rows,
                    law.map.columns,
                    receiving_period,
                )?;
                if !positive
                    .subtract(&foil)?
                    .add(&phase)?
                    .subtract(&flow.covector)?
                    .is_zero()
                {
                    return Err(refused(
                        "receiving positive minus foil plus phase must equal its exact fresh news",
                    ));
                }
                receiving_series = Some(EpochReceivingSeries {
                    positive: EpochSeriesReading::of(&positive),
                    foil: EpochSeriesReading::of(&foil),
                    phase: EpochSeriesReading::of(&phase),
                });
                if !locus_samples.is_empty() {
                    let direction = fresh.direction.to_rows();
                    let certificate = receiving_epoch_certificate(
                        locus_samples,
                        receiving_parts,
                        &direction,
                        exponent,
                    )?;
                    if certificate.alignment != fresh.alignment.scalar_ratio()? {
                        return Err(refused(
                            "the receiving Fisher alignment must pair the same fresh G and direction",
                        ));
                    }
                    let EpochReceivingCertificate {
                        moves,
                        oscillation,
                        alignment,
                        odometer,
                        partition,
                    } = certificate;
                    let defect = &odometer + partition.clone().max(Rat::zero());
                    face.alignment = (alignment - defect).max(Rat::zero());
                    face.moves = moves;
                    face.covector = face.covector.max(oscillation).max(Rat::one());
                    alignment_defects.insert(*kind, (odometer, partition));
                }
            }
            observe(EpochDepositPhase::Certificate(*kind));
            faces.push((*kind, face));
            laws.insert(*kind, law);
            flows.insert(*kind, flow);
        }
        // The envelope only declares the union medium and longest local span.
        // The certificate reads each original local reach for the actual gains.
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
        let mut next = self.clone();
        let mut factor_steps: Vec<_> = factors.into_values().collect();
        for step in &mut factor_steps {
            if let FactorGradient::PairPort {
                ring,
                offset,
                outputs,
                current,
                earlier,
                speed,
            } = &mut step.gradient
            {
                let pair = self
                    .rings
                    .get(*ring)
                    .and_then(|m| m.pairs.iter().find(|(d, _)| d == offset))
                    .map(|(_, p)| p)
                    .ok_or(HnnError::Offset { offset: *offset })?;
                *speed = pair_speed(*ring, *offset, pair, [outputs, current, earlier])?;
            }
        }
        observe(EpochDepositPhase::PairDirections);
        let mut groups: BTreeMap<Locus, Vec<(usize, LocusStep<'_>)>> = BTreeMap::new();
        for (index, step) in factor_steps.iter().enumerate() {
            groups
                .entry(step.gradient.locus())
                .or_default()
                .push((index, LocusStep::Factor(step)));
        }
        for (index, step) in population.iter().enumerate() {
            groups
                .entry(Locus::ReceivingMap(step.ring))
                .or_default()
                .push((factor_steps.len() + index, LocusStep::Receiving(step)));
        }
        let mut local: BTreeMap<Locus, Carries> =
            groups.keys().map(|l| (*l, Carries::new())).collect();
        let mut rest = Carries::new();
        for (key, carry) in std::mem::take(&mut next.carries) {
            if let Some(map) = local.get_mut(&key.0) {
                map.insert(key, carry);
            } else {
                rest.insert(key, carry);
            }
        }
        let mut materials = LocusMaterial::split(&mut next.rings, &mut next.contacts, &groups);
        let mut regions: Vec<_> = groups
            .iter()
            .map(|(l, steps)| {
                (
                    *l,
                    steps,
                    materials.remove(l),
                    local.remove(l).unwrap_or_default(),
                )
            })
            .collect();
        drop(materials);
        let mut ready = Vec::new();
        for (locus, steps, material, carries) in &mut regions {
            let prepared = self
                .prepare_at(*locus, steps, material.as_mut(), carries)
                .map_err(|(_, e)| e)?;
            ready.push(prepared);
        }
        observe(EpochDepositPhase::RegionPreparation);
        let factor_faces: Vec<_> = regions
            .iter()
            .zip(&ready)
            .flat_map(|((l, ..), p)| p.factors.iter().map(move |p| (*l, p)))
            .collect();
        let linear_faces: Vec<_> = faces
            .iter()
            .map(|(kind, face)| (kind.locus(), *kind, face.direction()))
            .collect();
        let readout = &laws[&LinearLocus::Receiving(receiver)].spectral;
        let bound = readout.upper();
        let (mut certified, joint, pumped, loaded) = self
            .certify_steps(
                Some(&envelope),
                &linear_faces,
                &factor_faces,
                None,
                StepSource::Certified,
                Some(&bound),
                Some(&reaches),
            )?
            .map_err(|_| refused("the native epoch joint certificate refused its candidate"))?;
        drop(factor_faces);
        observe(EpochDepositPhase::JointCertificate);
        let stepping: Vec<_> = regions
            .iter()
            .zip(&ready)
            .filter_map(|((l, steps, ..), p)| {
                let Locus::Standing(ring) = *l else {
                    return None;
                };
                let gradient = steps.iter().find_map(|(_, s)| match s {
                    LocusStep::Factor(FactorStep {
                        gradient: FactorGradient::Standing { gradient, .. },
                        ..
                    }) => Some(gradient.as_slice()),
                    _ => None,
                })?;
                let scale = p
                    .factors
                    .iter()
                    .find(|p| p.family == Family::Standing)?
                    .scale
                    .clone();
                Some((ring, gradient, scale))
            })
            .collect();
        let (lobe, lock) = self.lobe(Some(&envelope), retained, &stepping, &mut certified)?;
        drop(stepping);
        let mut strokes = BTreeMap::new();
        for ((locus, steps, material, carries), prepared) in regions.iter_mut().zip(ready) {
            let (stroke, _) = self
                .deposit_at(
                    *locus,
                    steps,
                    material.as_mut(),
                    carries,
                    prepared,
                    &certified,
                )
                .map_err(|(_, e)| e)?;
            strokes.insert(*locus, stroke);
        }
        for (locus, _, _, carries) in regions {
            rest.extend(carries);
            let _ = locus;
        }
        next.carries = rest;
        let mut normal_moves = 0u64;
        let mut vanished = Vec::new();
        let mut locus_readings = Vec::new();
        for kind in &kinds {
            let gamma = certified
                .get(&(kind.locus(), Family::Map))
                .map(|r| r.step.step.clone())
                .unwrap_or_else(Rat::zero);
            let deposit =
                laws[kind].deposit(&flows[kind], &EpochArray::from_dyadic_scalar(&gamma)?)?;
            normal_moves = normal_moves
                .checked_add(deposit.step.values.iter().filter(|v| !v.is_zero()).count() as u64)
                .ok_or_else(extent)?;
            if gamma.is_positive() && deposit.step.is_zero() {
                vanished.push((kind.locus(), Family::Map));
            }
            let normal = next.epoch_normal_mut(*kind)?;
            if matches!(kind, LinearLocus::Receiving(_)) {
                if let Some(phase) = normal.phase.as_mut() {
                    let opening = laws[kind].map.to_matrix()?;
                    absorb_receiving_phase(
                        phase,
                        &opening,
                        samples.get(kind).map(Vec::as_slice).unwrap_or(&[]),
                        receiving_parts,
                    )?;
                }
            }
            let eta = Rat::new(
                deposit.eta_numerator.clone(),
                deposit.eta_denominator.clone(),
            );
            let fall = deposit.fall.scalar_ratio()?;
            let direction = EpochArrayReading::of(&deposit.direction);
            let represented_step = EpochArrayReading::of(&deposit.step);
            let shares = deposit.shares.clone();
            normal.publish_epoch(deposit.successor)?;
            let certificate = &faces
                .iter()
                .find(|(k, _)| k == kind)
                .expect("one fresh face per normal locus")
                .1;
            locus_readings.push(EpochLocusDepositReading {
                locus: *kind,
                records: flows[kind].records,
                fresh_covector_scale: raw_covector_scales[kind].clone(),
                fresh_alignment: raw_alignments[kind].clone(),
                odometer_alignment_defect: alignment_defects[kind].0.clone(),
                partition_alignment_extra: alignment_defects[kind].1.clone(),
                certificate_alignment: certificate.alignment.clone(),
                certificate_moves: certificate.moves.clone(),
                certificate_covector_scale: certificate.covector.clone(),
                gamma,
                eta,
                fall,
                shares,
                gram_update: EpochArrayReading::of(&flows[kind].gram),
                fresh_news: EpochArrayReading::of(&flows[kind].covector),
                direction,
                represented_step,
                storage: normal
                    .epoch_storage()
                    .expect("published grouped epoch storage"),
            });
        }
        next.rings
            .get_mut(receiver)
            .ok_or(HnnError::MissingReceivingMap { ring: receiver })?
            .tree = Some(tree);
        for (ring, material) in next.rings.iter().enumerate() {
            if let (Some(resonator), Some(hop)) = (&material.resonator, &material.resonator_step) {
                resonator.certify(ring, hop)?;
            }
        }
        next.commit = next.commit.checked_add(1).ok_or_else(extent)?;
        let mut released = Vec::new();
        let mut stepped = normal_moves;
        for (locus, at) in &strokes {
            if at.moved() {
                next.clocks.insert(*locus, at.clock());
            }
            stepped = stepped.checked_add(at.stepped()).ok_or_else(extent)?;
            released.extend(
                at.released()
                    .into_iter()
                    .map(|(carrier, entry, residual)| (*locus, carrier, entry, residual)),
            );
        }
        let storage_growth =
            certify_storage_growth(&self.storage_forms()?, &next.storage_forms()?)?
                .ok_or(HnnError::UncertifiedStorage)?;
        next.storage_product = &self.storage_product * (Rat::one() + &storage_growth);
        let counted = next.bits_within(retained);
        if counted > self.budget {
            return Err(HnnError::ConstitutionBudget {
                bits: counted,
                budget: self.budget,
                commit: self.commit,
                loci: reached.iter().copied().collect(),
            });
        }
        let reading = DepositReading {
            epoch: Some(EpochDepositReading {
                actual_receiving_ingress: epoch_index,
                heard_cells,
                declared_cells: epoch_cells,
                receiver_partition_bits: grain,
                partition_exponent: exponent,
                loci: locus_readings,
                receiving: receiving_series
                    .ok_or_else(|| refused("an epoch close keeps its receiving series"))?,
            }),
            storage_growth,
            storage_product: next.storage_product.clone(),
            unresolved_contact_material: next
                .carries
                .iter()
                .filter(|((l, c), _)| {
                    retained.contains(l)
                        && matches!(l, Locus::Channel(_))
                        && matches!(c, Carrier::Factor(_) | Carrier::FactorScale(_))
                })
                .flat_map(|((l, c), carry)| carry.0.iter().map(|(i, r)| (*l, *c, *i, r.clone())))
                .collect(),
            steps: certified.into_iter().map(|((l, _), r)| (l, r)).collect(),
            joint,
            amplitude: next.amplitude()?,
            commit: next.commit,
            bits: next.exact_bits(),
            budget: self.budget,
            loci: reached.into_iter().collect(),
            released_bits: released.iter().map(|(.., r)| bits(r)).sum(),
            released,
            stepped,
            vanished,
            charts: Vec::new(),
            landmarks,
            backtracks: strokes
                .values()
                .flat_map(|at| at.backtracks().iter().cloned())
                .collect(),
            lobe,
            lock,
            pumped,
            loaded,
        };
        observe(EpochDepositPhase::Publication);
        Ok((next, reading))
    }
}

fn absorb_receiving_phase(
    phase: &mut PhaseStatistics,
    map: &ExactRatMatrix,
    samples: &[Sample],
    parts: &[EpochReceivingRecord],
) -> Result<(), HnnError> {
    // q is the actual heard class, not p_tilde+(q-p_hat). Reconstructing q
    // from the latter would absorb the released foil as spurious target mass.
    for (sample, part) in samples.iter().zip(parts) {
        if sample.feature.iter().all(Zero::is_zero) {
            continue;
        }
        let observed: Vec<_> = part.positive.iter().step_by(2).cloned().collect();
        let targets: Vec<Rat> = observed
            .iter()
            .enumerate()
            .map(|(class, mass)| {
                let predicted: Rat = (0..map.columns())
                    .map(|j| {
                        map.get(2 * class + 1, j).expect("declared receiving shape")
                            * &sample.feature[j]
                    })
                    .sum();
                if mass.is_positive() {
                    predicted + Rat::from_integer(4.into()) * &part.phase[2 * class + 1] / mass
                } else {
                    predicted
                }
            })
            .collect();
        phase
            .absorb(&sample.weight, &sample.feature, &observed, &targets)
            .map_err(|_| {
                refused("the receiving epoch phase statistics refuse their actual heard class")
            })?;
    }
    Ok(())
}

fn receiving_series_for(
    samples: &[Sample],
    parts: &[EpochReceivingRecord],
    rows: usize,
    columns: usize,
    period: u64,
) -> Result<(EpochArray, EpochArray, EpochArray), HnnError> {
    if samples.len() != parts.len() {
        return Err(refused(
            "one receiving positive/foil/phase split is required per actual receiving record",
        ));
    }
    let mut positive = EpochArray::zero(rows, columns)?;
    let mut foil = EpochArray::zero(rows, columns)?;
    let mut phase = EpochArray::with_row_divisors(
        rows,
        columns,
        0,
        vec![BigInt::zero(); rows.checked_mul(columns).ok_or_else(extent)?],
        (0..rows)
            .map(|row| if row % 2 == 0 { 1 } else { period })
            .collect(),
    )?;
    let phase_rows: Vec<_> = (1..rows).step_by(2).collect();
    for (sample, part) in samples.iter().zip(parts) {
        if part.feature != sample.feature
            || part.positive.len() != rows
            || part.foil.len() != rows
            || part.phase.len() != rows
            || part.positive.iter().enumerate().any(|(i, v)| {
                if i % 2 == 1 {
                    !v.is_zero()
                } else {
                    *v != Rat::zero() && *v != Rat::one()
                }
            })
            || part.positive.iter().step_by(2).sum::<Rat>() != Rat::one()
            || part.foil.iter().enumerate().any(|(i, v)| {
                if i % 2 == 1 {
                    !v.is_zero()
                } else {
                    v.is_negative() || *v > Rat::one()
                }
            })
            || part.foil.iter().step_by(2).sum::<Rat>() > Rat::one()
            || part.phase.iter().step_by(2).any(|v| !v.is_zero())
            || part
                .positive
                .iter()
                .zip(&part.foil)
                .zip(&part.phase)
                .zip(&sample.covector)
                .any(|(((q, p), phase), g)| q - p + phase != *g)
        {
            return Err(refused(
                "receiving series must retain the heard class, partitioned foil, phase, and actual feature exactly",
            ));
        }
        let record = |covector: &[Rat], phase: bool| {
            let sample = Sample {
                weight: Rat::one(),
                feature: part.feature.clone(),
                covector: covector.to_vec(),
                masses: None,
            };
            if phase {
                EpochRecord::from_sample_with_phase_rows(&sample, &phase_rows, period)
            } else {
                EpochRecord::from_sample(&sample)
            }
        };
        let q = record(&part.positive, false)?;
        let p = record(&part.foil, false)?;
        let angle = record(&part.phase, true)?;
        positive = positive.add(&q.covector.multiply(&q.feature)?)?;
        foil = foil.add(&p.covector.multiply(&p.feature)?)?;
        phase = phase.add(&angle.covector.multiply(&angle.feature)?)?;
    }
    Ok((positive, foil, phase))
}

fn add_rows(left: &mut [Vec<Rat>], right: &[Vec<Rat>]) -> Result<(), HnnError> {
    if left.len() != right.len() || left.iter().zip(right).any(|(a, b)| a.len() != b.len()) {
        return Err(refused(
            "epoch factor terms must meet their declared family shape",
        ));
    }
    for (a, b) in left.iter_mut().zip(right) {
        for (x, y) in a.iter_mut().zip(b) {
            *x += y;
        }
    }
    Ok(())
}
fn add_vector(left: &mut [Rat], right: &[Rat]) -> Result<(), HnnError> {
    if left.len() != right.len() {
        return Err(refused(
            "epoch factor vectors must meet their declared family shape",
        ));
    }
    for (a, b) in left.iter_mut().zip(right) {
        *a += b;
    }
    Ok(())
}
fn add_factor(left: &mut FactorStep, right: &FactorStep) -> Result<(), HnnError> {
    if (left.gradient.locus(), left.gradient.family())
        != (right.gradient.locus(), right.gradient.family())
    {
        return Err(refused("epoch factors must keep their own reached family"));
    }
    match (&mut left.gradient, &right.gradient) {
        (
            FactorGradient::Passive { gradient: a, .. },
            FactorGradient::Passive { gradient: b, .. },
        )
        | (
            FactorGradient::Storage { gradient: a, .. },
            FactorGradient::Storage { gradient: b, .. },
        )
        | (
            FactorGradient::Stiffness { gradient: a, .. },
            FactorGradient::Stiffness { gradient: b, .. },
        )
        | (
            FactorGradient::Dissipation { gradient: a, .. },
            FactorGradient::Dissipation { gradient: b, .. },
        ) => *a = a.add(b)?,
        (
            FactorGradient::Slices { gradient: a, .. },
            FactorGradient::Slices { gradient: b, .. },
        ) => {
            if a.len() != b.len() {
                return Err(refused(
                    "epoch slice families must meet their declared ranks",
                ));
            }
            for ((au, av), (bu, bv)) in a.iter_mut().zip(b) {
                add_vector(au, bu)?;
                add_vector(av, bv)?;
            }
        }
        (
            FactorGradient::Standing {
                gradient: a,
                reach: ar,
                ..
            },
            FactorGradient::Standing {
                gradient: b,
                reach: br,
                ..
            },
        ) => {
            add_vector(a, b)?;
            let mut map: BTreeMap<usize, Rat> = std::mem::take(ar).into_iter().collect();
            for (ring, energy) in br {
                *map.entry(*ring).or_default() += energy;
            }
            *ar = map.into_iter().collect();
        }
        (
            FactorGradient::Resonator { gradient: a, .. },
            FactorGradient::Resonator { gradient: b, .. },
        ) => *a += b,
        (
            FactorGradient::PairPort {
                outputs: a,
                current: ac,
                earlier: ae,
                speed,
                ..
            },
            FactorGradient::PairPort {
                outputs: b,
                current: bc,
                earlier: be,
                ..
            },
        ) => {
            add_rows(a, b)?;
            add_rows(ac, bc)?;
            add_rows(ae, be)?;
            // Not consumed: grouped preparation explicitly selects the existing
            // rank-norm certificate instead of an unrelated per-word ray speed.
            *speed = [Rat::zero(), Rat::zero()];
        }
        _ => {
            return Err(refused(
                "epoch factors must retain their declared material kind",
            ));
        }
    }
    left.energy += &right.energy;
    left.covector = left.covector.clone().max(right.covector.clone());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn certificate_sample(
        index: usize,
        normalizer: i64,
        bits: u32,
    ) -> (Sample, EpochReceivingRecord) {
        let masses = vec![rat(1, normalizer), rat(normalizer - 1, normalizer)];
        let denominator = BigInt::one() << bits as usize;
        let foil: Vec<_> = masses
            .iter()
            .map(|p| Rat::new(p.numer() * &denominator / p.denom(), denominator.clone()))
            .collect();
        // Soft targets and an odd-period phase retain their exact producing
        // operands; no target is inferred from the signs of the covector.
        let q = rat((index % 3 + 1) as i64, 4);
        let feature = vec![
            rat((index % 5) as i64 - 2, 4),
            rat((index % 3) as i64 - 1, 2),
        ];
        let part = EpochReceivingRecord {
            feature: feature.clone(),
            positive: vec![q.clone(), Rat::zero(), Rat::one() - &q, Rat::zero()],
            foil: vec![foil[0].clone(), Rat::zero(), foil[1].clone(), Rat::zero()],
            phase: vec![
                Rat::zero(),
                rat((index % 3) as i64 - 1, 11),
                Rat::zero(),
                rat(1, 22),
            ],
        };
        let sample = Sample {
            weight: match index % 3 {
                0 => Rat::one(),
                1 => rat(-1, 2),
                _ => Rat::zero(),
            },
            feature,
            covector: part
                .positive
                .iter()
                .zip(&part.foil)
                .zip(&part.phase)
                .map(|((q, p), phase)| q - p + phase)
                .collect(),
            masses: Some(masses),
        };
        (sample, part)
    }

    fn certificate_direction() -> Vec<Vec<Rat>> {
        vec![
            vec![rat(1, 2), rat(-1, 4)],
            vec![rat(-1, 2), rat(1, 4)],
            vec![rat(-3, 4), rat(1, 2)],
            vec![rat(1, 4), Rat::one()],
        ]
    }

    // The literal pre-enclosure partition sum, deliberately retaining its
    // signed cancellation and its existing unweighted operands.
    fn exact_partition(
        samples: &[Sample],
        parts: &[EpochReceivingRecord],
        direction: &[Vec<Rat>],
    ) -> Rat {
        let mut partition = Rat::zero();
        for (sample, part) in samples.iter().zip(parts) {
            for (class, mass) in face_masses(sample).unwrap().iter().enumerate() {
                let delta: Rat = direction[2 * class]
                    .iter()
                    .zip(&sample.feature)
                    .map(|(d, f)| d * f)
                    .sum();
                partition += (mass - &part.foil[2 * class]) * delta;
            }
        }
        partition
    }

    #[test]
    fn epoch_certificate_grid_ceil_keeps_signed_and_exact_endpoints() {
        let denominator = BigInt::from(16);
        for (value, numerator) in [
            (rat(1, 3), 6),
            (rat(-1, 3), -5),
            (rat(1, 2), 8),
            (rat(-1, 2), -8),
            (Rat::zero(), 0),
        ] {
            let upper = Rat::new(
                upper_grid_numerator(&value, &denominator),
                denominator.clone(),
            );
            assert_eq!(
                upper.numer() * (&denominator / upper.denom()),
                BigInt::from(numerator)
            );
            assert!(upper >= value);
            assert!(upper - value < rat(1, 16));
        }
        let ordered: Vec<_> = (-32..=32)
            .map(|n| upper_grid_numerator(&rat(n, 17), &denominator))
            .collect();
        assert!(ordered.windows(2).all(|pair| pair[0] <= pair[1]));
    }

    #[test]
    fn epoch_certificate_encloses_exact_coprime_signed_soft_target_reference() {
        let bits = 7;
        let (samples, parts): (Vec<_>, Vec<_>) = [3, 5, 7, 11, 13, 17, 19, 23, 29]
            .into_iter()
            .enumerate()
            .map(|(i, z)| certificate_sample(i, z, bits))
            .unzip();
        let direction = certificate_direction();
        let exact = receiving_fisher_face(&samples, &direction).unwrap();
        let odometer = odometer_alignment_defect(&samples, &direction).unwrap();
        let partition = exact_partition(&samples, &parts, &direction);
        let bounded = receiving_epoch_certificate(&samples, &parts, &direction, bits).unwrap();
        let unit = Rat::new(BigInt::one(), BigInt::one() << (2 * bits) as usize);
        let budget = Rat::from_integer(BigInt::from(samples.len())) * &unit;
        for (upper, exact) in [
            (&bounded.moves, &exact.0),
            (&bounded.odometer, &odometer),
            (&bounded.partition, &partition),
        ] {
            assert!(upper >= exact);
            assert!(upper - exact < budget);
        }
        assert_eq!(bounded.alignment, exact.2);
        assert_eq!(bounded.oscillation, exact.1);
        let old_lower = (&exact.2 - odometer - partition.max(Rat::zero())).max(Rat::zero());
        let new_lower =
            (&bounded.alignment - &bounded.odometer - bounded.partition.clone().max(Rat::zero()))
                .max(Rat::zero());
        assert!(new_lower <= old_lower);
        assert!(&old_lower - &new_lower < &budget * rat(2, 1));
        // Both signs really occur; a per-sample positive-part shortcut would
        // discard the cancellation this certificate must preserve.
        let signs: Vec<_> = samples
            .iter()
            .zip(&parts)
            .map(|(s, p)| {
                exact_partition(std::slice::from_ref(s), std::slice::from_ref(p), &direction)
            })
            .collect();
        assert!(signs.iter().any(Signed::is_negative));
        assert!(signs.iter().any(Signed::is_positive));
        // The exact representation keeps the raw masses attached to each
        // sample and never replaces them with the retained foil.
        assert!(
            samples
                .iter()
                .zip(&parts)
                .all(|(s, p)| s.masses.as_ref().unwrap()[0] != p.foil[0])
        );
    }

    #[test]
    fn epoch_certificate_denominator_does_not_accumulate_sample_normalizers() {
        let bits = 9;
        let mut primes = Vec::new();
        let mut candidate = 3i64;
        while primes.len() < 231 {
            if (2..)
                .take_while(|d| d * d <= candidate)
                .all(|d| candidate % d != 0)
            {
                primes.push(candidate);
            }
            candidate += 2;
        }
        let (samples, parts): (Vec<_>, Vec<_>) = primes
            .into_iter()
            .enumerate()
            .map(|(i, z)| certificate_sample(i, z, bits))
            .unzip();
        let bounded =
            receiving_epoch_certificate(&samples, &parts, &certificate_direction(), bits).unwrap();
        let grid = BigInt::one() << (2 * bits) as usize;
        for upper in [&bounded.moves, &bounded.odometer, &bounded.partition] {
            assert!((&grid % upper.denom()).is_zero());
            assert!(upper.denom().bits() <= u64::from(2 * bits) + 1);
            // Here |w|<=1, |feature_j|<=1, |D_ij|<=1 and two columns give
            // |delta_i|<=2. For two classes Var<=4, phase<=8, hence each
            // move <=2(119/80*4+8/4)<18; odometer<=4/16 and |P|<=4.
            // Upward rounding adds less than one (u<=1) per sample, so
            // every accumulated |numerator| is strictly below 19 n 2^(2L).
            assert!(upper.numer().abs() < BigInt::from(19 * samples.len()) * &grid);
        }
        let mut invalid = samples[0].clone();
        invalid.masses = Some(vec![rat(-1, 3), rat(4, 3)]);
        assert!(
            receiving_epoch_certificate(&[invalid], &parts[..1], &certificate_direction(), bits)
                .is_err()
        );
        assert!(
            receiving_epoch_certificate(&samples, &parts[..1], &certificate_direction(), bits)
                .is_err()
        );
        assert!(receiving_epoch_certificate(&[], &[], &certificate_direction(), u32::MAX).is_err());
    }

    #[test]
    fn epoch_certificate_admitted_steps_hold_under_old_exact_scalar_readings() {
        let bits = 7;
        let (samples, parts): (Vec<_>, Vec<_>) = [7, 11, 13]
            .into_iter()
            .map(|z| {
                let (mut sample, mut part) = certificate_sample(2, z, bits);
                sample.weight = Rat::one();
                sample.feature = vec![Rat::one(), Rat::zero()];
                part.feature = sample.feature.clone();
                (sample, part)
            })
            .unzip();
        let direction = certificate_direction();
        let bounded = receiving_epoch_certificate(&samples, &parts, &direction, bits).unwrap();
        let exact = receiving_fisher_face(&samples, &direction).unwrap();
        let exact_alignment = (&exact.2
            - odometer_alignment_defect(&samples, &direction).unwrap()
            - exact_partition(&samples, &parts, &direction).max(Rat::zero()))
        .max(Rat::zero());
        let bounded_alignment =
            (&bounded.alignment - &bounded.odometer - bounded.partition.clone().max(Rat::zero()))
                .max(Rat::zero());
        assert!(bounded_alignment.is_positive());
        let score = rat(1, 2);
        let covector = bounded.oscillation.clone().max(Rat::one());
        let certified =
            CertifiedStep::certify(&bounded_alignment, &(&score * &bounded.moves), &covector)
                .unwrap()
                .unwrap();
        assert!(certified.holds());
        assert!(&certified.step * &score * &exact.0 <= exact_alignment);
        // Exercise the joint consumer too, including one unchanged second
        // family. Every bounded admission in this dyadic family remains an
        // admission under the exact old scalar operands at that SAME step.
        let bounded_move = crate::holon::deposition::root_ceiling(&bounded.moves);
        let exact_move = crate::holon::deposition::root_ceiling(&exact.0);
        let mut admitted = 0;
        for exponent in -12..=3 {
            let eta = crate::holon::deposition::dyadic(exponent);
            let conservative = crate::holon::deposition::JointReading::read(
                &score,
                [
                    (&eta, &bounded_alignment, &bounded_move),
                    (&eta, &Rat::one(), &Rat::one()),
                ],
            );
            if conservative.holds() {
                admitted += 1;
                let old = crate::holon::deposition::JointReading::read(
                    &score,
                    [
                        (&eta, &exact_alignment, &exact_move),
                        (&eta, &Rat::one(), &Rat::one()),
                    ],
                );
                assert!(old.holds());
                assert!(old.curvature <= conservative.curvature);
                assert!(old.decrease >= conservative.decrease);
            }
        }
        assert!(admitted > 0);
        // More conservative operands may select a smaller gamma or hold a
        // step; equality of published successors is deliberately not asserted.
    }

    #[test]
    fn receiving_split_keeps_one_partition_and_the_producing_fisher_masses() {
        let sample = Sample {
            weight: Rat::one(),
            feature: vec![rat(1, 2), rat(-1, 4)],
            covector: vec![rat(3, 4), rat(1, 11), rat(-1, 2), Rat::zero()],
            masses: Some(vec![rat(1, 3), rat(2, 3)]),
        };
        let part = EpochReceivingRecord {
            feature: sample.feature.clone(),
            positive: vec![Rat::one(), Rat::zero(), Rat::zero(), Rat::zero()],
            foil: vec![rat(1, 4), Rat::zero(), rat(1, 2), Rat::zero()],
            phase: vec![Rat::zero(), rat(1, 11), Rat::zero(), Rat::zero()],
        };
        let (positive, foil, phase) = receiving_series_for(
            std::slice::from_ref(&sample),
            std::slice::from_ref(&part),
            4,
            2,
            11,
        )
        .unwrap();
        let flow = EpochFlow::from_records(
            4,
            2,
            6,
            231,
            0,
            1,
            &[EpochRecord::from_sample_with_phase_rows(&sample, &[1, 3], 11).unwrap()],
        )
        .unwrap();
        assert!(
            positive
                .subtract(&foil)
                .unwrap()
                .add(&phase)
                .unwrap()
                .subtract(&flow.covector)
                .unwrap()
                .is_zero()
        );
        assert_eq!(phase.row_divisors, vec![1, 11, 1, 11]);
        let law = EpochLaw::founded(4, 2, 6, 0)
            .unwrap()
            .with_phase_rows(&[1, 3], 11)
            .unwrap();
        let direction = law.fresh(&flow).unwrap().direction.to_rows();
        assert!(receiving_fisher_face(std::slice::from_ref(&sample), &direction).is_some());
        let mut inferred = sample.clone();
        inferred.masses = None;
        assert!(receiving_fisher_face(&[inferred], &direction).is_none());
        let opening = EpochArray::zero(4, 2).unwrap().to_matrix().unwrap();
        let mut actual = PhaseStatistics::founded(2, 2);
        absorb_receiving_phase(
            &mut actual,
            &opening,
            std::slice::from_ref(&sample),
            std::slice::from_ref(&part),
        )
        .unwrap();
        let mut expected = PhaseStatistics::founded(2, 2);
        expected
            .absorb(
                &Rat::one(),
                &sample.feature,
                &[Rat::one(), Rat::zero()],
                &[rat(4, 11), Rat::zero()],
            )
            .unwrap();
        assert_eq!(actual, expected);
        let mut invalid = part.clone();
        invalid.foil[0] = rat(1, 8);
        assert!(receiving_series_for(&[sample], &[invalid], 4, 2, 11).is_err());
    }
}
