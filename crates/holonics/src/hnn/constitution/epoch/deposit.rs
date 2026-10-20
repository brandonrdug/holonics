//! Native epoch publication: one canonical grouped normal law per locus, with
//! independent word reaches admitted by the existing joint certificate.
//! Upstream normal moves require a consuming same-epoch finite comparison.
//! The ordinary close retains its receiving-only certificate and typed refusal.
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

/// Transient grouped successor. Only the observed comparison owner may consume an
/// upstream candidate after its one same-opening finite probe; no probe state is retained.
#[derive(Debug)]
pub(crate) struct StagedEpochCandidate {
    material: Constitution,
    reading: DepositReading,
    upstream: bool,
    physical_motion: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EpochCandidateScope {
    Whole,
    Joint,
    ReceivingOnly,
}

/// Sufficient operands of this one unpublished batch. Neither a rejected successor nor a
/// sample archive is kept here. The enclosing stage binds these readings to all their inputs.
#[derive(Clone)]
struct PreparedEpochNormals {
    laws: BTreeMap<LinearLocus, EpochLaw>,
    flows: BTreeMap<LinearLocus, EpochFlow>,
    faces: Vec<(LinearLocus, EpochCertificateFace)>,
    receiving_series: Option<EpochReceivingSeries>,
    raw_covector_scales: BTreeMap<LinearLocus, Rat>,
    raw_alignments: BTreeMap<LinearLocus, Rat>,
    alignment_defects: BTreeMap<LinearLocus, (Rat, Rat)>,
    certified: BTreeMap<(Locus, Family), StepReading>,
    fresh_joint: Option<JointReading>,
}

/// One same-opening NormalMaps transaction. Borrowed inputs cannot be replaced between rungs;
/// only current-batch normal statistics and their actually certified fresh gains are shared.
/// This object is never installed in Constitution or Resident and has no checkpoint codec.
pub(crate) struct ObservedNormalEpochStage<'a> {
    opening: &'a Constitution,
    deposits: &'a [Deposit],
    receiver: usize,
    receiving_period: u64,
    heard_cells: u64,
    epoch_cells: u64,
    epoch_index: u64,
    exponent: u32,
    retained: &'a BTreeSet<Locus>,
    tree: Landmarks,
    pair_speed: &'a dyn Fn(usize, usize, &PairPort, [&[Vec<Rat>]; 3]) -> Result<[Rat; 2], HnnError>,
    receiving_parts: &'a [EpochReceivingRecord],
    execution: &'a dyn crate::hnn::reference::observed::ObservedEpochExecution,
    allow_channel_dissipation: bool,
    channel_grain: Option<ObservedChannelGrainPlan>,
    prepared: Option<PreparedEpochNormals>,
}

impl<'a> ObservedNormalEpochStage<'a> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        opening: &'a Constitution,
        deposits: &'a [Deposit],
        receiver: usize,
        receiving_period: u64,
        heard_cells: u64,
        epoch_cells: u64,
        epoch_index: u64,
        exponent: u32,
        retained: &'a BTreeSet<Locus>,
        tree: Landmarks,
        pair_speed: &'a dyn Fn(
            usize,
            usize,
            &PairPort,
            [&[Vec<Rat>]; 3],
        ) -> Result<[Rat; 2], HnnError>,
        receiving_parts: &'a [EpochReceivingRecord],
        execution: &'a dyn crate::hnn::reference::observed::ObservedEpochExecution,
        allow_channel_dissipation: bool,
    ) -> Result<Self, HnnError> {
        if deposits.iter().flat_map(|deposit| deposit.factors()).any(|factor| {
            !allow_channel_dissipation
                || !matches!(&factor.gradient, FactorGradient::Dissipation { .. })
        }) {
            return Err(refused(
                "shared epoch staging holds every physical family except explicitly scoped channel D",
            ));
        }
        Ok(Self {
            opening,
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
            execution,
            allow_channel_dissipation,
            channel_grain: None,
            prepared: None,
        })
    }

    /// Immutable across Whole/Joint; ReceivingOnly deliberately replays with no channel target.
    pub(crate) fn with_channel_grain(mut self, plan: ObservedChannelGrainPlan) -> Result<Self, HnnError> {
        if !self.allow_channel_dissipation || self.prepared.is_some()
            || plan.receiver != self.receiver || plan.ingress_before != self.epoch_index
            || plan.ingress_after <= plan.ingress_before {
            return Err(refused("a channel grain plan binds the original D stage and actual receiver ingress"));
        }
        self.channel_grain = Some(plan);
        Ok(self)
    }

    pub(crate) fn stage(
        &mut self,
        scope: EpochCandidateScope,
        observe: &mut dyn FnMut(EpochDepositPhase),
    ) -> Result<StagedEpochCandidate, EpochStageFailure> {
        // A zero fallback is an independently fully certified successor, never an error catch.
        let mut canonical = self.stage_projection(scope, observe, None)?;
        if scope != EpochCandidateScope::ReceivingOnly {
            return Ok(canonical);
        }
        let mut receipt = EpochQuantumProjectionReading {
            eligible: false,
            skip_reason: None,
            trials: vec![],
        };
        let kind = LinearLocus::Receiving(self.receiver);
        let prepared = self
            .prepared
            .as_ref()
            .expect("successful shared stage prepared its normals");
        let law = prepared.laws[&kind].clone();
        let flow = prepared.flows[&kind].clone();
        let gamma = prepared
            .certified
            .get(&(kind.locus(), Family::Map))
            .map(|r| r.step.step.clone())
            .unwrap_or_else(Rat::zero);
        let gain = EpochArray::from_dyadic_scalar(&gamma)
            .map_err(|e| EpochStageTrace::default().failed(e))?;
        let (skip, options) = quantum_projection::alternatives(&law, &flow, &gain)
            .map_err(|e| EpochStageTrace::default().failed(e))?;
        receipt.skip_reason = skip;
        receipt.eligible = skip.is_none();
        for option in options {
            let mut trial = EpochQuantumTrialReading {
                row: option.row,
                column: option.column,
                sign: option.sign,
                normal_admitted: false,
                actual_admitted: false,
                refusal: None,
                reason: None,
            };
            match law.deposit_quantum(&flow, &gain, &option) {
                Ok(_) => trial.normal_admitted = true,
                Err(HnnError::EpochStepNonDescending { .. }) => {
                    trial.reason = Some(
                        "one-quantum alternative fails an unchanged retained normal-fall guard"
                            .into(),
                    );
                    receipt.trials.push(trial);
                    continue;
                }
                Err(error) => return Err(EpochStageTrace::default().failed(error)),
            }
            // All branches replay original opening with immutable prepared operands.
            // CandidateStaged callbacks describe these unpublished stages; only this
            // returned candidate can reach the caller's existing publication owner.
            match self.stage_projection(scope, observe, Some(&option)) {
                Ok(mut candidate) => {
                    trial.actual_admitted = true;
                    receipt.trials.push(trial);
                    candidate
                        .reading
                        .epoch
                        .as_mut()
                        .expect("epoch stage receipt")
                        .quantum_projection = Some(receipt);
                    return Ok(candidate);
                }
                Err(failure) if quantum_projection::optional_refusal(&failure, self.receiver) => {
                    trial.reason = Some(failure.error.to_string());
                    trial.refusal = Some(failure.evidence);
                    receipt.trials.push(trial);
                }
                Err(failure) => return Err(failure),
            }
        }
        canonical
            .reading
            .epoch
            .as_mut()
            .expect("epoch stage receipt")
            .quantum_projection = Some(receipt);
        Ok(canonical)
    }

    fn stage_projection(
        &mut self,
        scope: EpochCandidateScope,
        observe: &mut dyn FnMut(EpochDepositPhase),
        quantum: Option<&QuantumProjection>,
    ) -> Result<StagedEpochCandidate, EpochStageFailure> {
        let mut trace = EpochStageTrace::default();
        if scope != EpochCandidateScope::Whole && self.prepared.is_none() {
            return Err(trace.failed(refused(
                "a restaged normal epoch needs the same opening's actually certified fresh gains",
            )));
        }
        self.opening
            .prepare_observed_epoch_with_execution(
                self.deposits,
                self.receiver,
                self.receiving_period,
                self.heard_cells,
                self.epoch_cells,
                self.epoch_index,
                self.exponent,
                self.retained,
                self.tree.clone(),
                self.pair_speed,
                self.receiving_parts,
                observe,
                self.execution,
                Some(scope),
                &mut trace,
                Some(&mut self.prepared),
                quantum,
                self.allow_channel_dissipation,
                if scope == EpochCandidateScope::ReceivingOnly { None } else { self.channel_grain.as_ref() },
            )
            .map_err(|error| {
                let mut failure = trace.failed(error);
                failure.normal_inputs_prepared = self.prepared.is_some();
                failure
            })
    }
}

impl StagedEpochCandidate {
    pub(crate) fn joint_directions(&self) -> Vec<EpochJointDirectionReading> {
        self.reading
            .epoch
            .as_ref()
            .into_iter()
            .flat_map(|epoch| &epoch.loci)
            .filter_map(|locus| locus.joint_direction.clone())
            .collect()
    }
    /// New physical maps and channel D material against predecessor context.
    /// Neither the candidate's independently staged tree nor its received
    /// population may make its own prospective comparison easier.
    pub(crate) fn comparison_material(
        &self,
        opening: &Constitution,
    ) -> Result<Constitution, HnnError> {
        if opening.commit.checked_add(1) != Some(self.material.commit)
            || opening.rings.len() != self.material.rings.len()
        {
            return Err(refused(
                "the epoch comparison keeps its producing material predecessor",
            ));
        }
        let mut material = self.material.clone();
        for (candidate, original) in material.rings.iter_mut().zip(&opening.rings) {
            candidate.tree = original.tree.clone();
            candidate.population = original.population.clone();
        }
        Ok(material)
    }
    /// Includes represented normal maps and an admitted actual channel D ray.
    /// Physical factors have already passed their scoped endpoint guard.
    pub(crate) fn has_physical_motion(&self) -> bool {
        self.physical_motion
    }
    pub(crate) fn requires_comparison(&self) -> bool {
        self.upstream
    }
    pub(crate) fn admit_receiving(self) -> Result<(Constitution, DepositReading), HnnError> {
        if self.upstream {
            return Err(refused(
                "an upstream epoch candidate needs its finite comparison",
            ));
        }
        Ok((self.material, self.reading))
    }
    pub(crate) fn admit_change(
        self,
        change: &crate::ratio::algebraic::ExactInterval,
    ) -> Option<(Constitution, DepositReading)> {
        (change.upper < Rat::zero()).then_some((self.material, self.reading))
    }
    /// Called only for identical executed objectives or the correlated enclosure [0,0].
    pub(crate) fn admit_neutral(self) -> (Constitution, DepositReading) {
        (self.material, self.reading)
    }
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
    CandidateStaged,
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

fn carrier_family(carrier: Carrier) -> Option<Family> {
    Some(match carrier {
        Carrier::Map | Carrier::Gram => Family::Map,
        Carrier::Passive | Carrier::PassiveScale => Family::Passive,
        Carrier::Slices | Carrier::SliceScale => Family::Slices,
        Carrier::Standing | Carrier::StandingScale => Family::Standing,
        Carrier::Resonator(family) | Carrier::ResonatorScale(family) => Family::Resonator(family),
        Carrier::Pair { offset, .. } => Family::Pair(offset),
        Carrier::Factor(family) | Carrier::FactorScale(family) => Family::Factor(family),
        Carrier::PairScale => return None,
    })
}

#[cfg(test)]
fn admit_actual_factor_displacements(
    opening: &Constitution, endpoint: &Constitution,
    strokes: &BTreeMap<Locus, BudgetedCarry>, requests: &[FactorStep],
    certified: &BTreeMap<(Locus, Family), StepReading>,
    original_faces: &BTreeMap<(Locus, Family), FactorPrepared>,
    allow_channel_dissipation: bool, evidence: &mut Option<EpochStageRefusal>,
) -> Result<Vec<channel_ray::ActualChannelRayFace>, HnnError> {
    admit_actual_factor_displacements_with_rebases(opening, endpoint, strokes, requests,
        certified, original_faces, allow_channel_dissipation, &BTreeMap::new(), evidence)
}

#[allow(clippy::too_many_arguments)]
fn admit_actual_factor_displacements_with_rebases(
    opening: &Constitution,
    endpoint: &Constitution,
    strokes: &BTreeMap<Locus, BudgetedCarry>,
    requests: &[FactorStep],
    certified: &BTreeMap<(Locus, Family), StepReading>,
    original_faces: &BTreeMap<(Locus, Family), FactorPrepared>,
    allow_channel_dissipation: bool,
    rebases: &BTreeMap<usize, channel_grain::ChannelGrainRebase>,
    evidence: &mut Option<EpochStageRefusal>,
) -> Result<Vec<channel_ray::ActualChannelRayFace>, HnnError> {
    // The endpoint remains authoritative. Only the explicitly scoped D family
    // can use this first-variation bridge; C/K and every other family stay held.
    let mut actual_faces = Vec::new();
    let mut admitted_channel_d = BTreeSet::new();
    for ray in channel_ray::ChannelFactorDisplacement::read_all(opening, endpoint)? {
        let locus = Locus::Channel(ray.contact);
        let family = Family::Factor(ray.family);
        let rebase_delta = rebases.get(&ray.contact).map(|r| &r.factor_delta[ray.family]);
        let mut refusal = EpochStageRefusal::at(
            "actual_factor_displacement",
            EpochStageCondition::NonlinearFactorRay,
            "only a matching actual channel D ray has a finite-admission path",
            Some(locus), Some(family),
        ).read("actual_parameter_displacement", match EpochArray::from_dyadic_matrix(&ray.displacement) {
            Ok(delta) => EpochStageValue::Series(EpochSeriesReading::of(&delta)),
            Err(_) => EpochStageValue::Unavailable("the exact parameter delta is not dyadic"),
        }).read("actual_delta_matches_staged_quotient", EpochStageValue::Index(usize::from(
            strokes.get(&locus).is_some_and(|stroke| ray.matches_stroke_after_rebase(stroke, rebase_delta))
        )));
        if !allow_channel_dissipation || ray.family != 2 {
            refusal.first(evidence);
            return Err(refused("actual epoch certification still holds C/K and unscoped physical factor rays"));
        }
        let request = requests.iter().enumerate().find(|(_, step)| step.gradient.locus() == locus
            && step.gradient.family() == family);
        let fresh = certified.get(&(locus, family));
        let original = original_faces.get(&(locus, family));
        if rebases.contains_key(&ray.contact) && request.is_some() && original.is_some()
            && !fresh.is_some_and(|reading| reading.step.step.is_positive()) {
            refusal = refusal.read("actual_ray_rate", EpochStageValue::Unavailable(
                "the scheduled D rebase waits for its actually certified fresh positive rate"));
            refusal.first(evidence);
            return Err(refused("a scheduled channel rebase waits for its original fresh positive D rate"));
        }
        let (Some((request_index, request)), Some(fresh), Some(original)) = (request, fresh, original) else {
            refusal = refusal.read("actual_ray_rate", EpochStageValue::Unavailable(
                "the changed D endpoint has no original request, fresh positive rate, or prepared metadata"
            ));
            refusal.first(evidence);
            return Err(refused("an actual channel D ray needs its original fresh positive rate"));
        };
        if !fresh.step.step.is_positive() {
            refusal = refusal.read("actual_ray_rate", EpochStageValue::Unavailable(
                "the original D family was held; no positive rate is invented"
            ));
            refusal.first(evidence);
            return Err(refused("an actual channel D ray needs its original fresh positive rate"));
        }
        if !strokes.get(&locus).is_some_and(|stroke| ray.matches_stroke_after_rebase(stroke, rebase_delta)) {
            refusal.first(evidence);
            return Err(refused("the actual channel D endpoint must equal its rebase delta plus staged applied quotient"));
        }
        let face = ray.actual_face(original, request_index, request, fresh, &opening.hop)?;
        admitted_channel_d.insert(locus);
        actual_faces.push(face);
    }
    let first = strokes.iter().find_map(|(locus, at)| {
        at.staged
            .iter()
            .find(|((carrier, _), (_, q))| {
                !q.is_zero()
                    && matches!(
                        carrier,
                        Carrier::Passive
                            | Carrier::Slices
                            | Carrier::Standing
                            | Carrier::Resonator(_)
                            | Carrier::Pair { .. }
                            | Carrier::Factor(_)
                    )
                    && !(allow_channel_dissipation
                        && admitted_channel_d.contains(locus)
                        && matches!(carrier, Carrier::Factor(2)))
            })
            .map(|((carrier, entry), (_, q))| (*locus, at, *carrier, *entry, q))
    });
    if let Some((locus, at, carrier, entry, q)) = first {
        EpochStageRefusal::at(
            "actual_factor_displacement",
            EpochStageCondition::NonlinearFactorRay,
            "represented nonlinear factor displacement q * 2^(-L) must have its own certified ray",
            Some(locus),
            carrier_family(carrier),
        )
        .read("carrier", EpochStageValue::Carrier(carrier))
        .read("entry", EpochStageValue::Index(entry))
        .read("applied_coordinate_q", EpochStageValue::Integer(q.clone()))
        .read("lattice_exponent_L", EpochStageValue::Exponent(at.lattice.exponent()))
        .read("displacement_q_times_two_minus_L", EpochStageValue::Ratio(
            Rat::from_integer(q.clone()) * at.lattice.unit(),
        ))
        .first(evidence);
        return Err(refused("actual epoch certification requires the represented nonlinear factor rays"));
    }
    Ok(actual_faces)
}

/// The receiving map acts once on fixed producing features, so its logit ray
/// is affine. Upstream normal maps can change the executed trajectory: loaded
/// dynamics, repeated contrast action, transient splits, and a simultaneous
/// readout move need second variations absent from the current reach records.
/// A first-order gain/tube certificate must not silently stand in for them.
fn admit_actual_normal_domain(
    receiver: usize,
    candidates: &BTreeMap<LinearLocus, EpochDeposit>,
) -> Result<(), HnnError> {
    for (kind, candidate) in candidates {
        if candidate.step.is_zero() {
            continue;
        }
        match kind {
            LinearLocus::Receiving(ring) if *ring == receiver => {}
            LinearLocus::Receiving(_) => {
                return Err(refused(
                    "an actual receiving epoch move must keep its producing receiver",
                ));
            }
            LinearLocus::SourcePort(_) => {
                return Err(refused(
                    "an actual source epoch move requires its affine executed-transport or second-variation certificate",
                ));
            }
            LinearLocus::Contrast(_) => {
                return Err(refused(
                    "an actual contrast epoch move requires its executed second-variation certificate",
                ));
            }
        }
    }
    Ok(())
}

fn admit_refined_source_carries(
    locus: Locus,
    finer: u32,
    carries: &Carries,
    evidence: &mut Option<EpochStageRefusal>,
) -> Result<(), HnnError> {
    let half_exponent = finer.checked_add(1).ok_or_else(extent)?;
    let half = Rat::new(BigInt::one(), BigInt::one() << half_exponent as usize);
    let first =
        carries
            .iter()
            .filter(|((at, _), _)| *at == locus)
            .find_map(|((_, carrier), carry)| {
                carry
                    .0
                    .iter()
                    .find(|(_, r)| **r < -&half || **r >= half)
                    .map(|(entry, residual)| (*carrier, *entry, residual))
            });
    if let Some((carrier, entry, residual)) = first {
        EpochStageRefusal::at(
            "source_refinement",
            EpochStageCondition::SourceRefinementHalfCell,
            "-half <= carried residual < half on the finer source lattice",
            Some(locus),
            carrier_family(carrier),
        )
        .read("carrier", EpochStageValue::Carrier(carrier))
        .read("entry", EpochStageValue::Index(entry))
        .read("residual", EpochStageValue::Ratio(residual.clone()))
        .read("half", EpochStageValue::Ratio(half.clone()))
        .read("finer_lattice_exponent", EpochStageValue::Exponent(finer))
        .first(evidence);
        return Err(refused(
            "source refinement needs its pair-factor remainders inside the finer half-cell",
        ));
    }
    Ok(())
}

/// The represented normal delta is its own fixed unit ray. Read its true
/// producing samples, not the fresh Jacobi direction that selected gamma.
/// Per-sample scalar enclosures keep one dyadic denominator across the epoch.
pub(super) fn actual_epoch_face(
    kind: LinearLocus,
    delta: &EpochArray,
    samples: &[Sample],
    receiving_parts: &[EpochReceivingRecord],
    partition_bits: u32,
    admitted_covector: Rat,
    evidence: &mut Option<EpochStageRefusal>,
) -> Result<EpochCertificateFace, HnnError> {
    let rows = delta.to_rows();
    let (alignment, moves) = if matches!(kind, LinearLocus::Receiving(_)) {
        let face = receiving_epoch_certificate(samples, receiving_parts, &rows, partition_bits)?;
        (
            face.alignment - face.odometer - face.partition.max(Rat::zero()),
            face.moves,
        )
    } else {
        // Precision follows both the flow partition and actual material grain.
        // A tiny positive alignment still unresolved on this declared grid is
        // refused, never rounded up into a descent certificate.
        let bits = partition_bits
            .checked_add(delta.exponent)
            .and_then(|b| b.checked_mul(2))
            .ok_or_else(extent)?;
        let denominator = BigInt::one() << bits as usize;
        let (mut alignment, mut moves) = (BigInt::zero(), BigInt::zero());
        for sample in samples {
            if sample.feature.len() != delta.columns
                || sample.covector.len() != delta.rows
                || sample.weight.is_negative()
            {
                EpochStageRefusal::at("actual_ray", EpochStageCondition::SampleShape,
                    "producing feature/covector dimensions match the represented ray and sample weight >= 0", Some(kind.locus()), Some(Family::Map))
                    .read("feature_columns", EpochStageValue::Index(sample.feature.len()))
                    .read("ray_columns", EpochStageValue::Index(delta.columns))
                    .read("covector_rows", EpochStageValue::Index(sample.covector.len()))
                    .read("ray_rows", EpochStageValue::Index(delta.rows))
                    .read("weight", EpochStageValue::Ratio(sample.weight.clone())).first(evidence);
                return Err(refused(
                    "an actual epoch ray needs its producing sample shapes and metric",
                ));
            }
            let image: Vec<Rat> = rows
                .iter()
                .map(|row| row.iter().zip(&sample.feature).map(|(p, f)| p * f).sum())
                .collect();
            let a = &sample.weight
                * image
                    .iter()
                    .zip(&sample.covector)
                    .map(|(p, g)| p * g)
                    .sum::<Rat>();
            let m = &sample.weight * image.iter().map(|p| p * p).sum::<Rat>();
            alignment -= upper_grid_numerator(&(-a), &denominator);
            moves += upper_grid_numerator(&m, &denominator);
        }
        (
            Rat::new(alignment, denominator.clone()),
            Rat::new(moves, denominator),
        )
    };
    if !alignment.is_positive() {
        EpochStageRefusal::at(
            "actual_ray",
            EpochStageCondition::ActualRayAlignment,
            "actual represented ray alignment > 0",
            Some(kind.locus()),
            Some(Family::Map),
        )
        .read("alignment", EpochStageValue::Ratio(alignment.clone()))
        .read("moves", EpochStageValue::Ratio(moves.clone()))
        .read(
            "admitted_covector",
            EpochStageValue::Ratio(admitted_covector.clone()),
        )
        .read("partition_bits", EpochStageValue::Exponent(partition_bits))
        .read(
            "represented_step",
            EpochStageValue::Array(EpochArrayReading::of(delta)),
        )
        .first(evidence);
        return Err(refused(
            "a moving actual epoch ray must descend its contemporary comparison",
        ));
    }
    let (numerators, denominator) = delta.integral_chart()?;
    let unit = IntegralMatrix::from_grouped(delta.rows, delta.columns, numerators, denominator)?;
    let unit_norms = unit.schur_norms();
    Ok(EpochCertificateFace {
        unit,
        alignment,
        moves,
        covector: admitted_covector,
        unit_norms,
        norm: EpochSpectral::grouped_frobenius(delta),
    })
}

/// Enrich only the first, already failed normal candidate. Reconstructing these operands is
/// exterior observation: a diagnostic error cannot replace the native refusal or change its
/// order. All arrays below die with this staging attempt, never with the continuing state.
#[allow(clippy::too_many_arguments)]
fn enrich_failed_normal_ray(
    evidence: &mut Option<EpochStageRefusal>,
    kind: LinearLocus,
    law: &EpochLaw,
    flow: &EpochFlow,
    deposit: &EpochDeposit,
    gamma: &Rat,
    active_lattice: Option<u32>,
    samples: &[Sample],
) {
    let Some(evidence) = evidence.as_mut().filter(|evidence| {
        evidence.locus == Some(kind.locus()) && evidence.family == Some(Family::Map)
    }) else {
        return;
    };
    let push = |evidence: &mut EpochStageRefusal, name, value| {
        evidence.readings.push(EpochStageReading { name, value });
    };
    push(
        evidence,
        "active_lattice_L",
        active_lattice
            .map(EpochStageValue::Exponent)
            .unwrap_or(EpochStageValue::Unavailable(
                "the active material lattice was not exported",
            )),
    );
    push(
        evidence,
        "opening_map_lattice_L",
        EpochStageValue::Exponent(law.map_lattice),
    );
    push(
        evidence,
        "candidate_map_lattice_L",
        EpochStageValue::Exponent(deposit.successor.map_lattice),
    );
    let refined = match (kind, active_lattice) {
        (LinearLocus::SourcePort(_), Some(active)) => {
            EpochStageValue::Text(if deposit.successor.map_lattice > active {
                "yes"
            } else {
                "no"
            })
        }
        (LinearLocus::SourcePort(_), None) => EpochStageValue::Unavailable(
            "refinement relative to the active lattice is unknown because that lattice was not exported",
        ),
        _ => EpochStageValue::Text("not a source refinement"),
    };
    push(evidence, "source_lattice_refined", refined);
    push(
        evidence,
        "projection_rule",
        EpochStageValue::Text(if deposit.quantum_projection.is_some() {
            "one signed existing-lattice coordinate after wholly-zero canonical projection"
        } else {
            "componentwise truncation toward zero on candidate map lattice"
        }),
    );
    push(
        evidence,
        "fresh_gain_gamma",
        EpochStageValue::Ratio(gamma.clone()),
    );
    let diagnostic = || -> Result<Vec<EpochStageReading>, HnnError> {
        // Use exactly the normal owner's paired flow, Gram and reached support. Raw producer
        // sample alignment is reported separately; it is not substituted for paired G.
        let paired = law.symmetry.as_ref().map(|s| flow.paired(s)).transpose()?;
        let flow = paired.as_ref().unwrap_or(flow);
        let gram = &deposit.successor.gram;
        let scaled_fresh = flow
            .covector
            .scalar_product(&EpochArray::from_dyadic_scalar(gamma)?)?;
        let r_star = law.news.add(&scaled_fresh)?;
        let (retained_direction, _) = law.direction(&law.news, gram, &flow.support)?;
        let (fresh_direction, _) = law.direction(&scaled_fresh, gram, &flow.support)?;
        let residual = deposit.direction.subtract(&deposit.step)?;
        let scalar = |left: &EpochArray, right: &EpochArray| left.dot(right)?.scalar_ratio();
        let g_d = scalar(&flow.covector, &deposit.direction)?;
        let g_p = scalar(&flow.covector, &deposit.step)?;
        let retained_alignment = scalar(&flow.covector, &retained_direction)?;
        let fresh_alignment = scalar(&flow.covector, &fresh_direction)?;
        let projection_alignment = -scalar(&flow.covector, &residual)?;
        let rows = [
            ("paired_G_dot_D", g_d.clone()),
            ("paired_G_dot_P", g_p.clone()),
            ("Rstar_dot_P", scalar(&r_star, &deposit.step)?),
            ("Rold_dot_P", scalar(&law.news, &deposit.step)?),
            ("retained_alignment_component", retained_alignment.clone()),
            ("fresh_alignment_component", fresh_alignment.clone()),
            (
                "projection_alignment_component",
                projection_alignment.clone(),
            ),
            (
                "direction_decomposition_residual",
                g_d - &retained_alignment - &fresh_alignment,
            ),
            (
                "represented_alignment_decomposition_residual",
                g_p - retained_alignment - fresh_alignment - projection_alignment,
            ),
            ("normal_quadratic_fall", deposit.fall.scalar_ratio()?),
        ];
        let mut readings: Vec<_> = rows
            .into_iter()
            .map(|(name, value)| EpochStageReading {
                name,
                value: EpochStageValue::Ratio(value),
            })
            .collect();
        readings.push(EpochStageReading {
            name: "projection_residual_D_minus_P",
            value: EpochStageValue::Series(EpochSeriesReading::of(&residual)),
        });
        readings.push(EpochStageReading {
            name: "projection_changed_direction",
            value: EpochStageValue::Text(if residual.is_zero() { "no" } else { "yes" }),
        });
        Ok(readings)
    };
    if let Some(joint) = &deposit.joint_direction {
        push(
            evidence,
            "proposal_origin",
            EpochStageValue::Text(
                "joint minimum-segment direction; no whole-direction decomposition is asserted",
            ),
        );
        if !evidence.readings.iter().any(|reading| {
            matches!(&reading.value,
            EpochStageValue::JointDirection(existing) if existing.locus == joint.locus)
        }) {
            push(
                evidence,
                "joint_direction",
                EpochStageValue::JointDirection(joint.clone()),
            );
        }
    } else {
        match diagnostic() {
            Ok(readings) => evidence.readings.extend(readings),
            Err(_) => push(
                evidence,
                "normal_alignment_decomposition",
                EpochStageValue::Unavailable(
                    "the failed candidate's normal diagnostic operands could not be reconstructed; native refusal preserved",
                ),
            ),
        }
    }
    if !matches!(kind, LinearLocus::Receiving(_)) {
        let raw_alignment = |delta: &EpochArray| -> Option<Rat> {
            let rows = delta.to_rows();
            let mut total = Rat::zero();
            for sample in samples {
                if sample.feature.len() != delta.columns || sample.covector.len() != delta.rows {
                    return None;
                }
                total += &sample.weight
                    * rows
                        .iter()
                        .zip(&sample.covector)
                        .map(|(row, g)| {
                            g * row
                                .iter()
                                .zip(&sample.feature)
                                .map(|(p, f)| p * f)
                                .sum::<Rat>()
                        })
                        .sum::<Rat>();
            }
            Some(total)
        };
        for (name, delta) in [
            ("raw_sample_G_dot_D", &deposit.direction),
            ("raw_sample_G_dot_P", &deposit.step),
        ] {
            push(
                evidence,
                name,
                raw_alignment(delta)
                    .map(|value| {
                        EpochStageValue::Ratio(if name == "raw_sample_G_dot_D" {
                            value / Rat::from_integer(deposit.direction_divisor.clone())
                        } else {
                            value
                        })
                    })
                    .unwrap_or(EpochStageValue::Unavailable(
                        "the failed sample shape does not pair with this ray",
                    )),
            );
        }
        let guarded_alignment = evidence
            .readings
            .iter()
            .find_map(|reading| match &reading.value {
                EpochStageValue::Step(step) if reading.name == "step" => {
                    Some(step.alignment.clone())
                }
                EpochStageValue::Ratio(value) if reading.name == "alignment" => Some(value.clone()),
                _ => None,
            });
        if let (Some(raw), Some(guarded)) = (raw_alignment(&deposit.step), guarded_alignment) {
            push(
                evidence,
                "raw_minus_guarded_alignment",
                EpochStageValue::Ratio(raw - guarded),
            );
        }
    }
    if !evidence
        .readings
        .iter()
        .any(|reading| reading.name == "curvature_model")
    {
        push(
            evidence,
            "curvature_model",
            EpochStageValue::Unavailable(
                "the actual curvature reader was not reached at this failed guard; no executed jet was read",
            ),
        );
        push(
            evidence,
            "alignment_over_curvature",
            EpochStageValue::Unavailable("actual curvature has not been read"),
        );
        push(
            evidence,
            "largest_local_admissible_dyadic_k",
            EpochStageValue::Unavailable("the actual local step certificate has not been read"),
        );
    }
}

/// Diagnostic only: the exact same paired normal metric used by every proposal rung.
fn normal_news_metric_squared(
    law: &EpochLaw,
    flow: &EpochFlow,
    gamma: &Rat,
) -> Result<(Rat, Rat), HnnError> {
    let paired = law.symmetry.as_ref().map(|s| flow.paired(s)).transpose()?;
    let flow = paired.as_ref().unwrap_or(flow);
    let gram = law.gram.add(&flow.gram)?;
    let b = flow
        .covector
        .scalar_product(&EpochArray::from_dyadic_scalar(gamma)?)?;
    let a = law.news.add(&b)?;
    let (a_direction, _) = law.direction(&a, &gram, &flow.support)?;
    let (b_direction, _) = law.direction(&b, &gram, &flow.support)?;
    Ok((
        a.dot(&a_direction)?.scalar_ratio()?,
        b.dot(&b_direction)?.scalar_ratio()?,
    ))
}

fn epoch_locus_scale_reading(deposit: &EpochDeposit) -> EpochLocusScaleReading {
    let gram = &deposit.successor.gram;
    let gram_unit = BigInt::one() << gram.exponent as usize;
    let gram_column_absolute_sums = (0..gram.columns)
        .map(|column| {
            (0..gram.rows)
                .map(|row| {
                    Rat::new(
                        gram.values[row * gram.columns + column].abs(),
                        &gram_unit * gram.row_divisors[row],
                    )
                })
                .sum()
        })
        .collect();
    let columns = deposit.direction.columns;
    let mut proposed_nonzero_by_row = Vec::with_capacity(deposit.direction.rows);
    let mut represented_nonzero_by_row = Vec::with_capacity(deposit.direction.rows);
    let mut nonzero_proposal_zero_in_step_by_row = Vec::with_capacity(deposit.direction.rows);
    let mut proposed_maximum_absolute_by_row = Vec::with_capacity(deposit.direction.rows);
    let unit = BigInt::one() << deposit.direction.exponent as usize;
    for (row, (proposed, represented)) in deposit
        .direction
        .values
        .chunks_exact(columns)
        .zip(deposit.step.values.chunks_exact(columns))
        .enumerate()
    {
        proposed_nonzero_by_row.push(proposed.iter().filter(|v| !v.is_zero()).count());
        represented_nonzero_by_row.push(represented.iter().filter(|v| !v.is_zero()).count());
        nonzero_proposal_zero_in_step_by_row.push(
            proposed
                .iter()
                .zip(represented)
                .filter(|(a, b)| !a.is_zero() && b.is_zero())
                .count(),
        );
        proposed_maximum_absolute_by_row.push(Rat::new(
            proposed.iter().map(Signed::abs).max().unwrap_or_default(),
            &unit * deposit.direction.row_divisors[row] * &deposit.direction_divisor,
        ));
    }
    EpochLocusScaleReading {
        gram_column_absolute_sums,
        positive_eta: deposit.eta_numerator.is_positive(),
        proposed_nonzero_by_row,
        represented_nonzero_by_row,
        nonzero_proposal_zero_in_step_by_row,
        proposed_maximum_absolute_by_row,
    }
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
        self.prepare_observed_epoch_with_execution(
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
            execution,
            None,
            &mut EpochStageTrace::default(),
            None,
            None,
            false,
            None,
        )?
        .admit_receiving()
    }

    /// Stage once; this method grants no publication capability to a score supplied
    /// outside the actual observed execution owner.
    #[allow(clippy::too_many_arguments)]
    #[allow(
        dead_code,
        reason = "the original staging entry remains a no-observer control for diagnosed staging"
    )]
    pub(crate) fn stage_observed_epoch_with_execution(
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
        scope: EpochCandidateScope,
    ) -> Result<StagedEpochCandidate, HnnError> {
        self.stage_observed_epoch_with_evidence(
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
            execution,
            scope,
        )
        .map_err(|failure| failure.error)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn stage_observed_epoch_with_evidence(
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
        scope: EpochCandidateScope,
    ) -> Result<StagedEpochCandidate, EpochStageFailure> {
        let mut trace = EpochStageTrace::default();
        self.prepare_observed_epoch_with_execution(
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
            execution,
            Some(scope),
            &mut trace,
            None,
            None,
            false,
            None,
        )
        .map_err(|error| trace.failed(error))
    }

    #[allow(clippy::too_many_arguments)]
    fn prepare_observed_epoch_with_execution(
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
        scope: Option<EpochCandidateScope>,
        trace: &mut EpochStageTrace,
        mut prepared: Option<&mut Option<PreparedEpochNormals>>,
        quantum: Option<&QuantumProjection>,
        allow_channel_dissipation: bool,
        channel_grain: Option<&ObservedChannelGrainPlan>,
    ) -> Result<StagedEpochCandidate, HnnError> {
        if quantum.is_some()
            && (scope != Some(EpochCandidateScope::ReceivingOnly) || prepared.is_none())
        {
            return Err(refused(
                "a quantum alternative belongs only to the shared receiving-only stage",
            ));
        }
        let grain = self.observed_epoch_grain(receiver)?;
        let mut expected_partition = None;
        if heard_cells == 0
            || heard_cells > epoch_cells
            || receiving_period <= 1
            || receiving_period % 2 == 0
            || {
                let expected = partition_exponent(grain, epoch_cells, epoch_index)?;
                expected_partition = Some(expected);
                expected != exponent
            }
        {
            let required = if heard_cells == 0 {
                "heard_cells > 0"
            } else if heard_cells > epoch_cells {
                "heard_cells <= declared epoch cells"
            } else if receiving_period <= 1 {
                "receiving period > 1"
            } else if receiving_period % 2 == 0 {
                "receiving period is odd"
            } else {
                "provided partition exponent equals the actual receiver-derived exponent"
            };
            let mut failure = EpochStageRefusal::at(
                "admission",
                EpochStageCondition::EpochAdmission,
                required,
                None,
                None,
            )
            .read("heard_cells", EpochStageValue::Integer(heard_cells.into()))
            .read(
                "declared_cells",
                EpochStageValue::Integer(epoch_cells.into()),
            )
            .read(
                "receiving_period",
                EpochStageValue::Integer(receiving_period.into()),
            )
            .read("epoch_index", EpochStageValue::Integer(epoch_index.into()))
            .read("receiver_grain", EpochStageValue::Exponent(grain))
            .read(
                "provided_partition_exponent",
                EpochStageValue::Exponent(exponent),
            );
            if let Some(expected) = expected_partition {
                failure = failure.read(
                    "expected_partition_exponent",
                    EpochStageValue::Exponent(expected),
                );
            }
            failure.first(&mut trace.evidence);
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
        trace.at("grouped_inputs", None, None);
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
        if scope == Some(EpochCandidateScope::ReceivingOnly) {
            // A refused whole branch never carries physical factors into the
            // receiving-only candidate. When shared normals were prepared,
            // their current-batch statistics may be replayed with zero steps.
            factors.clear();
            if prepared.is_none() {
                // A fresh receiving-only branch also has no upstream H/R state.
                kinds.retain(|kind| *kind == LinearLocus::Receiving(receiver));
            }
        }
        if scope == Some(EpochCandidateScope::Joint) && prepared.is_none() {
            return Err(refused(
                "a joint normal proposal needs its bound same-opening staging transaction",
            ));
        }
        observe(EpochDepositPhase::GroupedInputs);
        let cached = prepared.as_deref().and_then(|slot| slot.as_ref());
        let mut laws = cached.map(|p| p.laws.clone()).unwrap_or_default();
        let mut flows = cached.map(|p| p.flows.clone()).unwrap_or_default();
        let mut faces = cached.map(|p| p.faces.clone()).unwrap_or_default();
        let mut receiving_series = cached.and_then(|p| p.receiving_series.clone());
        let mut raw_covector_scales = cached
            .map(|p| p.raw_covector_scales.clone())
            .unwrap_or_default();
        let mut raw_alignments = cached.map(|p| p.raw_alignments.clone()).unwrap_or_default();
        let mut alignment_defects = cached
            .map(|p| p.alignment_defects.clone())
            .unwrap_or_default();
        for kind in &kinds {
            if cached.is_some() {
                continue;
            }
            trace.at("normal_flow", Some(kind.locus()), Some(Family::Map));
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
                EpochStageRefusal::at("normal_flow", EpochStageCondition::FlowContract,
                    "executed flow shapes, producer/heard/declared counts, partition and support equal their producing operands", Some(kind.locus()), Some(Family::Map))
                    .read("expected_rows", EpochStageValue::Index(law.map.rows))
                    .read("expected_columns", EpochStageValue::Index(law.map.columns))
                    .read("actual_gram_rows", EpochStageValue::Index(reading.gram.rows))
                    .read("actual_gram_columns", EpochStageValue::Index(reading.gram.columns))
                    .read("actual_covector_rows", EpochStageValue::Index(reading.covector.rows))
                    .read("actual_covector_columns", EpochStageValue::Index(reading.covector.columns))
                    .read("expected_records", EpochStageValue::Integer(records_count.into()))
                    .read("actual_records", EpochStageValue::Integer(reading.records.into()))
                    .read("expected_heard_cells", EpochStageValue::Integer(heard_cells.into()))
                    .read("actual_heard_cells", EpochStageValue::Integer(reading.heard_cells.into()))
                    .read("expected_declared_cells", EpochStageValue::Integer(epoch_cells.into()))
                    .read("actual_declared_cells", EpochStageValue::Integer(reading.declared_cells.into()))
                    .read("expected_partition_exponent", EpochStageValue::Exponent(partition_exponent))
                    .read("actual_partition_exponent", EpochStageValue::Exponent(reading.partition_exponent))
                    .read("expected_support", EpochStageValue::Indices(support.clone()))
                    .read("actual_support", EpochStageValue::Indices(reading.support.clone())).first(&mut trace.evidence);
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
                let split_residual = positive
                    .subtract(&foil)?
                    .add(&phase)?
                    .subtract(&flow.covector)?;
                if !split_residual.is_zero() {
                    EpochStageRefusal::at(
                        "receiving_split",
                        EpochStageCondition::ReceivingSplit,
                        "positive - foil + phase equals the actual fresh covector",
                        Some(kind.locus()),
                        Some(Family::Map),
                    )
                    .read(
                        "split_residual",
                        EpochStageValue::Array(EpochArrayReading::of(&split_residual)),
                    )
                    .first(&mut trace.evidence);
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
                    let fresh_alignment = fresh.alignment.scalar_ratio()?;
                    if certificate.alignment != fresh_alignment {
                        EpochStageRefusal::at(
                            "receiving_fresh_alignment",
                            EpochStageCondition::FreshAlignment,
                            "Fisher alignment equals the same fresh covector/direction pairing",
                            Some(kind.locus()),
                            Some(Family::Map),
                        )
                        .read(
                            "fisher_alignment",
                            EpochStageValue::Ratio(certificate.alignment.clone()),
                        )
                        .read("fresh_alignment", EpochStageValue::Ratio(fresh_alignment))
                        .first(&mut trace.evidence);
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
        // Published self stays the actual-ray opening. Every rebase is local to the candidate,
        // before preparation advances a fresh statistic or stages its quotient. Refusal here
        // precedes fresh certification and cannot invent gains for a receiving-only retry.
        trace.at("channel_grain_rebase", None, None);
        let mut eligible_channel_grain = BTreeSet::new();
        let mut rebases = match channel_grain {
            Some(plan) => {
                if !allow_channel_dissipation || scope == Some(EpochCandidateScope::ReceivingOnly)
                    || plan.receiver != receiver || plan.ingress_before != epoch_index {
                    return Err(refused("a staged channel target keeps its D scope and actual receiver clock"));
                }
                let targets = plan.targets.iter().filter_map(|(&contact, &target)| {
                    let active = factors.values().any(|step| match &step.gradient {
                        FactorGradient::Dissipation { contact: at, gradient } => *at == contact &&
                            (!step.energy.is_zero() || gradient.entries().iter().any(|v| !v.is_zero())),
                        _ => false,
                    });
                    if active { eligible_channel_grain.insert(contact); Some((contact, target)) } else { None }
                }).collect();
                channel_grain::stage_rebases(self, &mut next, &targets, retained)?
            }
            None => BTreeMap::new(),
        };
        let rebased_material = channel_grain.map(|_| next.clone());
        let candidate_lattices = next.lattices.clone();
        let mut factor_steps: Vec<_> = factors.into_values().collect();
        for step in &mut factor_steps {
            trace.at(
                "pair_directions",
                Some(step.gradient.locus()),
                Some(step.gradient.family()),
            );
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
        trace.at("pair_directions", None, None);
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
            trace.at("region_preparation", Some(*locus), None);
            let prepared = self
                .prepare_at_on_lattice(*locus, steps, material.as_mut(), carries,
                    if matches!(locus, Locus::Channel(_)) && channel_grain.is_some() {
                        candidate_lattices.get(locus).copied()
                    } else { None })
                .map_err(|(index, error)| {
                    trace.family =
                        steps
                            .iter()
                            .find(|(at, _)| *at == index)
                            .map(|(_, step)| match step {
                                LocusStep::Factor(factor) => factor.gradient.family(),
                                _ => Family::Map,
                            });
                    error
                })?;
            ready.push(prepared);
        }
        observe(EpochDepositPhase::RegionPreparation);
        let factor_faces: Vec<_> = regions
            .iter()
            .zip(&ready)
            .flat_map(|((l, ..), p)| p.factors.iter().map(move |p| (*l, p)))
            .collect();
        let original_channel_faces: BTreeMap<_, _> = factor_faces
            .iter()
            .filter(|(locus, face)| {
                matches!(locus, Locus::Channel(_)) && face.family == Family::Factor(2)
            })
            .map(|(locus, face)| ((*locus, face.family), (**face).clone()))
            .collect();
        let linear_faces: Vec<_> = faces
            .iter()
            .map(|(kind, face)| (kind.locus(), *kind, face.direction()))
            .collect();
        let readout = &laws[&LinearLocus::Receiving(receiver)].spectral;
        let bound = readout.upper();
        trace.at("fresh_joint_certificate", None, None);
        let (mut certified, fresh_joint, _fresh_pumped, _fresh_loaded) =
            if let Some(cached) = cached {
                (
                    cached.certified.clone(),
                    cached.fresh_joint.clone(),
                    None,
                    None,
                )
            } else {
                self.certify_steps_with_epoch_evidence(
                    Some(&envelope),
                    &linear_faces,
                    &factor_faces,
                    None,
                    StepSource::Certified,
                    Some(&bound),
                    Some(&reaches),
                    &mut trace.evidence,
                )?
                .map_err(|_| refused("the native epoch joint certificate refused its candidate"))?
            };
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
        trace.at("lobe", None, None);
        let (lobe, lock) = self
            .lobe(Some(&envelope), retained, &stepping, &mut certified)
            .map_err(|error| {
                let mut evidence = EpochStageRefusal::at(
                    "lobe",
                    EpochStageCondition::Lobe,
                    "native lock-chart lobe admission (failed family unknown if not exported)",
                    None,
                    None,
                );
                evidence.participating_families = stepping
                    .iter()
                    .map(|(ring, ..)| (Locus::Standing(*ring), Family::Standing))
                    .collect();
                evidence.first(&mut trace.evidence);
                error
            })?;
        drop(stepping);
        if let Some(slot) = prepared.as_deref_mut() {
            if slot.is_none() {
                *slot = Some(PreparedEpochNormals {
                    laws: laws.clone(),
                    flows: flows.clone(),
                    faces: faces.clone(),
                    receiving_series: receiving_series.clone(),
                    raw_covector_scales: raw_covector_scales.clone(),
                    raw_alignments: raw_alignments.clone(),
                    alignment_defects: alignment_defects.clone(),
                    certified: certified.clone(),
                    fresh_joint: fresh_joint.clone(),
                });
            }
        }
        let mut strokes = BTreeMap::new();
        for ((locus, steps, material, carries), prepared) in regions.iter_mut().zip(ready) {
            trace.at("factor_carrier_deposition", Some(*locus), None);
            let (stroke, _) = self
                .deposit_at(
                    *locus,
                    steps,
                    material.as_mut(),
                    carries,
                    prepared,
                    &certified,
                )
                .map_err(|(index, error)| {
                    trace.family =
                        steps
                            .iter()
                            .find(|(at, _)| *at == index)
                            .map(|(_, step)| match step {
                                LocusStep::Factor(factor) => factor.gradient.family(),
                                _ => Family::Map,
                            });
                    error
                })?;
            strokes.insert(*locus, stroke);
        }
        for (locus, _, _, carries) in regions {
            rest.extend(carries);
            let _ = locus;
        }
        next.carries = rest;
        // A rebase alone never ticks the channel clock. If its one fresh D stroke was held
        // wholly at zero, restore that channel exactly and let its lattice wait. No statistic
        // update is lost: moved() is false only when every fresh carrier update was zero.
        let waiting: Vec<_> = channel_grain.into_iter().flat_map(|plan| plan.targets.keys().copied()).filter(|contact| {
            !strokes.get(&Locus::Channel(*contact)).is_some_and(BudgetedCarry::moved)
        }).collect();
        for contact in waiting {
            let locus = Locus::Channel(contact);
            next.contacts[contact] = self.contacts[contact].clone();
            next.lattices.insert(locus, self.lattice(locus)?);
            next.carries.retain(|(at, _), _| *at != locus);
            next.carries.extend(self.carries.iter().filter(|((at, _), _)| *at == locus).map(|(key, value)| (*key, value.clone())));
            rebases.remove(&contact);
            eligible_channel_grain.remove(&contact);
        }
        let channel_grain_reading = if let (Some(plan), Some(mut rebase_reading_material)) = (channel_grain, rebased_material) {
            for &contact in plan.targets.keys() {
                if !eligible_channel_grain.contains(&contact) {
                    rebase_reading_material.contacts[contact] = self.contacts[contact].clone();
                    rebase_reading_material.lattices.insert(Locus::Channel(contact), self.lattice(Locus::Channel(contact))?);
                }
            }
            Some(plan.reading(self, &rebase_reading_material, &rebases, &eligible_channel_grain)?)
        } else { None };
        // A budgeted factor's rounded/backtracked displacement is generally
        // not its prepared ray. Until that exact ray is supplied to the shared
        // certificate, refuse a mixed physical factor move rather than attach
        // a fresh-direction certificate to different material. Sufficient
        // factor statistics/carries may change while their material stays put.
        trace.at("actual_factor_displacement", None, None);
        let actual_channel_faces = admit_actual_factor_displacements_with_rebases(
            self,
            &next,
            &strokes,
            &factor_steps,
            &certified,
            &original_channel_faces,
            allow_channel_dissipation,
            &rebases,
            &mut trace.evidence,
        )?;
        let mut candidates = BTreeMap::new();
        let mut actual_faces = Vec::new();
        let mut actual_exponents = DeclaredExponents {
            steps: BTreeMap::new(),
        };
        for kind in &kinds {
            trace.at("normal_candidate", Some(kind.locus()), Some(Family::Map));
            let fresh = certified.get(&(kind.locus(), Family::Map));
            let gamma = fresh.map(|r| r.step.step.clone()).unwrap_or_else(Rat::zero);
            let gain = EpochArray::from_dyadic_scalar(&gamma)?;
            let held = prepared.is_some()
                && scope == Some(EpochCandidateScope::ReceivingOnly)
                && !matches!(kind, LinearLocus::Receiving(_));
            let joint = prepared.is_some()
                && scope == Some(EpochCandidateScope::Joint)
                && !matches!(kind, LinearLocus::Receiving(_));
            if joint {
                trace.at(
                    "joint_normal_candidate",
                    Some(kind.locus()),
                    Some(Family::Map),
                );
            }
            let deposit = match *kind {
                LinearLocus::Receiving(_) if quantum.is_some() => laws[kind].deposit_quantum(
                    &flows[kind],
                    &gain,
                    quantum.expect("matched quantum alternative"),
                )?,
                LinearLocus::SourcePort(ring) if joint => laws[kind].deposit_joint(
                    &flows[kind],
                    &gain,
                    *kind,
                    Some((
                        self.lattice(kind.locus())?.exponent(),
                        self.budget,
                        self.commit,
                        ring,
                    )),
                    &mut trace.evidence,
                )?,
                _ if joint => laws[kind].deposit_joint(
                    &flows[kind],
                    &gain,
                    *kind,
                    None,
                    &mut trace.evidence,
                )?,
                LinearLocus::SourcePort(ring) if held => laws[kind].deposit_source_at_eta(
                    &flows[kind],
                    &gain,
                    self.lattice(kind.locus())?.exponent(),
                    self.budget,
                    self.commit,
                    ring,
                    BigInt::zero(),
                )?,
                LinearLocus::SourcePort(ring) => laws[kind].deposit_source(
                    &flows[kind],
                    &gain,
                    self.lattice(kind.locus())?.exponent(),
                    self.budget,
                    self.commit,
                    ring,
                )?,
                _ if held => {
                    laws[kind].deposited_at(&flows[kind], &gain, BigInt::zero(), BigInt::one())?
                }
                _ => laws[kind].deposit(&flows[kind], &gain)?,
            };
            if matches!(kind, LinearLocus::SourcePort(_)) && deposit.successor.source_refinement {
                let finer = deposit.successor.map_lattice;
                if finer > self.lattice(kind.locus())?.exponent() {
                    admit_refined_source_carries(
                        kind.locus(),
                        finer,
                        &next.carries,
                        &mut trace.evidence,
                    )?;
                }
            }
            candidates.insert(*kind, deposit);
        }
        // Read EVERY represented normal delta before any actual certificate
        // or publication. A refusal discards all candidates and the staged
        // factor/statistic/carry clone, including any proposed refinement.
        if scope.is_none() {
            admit_actual_normal_domain(receiver, &candidates)?;
        }
        let upstream = rebases.values().any(|r| r.after_lattice != r.before_lattice) || !actual_channel_faces.is_empty() || candidates.iter().any(|(kind, candidate)| {
            !matches!(kind, LinearLocus::Receiving(_)) && !candidate.step.is_zero()
        });
        let physical_motion = !actual_channel_faces.is_empty() || candidates
            .values()
            .any(|candidate| !candidate.step.is_zero());
        for (kind, deposit) in &candidates {
            trace.at("actual_ray", Some(kind.locus()), Some(Family::Map));
            if !deposit.step.is_zero() {
                let fresh = certified.get(&(kind.locus(), Family::Map)).ok_or_else(|| {
                    EpochStageRefusal::at(
                        "actual_ray",
                        EpochStageCondition::DeclaredFamily,
                        "a moving represented normal ray must have its certified fresh family",
                        Some(kind.locus()),
                        Some(Family::Map),
                    )
                    .read(
                        "represented_step",
                        EpochStageValue::Array(EpochArrayReading::of(&deposit.step)),
                    )
                    .first(&mut trace.evidence);
                    refused("retained epoch news cannot invent an uncertified fresh family")
                })?;
                let face = actual_epoch_face(
                    *kind,
                    &deposit.step,
                    samples.get(kind).map(Vec::as_slice).unwrap_or(&[]),
                    receiving_parts,
                    exponent,
                    &fresh.step.step * &fresh.step.covector,
                    &mut trace.evidence,
                )
                .map_err(|error| {
                    enrich_failed_normal_ray(
                        &mut trace.evidence,
                        *kind,
                        &laws[kind],
                        &flows[kind],
                        deposit,
                        &fresh.step.step,
                        self.lattice(kind.locus())
                            .ok()
                            .map(|lattice| lattice.exponent()),
                        samples.get(kind).map(Vec::as_slice).unwrap_or(&[]),
                    );
                    error
                })?;
                actual_faces.push((*kind, face));
                actual_exponents.steps.insert(
                    (kind.locus(), Family::Map),
                    DeclaredExponent {
                        exponent: 0,
                        reach: None,
                    },
                );
            }
        }
        let actual_linear: Vec<_> = actual_faces
            .iter()
            .map(|(kind, face)| (kind.locus(), *kind, face.direction()))
            .collect();
        trace.at("actual_joint_certificate", None, None);
        let actual_factor_faces: Vec<_> = actual_channel_faces
            .iter()
            .map(|face| (Locus::Channel(face.contact()), face.prepared()))
            .collect();
        for face in &actual_channel_faces {
            actual_exponents.steps.insert(
                (Locus::Channel(face.contact()), Family::Factor(2)),
                DeclaredExponent { exponent: face.exponent(), reach: None },
            );
        }
        let (actual_certified, joint, pumped, loaded) = self
            .certify_steps_with_epoch_evidence(
                Some(&envelope),
                &actual_linear,
                &actual_factor_faces,
                None,
                StepSource::Actual(&actual_exponents),
                Some(&bound),
                Some(&reaches),
                &mut trace.evidence,
            )
            .map_err(|error| {
                if scope == Some(EpochCandidateScope::Joint) {
                    if let Some(evidence) = &mut trace.evidence {
                        for candidate in candidates.values() {
                            if let Some(joint) = &candidate.joint_direction {
                                evidence.readings.push(EpochStageReading {
                                    name: "joint_direction",
                                    value: EpochStageValue::JointDirection(joint.clone()),
                                });
                            }
                        }
                    }
                }
                if let Some(kind) = candidates.keys().copied().find(|kind| {
                    trace.evidence.as_ref().is_some_and(|evidence| {
                        evidence.locus == Some(kind.locus()) && evidence.family == Some(Family::Map)
                    })
                }) {
                    let gamma = certified
                        .get(&(kind.locus(), Family::Map))
                        .map(|reading| reading.step.step.clone())
                        .unwrap_or_else(Rat::zero);
                    enrich_failed_normal_ray(
                        &mut trace.evidence,
                        kind,
                        &laws[&kind],
                        &flows[&kind],
                        &candidates[&kind],
                        &gamma,
                        self.lattice(kind.locus())
                            .ok()
                            .map(|lattice| lattice.exponent()),
                        samples.get(&kind).map(Vec::as_slice).unwrap_or(&[]),
                    );
                }
                error
            })?
            .map_err(|_| refused("the fixed actual epoch rays were not all admitted"))?;
        // Every candidate remains local to next until ALL exact actual-ray,
        // tube, storage and budget checks pass. No live resident is mutated.
        let mut normal_moves = 0u64;
        let mut vanished = Vec::new();
        let mut locus_readings = Vec::new();
        for kind in &kinds {
            trace.at("normal_publication", Some(kind.locus()), Some(Family::Map));
            let gamma = certified
                .get(&(kind.locus(), Family::Map))
                .map(|r| r.step.step.clone())
                .unwrap_or_else(Rat::zero);
            let deposit = candidates
                .remove(kind)
                .expect("one staged candidate per normal locus");
            if matches!(kind, LinearLocus::SourcePort(_)) && deposit.successor.source_refinement {
                next.lattices
                    .insert(kind.locus(), Lattice::new(deposit.successor.map_lattice));
            }
            normal_moves = normal_moves
                .checked_add(deposit.step.values.iter().filter(|v| !v.is_zero()).count() as u64)
                .ok_or_else(extent)?;
            if gamma.is_positive() && deposit.eta_numerator.is_positive() && deposit.step.is_zero()
            {
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
            let metric_norms = normal_news_metric_squared(&laws[kind], &flows[kind], &gamma).ok();
            let eta = Rat::new(
                deposit.eta_numerator.clone(),
                deposit.eta_denominator.clone(),
            );
            let fall = deposit.fall.scalar_ratio()?;
            let direction = EpochArrayReading::of(&deposit.direction);
            let represented_step = EpochArrayReading::of(&deposit.step);
            let shares = deposit.shares.clone();
            let scale = epoch_locus_scale_reading(&deposit);
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
                actual_alignment: actual_certified
                    .get(&(kind.locus(), Family::Map))
                    .map(|r| r.step.alignment.clone())
                    .unwrap_or_else(Rat::zero),
                actual_moves: actual_certified
                    .get(&(kind.locus(), Family::Map))
                    .map(|r| r.moves.clone())
                    .unwrap_or_else(Rat::zero),
                eta,
                fall,
                shares,
                gram_update: EpochArrayReading::of(&flows[kind].gram),
                fresh_news: EpochArrayReading::of(&flows[kind].covector),
                direction,
                direction_divisor: deposit.direction_divisor.clone(),
                joint_direction: deposit.joint_direction.clone(),
                retained_news_metric_squared: metric_norms.as_ref().map(|norms| norms.0.clone()),
                fresh_news_metric_squared: metric_norms.map(|norms| norms.1),
                represented_step,
                scale,
                storage: normal
                    .epoch_storage()
                    .expect("published grouped epoch storage"),
            });
        }
        trace.at("candidate_finalization", None, None);
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
                channel_grain: channel_grain_reading,
                channel_grain_deferred: None,
                quantum_projection: None,
                actual_receiving_ingress: epoch_index,
                heard_cells,
                declared_cells: epoch_cells,
                receiver_partition_bits: grain,
                partition_exponent: exponent,
                loci: locus_readings,
                fresh_joint,
                fresh_steps: certified.into_iter().map(|((l, _), r)| (l, r)).collect(),
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
            steps: actual_certified
                .into_iter()
                .map(|((l, _), r)| (l, r))
                .collect(),
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
        observe(if scope.is_some() {
            EpochDepositPhase::CandidateStaged
        } else {
            EpochDepositPhase::Publication
        });
        Ok(StagedEpochCandidate {
            material: next,
            reading,
            upstream,
            physical_motion,
        })
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

    #[test]
    fn epoch_scale_reading_separates_row_projection_from_exact_proposal() {
        let law = EpochLaw::founded(2, 1, 2, 0).unwrap();
        let before = law.encode_checkpoint();
        let sample = Sample {
            weight: Rat::one(),
            feature: vec![Rat::one()],
            covector: vec![rat(1, 4), -Rat::one()],
            masses: None,
        };
        let record = EpochRecord::from_sample(&sample).unwrap();
        let flow = EpochFlow::from_records(2, 1, 2, 1, 0, 1, &[record]).unwrap();
        let gain = EpochArray::from_dyadic_scalar(&Rat::one()).unwrap();
        let candidate = law.deposit(&flow, &gain).unwrap();
        let reading = epoch_locus_scale_reading(&candidate);
        // H+=2, D=(1/8,-1/2); on the actual 1/4 lattice only the second row moves.
        assert_eq!(reading.gram_column_absolute_sums, vec![rat(2, 1)]);
        assert_eq!(
            reading.proposed_maximum_absolute_by_row,
            vec![rat(1, 8), rat(1, 2)]
        );
        assert_eq!(reading.proposed_nonzero_by_row, vec![1, 1]);
        assert_eq!(reading.represented_nonzero_by_row, vec![0, 1]);
        assert_eq!(reading.nonzero_proposal_zero_in_step_by_row, vec![1, 0]);
        assert!(reading.positive_eta);
        assert_eq!(law.encode_checkpoint(), before);
        assert_eq!(
            candidate.step.to_matrix().unwrap().to_rows(),
            vec![vec![Rat::zero()], vec![rat(-1, 2)]]
        );
    }

    #[test]
    fn epoch_scale_reading_distinguishes_held_eta_from_lattice_truncation() {
        let law = EpochLaw::founded(1, 1, 2, 0).unwrap();
        let sample = Sample {
            weight: Rat::one(),
            feature: vec![Rat::one()],
            covector: vec![Rat::one()],
            masses: None,
        };
        let record = EpochRecord::from_sample(&sample).unwrap();
        let flow = EpochFlow::from_records(1, 1, 2, 1, 0, 1, &[record]).unwrap();
        let gain = EpochArray::from_dyadic_scalar(&Rat::one()).unwrap();
        let held = law
            .deposited_at(&flow, &gain, BigInt::zero(), BigInt::one())
            .unwrap();
        let moving = law.deposit(&flow, &gain).unwrap();
        let a = epoch_locus_scale_reading(&held);
        let b = epoch_locus_scale_reading(&moving);
        assert_eq!(a.proposed_maximum_absolute_by_row, vec![rat(1, 2)]);
        assert_eq!(
            a.proposed_maximum_absolute_by_row,
            b.proposed_maximum_absolute_by_row
        );
        assert!(!a.positive_eta);
        assert!(b.positive_eta);
        assert_eq!(a.nonzero_proposal_zero_in_step_by_row, vec![1]);
        assert_eq!(b.nonzero_proposal_zero_in_step_by_row, vec![0]);
        assert!(held.step.is_zero());
        assert!(!moving.step.is_zero());
        assert_eq!(held.successor.gram, moving.successor.gram);
    }

    /// A real receiving ratio at one fixed anchor. The optional upstream
    /// records probe the close's refusal domain; they assert no upstream
    /// executed-transport or second-variation witness.
    fn normal_domain_fixture(
        upstream: Option<LinearLocus>,
        receiving: bool,
    ) -> (Field, Constitution, Deposit, Vec<EpochReceivingRecord>, u32) {
        let mut declaration = crate::hnn::tests::learning::chain_declaration(1 << 16);
        declaration.receivers[0].aperture = 1;
        declaration.rings[2] = declaration.rings[1].clone();
        declaration.rings[2].lock.clear();
        declaration.lattice.clear();
        let field = Field::declare(declaration.by_lattice_rule()).unwrap();
        let material = Constitution::initial(&field, 1 << 40).unwrap();
        let receiver = field.receivers()[0].ring;
        let map = material.receiving_law(receiver).unwrap().map();
        assert!(map.entries().iter().all(Zero::is_zero));
        let grain = material.observed_epoch_grain(receiver).unwrap();
        let exponent = partition_exponent(grain, 1, 0).unwrap();
        let mut linear = Vec::new();
        let mut parts = Vec::new();
        if receiving {
            let mut feature = vec![Rat::zero(); map.columns()];
            feature[0] = Rat::one();
            let read = crate::hnn::receiving::ReceivingRead::of_logits(
                map.apply(&feature).unwrap(),
                field.finest_grain(),
            );
            let faces = crate::hnn::ratio::Faces::of_reads(&[read], field.finest_grain()).unwrap();
            let ratio = crate::hnn::ratio::HolonRatio::compare(
                faces,
                &[0],
                &crate::hnn::ratio::TargetPhases {
                    branch: BigInt::zero(),
                    phases: vec![Rat::zero()],
                },
            )
            .unwrap();
            let (covector, _) = ratio.epoch_covector(exponent).unwrap();
            let descent = covector.descent(0);
            let mut positive = vec![Rat::zero(); map.rows()];
            positive[0] = Rat::one();
            let mut foil = vec![Rat::zero(); map.rows()];
            let mut phase = vec![Rat::zero(); map.rows()];
            for row in 0..map.rows() {
                if row % 2 == 0 {
                    foil[row] = &positive[row] - &descent[row];
                } else {
                    phase[row] = descent[row].clone();
                }
            }
            let sample = Sample {
                weight: Rat::one(),
                feature: feature.clone(),
                covector: descent,
                masses: Some(ratio.faces().faces[0].odometer_masses().unwrap()),
            };
            parts.push(EpochReceivingRecord {
                feature,
                positive,
                foil,
                phase,
            });
            linear.push(LinearStep {
                locus: LinearLocus::Receiving(receiver),
                samples: vec![sample],
            });
        }
        if let Some(kind) = upstream {
            let map = material.epoch_normal(kind).unwrap().map();
            let mut feature = vec![Rat::zero(); map.columns()];
            feature[0] = Rat::one();
            let mut covector = vec![Rat::zero(); map.rows()];
            covector[0] = rat(1, 2);
            linear.push(LinearStep {
                locus: kind,
                samples: vec![Sample {
                    weight: Rat::one(),
                    feature,
                    covector,
                    masses: None,
                }],
            });
        }
        let loci: BTreeSet<_> = crate::hnn::retention::loci(&field).into_iter().collect();
        let reached = linear.iter().map(|step| step.locus.locus()).collect();
        let deposit =
            Deposit::new(material.commit, linear, Vec::new(), reached).with_reach(Reach {
                receiver,
                // More than one tick: contrast cannot masquerade as a once-only
                // affine map merely because each local tick is linear in it.
                stations: vec![2, 4],
                entries: vec![0],
                phases: 1,
                loci,
                passages: Vec::new(),
            });
        (field, material, deposit, parts, exponent)
    }

    fn close_normal_domain_fixture(
        field: &Field,
        material: &Constitution,
        deposit: &Deposit,
        parts: &[EpochReceivingRecord],
        exponent: u32,
    ) -> Result<(Constitution, DepositReading), HnnError> {
        let receiver = field.receivers()[0].ring;
        material.deposit_observed_epoch(
            std::slice::from_ref(deposit),
            receiver,
            field.ring(receiver).period(),
            1,
            1,
            0,
            exponent,
            &crate::hnn::retention::loci(field).into_iter().collect(),
            material.landmarks(receiver).unwrap().clone(),
            &|_, _, _, _| panic!("this fixture has no pair-factor records"),
            parts,
            &mut |_| {},
        )
    }

    /// The retained news is a synthetic exact native fixture, not a historical receipt.
    /// Fresh G/gamma and every physical witness are produced again from the real stage.
    fn quantum_replay_fixture(opposed: bool) {
        let (field, mut material, deposit, parts, exponent) = normal_domain_fixture(None, true);
        let receiver = field.receivers()[0].ring;
        let kind = LinearLocus::Receiving(receiver);
        let deposits = [deposit];
        // Synthetic pre-existing positive curvature makes this fixture's dyadic
        // majorizer gap strict; the original feature happened to land on a power
        // of two. Seed it before producing fresh G/gamma and never alter guards.
        let mut seed = EpochLaw::from_normal(material.epoch_normal(kind).unwrap(), material.observed_epoch_grain(receiver).unwrap()).unwrap();
        let phase_rows: Vec<_> = (1..seed.map.rows).step_by(2).collect();
        seed = seed.with_phase_rows(&phase_rows, field.ring(receiver).period()).unwrap();
        let mut extra = vec![BigInt::zero(); seed.gram.values.len()];
        extra[0] = BigInt::one();
        seed.gram = seed.gram.add(&EpochArray::new(seed.gram.rows, seed.gram.columns, 1, extra).unwrap()).unwrap();
        material.epoch_normal_mut(kind).unwrap().publish_epoch(seed).unwrap();
        let retained = crate::hnn::retention::loci(&field).into_iter().collect();
        let pair_speed = |_, _, _: &PairPort, _: [&[Vec<Rat>]; 3]| panic!("no factor proposal");
        let (mut law, flow, gamma) = {
            let mut probe = ObservedNormalEpochStage::new(
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
                &crate::hnn::reference::observed::HostObservedEpochExecution,
                false,
            )
            .unwrap();
            let _ = probe.stage(EpochCandidateScope::Whole, &mut |_| {});
            let prepared = probe
                .prepared
                .as_ref()
                .expect("fixture fresh normal certificate");
            (
                prepared.laws[&kind].clone(),
                prepared.flows[&kind].clone(),
                prepared.certified[&(kind.locus(), Family::Map)]
                    .step
                    .step
                    .clone(),
            )
        };
        assert!(gamma.is_positive());
        assert!(law.symmetry.is_none());
        let gain = EpochArray::from_dyadic_scalar(&gamma).unwrap();
        let gram = law.gram.add(&flow.gram).unwrap();
        let (_, shares) = law.direction(&flow.covector, &gram, &flow.support).unwrap();
        let column = flow.support[0];
        let share = shares[column];
        let s = if share >= 0 {
            Rat::from_integer(BigInt::one() << share as usize)
        } else {
            Rat::new(BigInt::one(), BigInt::one() << (-share) as usize)
        };
        let h = Rat::new(BigInt::one(), BigInt::one() << law.map_lattice as usize);
        let diagonal = gram.to_matrix().unwrap().entries()[column * gram.columns + column].clone();
        assert!(diagonal < s, "fixture has a strict majorizer gap");
        let magnitude = &h * (diagonal + s) / Rat::from_integer(2.into());
        let target =
            EpochArray::from_dyadic_scalar(&if opposed { -magnitude } else { magnitude }).unwrap();
        let mut values = vec![BigInt::zero(); law.map.values.len()];
        values[column] = target.values[0].clone(); // magnitude row 0; phase rows remain exactly zero.
        let target =
            EpochArray::new(law.map.rows, law.map.columns, target.exponent, values).unwrap();
        law.news = target
            .subtract(&flow.covector.scalar_product(&gain).unwrap())
            .unwrap();
        assert!(law.deposit(&flow, &gain).unwrap().step.is_zero());
        material
            .epoch_normal_mut(kind)
            .unwrap()
            .publish_epoch(law.clone())
            .unwrap();
        let before = material.continuing_state(0).unwrap().to_text();
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
            &crate::hnn::reference::observed::HostObservedEpochExecution,
            false,
        )
        .unwrap();
        let _ = stage.stage(EpochCandidateScope::Whole, &mut |_| {});
        let actual_gamma = &stage.prepared.as_ref().unwrap().certified
            [&(kind.locus(), Family::Map)]
            .step
            .step;
        assert_eq!(
            *actual_gamma, gamma,
            "retained news cannot change the fresh certificate"
        );
        let candidate = stage
            .stage(EpochCandidateScope::ReceivingOnly, &mut |_| {})
            .unwrap();
        let (next, reading) = candidate.admit_receiving().unwrap();
        let receipt = reading.epoch.unwrap().quantum_projection.unwrap();
        assert!(receipt.eligible);
        assert_eq!(receipt.trials.len(), 1);
        let trial = &receipt.trials[0];
        assert!(trial.normal_admitted);
        if opposed {
            assert!(!trial.actual_admitted);
            assert_eq!(
                trial.refusal.as_ref().unwrap().condition,
                EpochStageCondition::ActualRayAlignment
            );
            assert_eq!(
                next.epoch_normal(kind).unwrap().map(),
                material.epoch_normal(kind).unwrap().map()
            );
        } else {
            assert!(
                trial.actual_admitted,
                "aligned fixture must pass the complete existing physical stage: {:?}",
                trial.refusal
            );
            assert!(trial.refusal.is_none());
            assert_ne!(
                next.epoch_normal(kind).unwrap().map(),
                material.epoch_normal(kind).unwrap().map()
            );
        }
        let successor = next.epoch_normal(kind).unwrap().epoch_law().unwrap();
        let step = successor.map.subtract(&law.map).unwrap();
        assert_eq!(successor.gram, gram);
        assert_eq!(
            successor.news,
            law.news
                .add(&flow.covector.scalar_product(&gain).unwrap())
                .unwrap()
                .subtract(&step.multiply(&gram).unwrap())
                .unwrap()
        );
        assert_eq!(successor.crossings, law.crossings + 1);
        assert_eq!(material.continuing_state(0).unwrap().to_text(), before);
    }

    #[test]
    fn quantum_optional_replay_uses_actual_stage_and_absorbs_news_once() {
        quantum_replay_fixture(false);
    }

    #[test]
    fn quantum_retained_normal_fall_cannot_override_opposed_fresh_actual_ray() {
        quantum_replay_fixture(true);
    }

    #[test]
    fn a_nonzero_upstream_joint_candidate_cannot_publish_without_its_finite_comparison() {
        let (field, material, deposit, parts, exponent) =
            normal_domain_fixture(Some(LinearLocus::SourcePort(0)), false);
        let receiver = field.receivers()[0].ring;
        let deposits = [deposit];
        let retained = crate::hnn::retention::loci(&field).into_iter().collect();
        let pair_speed =
            |_, _, _: &PairPort, _: [&[Vec<Rat>]; 3]| panic!("NormalMaps holds physical factors");
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
            &crate::hnn::reference::observed::HostObservedEpochExecution,
            false,
        )
        .unwrap();
        let before = material.continuing_state(0).unwrap().to_text();
        let _whole = stage.stage(EpochCandidateScope::Whole, &mut |_| {});
        let joint = stage
            .stage(EpochCandidateScope::Joint, &mut |_| {})
            .unwrap();
        assert!(joint.requires_comparison());
        assert!(joint.has_physical_motion());
        let readings = joint.joint_directions();
        assert!(readings.iter().any(|reading| !reading.zero_direction));
        assert!(matches!(
            joint.admit_receiving(),
            Err(HnnError::Unadmitted {
                reason: "an upstream epoch candidate needs its finite comparison"
            })
        ));
        assert_eq!(material.continuing_state(0).unwrap().to_text(), before);
    }

    #[test]
    fn shared_receiving_restage_absorbs_all_normal_news_once_while_holding_upstream_maps() {
        let (field, material, deposit, parts, exponent) =
            normal_domain_fixture(Some(LinearLocus::SourcePort(0)), true);
        let receiver = field.receivers()[0].ring;
        let deposits = [deposit];
        let retained = crate::hnn::retention::loci(&field).into_iter().collect();
        let pair_speed = |_, _, _: &PairPort, _: [&[Vec<Rat>]; 3]| {
            panic!("no physical factor proposal in NormalMaps")
        };
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
            &crate::hnn::reference::observed::HostObservedEpochExecution,
            false,
        )
        .unwrap();
        let before = material.continuing_state(0).unwrap().to_text();
        let premature = stage
            .stage(EpochCandidateScope::ReceivingOnly, &mut |_| {})
            .unwrap_err();
        assert!(!premature.normal_inputs_prepared);
        assert!(stage.prepared.is_none());
        let legacy = material.stage_observed_epoch_with_execution(
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
            &mut |_| {},
            &crate::hnn::reference::observed::HostObservedEpochExecution,
            EpochCandidateScope::Whole,
        );
        let shared = stage.stage(EpochCandidateScope::Whole, &mut |_| {});
        match (legacy, shared) {
            (Ok(legacy), Ok(shared)) => {
                assert_eq!(
                    legacy.material, shared.material,
                    "canonical whole material is unchanged"
                );
                assert_eq!(legacy.upstream, shared.upstream);
                assert_eq!(legacy.physical_motion, shared.physical_motion);
            }
            (Err(legacy), Err(shared)) => assert_eq!(
                legacy.to_string(),
                shared.error.to_string(),
                "canonical whole keeps its original refusal"
            ),
            _ => panic!("shared preparation must not change whole admission"),
        }
        let prepared = stage
            .prepared
            .as_ref()
            .expect("actual whole fresh certificate was formed")
            .clone();
        let _discarded_joint = stage.stage(EpochCandidateScope::Joint, &mut |_| {});
        let candidate = stage
            .stage(EpochCandidateScope::ReceivingOnly, &mut |_| {})
            .unwrap();
        assert!(!candidate.requires_comparison());
        let (next, reading) = candidate.admit_receiving().unwrap();
        let repeat = stage
            .stage(EpochCandidateScope::ReceivingOnly, &mut |_| {})
            .unwrap()
            .admit_receiving()
            .unwrap()
            .0;
        assert_eq!(
            repeat, next,
            "every branch starts at the same opening, never a rejected successor"
        );
        for (kind, old) in &prepared.laws {
            let flow = &prepared.flows[kind];
            let paired = old
                .symmetry
                .as_ref()
                .map(|symmetry| flow.paired(symmetry).unwrap());
            let flow = paired.as_ref().unwrap_or(flow);
            let gamma = prepared
                .certified
                .get(&(kind.locus(), Family::Map))
                .map(|r| r.step.step.clone())
                .unwrap_or_else(Rat::zero);
            let new = next.epoch_normal(*kind).unwrap().epoch_law().unwrap();
            let h_plus = old.gram.add(&flow.gram).unwrap();
            let p = new.map.subtract(&old.map).unwrap();
            let expected_r = old
                .news
                .add(
                    &flow
                        .covector
                        .scalar_product(&EpochArray::from_dyadic_scalar(&gamma).unwrap())
                        .unwrap(),
                )
                .unwrap()
                .subtract(&p.multiply(&h_plus).unwrap())
                .unwrap();
            assert_eq!(new.gram, h_plus);
            assert_eq!(new.news, expected_r);
            assert_eq!(new.crossings, old.crossings + 1);
            if *kind != LinearLocus::Receiving(receiver) {
                assert_eq!(new.map, old.map);
            }
        }
        let source = LinearLocus::SourcePort(0);
        let old = &prepared.laws[&source];
        let new = next.epoch_normal(source).unwrap().epoch_law().unwrap();
        assert_ne!(
            new.news, old.news,
            "positive actual fresh source news is absorbed despite the held source map"
        );
        assert_ne!(new.gram, old.gram);
        assert_eq!(next.lattices, material.lattices);
        assert_eq!(next.carries, material.carries);
        assert_eq!(next.commit, material.commit + 1);
        assert_eq!(reading.epoch.unwrap().loci.len(), prepared.laws.len());
        assert_eq!(material.continuing_state(0).unwrap().to_text(), before);
        let parsed =
            ContinuingState::from_text(&next.continuing_state(0).unwrap().to_text(), next.budget)
                .unwrap();
        let cold = material.continued_on(&field, &parsed).unwrap();
        assert_eq!(cold, next);
    }

    #[test]
    fn legacy_direct_receiving_restage_discards_all_upstream_statistics_and_lattice() {
        let (field, material, deposit, parts, exponent) =
            normal_domain_fixture(Some(LinearLocus::SourcePort(0)), true);
        let receiver = field.receivers()[0].ring;
        let original = material.clone();
        let candidate = material
            .stage_observed_epoch_with_execution(
                &[deposit],
                receiver,
                field.ring(receiver).period(),
                1,
                1,
                0,
                exponent,
                &crate::hnn::retention::loci(&field).into_iter().collect(),
                material.landmarks(receiver).unwrap().clone(),
                &|_, _, _, _| panic!("the control has no pair records"),
                &parts,
                &mut |_| {},
                &crate::hnn::reference::observed::HostObservedEpochExecution,
                EpochCandidateScope::ReceivingOnly,
            )
            .unwrap();
        assert!(!candidate.requires_comparison());
        assert!(candidate.has_physical_motion());
        let (next, reading) = candidate.admit_receiving().unwrap();
        assert_eq!(material, original);
        for ring in 0..field.rings().len() {
            assert_eq!(next.rings[ring].source, original.rings[ring].source);
            assert_eq!(next.rings[ring].contrast, original.rings[ring].contrast);
            assert_eq!(next.rings[ring].passive, original.rings[ring].passive);
        }
        assert_eq!(next.carries, original.carries);
        assert_eq!(next.lattices, original.lattices);
        assert!(
            reading
                .epoch
                .unwrap()
                .loci
                .iter()
                .all(|locus| locus.locus == LinearLocus::Receiving(receiver))
        );
    }

    #[test]
    fn actual_normal_domain_receiving_only_publishes_its_fixed_feature_comparison() {
        let (field, material, deposit, parts, exponent) = normal_domain_fixture(None, true);
        let receiver = field.receivers()[0].ring;
        let before = material.continuing_state(0).unwrap().to_text();
        let (next, reading) =
            close_normal_domain_fixture(&field, &material, &deposit, &parts, exponent).unwrap();
        assert_eq!(material.continuing_state(0).unwrap().to_text(), before);
        assert_ne!(
            next.receiving_map(receiver),
            material.receiving_map(receiver)
        );
        let epoch = reading.epoch.unwrap();
        assert!(epoch.loci.iter().all(|at| {
            at.locus == LinearLocus::Receiving(receiver)
                || at.represented_step.numerator_l1_bound.is_zero()
        }));
        let receiving = epoch
            .loci
            .iter()
            .find(|at| at.locus == LinearLocus::Receiving(receiver))
            .unwrap();
        assert!(receiving.actual_alignment.is_positive());
        assert!(receiving.represented_step.numerator_l1_bound.is_positive());
        for ring in 0..field.rings().len() {
            assert_eq!(
                next.rings[ring].source.as_ref().map(NormalLaw::map),
                material.rings[ring].source.as_ref().map(NormalLaw::map)
            );
            assert_eq!(
                next.rings[ring].contrast.map(),
                material.rings[ring].contrast.map()
            );
        }
    }

    fn assert_normal_domain_refusal(upstream: LinearLocus, receiving: bool, reason: &'static str) {
        let (field, material, deposit, parts, exponent) =
            normal_domain_fixture(Some(upstream), receiving);
        let original = material.clone();
        let checkpoint = material.continuing_state(0).unwrap().to_text();
        assert!(matches!(
            close_normal_domain_fixture(&field, &material, &deposit, &parts, exponent),
            Err(HnnError::Unadmitted { reason: actual }) if actual == reason
        ));
        // Includes W/H/R, source lattice, all family carries/statistics,
        // clocks, tree/population and material commit: no partial R publish.
        assert_eq!(material, original);
        assert_eq!(material.continuing_state(0).unwrap().to_text(), checkpoint);
    }

    #[test]
    fn actual_normal_domain_source_only_refuses_without_an_executed_witness() {
        assert_normal_domain_refusal(
            LinearLocus::SourcePort(0),
            false,
            "an actual source epoch move requires its affine executed-transport or second-variation certificate",
        );
    }

    #[test]
    fn actual_normal_domain_recurrent_contrast_refuses_its_missing_second_variation() {
        assert_normal_domain_refusal(
            LinearLocus::Contrast(0),
            false,
            "an actual contrast epoch move requires its executed second-variation certificate",
        );
    }

    #[test]
    fn actual_normal_domain_mixed_source_receiving_refuses_without_partial_publication() {
        assert_normal_domain_refusal(
            LinearLocus::SourcePort(0),
            true,
            "an actual source epoch move requires its affine executed-transport or second-variation certificate",
        );
    }

    #[test]
    fn actual_normal_domain_mixed_contrast_receiving_refuses_without_partial_publication() {
        assert_normal_domain_refusal(
            LinearLocus::Contrast(0),
            true,
            "an actual contrast epoch move requires its executed second-variation certificate",
        );
    }

    #[test]
    fn failed_normal_ray_decomposes_retained_fresh_and_projected_alignment_without_mutation() {
        let kind = LinearLocus::SourcePort(0);
        let mut law = EpochLaw::founded(1, 1, 2, 0).unwrap();
        law.news = EpochArray::new(1, 1, 1, vec![(-3).into()]).unwrap();
        let sample = Sample {
            weight: Rat::one(),
            feature: vec![Rat::one()],
            covector: vec![rat(3, 8)],
            masses: None,
        };
        let record = EpochRecord::from_sample(&sample).unwrap();
        let flow = EpochFlow::from_records(1, 1, 2, 1, 0, 1, &[record]).unwrap();
        let gain = EpochArray::from_dyadic_scalar(&Rat::one()).unwrap();
        let candidate = law.deposit_source(&flow, &gain, 2, u64::MAX, 0, 0).unwrap();
        let opening = law.clone();
        let candidate_before = candidate.clone();
        let mut evidence = None;
        let error = match actual_epoch_face(
            kind,
            &candidate.step,
            std::slice::from_ref(&sample),
            &[],
            2,
            Rat::one(),
            &mut evidence,
        ) {
            Err(error) => error,
            Ok(_) => panic!("the represented negative ray must refuse the positive current"),
        };
        assert!(matches!(
            error,
            HnnError::Unadmitted {
                reason: "a moving actual epoch ray must descend its contemporary comparison"
            }
        ));
        enrich_failed_normal_ray(
            &mut evidence,
            kind,
            &law,
            &flow,
            &candidate,
            &Rat::one(),
            Some(2),
            std::slice::from_ref(&sample),
        );
        let evidence = evidence.unwrap();
        assert_eq!(evidence.condition, EpochStageCondition::ActualRayAlignment);
        assert_eq!(
            (evidence.locus, evidence.family),
            (Some(kind.locus()), Some(Family::Map))
        );
        let scalar = |name| {
            evidence
                .readings
                .iter()
                .find_map(|reading| match &reading.value {
                    EpochStageValue::Ratio(value) if reading.name == name => Some(value.clone()),
                    _ => None,
                })
                .unwrap()
        };
        for (name, expected) in [
            ("paired_G_dot_D", rat(-27, 128)),
            ("paired_G_dot_P", rat(-3, 16)),
            ("Rstar_dot_P", rat(9, 16)),
            ("Rold_dot_P", rat(3, 4)),
            ("retained_alignment_component", rat(-9, 32)),
            ("fresh_alignment_component", rat(9, 128)),
            ("projection_alignment_component", rat(3, 128)),
            ("direction_decomposition_residual", Rat::zero()),
            ("represented_alignment_decomposition_residual", Rat::zero()),
            ("normal_quadratic_fall", rat(5, 16)),
            ("raw_sample_G_dot_P", rat(-3, 16)),
            ("raw_minus_guarded_alignment", Rat::zero()),
        ] {
            assert_eq!(scalar(name), expected, "{name}");
        }
        let residual = candidate.direction.subtract(&candidate.step).unwrap();
        assert_eq!(residual.scalar_ratio().unwrap(), rat(-1, 16));
        assert!(
            evidence
                .readings
                .iter()
                .any(|reading| reading.name == "projection_residual_D_minus_P"
                    && reading.value == EpochStageValue::Series(EpochSeriesReading::of(&residual)))
        );
        assert!(evidence.readings.iter().any(|reading| reading.name
            == "largest_local_admissible_dyadic_k"
            && matches!(reading.value, EpochStageValue::Unavailable(_))));
        for (name, expected) in [
            ("active_lattice_L", EpochStageValue::Exponent(2)),
            ("candidate_map_lattice_L", EpochStageValue::Exponent(2)),
            ("source_lattice_refined", EpochStageValue::Text("no")),
            ("projection_changed_direction", EpochStageValue::Text("yes")),
        ] {
            assert!(
                evidence
                    .readings
                    .iter()
                    .any(|reading| reading.name == name && reading.value == expected),
                "{name}"
            );
        }
        assert!(!evidence.seal_formed && !evidence.finite_probe_executed);
        assert_eq!(law, opening);
        assert_eq!(candidate.successor, candidate_before.successor);
        assert_eq!(candidate.step, candidate_before.step);
        assert_eq!(candidate.direction, candidate_before.direction);
        // Evidence from another first failure is not overwritten or enriched by this family.
        let mut first = Some(EpochStageRefusal::at(
            "earlier",
            EpochStageCondition::NativeOwner,
            "earlier guard",
            Some(Locus::ReceivingMap(2)),
            Some(Family::Map),
        ));
        let first_before = first.clone();
        enrich_failed_normal_ray(
            &mut first,
            kind,
            &law,
            &flow,
            &candidate,
            &Rat::one(),
            Some(2),
            &[sample],
        );
        assert_eq!(first, first_before);
    }

    #[test]
    fn actual_source_face_reads_the_signed_represented_delta_and_refuses_opposition() {
        let delta = EpochArray::new(1, 1, 24, vec![1.into()]).unwrap();
        let sample = Sample {
            weight: Rat::one(),
            feature: vec![Rat::one()],
            covector: vec![rat(1, 8)],
            masses: None,
        };
        let face = actual_epoch_face(
            LinearLocus::SourcePort(0),
            &delta,
            std::slice::from_ref(&sample),
            &[],
            16,
            Rat::one(),
            &mut None,
        )
        .unwrap();
        assert_eq!(face.alignment, rat(1, 8) * delta.scalar_ratio().unwrap());
        assert_eq!(
            face.moves,
            delta.scalar_ratio().unwrap() * delta.scalar_ratio().unwrap()
        );
        let opposite = EpochArray::new(1, 1, 24, vec![(-1).into()]).unwrap();
        let mut evidence = None;
        assert!(matches!(
            actual_epoch_face(
                LinearLocus::SourcePort(0),
                &opposite,
                &[sample],
                &[],
                16,
                Rat::one(),
                &mut evidence
            ),
            Err(HnnError::Unadmitted { .. })
        ));
        let evidence = evidence.unwrap();
        assert_eq!(evidence.condition, EpochStageCondition::ActualRayAlignment);
        assert_eq!(
            (evidence.locus, evidence.family),
            (Some(Locus::SourcePort(0)), Some(Family::Map))
        );
        assert!(!evidence.seal_formed && !evidence.finite_probe_executed);
        assert!(evidence
            .readings
            .iter()
            .any(|reading| reading.name == "alignment"
                && matches!(&reading.value, EpochStageValue::Ratio(value) if value.is_negative())));
    }

    #[test]
    fn fixed_actual_ray_enforces_curvature_where_declared_only_records_it() {
        let field = crate::hnn::tests::learning::chain();
        let theta = Constitution::initial(&field, u64::MAX).unwrap();
        let receiver = field.receivers()[0].ring;
        let reach = Reach {
            receiver,
            stations: vec![1, 2],
            entries: vec![0],
            phases: 1,
            loci: crate::hnn::retention::loci(&field).into_iter().collect(),
            passages: Vec::new(),
        };
        let map = theta.receiving_law(receiver).unwrap().map();
        let mut entries = vec![BigInt::zero(); map.rows() * map.columns()];
        entries[0] = BigInt::one();
        let face = EpochCertificateFace {
            unit: IntegralMatrix::from_grouped(map.rows(), map.columns(), entries, 1.into())
                .unwrap(),
            alignment: Rat::one(),
            moves: Rat::from_integer(BigInt::one() << 20usize),
            covector: Rat::one(),
            unit_norms: (Rat::one(), Rat::one()),
            norm: Rat::one(),
        };
        let kind = LinearLocus::Receiving(receiver);
        let linear = [(kind.locus(), kind, face.direction())];
        let declared = DeclaredExponents {
            steps: BTreeMap::from([(
                (kind.locus(), Family::Map),
                DeclaredExponent {
                    exponent: 0,
                    reach: None,
                },
            )]),
        };
        let provisional = theta
            .certify_steps(
                Some(&reach),
                &linear,
                &[],
                None,
                StepSource::Declared(&declared),
                None,
                None,
            )
            .unwrap()
            .unwrap();
        assert!(!provisional.0[&(kind.locus(), Family::Map)].step.holds());
        let before = theta.continuing_state(0).unwrap().to_text();
        let mut evidence = None;
        assert!(matches!(
            theta.certify_steps_with_epoch_evidence(
                Some(&reach),
                &linear,
                &[],
                None,
                StepSource::Actual(&declared),
                None,
                None,
                &mut evidence
            ),
            Err(HnnError::Unadmitted { .. })
        ));
        let evidence = evidence.unwrap();
        assert_eq!(evidence.condition, EpochStageCondition::ActualRayCurvature);
        assert_eq!(
            (evidence.locus, evidence.family),
            (Some(kind.locus()), Some(Family::Map))
        );
        assert!(evidence
            .readings
            .iter()
            .any(|reading| reading.name == "own_curvature_slack"
                && matches!(&reading.value, EpochStageValue::Ratio(value) if value.is_negative())));
        let recorded = evidence
            .readings
            .iter()
            .find_map(|reading| match &reading.value {
                EpochStageValue::Step(step) => Some(step),
                _ => None,
            })
            .unwrap();
        assert_eq!(recorded, &provisional.0[&(kind.locus(), Family::Map)].step);
        let local =
            CertifiedStep::certify(&recorded.alignment, &recorded.curvature, &recorded.covector)
                .unwrap()
                .unwrap();
        assert!(
            evidence
                .readings
                .iter()
                .any(|reading| reading.name == "alignment_over_curvature"
                    && reading.value
                        == EpochStageValue::Ratio(&recorded.alignment / &recorded.curvature))
        );
        assert!(evidence.readings.iter().any(|reading| reading.name
            == "largest_local_admissible_dyadic_k"
            && reading.value == EpochStageValue::Integer(BigInt::from(local.exponent))));
        assert!(
            evidence
                .readings
                .iter()
                .any(|reading| reading.name == "largest_local_admissible_dyadic"
                    && reading.value == EpochStageValue::Ratio(local.step.clone()))
        );
        assert!(!evidence.seal_formed && !evidence.finite_probe_executed);
        assert_eq!(theta.continuing_state(0).unwrap().to_text(), before);
    }

    #[test]
    fn actual_ray_guard_checks_the_joint_triangle_even_when_each_local_bound_holds() {
        let field = crate::hnn::tests::learning::chain();
        let theta = Constitution::initial(&field, u64::MAX).unwrap();
        let receiver = field.receivers()[0].ring;
        let reach = Reach {
            receiver,
            stations: vec![1, 2],
            entries: vec![0],
            phases: 1,
            loci: crate::hnn::retention::loci(&field).into_iter().collect(),
            passages: Vec::new(),
        };
        let kinds = [LinearLocus::SourcePort(0), LinearLocus::Receiving(receiver)];
        let mut faces: Vec<_> = kinds
            .iter()
            .map(|kind| {
                let map = theta.epoch_normal(*kind).unwrap().map();
                let mut values = vec![BigInt::zero(); map.rows() * map.columns()];
                values[0] = BigInt::one();
                EpochCertificateFace {
                    unit: IntegralMatrix::from_grouped(map.rows(), map.columns(), values, 1.into())
                        .unwrap(),
                    alignment: rat(3, 4),
                    moves: Rat::one(),
                    covector: Rat::one(),
                    unit_norms: (Rat::one(), Rat::one()),
                    norm: Rat::one(),
                }
            })
            .collect();
        let declared = DeclaredExponents {
            steps: kinds
                .iter()
                .map(|kind| {
                    (
                        (kind.locus(), Family::Map),
                        DeclaredExponent {
                            exponent: 0,
                            reach: None,
                        },
                    )
                })
                .collect(),
        };
        let read = |faces: &[EpochCertificateFace], source: StepSource<'_>| {
            let linear: Vec<_> = kinds
                .iter()
                .zip(faces)
                .map(|(kind, face)| (kind.locus(), *kind, face.direction()))
                .collect();
            theta.certify_steps(Some(&reach), &linear, &[], None, source, None, None)
        };
        let calibration = read(&faces, StepSource::Declared(&declared))
            .unwrap()
            .unwrap();
        for (kind, face) in kinds.iter().zip(&mut faces) {
            let gain = &calibration.0[&(kind.locus(), Family::Map)].gain;
            assert!(gain.is_positive());
            face.moves = Rat::one() / gain;
        }
        let proposal = read(&faces, StepSource::Declared(&declared))
            .unwrap()
            .unwrap();
        assert!(proposal.0.values().all(|r| r.step.holds()));
        assert!(!proposal.1.unwrap().holds());
        let linear: Vec<_> = kinds
            .iter()
            .zip(&faces)
            .map(|(kind, face)| (kind.locus(), *kind, face.direction()))
            .collect();
        let mut evidence = None;
        assert!(matches!(
            theta.certify_steps_with_epoch_evidence(
                Some(&reach),
                &linear,
                &[],
                None,
                StepSource::Actual(&declared),
                None,
                None,
                &mut evidence
            ),
            Err(HnnError::Unadmitted {
                reason: "the actual epoch rays violate the joint triangle bound",
            })
        ));
        let evidence = evidence.unwrap();
        assert_eq!(evidence.condition, EpochStageCondition::JointTriangle);
        assert_eq!((evidence.locus, evidence.family), (None, None));
        assert_eq!(
            evidence.participating_families,
            kinds
                .iter()
                .map(|kind| (kind.locus(), Family::Map))
                .collect::<Vec<_>>()
        );
        assert!(evidence.readings.iter().any(
            |reading| matches!(&reading.value, EpochStageValue::Joint(joint) if !joint.holds())
        ));
    }

    #[test]
    fn actual_channel_ray_detects_a_rebased_endpoint_and_preserves_cold_continuation() {
        let (field, mut material, _, _, _) = normal_domain_fixture(None, true);
        let opening = material.clone();
        let locus = Locus::Channel(0);
        let unit = material.lattice(locus).unwrap().unit();
        // A legitimate retained subgrain remainder, without any fresh deposition request.
        material.clocks.insert(locus, 2);
        material.carries.insert((locus, Carrier::Factor(2)),
            Carry(BTreeMap::from([(0, &unit / rat(4, 1))])));
        let retained = crate::hnn::retention::loci(&field).into_iter().collect();
        let rebased = material.rebased(locus, 2, &retained).unwrap();
        let rays = channel_ray::ChannelFactorDisplacement::read_all(&material, &rebased).unwrap();
        assert_eq!(rays.len(), 1);
        assert_eq!((rays[0].contact, rays[0].family), (0, 2));
        assert_eq!(rays[0].displacement.entries()[0], &unit / rat(4, 1));
        let before = material.continuing_state(0).unwrap().to_text();
        let after = rebased.continuing_state(0).unwrap().to_text();
        let mut evidence = None;
        assert!(admit_actual_factor_displacements(&material, &rebased,
            &BTreeMap::new(), &[], &BTreeMap::new(), &BTreeMap::new(), false, &mut evidence).is_err());
        let evidence = evidence.unwrap();
        assert_eq!((evidence.locus, evidence.family), (Some(locus), Some(Family::Factor(2))));
        assert_eq!(evidence.condition, EpochStageCondition::NonlinearFactorRay);
        assert!(evidence.readings.iter().any(|r| r.name == "actual_delta_matches_staged_quotient"
            && r.value == EpochStageValue::Index(0)));
        assert_eq!(material.continuing_state(0).unwrap().to_text(), before);
        assert_eq!(rebased.continuing_state(0).unwrap().to_text(), after);
        let state = ContinuingState::from_text(&after, material.budget()).unwrap();
        let cold = opening.continued_on(&field, &state).unwrap();
        assert_eq!(cold, rebased);
        assert_eq!(channel_ray::ChannelFactorDisplacement::read_all(&material, &cold).unwrap(), rays);
        // The next legitimate rebase agrees after restoring complete carrier state.
        assert_eq!(cold.rebased(locus, 1, &retained).unwrap(),
            rebased.rebased(locus, 1, &retained).unwrap());
    }

    #[test]
    fn actual_channel_ray_guard_attaches_its_matching_original_rate_and_covector() {
        let (_, material, _, _, _) = normal_domain_fixture(None, true);
        let locus = Locus::Channel(0);
        let family = Family::Factor(2);
        let unit = material.lattice(locus).unwrap().unit();
        let mut endpoint = material.clone();
        let factor = &material.contacts[0].dissipation;
        let mut rows = factor.to_rows();
        rows[0][0] += &unit;
        endpoint.contacts[0].dissipation = ExactRatMatrix::new(rows).unwrap();
        let mut gradient = ExactRatMatrix::zero(factor.rows(), factor.columns()).unwrap().to_rows();
        gradient[0][0] = rat(3, 1);
        let request = FactorStep { gradient: FactorGradient::Dissipation {
            contact: 0, gradient: ExactRatMatrix::new(gradient).unwrap(),
        }, energy: rat(2, 1), covector: rat(2, 1) };
        // Synthetic certificate input for this read-only guard control, never a publication seal.
        let step = CertifiedStep::certify(&Rat::one(), &Rat::one(), &rat(2, 1)).unwrap().unwrap();
        assert_eq!(step.step, rat(1, 2));
        let certified = BTreeMap::from([((locus, family), StepReading {
            family, step, gain: Rat::one(), moves: Rat::one(), bound: Rat::one(),
            readout: Rat::one(), amplitude: Rat::one(),
        })]);
        // Synthetic prepared metadata exercises the pure bridge only; its scale
        // is deliberately non-unit so a fake/reset statistic cannot pass.
        let original = FactorPrepared {
            index: 0,
            family,
            scale: rat(3, 1),
            alignment: Rat::one(),
            covector: rat(2, 1),
            energy: rat(2, 1),
            moves: channel_factor_moves(2, factor, (Rat::one(), Rat::one()), &material.hop),
        };
        let originals = BTreeMap::from([((locus, family), original)]);
        let mut stroke = BudgetedCarry::new(material.lattice(locus).unwrap(), 1);
        stroke.staged.insert((Carrier::Factor(2), 0), (Rat::zero(), BigInt::one()));
        let before = material.continuing_state(0).unwrap().to_text();
        let after = endpoint.continuing_state(0).unwrap().to_text();
        let faces = admit_actual_factor_displacements(&material, &endpoint,
            &BTreeMap::from([(locus, stroke)]), &[request], &certified, &originals, true, &mut None).unwrap();
        assert_eq!(faces.len(), 1);
        assert_eq!(faces[0].contact(), 0);
        assert_eq!(faces[0].exponent(), certified[&(locus, family)].step.exponent);
        assert_eq!(faces[0].prepared().scale, rat(3, 1));
        assert_eq!(faces[0].prepared().energy, rat(2, 1));
        assert_eq!(faces[0].prepared().covector, rat(2, 1));
        assert_eq!(faces[0].prepared().alignment, floor(&(rat(6, 1) * &unit)));
        assert!(faces[0].prepared().moves.own(&rat(2, 1), &rat(1, 2)).unwrap().is_positive());
        assert_eq!(material.continuing_state(0).unwrap().to_text(), before);
        assert_eq!(endpoint.continuing_state(0).unwrap().to_text(), after);
    }

    #[test]
    fn d_only_actual_ray_still_holds_storage_and_stiffness() {
        let (_, material, _, _, _) = normal_domain_fixture(None, true);
        for family in 0..2 {
            let mut endpoint = material.clone();
            let factor = if family == 0 {
                &mut endpoint.contacts[0].storage
            } else {
                &mut endpoint.contacts[0].stiffness
            };
            let mut rows = factor.to_rows();
            rows[0][0] += material.lattice(Locus::Channel(0)).unwrap().unit();
            *factor = ExactRatMatrix::new(rows).unwrap();
            let mut evidence = None;
            assert!(admit_actual_factor_displacements(
                &material,
                &endpoint,
                &BTreeMap::new(),
                &[],
                &BTreeMap::new(),
                &BTreeMap::new(),
                true,
                &mut evidence,
            )
            .is_err());
            assert_eq!(evidence.unwrap().family, Some(Family::Factor(family)));
        }
    }

    #[test]
    fn d_only_actual_ray_refuses_when_its_fresh_positive_rate_is_missing() {
        let (_, material, _, _, _) = normal_domain_fixture(None, true);
        let locus = Locus::Channel(0);
        let mut endpoint = material.clone();
        let mut rows = endpoint.contacts[0].dissipation.to_rows();
        rows[0][0] += material.lattice(locus).unwrap().unit();
        endpoint.contacts[0].dissipation = ExactRatMatrix::new(rows).unwrap();
        let mut stroke = BudgetedCarry::new(material.lattice(locus).unwrap(), 1);
        stroke.staged.insert((Carrier::Factor(2), 0), (Rat::zero(), BigInt::one()));
        let mut evidence = None;
        assert!(admit_actual_factor_displacements(
            &material,
            &endpoint,
            &BTreeMap::from([(locus, stroke)]),
            &[],
            &BTreeMap::new(),
            &BTreeMap::new(),
            true,
            &mut evidence,
        )
        .is_err());
        assert!(evidence.unwrap().readings.iter().any(|reading|
            reading.name == "actual_ray_rate"
                && matches!(&reading.value, EpochStageValue::Unavailable(_))));
    }

    #[test]
    fn actual_channel_ray_ignores_statistic_only_changes_without_absorbing_them_again() {
        let (_, material, _, _, _) = normal_domain_fixture(None, true);
        let mut endpoint = material.clone();
        endpoint.contacts[0].scales[2] += rat(1, 4);
        let before = material.continuing_state(0).unwrap().to_text();
        let after = endpoint.continuing_state(0).unwrap().to_text();
        assert!(admit_actual_factor_displacements(&material, &endpoint,
            &BTreeMap::new(), &[], &BTreeMap::new(), &BTreeMap::new(), false, &mut None).is_ok());
        assert_eq!(material.continuing_state(0).unwrap().to_text(), before);
        assert_eq!(endpoint.continuing_state(0).unwrap().to_text(), after);
    }

    #[test]
    fn nonlinear_material_and_finer_source_carry_refusals_keep_their_operands() {
        let (_, material, _, _, _) = normal_domain_fixture(None, true);
        let locus = Locus::SourcePort(0);
        let mut at = BudgetedCarry::new(Lattice::new(4), 1);
        at.staged.insert(
            (
                Carrier::Pair {
                    offset: 1,
                    family: 0,
                },
                0,
            ),
            (Rat::zero(), BigInt::one()),
        );
        let strokes = BTreeMap::from([(locus, at)]);
        let before = strokes.clone();
        let mut evidence = None;
        assert!(admit_actual_factor_displacements(
            &material, &material, &strokes, &[], &BTreeMap::new(), &BTreeMap::new(), false, &mut evidence,
        ).is_err());
        let evidence = evidence.unwrap();
        assert_eq!(
            (evidence.locus, evidence.family),
            (Some(locus), Some(Family::Pair(1)))
        );
        assert_eq!(evidence.condition, EpochStageCondition::NonlinearFactorRay);
        assert!(
            evidence
                .readings
                .iter()
                .any(|reading| reading.name == "displacement_q_times_two_minus_L"
                    && reading.value == EpochStageValue::Ratio(rat(1, 16)))
        );
        assert_eq!(strokes, before);
        let mut statistics = BudgetedCarry::new(Lattice::new(4), 1);
        statistics
            .staged
            .insert((Carrier::PairScale, 0), (Rat::zero(), BigInt::one()));
        assert!(
            admit_actual_factor_displacements(&material, &material,
                &BTreeMap::from([(locus, statistics)]), &[], &BTreeMap::new(), &BTreeMap::new(), false, &mut None)
                .is_ok()
        );
        for (remainder, admitted) in [
            (rat(1, 64), false),
            (rat(1, 128), false),
            (rat(-1, 128), true),
            (rat(1, 512), true),
        ] {
            let carries = BTreeMap::from([(
                (
                    locus,
                    Carrier::Pair {
                        offset: 1,
                        family: 0,
                    },
                ),
                Carry(BTreeMap::from([(0, remainder)])),
            )]);
            let before = carries.clone();
            let mut evidence = None;
            assert_eq!(
                admit_refined_source_carries(locus, 6, &carries, &mut evidence).is_ok(),
                admitted
            );
            if !admitted {
                let evidence = evidence.unwrap();
                assert_eq!(
                    evidence.condition,
                    EpochStageCondition::SourceRefinementHalfCell
                );
                assert_eq!(
                    (evidence.locus, evidence.family),
                    (Some(locus), Some(Family::Pair(1)))
                );
                assert!(
                    evidence
                        .readings
                        .iter()
                        .any(|reading| reading.name == "half"
                            && reading.value == EpochStageValue::Ratio(rat(1, 128)))
                );
            } else {
                assert!(evidence.is_none());
            }
            assert_eq!(carries, before);
        }
    }

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
    // A declared native synthetic covector tests publication mechanics, not a measured
    // model improvement. The finite comparison owner remains outside this stage.
    fn d_only_fixture_stage(
        field: &Field,
        material: &Constitution,
        epoch_index: u64,
        scope: EpochCandidateScope,
    ) -> StagedEpochCandidate {
        d_only_fixture_stage_with_grain(field, material, epoch_index, scope, false)
    }

    fn d_only_fixture_stage_with_grain(
        field: &Field, material: &Constitution, epoch_index: u64,
        scope: EpochCandidateScope, refining: bool,
    ) -> StagedEpochCandidate {
        d_only_fixture_stage_with_grain_gradient(field, material, epoch_index, scope, refining, rat(8, 1))
    }

    fn d_only_fixture_stage_with_grain_gradient(
        field: &Field, material: &Constitution, epoch_index: u64,
        scope: EpochCandidateScope, refining: bool, gradient: Rat,
    ) -> StagedEpochCandidate {
        let receiver = field.receivers()[0].ring;
        let requests = material.contacts.iter().enumerate().map(|(contact, factor)| FactorStep {
            gradient: FactorGradient::Dissipation {
                contact,
                gradient: scaled_identity(factor.dissipation.rows(), gradient.clone()),
            },
            energy: Rat::zero(),
            covector: Rat::one(),
        }).collect();
        let retention: BTreeSet<_> = crate::hnn::retention::loci(field).into_iter().collect();
        let deposit = Deposit::new(material.commit, vec![], requests,
            (0..material.contacts.len()).map(Locus::Channel).collect())
            .with_reach(Reach {
                receiver, stations: vec![2, 4], entries: vec![0], phases: 1,
                loci: retention.clone(), passages: vec![],
            });
        let deposits = [deposit];
        let pair_speed = |_, _, _: &PairPort, _: [&[Vec<Rat>]; 3]| panic!("D is not a pair-port request");
        let mut stage = ObservedNormalEpochStage::new(
            material, &deposits, receiver, field.ring(receiver).period(),
            1, 1, epoch_index,
            partition_exponent(material.observed_epoch_grain(receiver).unwrap(), 1, epoch_index).unwrap(),
            &retention, material.landmarks(receiver).unwrap().clone(), &pair_speed, &[],
            &crate::hnn::reference::observed::HostObservedEpochExecution, true,
        ).unwrap();
        if refining {
            let plan = ObservedChannelGrainPlan::at_section(field, &retention, receiver,
                epoch_index, epoch_index + 1).unwrap().unwrap();
            stage = stage.with_channel_grain(plan).unwrap();
        }
        if scope == EpochCandidateScope::ReceivingOnly {
            let whole = stage.stage(EpochCandidateScope::Whole, &mut |_| {}).unwrap();
            assert!(whole.requires_comparison());
            assert_ne!(whole.material.contacts[0].dissipation, material.contacts[0].dissipation);
            // Drop the unpublished whole before the same-opening receiving retry.
            assert!(whole.admit_change(&crate::ratio::algebraic::ExactInterval {
                lower: Rat::zero(), upper: Rat::one(),
            }).is_none());
        }
        stage.stage(scope, &mut |_| {}).unwrap()
    }

    #[test]
    fn d_only_real_staging_requires_comparison_and_receiving_retry_discards_factor_state() {
        let (field, material, _, _, _) = normal_domain_fixture(None, false);
        let before = material.continuing_state(0).unwrap().to_text();
        let candidate = d_only_fixture_stage(&field, &material, 0, EpochCandidateScope::Whole);
        assert!(candidate.requires_comparison());
        assert!(candidate.has_physical_motion());
        for contact in 0..material.contacts.len() {
            assert_ne!(candidate.material.contacts[contact].dissipation, material.contacts[contact].dissipation);
            assert!(candidate.reading.steps.iter().any(|(locus, step)|
                *locus == Locus::Channel(contact) && step.family == Family::Factor(2)),
                "each actual D face uses its own original prepared request index, including contact1/index1");
        }
        for (old, new) in material.contacts.iter().zip(&candidate.material.contacts) {
            assert_eq!(old.storage, new.storage);
            assert_eq!(old.stiffness, new.stiffness);
        }
        assert!(candidate.admit_receiving().is_err());
        let fallback = d_only_fixture_stage(&field, &material, 0, EpochCandidateScope::ReceivingOnly);
        assert!(!fallback.requires_comparison());
        assert_eq!(fallback.material.contacts, material.contacts,
            "discarded D parameters and statistics cannot leak to receiving-only publication");
        for contact in 0..material.contacts.len() {
            let locus = Locus::Channel(contact);
            assert_eq!(fallback.material.lattice(locus).unwrap(), material.lattice(locus).unwrap());
            assert_eq!(fallback.material.clock(locus), material.clock(locus));
        }
        assert_eq!(fallback.material.carries.iter().filter(|((l, _), _)| matches!(l, Locus::Channel(_))).collect::<Vec<_>>(),
            material.carries.iter().filter(|((l, _), _)| matches!(l, Locus::Channel(_))).collect::<Vec<_>>());
        assert_eq!(material.continuing_state(0).unwrap().to_text(), before);
    }

    #[test]
    fn d_only_real_staged_endpoint_roundtrips_complete_state_and_next_staging() {
        let (field, material, _, _, _) = normal_domain_fixture(None, false);
        let staged = d_only_fixture_stage(&field, &material, 0, EpochCandidateScope::Whole).material;
        let text = staged.continuing_state(0).unwrap().to_text();
        let state = ContinuingState::from_text(&text, material.budget()).unwrap();
        let cold = material.continued_on(&field, &state).unwrap();
        assert_eq!(cold, staged);
        assert_eq!(cold.continuing_state(0).unwrap().to_text(), text);
        let warm_next = d_only_fixture_stage(&field, &staged, 1, EpochCandidateScope::Whole);
        let cold_next = d_only_fixture_stage(&field, &cold, 1, EpochCandidateScope::Whole);
        assert_eq!(warm_next.material, cold_next.material);
        assert_eq!(warm_next.requires_comparison(), cold_next.requires_comparison());
    }

    #[test]
    fn grain_join_stages_two_rebased_d_endpoints_and_discards_all_channels_on_retry() {
        let (field, mut opening, _, _, _) = normal_domain_fixture(None, false);
        for contact in 0..opening.contacts.len() {
            let locus = Locus::Channel(contact);
            let amount = opening.lattice(locus).unwrap().unit() / rat(4, 1);
            opening.clocks.insert(locus, 7);
            for carrier in [Carrier::Factor(2), Carrier::FactorScale(2)] {
                opening.carries.insert((locus, carrier), Carry(BTreeMap::from([(0, amount.clone())])));
            }
        }
        let before = opening.clone();
        let staged = d_only_fixture_stage_with_grain(&field, &opening, 113, EpochCandidateScope::Whole, true);
        assert!(staged.requires_comparison());
        assert!(staged.has_physical_motion());
        let grain = staged.reading.epoch.as_ref().unwrap().channel_grain.as_ref().unwrap();
        assert_eq!((grain.ingress_before, grain.ingress_after, grain.grain_exponent), (113, 114, 3));
        assert_eq!(grain.contacts.len(), opening.contacts.len());
        assert_eq!(staged.material.commit, opening.commit + 1);
        for reading in &grain.contacts {
            let contact = reading.contact;
            let locus = Locus::Channel(contact);
            assert_eq!(reading.levels, 3);
            assert_eq!(reading.after_exponent, reading.founding_exponent + 3);
            assert!(reading.dissipation_rebase.numerators.iter().any(|x| !x.is_zero()));
            assert_eq!(staged.material.lattice(locus).unwrap().exponent(), reading.after_exponent);
            assert_eq!(staged.material.clock(locus), opening.clock(locus) + 1,
                "rebase cannot add a second persistent clock advance");
            assert_eq!(staged.material.contacts[contact].storage, opening.contacts[contact].storage);
            assert_eq!(staged.material.contacts[contact].stiffness, opening.contacts[contact].stiffness);
            assert_eq!(staged.material.contacts[contact].scales[..2], opening.contacts[contact].scales[..2]);
            assert!(staged.reading.steps.iter().any(|(at, step)| *at == locus && step.family == Family::Factor(2)));
        }
        assert!(staged.admit_change(&crate::ratio::algebraic::ExactInterval {
            lower: Rat::zero(), upper: Rat::one(),
        }).is_none(), "a non-descending same-opening comparison cannot publish the rebased endpoint");
        let fallback = d_only_fixture_stage_with_grain(&field, &opening, 113, EpochCandidateScope::ReceivingOnly, true);
        assert!(!fallback.requires_comparison());
        assert!(fallback.reading.epoch.as_ref().unwrap().channel_grain.is_none());
        assert_eq!(fallback.material.contacts, opening.contacts);
        for contact in 0..opening.contacts.len() {
            let locus = Locus::Channel(contact);
            assert_eq!(fallback.material.lattice(locus).unwrap(), opening.lattice(locus).unwrap());
            assert_eq!(fallback.material.clock(locus), opening.clock(locus));
        }
        assert_eq!(fallback.material.carries.iter().filter(|((l, _), _)| matches!(l, Locus::Channel(_))).collect::<Vec<_>>(),
            opening.carries.iter().filter(|((l, _), _)| matches!(l, Locus::Channel(_))).collect::<Vec<_>>());
        assert_eq!(opening, before);
    }

    #[test]
    fn grain_join_complete_cold_restore_and_next_staging_keep_absolute_target() {
        let (field, mut opening, _, _, _) = normal_domain_fixture(None, false);
        let founding = opening.clone();
        for contact in 0..opening.contacts.len() {
            let locus = Locus::Channel(contact);
            let amount = opening.lattice(locus).unwrap().unit() / rat(4, 1);
            opening.clocks.insert(locus, 7);
            opening.carries.insert((locus, Carrier::Factor(2)), Carry(BTreeMap::from([(0, amount)])));
        }
        let staged = d_only_fixture_stage_with_grain(&field, &opening, 113, EpochCandidateScope::Whole, true).material;
        let text = staged.continuing_state(0).unwrap().to_text();
        let state = ContinuingState::from_text(&text, staged.budget()).unwrap();
        let cold = founding.continued_on(&field, &state).unwrap();
        assert_eq!(cold, staged);
        assert_eq!(cold.continuing_state(0).unwrap().to_text(), text);
        let warm_next = d_only_fixture_stage_with_grain(&field, &staged, 114, EpochCandidateScope::Whole, true);
        let cold_next = d_only_fixture_stage_with_grain(&field, &cold, 114, EpochCandidateScope::Whole, true);
        assert_eq!(warm_next.material, cold_next.material);
        assert_eq!(warm_next.reading, cold_next.reading);
        assert!(warm_next.reading.epoch.unwrap().channel_grain.unwrap().contacts.iter().all(|r| r.levels == 0));
    }

    #[test]
    fn grain_join_without_nonzero_fresh_d_update_keeps_all_channel_state() {
        let (field, mut opening, _, _, _) = normal_domain_fixture(None, false);
        for contact in 0..opening.contacts.len() {
            let locus = Locus::Channel(contact);
            let amount = opening.lattice(locus).unwrap().unit() / rat(4, 1);
            opening.clocks.insert(locus, 7);
            opening.carries.insert((locus, Carrier::Factor(2)), Carry(BTreeMap::from([(0, amount)])));
        }
        let staged = d_only_fixture_stage_with_grain_gradient(&field, &opening, 113, EpochCandidateScope::Whole, true, Rat::zero());
        assert_eq!(staged.material.contacts, opening.contacts);
        let grain = staged.reading.epoch.unwrap().channel_grain.unwrap();
        for reading in grain.contacts {
            let locus = Locus::Channel(reading.contact);
            assert_eq!(reading.levels, 0);
            assert_eq!(reading.shortfall, 3);
            assert!(reading.deferred_without_fresh_update);
            assert_eq!(staged.material.lattice(locus).unwrap(), opening.lattice(locus).unwrap());
            assert_eq!(staged.material.clock(locus), opening.clock(locus));
        }
        assert_eq!(staged.material.carries.iter().filter(|((l, _), _)| matches!(l, Locus::Channel(_))).collect::<Vec<_>>(),
            opening.carries.iter().filter(|((l, _), _)| matches!(l, Locus::Channel(_))).collect::<Vec<_>>());
    }

}
