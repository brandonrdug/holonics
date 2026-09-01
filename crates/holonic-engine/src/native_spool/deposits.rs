use super::refusal::NativeSpoolRefusal;
use super::*;
/// One exact serial composition joining threads owned by two different spools.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeSpoolComposition {
    pub left_spool: String,
    pub right_spool: String,
    pub pullback: NativeSerialPullback,
}

/// The exact occurrence-fibre change carried by one novel native thread.
///
/// These deltas must partition the deposited thread's complete occurrence population by its
/// emitting native state.  They are not counts and cannot be supplied independently of the
/// carrying occurrences.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeDepositFibreDelta {
    pub native: NativeStateId,
    pub occurrences: BTreeSet<EventId>,
}

/// A compact, exact finite-Leibniz family over an incident pair of native threads.
///
/// `pair_population` testifies for the whole addressed support population; this is intentionally
/// not expanded into a quadratic list of rational pair terms.  The currents are complex and the
/// mixed remainder is retained because omitting it changes the returned product.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeMixedConstitutiveFamily {
    pub address: String,
    pub left_thread: String,
    pub right_thread: String,
    pub receiver: ReceiverId,
    pub storage: Rat,
    pub candidate_left: ExactComplexWaveCurrent,
    pub candidate_right: ExactComplexWaveCurrent,
    pub returned_left: ExactComplexWaveCurrent,
    pub returned_right: ExactComplexWaveCurrent,
    pub left_difference: ExactComplexWaveCurrent,
    pub right_difference: ExactComplexWaveCurrent,
    pub candidate_product: ExactComplexWaveCurrent,
    pub source_linear_terms: ExactComplexWaveCurrent,
    pub mixed_remainder: ExactComplexWaveCurrent,
    pub reconstructed_returned_product: ExactComplexWaveCurrent,
    pub returned_product: ExactComplexWaveCurrent,
    pub dependent_receiver_support: BTreeSet<NativeStateId>,
    pub pair_population: u64,
}

impl NativeMixedConstitutiveFamily {
    pub fn validate(&self) -> Result<(), NativeSpoolRefusal> {
        let left_difference = self.returned_left.subtract(&self.candidate_left);
        let right_difference = self.returned_right.subtract(&self.candidate_right);
        let candidate_product = self
            .candidate_left
            .multiply(&self.candidate_right)
            .scaled(&self.storage);
        let source_linear_terms = self
            .candidate_left
            .multiply(&right_difference)
            .add(&left_difference.multiply(&self.candidate_right))
            .scaled(&self.storage);
        let mixed_remainder = left_difference
            .multiply(&right_difference)
            .scaled(&self.storage);
        let returned_product = self
            .returned_left
            .multiply(&self.returned_right)
            .scaled(&self.storage);
        let reconstructed = candidate_product
            .add(&source_linear_terms)
            .add(&mixed_remainder);
        let support = u64::try_from(self.dependent_receiver_support.len())
            .map_err(|_| NativeSpoolRefusal::MixedConstitutiveFamily(self.address.clone()))?;
        let expected_population = support
            .checked_mul(support.saturating_sub(1))
            .and_then(|population| population.checked_div(2))
            .ok_or_else(|| NativeSpoolRefusal::MixedConstitutiveFamily(self.address.clone()))?;
        if self.address.is_empty()
            || self.left_thread.is_empty()
            || self.right_thread.is_empty()
            || self.storage == Rat::from_integer(0.into())
            || self.dependent_receiver_support.is_empty()
            || self.pair_population != expected_population
            || self.left_difference != left_difference
            || self.right_difference != right_difference
            || self.candidate_product != candidate_product
            || self.source_linear_terms != source_linear_terms
            || self.mixed_remainder != mixed_remainder
            || self.reconstructed_returned_product != reconstructed
            || self.returned_product != returned_product
            || reconstructed != returned_product
        {
            return Err(NativeSpoolRefusal::MixedConstitutiveFamily(
                self.address.clone(),
            ));
        }
        Ok(())
    }
}

/// One exact affine/radical/obstruction fibre incident to a native deposited thread.
///
/// The occurrence fibre retains causal origin while `particular + span(radical)` retains every
/// solution hidden by the receiver.  An obstruction is a typed returned covector in the same
/// coordinate line, not a Boolean failure flag.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeExactReconstructionFibre {
    pub address: String,
    pub thread: String,
    pub return_operator: ExactRatMatrix,
    pub terminal_covector: Vec<Rat>,
    pub returned_covector: Vec<Rat>,
    pub particular: Vec<Rat>,
    pub radical: Vec<Vec<Rat>>,
    pub obstruction: Option<Vec<Rat>>,
    pub carrying_pullback: NativePullbackOccurrence,
    pub k3_native_support: BTreeSet<NativeStateId>,
    pub dependent_receiver_fibre: BTreeSet<NativeStateId>,
    pub occurrences: BTreeSet<EventId>,
    pub open_exterior: Vec<String>,
}

impl NativeExactReconstructionFibre {
    pub fn validate(&self) -> Result<(), NativeSpoolRefusal> {
        let domain_dimension = self.return_operator.columns();
        let codomain_dimension = self.return_operator.rows();
        let zero = Rat::from_integer(0.into());
        let mut radical = BTreeSet::new();
        let returned = self
            .return_operator
            .apply(&self.terminal_covector)
            .map_err(|_| NativeSpoolRefusal::ExactReconstructionFibre(self.address.clone()))?;
        let particular_return = self
            .return_operator
            .apply(&self.particular)
            .map_err(|_| NativeSpoolRefusal::ExactReconstructionFibre(self.address.clone()))?;
        let radical_is_malformed = self.radical.iter().any(|direction| {
            if direction.len() != domain_dimension
                || direction.iter().all(|coordinate| coordinate == &zero)
                || !radical.insert(direction)
            {
                return true;
            }
            match self.return_operator.apply(direction) {
                Ok(image) => image.iter().any(|coordinate| coordinate != &zero),
                Err(_) => true,
            }
        });
        if self.address.is_empty()
            || self.thread.is_empty()
            || domain_dimension == 0
            || codomain_dimension == 0
            || self.particular.len() != domain_dimension
            || self.terminal_covector.len() != domain_dimension
            || self.returned_covector.len() != codomain_dimension
            || returned != self.returned_covector
            || particular_return != self.returned_covector
            || self.k3_native_support.is_empty()
            || self.dependent_receiver_fibre.is_empty()
            || self.occurrences.is_empty()
            || !self.occurrences.contains(&self.carrying_pullback.left)
            || !self.occurrences.contains(&self.carrying_pullback.right)
            || !self
                .k3_native_support
                .contains(&self.carrying_pullback.joining_native)
            || self.open_exterior.iter().any(String::is_empty)
            || radical_is_malformed
            || self
                .obstruction
                .as_ref()
                .is_some_and(|obstruction| obstruction.len() != codomain_dimension)
        {
            return Err(NativeSpoolRefusal::ExactReconstructionFibre(
                self.address.clone(),
            ));
        }
        Ok(())
    }
}

/// One move-owned, source-neutral morphology change for an existing native spool.
///
/// The deposit carries the thread together with every incident relation which it introduces.  It
/// deliberately has no source identity, semantic label, authored width, executor, or foreign
/// coordinate.  `NativeTransportScaffold::deposit_thread` consumes this value, so the new morphology
/// cannot exist simultaneously inside and outside the continuing ecology.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeThreadDeposit {
    pub schema: String,
    pub spool_address: String,
    pub thread: NativeThread,
    pub serial_pullbacks: Vec<NativeSerialPullback>,
    pub generator_descents: Vec<NativeGeneratorDescent>,
    pub receiver_factors: Vec<ReceiverFactor>,
    pub mutual_constitutive_responses: Vec<NativeMutualConstitutiveResponse>,
    pub mixed_constitutive_families: Vec<NativeMixedConstitutiveFamily>,
    pub shortest_separators: Vec<NativeShortestSeparator>,
    pub interchanges: Vec<NativeInterchangeReceipt>,
    pub reconstruction_fibre_deltas: Vec<NativeDepositFibreDelta>,
    pub exact_reconstruction_fibres: Vec<NativeExactReconstructionFibre>,
}

impl NativeThreadDeposit {
    pub fn validate(&self) -> Result<(), NativeSpoolRefusal> {
        if self.schema != NATIVE_THREAD_DEPOSIT_SCHEMA {
            return Err(NativeSpoolRefusal::Schema(self.schema.clone()));
        }
        if self.spool_address.is_empty() {
            return Err(NativeSpoolRefusal::ThreadDeposit(
                "the addressed spool is empty".to_owned(),
            ));
        }
        self.thread.validate()?;
        for family in &self.mixed_constitutive_families {
            family.validate()?;
        }
        for fibre in &self.exact_reconstruction_fibres {
            fibre.validate()?;
        }
        let deposited_occurrences = self
            .thread
            .occurrences
            .iter()
            .map(|occurrence| (occurrence.occurrence, occurrence.emitting_native))
            .collect::<BTreeMap<_, _>>();
        let mut partition = BTreeMap::<EventId, NativeStateId>::new();
        let mut delta_states = BTreeSet::new();
        for delta in &self.reconstruction_fibre_deltas {
            if delta.occurrences.is_empty() || !delta_states.insert(delta.native) {
                return Err(NativeSpoolRefusal::ThreadDeposit(
                    "the reconstruction-fibre delta is empty or repeated".to_owned(),
                ));
            }
            for occurrence in &delta.occurrences {
                if deposited_occurrences.get(occurrence) != Some(&delta.native)
                    || partition.insert(*occurrence, delta.native).is_some()
                {
                    return Err(NativeSpoolRefusal::ThreadDeposit(
                        "the reconstruction-fibre delta does not follow the deposited boundary map"
                            .to_owned(),
                    ));
                }
            }
        }
        if partition != deposited_occurrences {
            return Err(NativeSpoolRefusal::ThreadDeposit(
                "the reconstruction-fibre deltas do not partition the deposited occurrences"
                    .to_owned(),
            ));
        }
        Ok(())
    }
}

/// The exact placement of one deposited fibre delta in its spool partition.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeDepositFibreReceipt {
    pub position: usize,
    pub native: NativeStateId,
    pub occurrences: BTreeSet<EventId>,
    pub fibre_was_founded: bool,
}

/// The inverse address of one atomic native-thread deposit.
///
/// It contains identities and insertion positions, never a duplicate of the deposited thread.
/// Consuming it through `withdraw_deposit` recovers both the predecessor ecology and the original
/// move-owned deposit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeThreadDepositReceipt {
    pub schema: String,
    pub predecessor_identity_sha256: String,
    pub successor_identity_sha256: String,
    pub deposit_identity_sha256: String,
    pub spool_address: String,
    pub thread_address: String,
    pub thread_position: usize,
    pub serial_pullback_positions: Vec<usize>,
    pub generator_descent_positions: Vec<usize>,
    pub receiver_factor_positions: Vec<usize>,
    pub mutual_constitutive_positions: Vec<usize>,
    pub mixed_constitutive_positions: Vec<usize>,
    pub shortest_separator_positions: Vec<usize>,
    pub interchange_positions: Vec<usize>,
    pub fibre_receipts: Vec<NativeDepositFibreReceipt>,
    pub exact_reconstruction_positions: Vec<usize>,
    pub predecessor_kind: SituatedNativeTransportPredecessorKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum SituatedNativeTransportPredecessorKind {
    NativeScaffold,
    SituatedScaffold,
}

impl NativeThreadDepositReceipt {
    pub fn validate(&self) -> Result<(), NativeSpoolRefusal> {
        let identities = [
            self.predecessor_identity_sha256.as_str(),
            self.successor_identity_sha256.as_str(),
            self.deposit_identity_sha256.as_str(),
        ];
        if self.schema != NATIVE_THREAD_DEPOSIT_RECEIPT_SCHEMA
            || self.spool_address.is_empty()
            || self.thread_address.is_empty()
            || identities
                .iter()
                .any(|identity| !is_sha256_identity(identity))
            || !positions_are_unique(&self.serial_pullback_positions)
            || !positions_are_unique(&self.generator_descent_positions)
            || !positions_are_unique(&self.receiver_factor_positions)
            || !positions_are_unique(&self.mutual_constitutive_positions)
            || !positions_are_unique(&self.mixed_constitutive_positions)
            || !positions_are_unique(&self.shortest_separator_positions)
            || !positions_are_unique(&self.interchange_positions)
            || !positions_are_unique(&self.exact_reconstruction_positions)
            || self.fibre_receipts.is_empty()
        {
            return Err(NativeSpoolRefusal::ThreadDepositReceipt);
        }
        let mut states = BTreeSet::new();
        let mut occurrences = BTreeSet::new();
        for fibre in &self.fibre_receipts {
            if fibre.occurrences.is_empty()
                || !states.insert(fibre.native)
                || !fibre
                    .occurrences
                    .iter()
                    .all(|occurrence| occurrences.insert(*occurrence))
            {
                return Err(NativeSpoolRefusal::ThreadDepositReceipt);
            }
        }
        Ok(())
    }
}

/// One thread's exact placement inside an atomic batch.  Unlike a sequence of singular receipts,
/// it carries no intermediate-body identity: the batch has one predecessor and one successor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeThreadDepositPlacement {
    pub spool_address: String,
    pub thread_address: String,
    pub thread_position: usize,
    pub serial_pullback_positions: Vec<usize>,
    pub generator_descent_positions: Vec<usize>,
    pub receiver_factor_positions: Vec<usize>,
    pub mutual_constitutive_positions: Vec<usize>,
    pub mixed_constitutive_positions: Vec<usize>,
    pub shortest_separator_positions: Vec<usize>,
    pub interchange_positions: Vec<usize>,
    pub fibre_receipts: Vec<NativeDepositFibreReceipt>,
    pub exact_reconstruction_positions: Vec<usize>,
}

/// One unordered term of the symmetric constitutive square.  Canonical address order is a wire
/// convention only; it introduces no chronology between the two cycle directions.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeSymmetricConstitutiveTerm {
    pub left_thread: String,
    pub right_thread: String,
    pub family_address: String,
}

/// The compact `Sym^2` body founded by one atomic cycle population.
///
/// For rank `n`, the diagonal population is `n`, the distinct-pair population is `n(n-1)/2`,
/// and their union is `n(n+1)/2`.  This is deliberately not the alternating-plane population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeSymmetricConstitutiveBody {
    pub thread_population: BTreeSet<String>,
    pub receiver: ReceiverId,
    pub dependent_receiver_support: BTreeSet<NativeStateId>,
    pub terms: Vec<NativeSymmetricConstitutiveTerm>,
    pub diagonal_population: u64,
    pub distinct_pair_population: u64,
    pub symmetric_population: u64,
}

impl NativeSymmetricConstitutiveBody {
    pub fn validate(&self) -> Result<(), NativeSpoolRefusal> {
        let rank = u64::try_from(self.thread_population.len())
            .map_err(|_| NativeSpoolRefusal::ThreadDepositBatchReceipt)?;
        let distinct = rank
            .checked_mul(rank.saturating_sub(1))
            .and_then(|population| population.checked_div(2))
            .ok_or(NativeSpoolRefusal::ThreadDepositBatchReceipt)?;
        let symmetric = rank
            .checked_mul(rank.saturating_add(1))
            .and_then(|population| population.checked_div(2))
            .ok_or(NativeSpoolRefusal::ThreadDepositBatchReceipt)?;
        let expected_pairs = self
            .thread_population
            .iter()
            .flat_map(|left| {
                self.thread_population
                    .range(left.clone()..)
                    .map(move |right| (left.as_str(), right.as_str()))
            })
            .collect::<BTreeSet<_>>();
        let mut actual_pairs = BTreeSet::new();
        let mut addresses = BTreeSet::new();
        if self.thread_population.is_empty()
            || self.dependent_receiver_support.is_empty()
            || self.diagonal_population != rank
            || self.distinct_pair_population != distinct
            || self.symmetric_population != symmetric
            || self.terms.len() as u64 != symmetric
            || self.terms.iter().any(|term| {
                term.left_thread > term.right_thread
                    || term.family_address.is_empty()
                    || !actual_pairs.insert((term.left_thread.as_str(), term.right_thread.as_str()))
                    || !addresses.insert(term.family_address.as_str())
            })
            || actual_pairs != expected_pairs
        {
            return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
        }
        Ok(())
    }
}

impl NativeThreadDepositPlacement {
    pub(crate) fn validate(&self) -> Result<(), NativeSpoolRefusal> {
        if self.spool_address.is_empty()
            || self.thread_address.is_empty()
            || !positions_are_unique(&self.serial_pullback_positions)
            || !positions_are_unique(&self.generator_descent_positions)
            || !positions_are_unique(&self.receiver_factor_positions)
            || !positions_are_unique(&self.mutual_constitutive_positions)
            || !positions_are_unique(&self.mixed_constitutive_positions)
            || !positions_are_unique(&self.shortest_separator_positions)
            || !positions_are_unique(&self.interchange_positions)
            || !positions_are_unique(&self.exact_reconstruction_positions)
            || self.fibre_receipts.is_empty()
        {
            return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
        }
        let mut states = BTreeSet::new();
        let mut occurrences = BTreeSet::new();
        if self.fibre_receipts.iter().any(|fibre| {
            fibre.occurrences.is_empty()
                || !states.insert(fibre.native)
                || !fibre
                    .occurrences
                    .iter()
                    .all(|occurrence| occurrences.insert(*occurrence))
        }) {
            return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
        }
        Ok(())
    }
}

/// One exact predecessor/successor receipt for a complete atomic deposit batch.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeThreadDepositBatchReceipt {
    pub schema: String,
    pub predecessor_identity_sha256: String,
    pub successor_identity_sha256: String,
    pub batch_identity_sha256: String,
    pub placements: Vec<NativeThreadDepositPlacement>,
    pub symmetric_constitutive_body: NativeSymmetricConstitutiveBody,
}

impl NativeThreadDepositBatchReceipt {
    pub fn validate(&self) -> Result<(), NativeSpoolRefusal> {
        if self.schema != NATIVE_THREAD_DEPOSIT_BATCH_RECEIPT_SCHEMA
            || !is_sha256_identity(&self.predecessor_identity_sha256)
            || !is_sha256_identity(&self.successor_identity_sha256)
            || !is_sha256_identity(&self.batch_identity_sha256)
            || self.placements.is_empty()
        {
            return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
        }
        self.symmetric_constitutive_body.validate()?;
        let mut threads = BTreeSet::new();
        let mut spools = BTreeSet::new();
        for placement in &self.placements {
            placement.validate()?;
            spools.insert(placement.spool_address.as_str());
            if !threads.insert((
                placement.spool_address.as_str(),
                placement.thread_address.as_str(),
            )) {
                return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
            }
        }
        if spools.len() != 1
            || threads
                .iter()
                .map(|(_, thread)| (*thread).to_owned())
                .collect::<BTreeSet<_>>()
                != self.symmetric_constitutive_body.thread_population
        {
            return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
        }
        Ok(())
    }
}
