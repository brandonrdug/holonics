use super::deposits::NativeSpoolBundle;
use super::refusal::NativeSpoolRefusal;
use super::*;
/// One source-neutral cultivated continuation of an admitted native spool bundle.
///
/// This is an explicit returned type transition: the admitted v2 native bundle remains readable
/// unchanged, while the new owner move-owns it together with the exact mixed and reconstruction
/// relations which the v2 wire did not claim to carry.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeSituatedSpoolBundle {
    pub schema: String,
    pub(crate) native: NativeSpoolBundle,
    pub(crate) mixed_constitutive_families: Vec<NativeMixedConstitutiveFamily>,
    pub(crate) exact_reconstruction_fibres: Vec<NativeExactReconstructionFibre>,
}

/// The exact predecessor returned when a situated deposit is withdrawn.  The first deposit
/// crosses back to its admitted native bundle; later deposits remain in the situated owner.
#[derive(Debug, PartialEq, Eq)]
pub enum NativeSituatedSpoolPredecessor {
    Native(NativeSpoolBundle),
    Situated(NativeSituatedSpoolBundle),
}

/// Recoverable ownership transfer for an arbitrary thread in a situated bundle.  Every compact
/// mixed family and exact affine fibre incident to that thread travels with the native withdrawal.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeSituatedThreadWithdrawal {
    pub original_situated_identity_sha256: String,
    pub native: NativeThreadWithdrawal,
    pub mixed_constitutive_families: Vec<(usize, NativeMixedConstitutiveFamily)>,
    pub exact_reconstruction_fibres: Vec<(usize, NativeExactReconstructionFibre)>,
}

/// Recoverable withdrawal of one receiver-radical direction from an exact situated fibre.
///
/// The direction is support-disjoint from the returned covector because validation has already
/// proved that the causal-adjoint return operator annihilates it.  Removing it changes the
/// reconstruction body while preserving the admitted conduct receiver; restoration consumes the
/// moved direction and recovers the original situated identity.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeSituatedRadicalWithdrawal {
    pub original_situated_identity_sha256: String,
    pub fibre_address: String,
    pub direction_position: usize,
    pub direction: Vec<Rat>,
}

impl NativeSituatedSpoolPredecessor {
    pub fn identity_sha256(&self) -> Result<String, NativeSpoolRefusal> {
        match self {
            Self::Native(bundle) => native_bundle_identity(bundle),
            Self::Situated(bundle) => bundle.identity_sha256(),
        }
    }
}

impl NativeSituatedSpoolBundle {
    pub fn read(bytes: &[u8]) -> Result<Self, NativeSpoolRefusal> {
        let situated: Self = serde_json::from_slice(bytes)
            .map_err(|error| NativeSpoolRefusal::Wire(error.to_string()))?;
        situated.validate()?;
        Ok(situated)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, NativeSpoolRefusal> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| NativeSpoolRefusal::Wire(error.to_string()))
    }

    pub fn identity_sha256(&self) -> Result<String, NativeSpoolRefusal> {
        let bytes = self.canonical_bytes()?;
        Ok(sha256_bytes(&bytes))
    }

    pub fn native(&self) -> &NativeSpoolBundle {
        &self.native
    }

    pub fn mixed_constitutive_families(&self) -> &[NativeMixedConstitutiveFamily] {
        &self.mixed_constitutive_families
    }

    pub fn exact_reconstruction_fibres(&self) -> &[NativeExactReconstructionFibre] {
        &self.exact_reconstruction_fibres
    }

    pub fn validate(&self) -> Result<(), NativeSpoolRefusal> {
        if self.schema != NATIVE_SITUATED_SPOOL_BUNDLE_SCHEMA {
            return Err(NativeSpoolRefusal::Schema(self.schema.clone()));
        }
        self.native.validate()?;
        validate_situated_relations(
            &self.native,
            &self.mixed_constitutive_families,
            &self.exact_reconstruction_fibres,
        )
    }

    /// Deposit another source-neutral thread into an already situated body.
    pub fn deposit_thread(
        self,
        deposit: NativeThreadDeposit,
    ) -> Result<(Self, NativeThreadDepositReceipt), NativeSpoolRefusal> {
        self.validate()?;
        stage_thread_deposit(
            self.native,
            self.mixed_constitutive_families,
            self.exact_reconstruction_fibres,
            deposit,
            NativeSituatedPredecessorKind::SituatedBundle,
            None,
        )
    }

    /// Deposit into a situated body whose complete wire has already been admitted by its owning
    /// rested type state. The exact predecessor identity is carried by that admission receipt;
    /// predecessor validation is not replayed at this hot continuation boundary. The successor
    /// is still validated completely before its receipt returns.
    pub fn deposit_thread_from_admitted(
        self,
        admitted_predecessor_identity_sha256: &str,
        deposit: NativeThreadDeposit,
    ) -> Result<(Self, NativeThreadDepositReceipt), NativeSpoolRefusal> {
        if admitted_predecessor_identity_sha256.len() != 64
            || !admitted_predecessor_identity_sha256
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit())
        {
            return Err(NativeSpoolRefusal::ThreadDepositReceipt);
        }
        stage_thread_deposit(
            self.native,
            self.mixed_constitutive_families,
            self.exact_reconstruction_fibres,
            deposit,
            NativeSituatedPredecessorKind::SituatedBundle,
            Some(admitted_predecessor_identity_sha256),
        )
    }

    /// Consume one exact deposit receipt and return both its predecessor and its original
    /// move-owned deposit.  No occurrence, mixed term, or affine fibre is copied or discarded.
    pub fn withdraw_deposit(
        self,
        receipt: NativeThreadDepositReceipt,
    ) -> Result<(NativeSituatedSpoolPredecessor, NativeThreadDeposit), NativeSpoolRefusal> {
        withdraw_situated_deposit(self, receipt)
    }

    /// Invert one deposit after the owning rested body has already admitted this exact situated
    /// identity.  This preserves every receipt check while avoiding repeated whole-ecology
    /// validation at nested continuation owners.
    pub fn withdraw_deposit_from_admitted(
        self,
        admitted_successor_identity_sha256: &str,
        receipt: NativeThreadDepositReceipt,
    ) -> Result<(NativeSituatedSpoolPredecessor, NativeThreadDeposit), NativeSpoolRefusal> {
        withdraw_situated_deposit_from_admitted(self, admitted_successor_identity_sha256, receipt)
    }

    /// Consume the one atomic batch receipt and return the admitted native predecessor together
    /// with every original deposit in batch order.
    pub fn withdraw_deposit_batch(
        self,
        receipt: NativeThreadDepositBatchReceipt,
    ) -> Result<(NativeSpoolBundle, Vec<NativeThreadDeposit>), NativeSpoolRefusal> {
        withdraw_native_deposit_batch(self, receipt)
    }

    /// Withdraw any addressed thread and all situated relations incident to it.
    pub fn withdraw_thread(
        self,
        spool_address: &str,
        thread_address: &str,
    ) -> Result<(Self, NativeSituatedThreadWithdrawal), NativeSpoolRefusal> {
        self.validate()?;
        let original_situated_identity_sha256 = self.identity_sha256()?;
        let (rest, withdrawal) = self.withdraw_thread_from_admitted(
            &original_situated_identity_sha256,
            spool_address,
            thread_address,
        )?;
        rest.validate()?;
        Ok((rest, withdrawal))
    }

    pub(crate) fn withdraw_thread_from_admitted(
        mut self,
        original_situated_identity_sha256: &str,
        spool_address: &str,
        thread_address: &str,
    ) -> Result<(Self, NativeSituatedThreadWithdrawal), NativeSpoolRefusal> {
        if !is_sha256_identity(original_situated_identity_sha256) {
            return Err(NativeSpoolRefusal::ThreadDepositReceipt);
        }
        let incident_occurrences = self
            .native
            .spools
            .iter()
            .find(|spool| spool.address == spool_address)
            .and_then(|spool| {
                spool
                    .threads
                    .iter()
                    .find(|thread| thread.address == thread_address)
            })
            .ok_or_else(|| NativeSpoolRefusal::UnknownThread(thread_address.to_owned()))?
            .occurrences
            .iter()
            .map(|occurrence| occurrence.occurrence)
            .collect::<BTreeSet<_>>();
        let mixed_constitutive_families =
            extract_indexed(&mut self.mixed_constitutive_families, |family| {
                family.left_thread == thread_address || family.right_thread == thread_address
            });
        let exact_reconstruction_fibres =
            extract_indexed(&mut self.exact_reconstruction_fibres, |fibre| {
                fibre.thread == thread_address
                    || !fibre.occurrences.is_disjoint(&incident_occurrences)
            });
        let admitted_native_identity_sha256 = native_bundle_identity_from_admitted(&self.native)?;
        let (native, withdrawal) = self.native.withdraw_thread_from_admitted(
            &admitted_native_identity_sha256,
            spool_address,
            thread_address,
        )?;
        self.native = native;
        Ok((
            self,
            NativeSituatedThreadWithdrawal {
                original_situated_identity_sha256: original_situated_identity_sha256.to_owned(),
                native: withdrawal,
                mixed_constitutive_families,
                exact_reconstruction_fibres,
            },
        ))
    }

    /// Restore an arbitrary situated withdrawal and prove the original canonical identity.
    pub fn restore_thread(
        mut self,
        withdrawal: NativeSituatedThreadWithdrawal,
    ) -> Result<Self, NativeSpoolRefusal> {
        self.native = self.native.restore_thread(withdrawal.native)?;
        restore_indexed(
            &mut self.mixed_constitutive_families,
            withdrawal.mixed_constitutive_families,
        )?;
        restore_indexed(
            &mut self.exact_reconstruction_fibres,
            withdrawal.exact_reconstruction_fibres,
        )?;
        self.validate()?;
        if self.identity_sha256()? != withdrawal.original_situated_identity_sha256 {
            return Err(NativeSpoolRefusal::Restoration);
        }
        Ok(self)
    }

    /// Withdraw one exact kernel direction which is invisible to the declared returned-covector
    /// receiver.  This is the support-disjoint L2 ablation; it is not a fabricated independent
    /// thread and does not discard the moved direction.
    pub fn withdraw_radical_direction(
        mut self,
        fibre_address: &str,
        direction_position: usize,
    ) -> Result<(Self, NativeSituatedRadicalWithdrawal), NativeSpoolRefusal> {
        self.validate()?;
        let original_situated_identity_sha256 = self.identity_sha256()?;
        let fibre = self
            .exact_reconstruction_fibres
            .iter_mut()
            .find(|fibre| fibre.address == fibre_address)
            .ok_or_else(|| {
                NativeSpoolRefusal::ExactReconstructionFibre(fibre_address.to_owned())
            })?;
        if direction_position >= fibre.radical.len() {
            return Err(NativeSpoolRefusal::ExactReconstructionFibre(
                fibre_address.to_owned(),
            ));
        }
        let direction = fibre.radical.remove(direction_position);
        self.validate()?;
        Ok((
            self,
            NativeSituatedRadicalWithdrawal {
                original_situated_identity_sha256,
                fibre_address: fibre_address.to_owned(),
                direction_position,
                direction,
            },
        ))
    }

    pub fn restore_radical_direction(
        mut self,
        withdrawal: NativeSituatedRadicalWithdrawal,
    ) -> Result<Self, NativeSpoolRefusal> {
        self.validate()?;
        let fibre = self
            .exact_reconstruction_fibres
            .iter_mut()
            .find(|fibre| fibre.address == withdrawal.fibre_address)
            .ok_or_else(|| {
                NativeSpoolRefusal::ExactReconstructionFibre(withdrawal.fibre_address.clone())
            })?;
        if withdrawal.direction_position > fibre.radical.len()
            || fibre.radical.contains(&withdrawal.direction)
        {
            return Err(NativeSpoolRefusal::Restoration);
        }
        fibre
            .radical
            .insert(withdrawal.direction_position, withdrawal.direction);
        self.validate()?;
        if self.identity_sha256()? != withdrawal.original_situated_identity_sha256 {
            return Err(NativeSpoolRefusal::Restoration);
        }
        Ok(self)
    }
}
