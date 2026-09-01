use super::*;
use crate::native_intelligence::laboratory_cultivation::{
    LaboratoryCellAffineSection, LaboratoryFactorCycleCorrespondence,
};
use crate::native_intelligence::membrane_transport::MembraneStanding;

impl SituatedCultivatedEcologyRest {
    /// Consume the predecessor and complete L1 product into one source-neutral native rest.
    pub fn cultivate(
        predecessor: NativeEcologyRest,
        product: ExchangeSituatedProduct,
    ) -> Result<Self, SituatedCultivationError> {
        predecessor
            .validate()
            .map_err(|error| SituatedCultivationError::Predecessor(error.to_string()))?;
        product
            .validate()
            .map_err(|error| SituatedCultivationError::Product(error.to_string()))?;
        let predecessor_wire_sha256 = predecessor
            .wire_sha256()
            .map_err(|error| SituatedCultivationError::Predecessor(error.to_string()))?;
        if predecessor_wire_sha256 != product.predecessor_rest_wire_sha256 {
            return Err(SituatedCultivationError::Predecessor(
                "the situated population was returned against a different rest".to_owned(),
            ));
        }

        let spool_address = super::resident::common_k3_spool_address(&product.k3_branches)?;
        let thread_addresses = product
            .k3_branches
            .iter()
            .enumerate()
            .map(|(branch, k3)| {
                format!(
                    "native-spool/situated-causal-adjoint/{branch}/{}",
                    k3.address
                )
            })
            .collect::<Vec<_>>();
        let dependent_receiver_support = product
            .native_covers
            .iter()
            .map(|cover| cover.native)
            .collect::<BTreeSet<_>>();

        let mut branches = Vec::with_capacity(product.k3_branches.len());
        let mut deposits = Vec::with_capacity(product.k3_branches.len());
        for branch in 0..product.k3_branches.len() {
            let (deposit, receipt) = super::resident::derive_branch_deposit(
                branch,
                &spool_address,
                &thread_addresses,
                &product.k3_branches,
                &product.native_covers,
                &product.mixed_interactions,
                product.constitutive_form.receiver,
                &dependent_receiver_support,
            )?;
            branches.push(receipt);
            deposits.push(deposit);
        }

        // `product` drops here.  Its source quotient, source reconstruction members, response
        // interiors, candidate seals, and exterior codec testimony cannot be reached from rest.
        let (ecology, deposit_receipt) = predecessor
            .ecology
            .deposit_threads(deposits)
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        if ecology
            .identity_sha256()
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?
            != deposit_receipt.successor_identity_sha256
        {
            return Err(SituatedCultivationError::Ecology(
                "the atomic rank-four receipt does not name its complete successor".to_owned(),
            ));
        }
        let realization = ReceiverHistoryRealizationPassage::found(ecology.native())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let mut rest = Self {
            schema: SITUATED_CULTIVATED_ECOLOGY_REST_SCHEMA.to_owned(),
            predecessor_wire_sha256,
            ecology,
            realization,
            branches,
            deposit_receipt,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, SituatedCultivationError> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| SituatedCultivationError::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, SituatedCultivationError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| SituatedCultivationError::Wire(error.to_string()))
    }

    pub fn identity(&self) -> &str {
        &self.identity_sha256
    }

    pub fn predecessor_wire_sha256(&self) -> &str {
        &self.predecessor_wire_sha256
    }

    pub fn ecology(&self) -> &NativeSituatedSpoolBundle {
        &self.ecology
    }

    pub fn realization(&self) -> &ReceiverHistoryRealizationPassage {
        &self.realization
    }

    pub fn branches(&self) -> &[SituatedCultivationBranch] {
        &self.branches
    }

    /// Move this rested ecology onto one coupled card body.  Factor and limb populations are
    /// derived from its deposited branches and compact mixed families; no width or grain is
    /// accepted from the caller.
    pub fn mount(self) -> Result<ResidentSituatedCultivatedEcology, SituatedCultivationError> {
        self.validate()?;
        let (incidence, front, interactions, factors, expected) =
            super::resident::derive_resident_coupling(&self)?;
        let card = CudaRefineExecutor::new()
            .map_err(|error| SituatedCultivationError::Apparatus(error.to_string()))?;
        let resident = ResidentCoupledComplexParametron::mount(
            card,
            format!("native-situated-coupled/{}", self.identity_sha256),
            incidence,
            front,
            interactions,
        )
        .map_err(|error| SituatedCultivationError::Apparatus(error.to_string()))?;
        Ok(ResidentSituatedCultivatedEcology {
            rest: self,
            factors,
            expected,
            resident,
        })
    }

    pub fn validate(&self) -> Result<(), SituatedCultivationError> {
        self.ecology
            .validate()
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let realization = ReceiverHistoryRealizationPassage::found(self.ecology.native())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let thread_addresses = self
            .ecology
            .native()
            .spools
            .iter()
            .flat_map(|spool| spool.threads.iter().map(|thread| thread.address.as_str()))
            .collect::<BTreeSet<_>>();
        let branch_addresses = self
            .branches
            .iter()
            .map(|branch| branch.thread_address.as_str())
            .collect::<BTreeSet<_>>();
        let receipt_addresses = self
            .deposit_receipt
            .placements
            .iter()
            .map(|placement| placement.thread_address.as_str())
            .collect::<BTreeSet<_>>();
        let active_symmetric_population = self
            .branches
            .len()
            .checked_mul(self.branches.len().saturating_add(1))
            .and_then(|population| population.checked_div(2));
        if self.schema != SITUATED_CULTIVATED_ECOLOGY_REST_SCHEMA
            || !is_sha256_digest(&self.predecessor_wire_sha256)
            || self.branches.is_empty()
            || branch_addresses.len() != self.branches.len()
            || !branch_addresses.is_subset(&receipt_addresses)
            || !branch_addresses.is_subset(&thread_addresses)
            || self
                .branches
                .windows(2)
                .any(|pair| pair[0].branch >= pair[1].branch)
            || self.branches.iter().any(|branch| {
                branch.k3_pullback_address.is_empty()
                    || branch.returned_source_covector.is_empty()
                    || branch.local_population == 0
                    || branch.exact_fibre_population != branch.local_population
                    || !is_sha256_digest(&branch.return_operator_identity_sha256)
                    || !is_sha256_digest(&branch.occurrence_population_identity_sha256)
            })
            || self.deposit_receipt.validate().is_err()
            || active_symmetric_population != Some(self.ecology.mixed_constitutive_families().len())
            || self.realization != realization
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(SituatedCultivationError::Wire(
                "the situated rest is not the exact projection of its singular ecology".to_owned(),
            ));
        }
        Ok(())
    }

    /// Remove an arbitrary factor and every exact relation incident to it by ownership transfer.
    pub fn withdraw_branch(
        mut self,
        branch_index: usize,
    ) -> Result<(Self, SituatedCultivationWithdrawal), SituatedCultivationError> {
        self.validate()?;
        let at = self
            .branches
            .iter()
            .position(|branch| branch.branch == branch_index)
            .ok_or_else(|| {
                SituatedCultivationError::Descent(format!("unknown situated branch {branch_index}"))
            })?;
        let original_rest_identity_sha256 = self.identity_sha256.clone();
        let branch = self.branches.remove(at);
        let spool = self
            .deposit_receipt
            .placements
            .iter()
            .find(|placement| placement.thread_address == branch.thread_address)
            .map(|placement| placement.spool_address.clone())
            .ok_or_else(|| {
                SituatedCultivationError::Ecology(
                    "the atomic batch receipt lost the withdrawn thread placement".to_owned(),
                )
            })?;
        let thread = branch.thread_address.clone();
        let (ecology, native) = self
            .ecology
            .withdraw_thread(&spool, &thread)
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        self.ecology = ecology;
        self.realization = ReceiverHistoryRealizationPassage::found(self.ecology.native())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        self.identity_sha256 = self.rederived_identity()?;
        self.validate()?;
        Ok((
            self,
            SituatedCultivationWithdrawal {
                original_rest_identity_sha256,
                branch,
                native,
            },
        ))
    }

    /// Restore a moved factor and prove exact recovery of the original situated rest identity.
    pub fn restore_branch(
        mut self,
        withdrawal: SituatedCultivationWithdrawal,
    ) -> Result<Self, SituatedCultivationError> {
        self.validate()?;
        self.ecology = self
            .ecology
            .restore_thread(withdrawal.native)
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let at = self
            .branches
            .partition_point(|branch| branch.branch < withdrawal.branch.branch);
        self.branches.insert(at, withdrawal.branch);
        self.realization = ReceiverHistoryRealizationPassage::found(self.ecology.native())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        self.identity_sha256 = self.rederived_identity()?;
        self.validate()?;
        if self.identity_sha256 != withdrawal.original_rest_identity_sha256 {
            return Err(SituatedCultivationError::Ecology(
                "branch restoration did not recover the original situated identity".to_owned(),
            ));
        }
        Ok(self)
    }

    /// Remove one source-neutral thread which entered with the admitted K3 predecessor.
    ///
    /// Inheritance is determined structurally: the thread is present in the continuing ecology but
    /// absent from every cultivation placement.  No former model name, modality label, or exterior
    /// witness participates in the choice.
    pub fn withdraw_inherited_thread(
        mut self,
        spool_address: &str,
        thread_address: &str,
    ) -> Result<(Self, SituatedInheritedThreadWithdrawal), SituatedCultivationError> {
        self.validate()?;
        if self
            .deposit_receipt
            .placements
            .iter()
            .any(|placement| placement.thread_address == thread_address)
            || self
                .branches
                .iter()
                .any(|branch| branch.thread_address == thread_address)
        {
            return Err(SituatedCultivationError::Descent(format!(
                "{thread_address} is cultivated morphology rather than inherited spool standing"
            )));
        }
        let original_rest_identity_sha256 = self.identity_sha256.clone();
        let (ecology, native) = self
            .ecology
            .withdraw_thread(spool_address, thread_address)
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        self.ecology = ecology;
        self.realization = ReceiverHistoryRealizationPassage::found(self.ecology.native())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        self.identity_sha256 = self.rederived_identity()?;
        let ablated_rest_identity_sha256 = self.identity_sha256.clone();
        self.validate()?;
        Ok((
            self,
            SituatedInheritedThreadWithdrawal {
                original_rest_identity_sha256,
                ablated_rest_identity_sha256,
                spool_address: spool_address.to_owned(),
                thread_address: thread_address.to_owned(),
                native,
            },
        ))
    }

    /// Consume an inherited-thread withdrawal and recover the exact prior Athena rest.
    pub fn restore_inherited_thread(
        mut self,
        withdrawal: SituatedInheritedThreadWithdrawal,
    ) -> Result<Self, SituatedCultivationError> {
        self.validate()?;
        if self.identity_sha256 != withdrawal.ablated_rest_identity_sha256
            || self
                .deposit_receipt
                .placements
                .iter()
                .any(|placement| placement.thread_address == withdrawal.thread_address)
        {
            return Err(SituatedCultivationError::Ecology(
                "the inherited spool fibre was offered to another situated body".to_owned(),
            ));
        }
        self.ecology = self
            .ecology
            .restore_thread(withdrawal.native)
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        self.realization = ReceiverHistoryRealizationPassage::found(self.ecology.native())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        self.identity_sha256 = self.rederived_identity()?;
        if self.identity_sha256 != withdrawal.original_rest_identity_sha256
            || !self.ecology.native().spools.iter().any(|spool| {
                spool.address == withdrawal.spool_address
                    && spool
                        .threads
                        .iter()
                        .any(|thread| thread.address == withdrawal.thread_address)
            })
        {
            return Err(SituatedCultivationError::Ecology(
                "inherited spool restoration did not recover the original situated identity"
                    .to_owned(),
            ));
        }
        self.validate()?;
        Ok(self)
    }

    /// Remove one exact receiver-kernel direction from the reconstruction fibre.  The active
    /// returned current and every mixed family remain owned by the continuing ecology.
    pub fn withdraw_radical_direction(
        mut self,
        fibre_address: &str,
        direction_position: usize,
    ) -> Result<(Self, SituatedRadicalWithdrawal), SituatedCultivationError> {
        self.validate()?;
        let original_rest_identity_sha256 = self.identity_sha256.clone();
        let (ecology, native) = self
            .ecology
            .withdraw_radical_direction(fibre_address, direction_position)
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        self.ecology = ecology;
        self.realization = ReceiverHistoryRealizationPassage::found(self.ecology.native())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        self.identity_sha256 = self.rederived_identity()?;
        self.validate()?;
        Ok((
            self,
            SituatedRadicalWithdrawal {
                original_rest_identity_sha256,
                native,
            },
        ))
    }

    /// Restore a receiver-radical direction and prove exact recovery of the original rest.
    pub fn restore_radical_direction(
        mut self,
        withdrawal: SituatedRadicalWithdrawal,
    ) -> Result<Self, SituatedCultivationError> {
        self.validate()?;
        self.ecology = self
            .ecology
            .restore_radical_direction(withdrawal.native)
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        self.realization = ReceiverHistoryRealizationPassage::found(self.ecology.native())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        self.identity_sha256 = self.rederived_identity()?;
        self.validate()?;
        if self.identity_sha256 != withdrawal.original_rest_identity_sha256 {
            return Err(SituatedCultivationError::Ecology(
                "radical restoration did not recover the original situated identity".to_owned(),
            ));
        }
        Ok(self)
    }

    /// Apply the atomic rank-four deposit inverse and recover the exact K3 predecessor bundle.
    pub fn withdraw_all(
        self,
    ) -> Result<CompleteSituatedCultivationWithdrawal, SituatedCultivationError> {
        self.validate()?;
        let cultivated_identity_sha256 = self.identity_sha256.clone();
        let predecessor_wire_sha256 = self.predecessor_wire_sha256.clone();
        let branch_population = self.branches.len();
        let (predecessor, withdrawn_deposits) = self
            .ecology
            .withdraw_deposit_batch(self.deposit_receipt)
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let restored_predecessor = NativeEcologyRest::found(predecessor)
            .map_err(|error| SituatedCultivationError::Predecessor(error.to_string()))?;
        let restored_wire = restored_predecessor
            .wire_sha256()
            .map_err(|error| SituatedCultivationError::Predecessor(error.to_string()))?;
        let complete_reverse_word_applied = restored_wire == predecessor_wire_sha256
            && withdrawn_deposits.len() == branch_population;
        if !complete_reverse_word_applied {
            return Err(SituatedCultivationError::Ecology(
                "the complete causal-adjoint deposit inverse did not recover K3".to_owned(),
            ));
        }
        Ok(CompleteSituatedCultivationWithdrawal {
            restored_predecessor,
            withdrawn_deposits,
            predecessor_wire_sha256,
            cultivated_identity_sha256,
            complete_reverse_word_applied,
        })
    }

    fn rederived_identity(&self) -> Result<String, SituatedCultivationError> {
        super::resident::digest_json(&(
            SITUATED_CULTIVATED_ECOLOGY_REST_SCHEMA,
            &self.predecessor_wire_sha256,
            self.ecology
                .identity_sha256()
                .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?,
            &self.realization,
            &self.branches,
            &self.deposit_receipt,
        ))
    }

    /// Consume one complete returned difference and cross into the L5 type state.  The four
    /// winding coefficients enter together through one native thread deposit; this method never
    /// founds coordinate-prefix rests.
    pub fn deposit_returned_difference(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<LaboratoryCultivatedRest, SituatedCultivationError> {
        self.validate()?;
        difference
            .validate()
            .map_err(|error| SituatedCultivationError::Descent(error.to_string()))?;
        let predecessor_rest_identity_sha256 = self.identity_sha256.clone();
        let (native_deposit, staged) = super::resident::derive_returned_difference_deposit(
            &self.ecology,
            &self.branches,
            &[],
            &difference,
        )?;
        let SituatedCultivatedEcologyRest {
            schema: _,
            predecessor_wire_sha256,
            ecology,
            realization: _,
            branches,
            deposit_receipt,
            identity_sha256: _,
        } = self;
        let (ecology, native_receipt) = ecology
            .deposit_thread(native_deposit)
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let returned_deposit = SituatedReturnedDifferenceDeposit {
            difference_identity_sha256: staged.difference_identity_sha256,
            thread_address: staged.thread_address,
            winding_coefficients: staged.winding_coefficients,
            return_operator_identity_sha256: staged.return_operator_identity_sha256,
            occurrence_population_identity_sha256: staged.occurrence_population_identity_sha256,
            native_receipt,
        };
        let realization = ReceiverHistoryRealizationPassage::found(ecology.native())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let mut rest = LaboratoryCultivatedRest {
            schema: LABORATORY_CULTIVATED_ECOLOGY_REST_SCHEMA.to_owned(),
            predecessor_rest_identity_sha256,
            predecessor_wire_sha256,
            ecology,
            realization,
            branches,
            predecessor_deposit_receipt: deposit_receipt,
            returned_deposit,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        rest.validate()?;
        Ok(rest)
    }
}

/// The situated ecology already has the singular causal mouth: its source-neutral inherited spool
/// and cultivated branches are one standing body. The later affine organ is required only by
/// constitutive-interior/radiation methods, which correctly return an empty-factor obstruction at
/// this earlier rest rather than preventing exact exterior occurrence contact.
impl MembraneStanding for SituatedCultivatedEcologyRest {
    fn validate_membrane_standing(&self) -> Result<(), String> {
        self.validate().map_err(|error| error.to_string())
    }

    fn membrane_identity(&self) -> &str {
        self.identity()
    }

    fn membrane_ecology(&self) -> &NativeSituatedSpoolBundle {
        self.ecology()
    }

    fn membrane_realization(&self) -> &ReceiverHistoryRealizationPassage {
        self.realization()
    }

    fn membrane_branches(&self) -> &[SituatedCultivationBranch] {
        self.branches()
    }

    fn membrane_correspondences(&self) -> &[LaboratoryFactorCycleCorrespondence] {
        &[]
    }

    fn membrane_affine_cells(&self) -> &[LaboratoryCellAffineSection] {
        &[]
    }
}
