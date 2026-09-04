use super::*;

impl LaboratoryCultivatedRest {
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

    pub fn predecessor_identity(&self) -> &str {
        &self.predecessor_rest_identity_sha256
    }

    pub fn ecology(&self) -> &SituatedNativeTransportScaffold {
        &self.ecology
    }

    pub fn realization(&self) -> &ReceiverHistoryRealizationPassage {
        &self.realization
    }

    pub fn branches(&self) -> &[SituatedCultivationBranch] {
        &self.branches
    }

    pub fn returned_deposit(&self) -> &SituatedReturnedDifferenceDeposit {
        &self.returned_deposit
    }

    pub fn validate(&self) -> Result<(), SituatedCultivationError> {
        self.ecology
            .validate()
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        self.returned_deposit
            .native_receipt
            .validate()
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let realization = ReceiverHistoryRealizationPassage::found(self.ecology.native())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let ecology_identity = self
            .ecology
            .identity_sha256()
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let thread_addresses = self
            .ecology
            .native()
            .spools
            .iter()
            .flat_map(|spool| spool.threads.iter().map(|thread| thread.address.as_str()))
            .collect::<BTreeSet<_>>();
        let primary_addresses = self
            .branches
            .iter()
            .map(|branch| branch.thread_address.as_str())
            .chain(std::iter::once(
                self.returned_deposit.thread_address.as_str(),
            ))
            .collect::<BTreeSet<_>>();
        let expected_symmetric = primary_addresses
            .len()
            .checked_mul(primary_addresses.len().saturating_add(1))
            .and_then(|population| population.checked_div(2));
        let returned_fibre = self
            .ecology
            .exact_reconstruction_fibres()
            .iter()
            .find(|fibre| fibre.thread == self.returned_deposit.thread_address)
            .ok_or_else(|| {
                SituatedCultivationError::Wire(
                    "the returned passage lost its exact reconstruction fibre".to_owned(),
                )
            })?;
        let return_operator_identity_sha256 = super::resident::digest_json(&(
            &returned_fibre.return_operator,
            &returned_fibre.terminal_covector,
            &returned_fibre.returned_covector,
        ))?;
        let occurrence_population_identity_sha256 =
            super::resident::digest_json(&returned_fibre.occurrences)?;
        if self.schema != LABORATORY_CULTIVATED_ECOLOGY_REST_SCHEMA
            || !is_sha256_digest(&self.predecessor_rest_identity_sha256)
            || !is_sha256_digest(&self.predecessor_wire_sha256)
            || self.branches.is_empty()
            || self.returned_deposit.winding_coefficients.len() != self.branches.len()
            || self
                .returned_deposit
                .winding_coefficients
                .iter()
                .all(|coefficient| coefficient == &Rat::from_integer(BigInt::from(0)))
            || !is_sha256_digest(&self.returned_deposit.difference_identity_sha256)
            || !is_sha256_digest(&self.returned_deposit.return_operator_identity_sha256)
            || !is_sha256_digest(&self.returned_deposit.occurrence_population_identity_sha256)
            || self.returned_deposit.return_operator_identity_sha256
                != return_operator_identity_sha256
            || self.returned_deposit.occurrence_population_identity_sha256
                != occurrence_population_identity_sha256
            || self.returned_deposit.winding_coefficients != returned_fibre.returned_covector
            || !primary_addresses.is_subset(&thread_addresses)
            || primary_addresses.len() != self.branches.len().saturating_add(1)
            || self.returned_deposit.native_receipt.thread_address
                != self.returned_deposit.thread_address
            || self
                .returned_deposit
                .native_receipt
                .predecessor_identity_sha256
                != self.predecessor_deposit_receipt.successor_identity_sha256
            || self
                .returned_deposit
                .native_receipt
                .successor_identity_sha256
                != ecology_identity
            || expected_symmetric != Some(self.ecology.mixed_constitutive_families().len())
            || self.realization != realization
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(SituatedCultivationError::Wire(
                "the laboratory rest is not the exact returned continuation of its L2 body"
                    .to_owned(),
            ));
        }
        Ok(())
    }

    pub fn mount(self) -> Result<ResidentLaboratoryCultivatedEcology, SituatedCultivationError> {
        self.validate()?;
        let mut primaries = self
            .branches
            .iter()
            .map(|branch| {
                Ok((
                    branch.thread_address.clone(),
                    super::resident::integral_i64_covector(&branch.returned_source_covector)?,
                ))
            })
            .collect::<Result<Vec<_>, SituatedCultivationError>>()?;
        // The new passage is one primary holon.  Its four winding coefficients occur in its
        // constitutive contacts; an incidence coefficient of one prevents their illicit scalar
        // summation at the apparatus boundary.
        primaries.push((self.returned_deposit.thread_address.clone(), 1));
        let (incidence, front, interactions, factors, expected) =
            super::resident::derive_resident_coupling_from(&self.ecology, &primaries)?;
        let card = CudaRefineExecutor::new()
            .map_err(|error| SituatedCultivationError::Apparatus(error.to_string()))?;
        let resident = ResidentCoupledComplexParametron::mount(
            card,
            format!("native-laboratory-coupled/{}", self.identity_sha256),
            incidence,
            front,
            interactions,
        )
        .map_err(|error| SituatedCultivationError::Apparatus(error.to_string()))?;
        Ok(ResidentLaboratoryCultivatedEcology {
            rest: self,
            factors,
            expected,
            resident,
        })
    }

    pub fn withdraw_returned_difference(
        self,
    ) -> Result<
        (
            SituatedCultivatedEcologyRest,
            SituatedReturnedDifferenceWithdrawal,
        ),
        SituatedCultivationError,
    > {
        self.validate()?;
        let LaboratoryCultivatedRest {
            schema: _,
            predecessor_rest_identity_sha256,
            predecessor_wire_sha256,
            ecology,
            realization: _,
            branches,
            predecessor_deposit_receipt,
            returned_deposit,
            identity_sha256,
        } = self;
        let (predecessor, native_deposit) = ecology
            .withdraw_deposit(returned_deposit.native_receipt.clone())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let SituatedNativeTransportPredecessor::Situated(ecology) = predecessor else {
            return Err(SituatedCultivationError::Ecology(
                "the L5 inverse did not return its L2 situated predecessor".to_owned(),
            ));
        };
        let realization = ReceiverHistoryRealizationPassage::found(ecology.native())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let predecessor = SituatedCultivatedEcologyRest {
            schema: SITUATED_CULTIVATED_ECOLOGY_REST_SCHEMA.to_owned(),
            predecessor_wire_sha256,
            ecology,
            realization,
            branches,
            deposit_receipt: predecessor_deposit_receipt,
            identity_sha256: predecessor_rest_identity_sha256.clone(),
        };
        predecessor.validate()?;
        Ok((
            predecessor,
            SituatedReturnedDifferenceWithdrawal {
                original_rest_identity_sha256: identity_sha256,
                predecessor_rest_identity_sha256,
                returned_deposit,
                native_deposit,
            },
        ))
    }

    pub fn restore_returned_difference(
        predecessor: SituatedCultivatedEcologyRest,
        withdrawal: SituatedReturnedDifferenceWithdrawal,
    ) -> Result<Self, SituatedCultivationError> {
        predecessor.validate()?;
        if predecessor.identity() != withdrawal.predecessor_rest_identity_sha256 {
            return Err(SituatedCultivationError::Ecology(
                "returned-difference restoration received a different predecessor".to_owned(),
            ));
        }
        let SituatedCultivatedEcologyRest {
            schema: _,
            predecessor_wire_sha256,
            ecology,
            realization: _,
            branches,
            deposit_receipt,
            identity_sha256: predecessor_rest_identity_sha256,
        } = predecessor;
        let (ecology, receipt) = ecology
            .deposit_thread(withdrawal.native_deposit)
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        if receipt != withdrawal.returned_deposit.native_receipt {
            return Err(SituatedCultivationError::Ecology(
                "returned-difference restoration changed the exact native placement".to_owned(),
            ));
        }
        let realization = ReceiverHistoryRealizationPassage::found(ecology.native())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let mut rest = Self {
            schema: LABORATORY_CULTIVATED_ECOLOGY_REST_SCHEMA.to_owned(),
            predecessor_rest_identity_sha256,
            predecessor_wire_sha256,
            ecology,
            realization,
            branches,
            predecessor_deposit_receipt: deposit_receipt,
            returned_deposit: withdrawal.returned_deposit,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        rest.validate()?;
        if rest.identity_sha256 != withdrawal.original_rest_identity_sha256 {
            return Err(SituatedCultivationError::Ecology(
                "returned-difference restoration did not recover the L5 identity".to_owned(),
            ));
        }
        Ok(rest)
    }

    pub(crate) fn rederived_identity(&self) -> Result<String, SituatedCultivationError> {
        super::resident::digest_json(&(
            LABORATORY_CULTIVATED_ECOLOGY_REST_SCHEMA,
            &self.predecessor_rest_identity_sha256,
            &self.predecessor_wire_sha256,
            self.ecology
                .identity_sha256()
                .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?,
            &self.realization,
            &self.branches,
            &self.predecessor_deposit_receipt,
            &self.returned_deposit,
        ))
    }
}

impl LaboratoryCultivatedRest {
    /// Deposit a genuinely later difference without replacing the already cultivated return.
    pub fn deposit_additional_returned_difference(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<RecurrentLaboratoryCultivatedRest, SituatedCultivationError> {
        self.validate()?;
        let rest = self.deposit_additional_returned_difference_admitted(difference)?;
        rest.validate()?;
        Ok(rest)
    }

    /// Hot continuation from an already admitted rested owner. The outer owner must validate the
    /// complete successor once before it can return publicly.
    pub(crate) fn deposit_additional_returned_difference_admitted(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<RecurrentLaboratoryCultivatedRest, SituatedCultivationError> {
        difference
            .validate()
            .map_err(|error| SituatedCultivationError::Descent(error.to_string()))?;
        let predecessor_identity = self.identity_sha256.clone();
        let admitted_ecology_identity = self
            .returned_deposit
            .native_receipt
            .successor_identity_sha256
            .clone();
        let (native_deposit, staged) = super::resident::derive_returned_difference_deposit(
            &self.ecology,
            &self.branches,
            std::slice::from_ref(&self.returned_deposit),
            &difference,
        )?;
        let LaboratoryCultivatedRest {
            schema: _,
            predecessor_rest_identity_sha256: origin_predecessor_rest_identity_sha256,
            predecessor_wire_sha256,
            ecology,
            realization: _,
            branches,
            predecessor_deposit_receipt,
            returned_deposit,
            identity_sha256: _,
        } = self;
        let (ecology, native_receipt) = ecology
            .deposit_thread_from_admitted(&admitted_ecology_identity, native_deposit)
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let successor_ecology_identity = native_receipt.successor_identity_sha256.clone();
        let returned_deposits = vec![
            returned_deposit,
            SituatedReturnedDifferenceDeposit {
                difference_identity_sha256: staged.difference_identity_sha256,
                thread_address: staged.thread_address,
                winding_coefficients: staged.winding_coefficients,
                return_operator_identity_sha256: staged.return_operator_identity_sha256,
                occurrence_population_identity_sha256: staged.occurrence_population_identity_sha256,
                native_receipt,
            },
        ];
        let realization = ReceiverHistoryRealizationPassage::found(ecology.native())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let mut rest = RecurrentLaboratoryCultivatedRest {
            schema: RECURRENT_LABORATORY_CULTIVATED_ECOLOGY_REST_SCHEMA.to_owned(),
            rest_identity_history: vec![predecessor_identity],
            origin_predecessor_rest_identity_sha256,
            predecessor_wire_sha256,
            ecology,
            realization,
            branches,
            predecessor_deposit_receipt,
            returned_deposits,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 =
            rest.rederived_identity_with_ecology_identity(&successor_ecology_identity)?;
        Ok(rest)
    }
}

impl RecurrentLaboratoryCultivatedRest {
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

    pub fn immediate_predecessor_identity(&self) -> &str {
        self.rest_identity_history
            .last()
            .expect("a recurrent rest has at least two returned deposits")
    }

    pub fn origin_predecessor_identity(&self) -> &str {
        &self.origin_predecessor_rest_identity_sha256
    }

    pub fn ecology(&self) -> &SituatedNativeTransportScaffold {
        &self.ecology
    }

    pub fn realization(&self) -> &ReceiverHistoryRealizationPassage {
        &self.realization
    }

    pub fn branches(&self) -> &[SituatedCultivationBranch] {
        &self.branches
    }

    pub fn returned_deposits(&self) -> &[SituatedReturnedDifferenceDeposit] {
        &self.returned_deposits
    }

    pub fn validate(&self) -> Result<(), SituatedCultivationError> {
        self.ecology
            .validate()
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let realization = ReceiverHistoryRealizationPassage::found(self.ecology.native())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let ecology_identity = super::resident::digest_json(&self.ecology)?;
        let threads = self
            .ecology
            .native()
            .spools
            .iter()
            .flat_map(|spool| &spool.threads)
            .map(|thread| thread.address.as_str())
            .collect::<BTreeSet<_>>();
        let primary_population = self
            .branches
            .len()
            .checked_add(self.returned_deposits.len())
            .ok_or_else(|| SituatedCultivationError::Wire("primary extent overflow".to_owned()))?;
        let expected_symmetric = primary_population
            .checked_mul(primary_population.saturating_add(1))
            .and_then(|population| population.checked_div(2));
        let receipts_chain = self.returned_deposits.first().is_some_and(|first| {
            first.native_receipt.predecessor_identity_sha256
                == self.predecessor_deposit_receipt.successor_identity_sha256
        }) && self.returned_deposits.windows(2).all(|pair| {
            pair[0].native_receipt.successor_identity_sha256
                == pair[1].native_receipt.predecessor_identity_sha256
        }) && self
            .returned_deposits
            .last()
            .is_some_and(|last| last.native_receipt.successor_identity_sha256 == ecology_identity);
        let fibres_complete = self.returned_deposits.iter().all(|deposit| {
            deposit.winding_coefficients.len() == self.branches.len()
                && deposit
                    .winding_coefficients
                    .iter()
                    .any(|coordinate| coordinate != &Rat::from_integer(BigInt::from(0)))
                && threads.contains(deposit.thread_address.as_str())
                && self
                    .ecology
                    .exact_reconstruction_fibres()
                    .iter()
                    .any(|fibre| {
                        fibre.thread == deposit.thread_address
                            && fibre.returned_covector == deposit.winding_coefficients
                            && super::resident::digest_json(&(
                                &fibre.return_operator,
                                &fibre.terminal_covector,
                                &fibre.returned_covector,
                            ))
                            .ok()
                            .as_deref()
                                == Some(deposit.return_operator_identity_sha256.as_str())
                            && super::resident::digest_json(&fibre.occurrences)
                                .ok()
                                .as_deref()
                                == Some(deposit.occurrence_population_identity_sha256.as_str())
                    })
        });
        if self.schema != RECURRENT_LABORATORY_CULTIVATED_ECOLOGY_REST_SCHEMA
            || self.returned_deposits.len() < 2
            || self.rest_identity_history.len() + 1 != self.returned_deposits.len()
            || self
                .rest_identity_history
                .iter()
                .any(|identity| !is_sha256_digest(identity))
            || !is_sha256_digest(&self.origin_predecessor_rest_identity_sha256)
            || !is_sha256_digest(&self.predecessor_wire_sha256)
            || self.branches.is_empty()
            || !receipts_chain
            || !fibres_complete
            || expected_symmetric != Some(self.ecology.mixed_constitutive_families().len())
            || self.realization != realization
            || self.identity_sha256
                != self.rederived_identity_with_ecology_identity(&ecology_identity)?
        {
            return Err(SituatedCultivationError::Wire(
                "the recurrent laboratory rest does not reconstruct its returned world-line"
                    .to_owned(),
            ));
        }
        Ok(())
    }

    pub fn deposit_additional_returned_difference(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<Self, SituatedCultivationError> {
        self.validate()?;
        let rest = self.deposit_additional_returned_difference_admitted(difference)?;
        rest.validate()?;
        Ok(rest)
    }

    pub(crate) fn deposit_additional_returned_difference_admitted(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<Self, SituatedCultivationError> {
        difference
            .validate()
            .map_err(|error| SituatedCultivationError::Descent(error.to_string()))?;
        let predecessor_identity = self.identity_sha256.clone();
        let admitted_ecology_identity = self
            .returned_deposits
            .last()
            .ok_or_else(|| SituatedCultivationError::Wire("return population empty".to_owned()))?
            .native_receipt
            .successor_identity_sha256
            .clone();
        let (native_deposit, staged) = super::resident::derive_returned_difference_deposit(
            &self.ecology,
            &self.branches,
            &self.returned_deposits,
            &difference,
        )?;
        let Self {
            schema,
            mut rest_identity_history,
            origin_predecessor_rest_identity_sha256,
            predecessor_wire_sha256,
            ecology,
            realization: _,
            branches,
            predecessor_deposit_receipt,
            mut returned_deposits,
            identity_sha256: _,
        } = self;
        let (ecology, native_receipt) = ecology
            .deposit_thread_from_admitted(&admitted_ecology_identity, native_deposit)
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let successor_ecology_identity = native_receipt.successor_identity_sha256.clone();
        rest_identity_history.push(predecessor_identity);
        returned_deposits.push(SituatedReturnedDifferenceDeposit {
            difference_identity_sha256: staged.difference_identity_sha256,
            thread_address: staged.thread_address,
            winding_coefficients: staged.winding_coefficients,
            return_operator_identity_sha256: staged.return_operator_identity_sha256,
            occurrence_population_identity_sha256: staged.occurrence_population_identity_sha256,
            native_receipt,
        });
        let realization = ReceiverHistoryRealizationPassage::found(ecology.native())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let mut rest = Self {
            schema,
            rest_identity_history,
            origin_predecessor_rest_identity_sha256,
            predecessor_wire_sha256,
            ecology,
            realization,
            branches,
            predecessor_deposit_receipt,
            returned_deposits,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 =
            rest.rederived_identity_with_ecology_identity(&successor_ecology_identity)?;
        Ok(rest)
    }

    pub fn withdraw_latest_returned_difference(
        self,
    ) -> Result<
        (
            RecurrentLaboratoryPredecessor,
            RecurrentSituatedDifferenceWithdrawal,
        ),
        SituatedCultivationError,
    > {
        self.validate()?;
        let (predecessor, withdrawal) = self.withdraw_latest_returned_difference_from_admitted()?;
        match &predecessor {
            RecurrentLaboratoryPredecessor::First(rest) => rest.validate()?,
            RecurrentLaboratoryPredecessor::Recurrent(rest) => rest.validate()?,
        }
        Ok((predecessor, withdrawal))
    }

    pub(crate) fn withdraw_latest_returned_difference_from_admitted(
        self,
    ) -> Result<
        (
            RecurrentLaboratoryPredecessor,
            RecurrentSituatedDifferenceWithdrawal,
        ),
        SituatedCultivationError,
    > {
        let Self {
            schema,
            mut rest_identity_history,
            origin_predecessor_rest_identity_sha256,
            predecessor_wire_sha256,
            ecology,
            realization: _,
            branches,
            predecessor_deposit_receipt,
            mut returned_deposits,
            identity_sha256,
        } = self;
        let returned_deposit = returned_deposits.pop().ok_or_else(|| {
            SituatedCultivationError::Wire("returned population empty".to_owned())
        })?;
        let expected_predecessor_identity = rest_identity_history
            .pop()
            .ok_or_else(|| SituatedCultivationError::Wire("return history empty".to_owned()))?;
        let admitted_ecology_identity_sha256 = returned_deposit
            .native_receipt
            .successor_identity_sha256
            .clone();
        let (predecessor, native_deposit) = ecology
            .withdraw_deposit_from_admitted(
                &admitted_ecology_identity_sha256,
                returned_deposit.native_receipt.clone(),
            )
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let SituatedNativeTransportPredecessor::Situated(ecology) = predecessor else {
            return Err(SituatedCultivationError::Ecology(
                "a recurrent withdrawal escaped the situated body".to_owned(),
            ));
        };
        let realization = ReceiverHistoryRealizationPassage::found(ecology.native())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let predecessor = if returned_deposits.len() == 1 {
            let rest = LaboratoryCultivatedRest {
                schema: LABORATORY_CULTIVATED_ECOLOGY_REST_SCHEMA.to_owned(),
                predecessor_rest_identity_sha256: origin_predecessor_rest_identity_sha256,
                predecessor_wire_sha256,
                ecology,
                realization,
                branches,
                predecessor_deposit_receipt,
                returned_deposit: returned_deposits.remove(0),
                identity_sha256: expected_predecessor_identity.clone(),
            };
            RecurrentLaboratoryPredecessor::First(rest)
        } else {
            let rest = RecurrentLaboratoryCultivatedRest {
                schema,
                rest_identity_history,
                origin_predecessor_rest_identity_sha256,
                predecessor_wire_sha256,
                ecology,
                realization,
                branches,
                predecessor_deposit_receipt,
                returned_deposits,
                identity_sha256: expected_predecessor_identity.clone(),
            };
            RecurrentLaboratoryPredecessor::Recurrent(rest)
        };
        Ok((
            predecessor,
            RecurrentSituatedDifferenceWithdrawal {
                original_rest_identity_sha256: identity_sha256,
                predecessor_rest_identity_sha256: expected_predecessor_identity,
                returned_deposit,
                native_deposit,
            },
        ))
    }

    pub fn restore_latest_returned_difference(
        predecessor: RecurrentLaboratoryPredecessor,
        withdrawal: RecurrentSituatedDifferenceWithdrawal,
    ) -> Result<Self, SituatedCultivationError> {
        let rest = Self::restore_latest_returned_difference_from_admitted(predecessor, withdrawal)?;
        rest.validate()?;
        Ok(rest)
    }

    pub(crate) fn restore_latest_returned_difference_from_admitted(
        predecessor: RecurrentLaboratoryPredecessor,
        withdrawal: RecurrentSituatedDifferenceWithdrawal,
    ) -> Result<Self, SituatedCultivationError> {
        if predecessor.identity() != withdrawal.predecessor_rest_identity_sha256 {
            return Err(SituatedCultivationError::Wire(
                "the recurrent return was offered to another predecessor".to_owned(),
            ));
        }
        let predecessor_identity = predecessor.identity().to_owned();
        let admitted_ecology_identity_sha256 = match &predecessor {
            RecurrentLaboratoryPredecessor::First(rest) => rest
                .returned_deposit
                .native_receipt
                .successor_identity_sha256
                .clone(),
            RecurrentLaboratoryPredecessor::Recurrent(rest) => rest
                .returned_deposits
                .last()
                .ok_or_else(|| {
                    SituatedCultivationError::Wire("return population empty".to_owned())
                })?
                .native_receipt
                .successor_identity_sha256
                .clone(),
        };
        let (
            predecessor_wire_sha256,
            ecology,
            branches,
            predecessor_deposit_receipt,
            mut returned_deposits,
            mut rest_identity_history,
            origin_predecessor_rest_identity_sha256,
        ) = match predecessor {
            RecurrentLaboratoryPredecessor::First(rest) => {
                let LaboratoryCultivatedRest {
                    schema: _,
                    predecessor_rest_identity_sha256: origin_predecessor_rest_identity_sha256,
                    predecessor_wire_sha256,
                    ecology,
                    realization: _,
                    branches,
                    predecessor_deposit_receipt,
                    returned_deposit,
                    identity_sha256: _,
                } = rest;
                (
                    predecessor_wire_sha256,
                    ecology,
                    branches,
                    predecessor_deposit_receipt,
                    vec![returned_deposit],
                    Vec::new(),
                    origin_predecessor_rest_identity_sha256,
                )
            }
            RecurrentLaboratoryPredecessor::Recurrent(rest) => {
                let Self {
                    schema: _,
                    rest_identity_history,
                    origin_predecessor_rest_identity_sha256,
                    predecessor_wire_sha256,
                    ecology,
                    realization: _,
                    branches,
                    predecessor_deposit_receipt,
                    returned_deposits,
                    identity_sha256: _,
                } = rest;
                (
                    predecessor_wire_sha256,
                    ecology,
                    branches,
                    predecessor_deposit_receipt,
                    returned_deposits,
                    rest_identity_history,
                    origin_predecessor_rest_identity_sha256,
                )
            }
        };
        let (ecology, receipt) = ecology
            .deposit_thread_from_admitted(
                &admitted_ecology_identity_sha256,
                withdrawal.native_deposit,
            )
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        if receipt != withdrawal.returned_deposit.native_receipt {
            return Err(SituatedCultivationError::Ecology(
                "recurrent restoration changed the exact native deposit".to_owned(),
            ));
        }
        rest_identity_history.push(predecessor_identity);
        returned_deposits.push(withdrawal.returned_deposit);
        let realization = ReceiverHistoryRealizationPassage::found(ecology.native())
            .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
        let rest = Self {
            schema: RECURRENT_LABORATORY_CULTIVATED_ECOLOGY_REST_SCHEMA.to_owned(),
            rest_identity_history,
            origin_predecessor_rest_identity_sha256,
            predecessor_wire_sha256,
            ecology,
            realization,
            branches,
            predecessor_deposit_receipt,
            returned_deposits,
            identity_sha256: withdrawal.original_rest_identity_sha256,
        };
        Ok(rest)
    }

    fn rederived_identity_with_ecology_identity(
        &self,
        ecology_identity: &str,
    ) -> Result<String, SituatedCultivationError> {
        super::resident::digest_json(&(
            RECURRENT_LABORATORY_CULTIVATED_ECOLOGY_REST_SCHEMA,
            &self.rest_identity_history,
            &self.origin_predecessor_rest_identity_sha256,
            &self.predecessor_wire_sha256,
            ecology_identity,
            &self.realization,
            &self.branches,
            &self.predecessor_deposit_receipt,
            &self.returned_deposits,
        ))
    }
}
