use super::*;
impl SourceNeutralReturnedEcology {
    pub(crate) fn found(
        ecology: NativeSituatedSpoolBundle,
        branches: Vec<SourceNeutralCultivationBranch>,
        predecessor_deposit_receipt: NativeThreadDepositBatchReceipt,
        returned_deposits: Vec<SourceNeutralReturnedDeposit>,
    ) -> Result<Self, SourceNeutralAthenaError> {
        let mut body = Self {
            schema: "soma-life.source-neutral-returned-ecology.v1".to_owned(),
            ecology,
            branches,
            predecessor_deposit_receipt,
            returned_deposits,
            identity_sha256: String::new(),
        };
        body.identity_sha256 = body.rederived_identity();
        body.validate()?;
        Ok(body)
    }

    pub(super) fn deposit_returned_difference(
        self,
        difference: &SituatedDifferenceSection,
    ) -> Result<(Self, SourceNeutralReturnedDeposit), SourceNeutralAthenaError> {
        difference
            .validate()
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        let branch_threads = self
            .branches
            .iter()
            .map(|branch| branch.thread_address.clone())
            .collect::<Vec<_>>();
        let prior_returns = self
            .returned_deposits
            .iter()
            .map(|returned| {
                (
                    returned.thread_address.clone(),
                    returned.winding_coefficients.clone(),
                )
            })
            .collect::<Vec<_>>();
        let (native_deposit, staged) = derive_returned_difference_deposit_from_history(
            &self.ecology,
            &branch_threads,
            &prior_returns,
            difference,
        )
        .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        let (ecology, native_receipt) = self
            .ecology
            .deposit_thread(native_deposit)
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        let returned = SourceNeutralReturnedDeposit {
            difference_identity_sha256: staged.difference_identity_sha256,
            thread_address: staged.thread_address,
            winding_coefficients: staged.winding_coefficients,
            return_operator_identity_sha256: staged.return_operator_identity_sha256,
            native_receipt,
        };
        let mut returned_deposits = self.returned_deposits;
        returned_deposits.push(returned.clone());
        let body = Self::found(
            ecology,
            self.branches,
            self.predecessor_deposit_receipt,
            returned_deposits,
        )?;
        Ok((body, returned))
    }

    pub fn validate(&self) -> Result<(), SourceNeutralAthenaError> {
        self.ecology
            .validate()
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        self.predecessor_deposit_receipt
            .validate()
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        let ecology_identity = digest(&self.ecology);
        let branch_rank = self.branches.len();
        let branch_threads = self
            .branches
            .iter()
            .map(|branch| branch.thread_address.as_str())
            .collect::<std::collections::BTreeSet<_>>();
        let threads = self
            .ecology
            .native()
            .spools
            .iter()
            .flat_map(|spool| &spool.threads)
            .map(|thread| thread.address.as_str())
            .collect::<std::collections::BTreeSet<_>>();
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
        let fibres = self.ecology.exact_reconstruction_fibres();
        let fibres_complete = self.returned_deposits.iter().all(|deposit| {
            deposit.winding_coefficients.len() == branch_rank
                && deposit
                    .winding_coefficients
                    .iter()
                    .any(|coordinate| coordinate != &Rat::from_integer(BigInt::from(0)))
                && threads.contains(deposit.thread_address.as_str())
                && fibres.iter().any(|fibre| {
                    fibre.thread == deposit.thread_address
                        && fibre.returned_covector == deposit.winding_coefficients
                        && digest(&(
                            &fibre.return_operator,
                            &fibre.terminal_covector,
                            &fibre.returned_covector,
                        )) == deposit.return_operator_identity_sha256
                })
        });
        let primary_population = branch_rank
            .checked_add(self.returned_deposits.len())
            .ok_or_else(|| SourceNeutralAthenaError::Body("primary extent overflow".to_owned()))?;
        let expected_symmetric = primary_population
            .checked_mul(primary_population.saturating_add(1))
            .and_then(|population| population.checked_div(2));
        if self.schema != "soma-life.source-neutral-returned-ecology.v1"
            || branch_rank == 0
            || self.returned_deposits.len() < 2
            || branch_threads.len() != branch_rank
            || self.branches.iter().any(|branch| {
                branch.k3_pullback_address.is_empty()
                    || branch.thread_address.is_empty()
                    || branch.returned_covector.is_empty()
                    || branch.local_population == 0
                    || branch.exact_fibre_population == 0
                    || !is_digest(&branch.return_operator_identity_sha256)
            })
            || self.returned_deposits.iter().any(|deposit| {
                deposit.thread_address.is_empty()
                    || deposit.winding_coefficients.len() != branch_rank
                    || !is_digest(&deposit.difference_identity_sha256)
                    || !is_digest(&deposit.return_operator_identity_sha256)
            })
            || !receipts_chain
            || !fibres_complete
            || expected_symmetric != Some(self.ecology.mixed_constitutive_families().len())
            || self.identity_sha256 != self.rederived_identity()
        {
            return Err(SourceNeutralAthenaError::Body(
                "the returned native ecology lost its addressed recurrence".to_owned(),
            ));
        }
        Ok(())
    }

    pub fn identity(&self) -> &str {
        &self.identity_sha256
    }

    pub fn ecology(&self) -> &NativeSituatedSpoolBundle {
        &self.ecology
    }

    pub fn branches(&self) -> &[SourceNeutralCultivationBranch] {
        &self.branches
    }

    pub fn returned_deposits(&self) -> &[SourceNeutralReturnedDeposit] {
        &self.returned_deposits
    }

    fn rederived_identity(&self) -> String {
        digest(&(
            "soma-life.source-neutral-returned-ecology.v1",
            &self.ecology,
            &self.branches,
            &self.predecessor_deposit_receipt,
            &self.returned_deposits,
        ))
    }
}

impl SourceNeutralAcousticMorphology {
    pub(crate) fn found(
        ordered_ports: Vec<(u32, u32)>,
        quadrature_population: u32,
        phase_extent: u32,
    ) -> Result<Self, SourceNeutralAthenaError> {
        let mut morphology = Self {
            schema: SOURCE_NEUTRAL_ACOUSTIC_MORPHOLOGY_SCHEMA.to_owned(),
            ordered_ports,
            quadrature_population,
            phase_extent,
            identity_sha256: String::new(),
        };
        morphology.identity_sha256 = morphology.rederived_identity();
        morphology.validate()?;
        Ok(morphology)
    }

    pub fn identity(&self) -> &str {
        &self.identity_sha256
    }

    pub fn ordered_ports(&self) -> &[(u32, u32)] {
        &self.ordered_ports
    }

    fn validate(&self) -> Result<(), SourceNeutralAthenaError> {
        let expected_extent = u32::try_from(self.ordered_ports.len())
            .ok()
            .and_then(|ports| ports.checked_mul(self.quadrature_population))
            .ok_or(SourceNeutralAthenaError::Sensory)?;
        let mut unique = self.ordered_ports.clone();
        unique.sort_unstable();
        unique.dedup();
        if self.schema != SOURCE_NEUTRAL_ACOUSTIC_MORPHOLOGY_SCHEMA
            || self.ordered_ports.is_empty()
            || self.quadrature_population != 2
            || self.phase_extent != expected_extent
            || unique.len() != self.ordered_ports.len()
            || self.identity_sha256 != self.rederived_identity()
        {
            return Err(SourceNeutralAthenaError::Sensory);
        }
        Ok(())
    }

    fn rederived_identity(&self) -> String {
        digest(&(
            SOURCE_NEUTRAL_ACOUSTIC_MORPHOLOGY_SCHEMA,
            &self.ordered_ports,
            self.quadrature_population,
            self.phase_extent,
        ))
    }
}

impl SourceNeutralOpticalMorphology {
    pub(crate) fn found(
        ordered_ports: Vec<(u32, u32)>,
        lattice_width: u32,
        lattice_height_per_order: u32,
        scale_spans: Vec<u32>,
    ) -> Result<Self, SourceNeutralAthenaError> {
        let mut morphology = Self {
            schema: SOURCE_NEUTRAL_OPTICAL_MORPHOLOGY_SCHEMA.to_owned(),
            ordered_ports,
            lattice_width,
            lattice_height_per_order,
            scale_spans,
            identity_sha256: String::new(),
        };
        morphology.identity_sha256 = morphology.rederived_identity();
        morphology.validate()?;
        Ok(morphology)
    }

    pub fn identity(&self) -> &str {
        &self.identity_sha256
    }

    pub fn ordered_ports(&self) -> &[(u32, u32)] {
        &self.ordered_ports
    }

    fn validate(&self) -> Result<(), SourceNeutralAthenaError> {
        let mut unique = self.ordered_ports.clone();
        unique.sort_unstable();
        unique.dedup();
        if self.schema != SOURCE_NEUTRAL_OPTICAL_MORPHOLOGY_SCHEMA
            || self.ordered_ports.is_empty()
            || self.lattice_width == 0
            || self.lattice_height_per_order == 0
            || self.scale_spans.is_empty()
            || self.scale_spans.windows(2).any(|pair| pair[0] >= pair[1])
            || unique.len() != self.ordered_ports.len()
            || self.identity_sha256 != self.rederived_identity()
        {
            return Err(SourceNeutralAthenaError::Sensory);
        }
        Ok(())
    }

    fn rederived_identity(&self) -> String {
        digest(&(
            SOURCE_NEUTRAL_OPTICAL_MORPHOLOGY_SCHEMA,
            &self.ordered_ports,
            self.lattice_width,
            self.lattice_height_per_order,
            &self.scale_spans,
        ))
    }
}

impl SourceNeutralAthenaRest {
    pub(crate) fn found(
        body: SourceNeutralReturnedEcology,
        granular: NativeGranularPotential,
        relational: SourceNeutralRelationalMorphology,
        realization: SourceNeutralExteriorRealizationMorphology,
        acoustic: SourceNeutralAcousticMorphology,
        optical: SourceNeutralOpticalMorphology,
    ) -> Result<Self, SourceNeutralAthenaError> {
        let mut rest = Self {
            schema: SOURCE_NEUTRAL_ATHENA_REST_SCHEMA.to_owned(),
            body,
            granular,
            relational,
            realization,
            acoustic,
            optical,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity();
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, SourceNeutralAthenaError> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| SourceNeutralAthenaError::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, SourceNeutralAthenaError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| SourceNeutralAthenaError::Wire(error.to_string()))
    }

    pub fn validate(&self) -> Result<(), SourceNeutralAthenaError> {
        self.body.validate()?;
        self.granular
            .validate()
            .map_err(|error| SourceNeutralAthenaError::Granular(error.to_string()))?;
        self.relational
            .validate()
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        self.realization
            .validate_relational(&self.relational)
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        self.acoustic.validate()?;
        self.optical.validate()?;
        if self.schema != SOURCE_NEUTRAL_ATHENA_REST_SCHEMA
            || self.acoustic.ordered_ports != self.optical.ordered_ports
            || self.relational.factor_population() != self.granular.factor_faces().len()
            || self.realization.relational_identity() != self.relational.identity()
            || self.identity_sha256 != self.rederived_identity()
        {
            return Err(SourceNeutralAthenaError::Wire(
                "the continuing organs lost their common boundary incidence".to_owned(),
            ));
        }
        Ok(())
    }

    pub fn identity(&self) -> &str {
        &self.identity_sha256
    }

    pub fn body(&self) -> &SourceNeutralReturnedEcology {
        &self.body
    }

    pub fn granular(&self) -> &NativeGranularPotential {
        &self.granular
    }

    pub fn relational(&self) -> &SourceNeutralRelationalMorphology {
        &self.relational
    }

    pub fn realization(&self) -> &SourceNeutralExteriorRealizationMorphology {
        &self.realization
    }

    pub fn acoustic(&self) -> &SourceNeutralAcousticMorphology {
        &self.acoustic
    }

    pub fn optical(&self) -> &SourceNeutralOpticalMorphology {
        &self.optical
    }

    /// Deposit one already-founded situated difference into this same source-neutral ecology.
    /// The complete native deposit is built by the shared situated-cultivation constructor; only
    /// the source-neutral wrapper changes, while every fine, relational, acoustic, and optical
    /// morphology is moved unchanged into the successor.
    pub fn deposit_returned_difference(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<(Self, SourceNeutralReturnedDifferenceReceipt), SourceNeutralAthenaError> {
        self.validate()?;
        let predecessor_rest_identity_sha256 = self.identity_sha256.clone();
        let SourceNeutralAthenaRest {
            body,
            granular,
            relational,
            realization,
            acoustic,
            optical,
            ..
        } = self;
        let granular_identity_sha256 = granular.identity().to_owned();
        let relational_identity_sha256 = relational.identity().to_owned();
        let realization_identity_sha256 = realization.identity().to_owned();
        let acoustic_identity_sha256 = acoustic.identity().to_owned();
        let optical_identity_sha256 = optical.identity().to_owned();
        let predecessor_ecology_identity = body
            .ecology
            .identity_sha256()
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        let (body, returned) = body.deposit_returned_difference(&difference)?;
        let successor = Self::found(body, granular, relational, realization, acoustic, optical)?;
        let morphologies_preserved = successor.granular.identity() == granular_identity_sha256
            && successor.relational.identity() == relational_identity_sha256
            && successor.realization.identity() == realization_identity_sha256
            && successor.acoustic.identity() == acoustic_identity_sha256
            && successor.optical.identity() == optical_identity_sha256;
        if !morphologies_preserved {
            return Err(SourceNeutralAthenaError::Body(
                "the returned difference changed a source-neutral organ morphology".to_owned(),
            ));
        }
        let receipt = SourceNeutralReturnedDifferenceReceipt {
            predecessor_rest_identity_sha256,
            successor_rest_identity_sha256: successor.identity_sha256.clone(),
            difference_identity_sha256: returned.difference_identity_sha256.clone(),
            thread_address: returned.thread_address.clone(),
            returned_covector: returned.winding_coefficients.clone(),
            native_receipt: returned.native_receipt.clone(),
            granular_identity_sha256,
            relational_identity_sha256,
            realization_identity_sha256,
            acoustic_identity_sha256,
            optical_identity_sha256,
            morphologies_preserved,
            source_detached_before_rest: true,
        };
        if receipt.native_receipt.predecessor_identity_sha256 != predecessor_ecology_identity
            || receipt.successor_rest_identity_sha256 != successor.identity_sha256
        {
            return Err(SourceNeutralAthenaError::Body(
                "the source-neutral returned-difference receipt lost its ecology lineage"
                    .to_owned(),
            ));
        }
        Ok((successor, receipt))
    }

    /// Remove the newest returned difference by consuming its exact native deposit. The returned
    /// predecessor owns the same source-neutral organs and is validated against the recovered
    /// ecology before the move-owned withdrawal is returned.
    pub fn withdraw_latest_returned_difference(
        self,
    ) -> Result<(Self, SourceNeutralReturnedDifferenceWithdrawal), SourceNeutralAthenaError> {
        self.validate()?;
        let original_rest_identity_sha256 = self.identity_sha256.clone();
        let SourceNeutralAthenaRest {
            body:
                SourceNeutralReturnedEcology {
                    ecology,
                    branches,
                    predecessor_deposit_receipt,
                    mut returned_deposits,
                    ..
                },
            granular,
            relational,
            realization,
            acoustic,
            optical,
            ..
        } = self;
        let returned = returned_deposits.pop().ok_or_else(|| {
            SourceNeutralAthenaError::Body(
                "the source-neutral body has no returned difference to withdraw".to_owned(),
            )
        })?;
        let admitted_successor_ecology_identity =
            returned.native_receipt.successor_identity_sha256.clone();
        let (predecessor, native_deposit) = ecology
            .withdraw_deposit_from_admitted(
                &admitted_successor_ecology_identity,
                returned.native_receipt.clone(),
            )
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        let NativeSituatedSpoolPredecessor::Situated(ecology) = predecessor else {
            return Err(SourceNeutralAthenaError::Body(
                "the returned source-neutral deposit escaped its situated ecology".to_owned(),
            ));
        };
        let body = SourceNeutralReturnedEcology::found(
            ecology,
            branches,
            predecessor_deposit_receipt,
            returned_deposits,
        )?;
        let predecessor = Self::found(body, granular, relational, realization, acoustic, optical)?;
        let predecessor_rest_identity_sha256 = predecessor.identity_sha256.clone();
        Ok((
            predecessor,
            SourceNeutralReturnedDifferenceWithdrawal {
                original_rest_identity_sha256,
                predecessor_rest_identity_sha256,
                returned,
                native_deposit,
            },
        ))
    }

    /// Restore a previously withdrawn latest return and recover its exact successor identity.
    pub fn restore_returned_difference(
        predecessor: Self,
        withdrawal: SourceNeutralReturnedDifferenceWithdrawal,
    ) -> Result<Self, SourceNeutralAthenaError> {
        predecessor.validate()?;
        if predecessor.identity_sha256 != withdrawal.predecessor_rest_identity_sha256 {
            return Err(SourceNeutralAthenaError::Body(
                "the source-neutral withdrawal was offered to another predecessor".to_owned(),
            ));
        }
        let SourceNeutralAthenaRest {
            body:
                SourceNeutralReturnedEcology {
                    ecology,
                    branches,
                    predecessor_deposit_receipt,
                    mut returned_deposits,
                    ..
                },
            granular,
            relational,
            realization,
            acoustic,
            optical,
            ..
        } = predecessor;
        let admitted_predecessor_ecology_identity = withdrawal
            .returned
            .native_receipt
            .predecessor_identity_sha256
            .clone();
        let (ecology, native_receipt) = ecology
            .deposit_thread_from_admitted(
                &admitted_predecessor_ecology_identity,
                withdrawal.native_deposit,
            )
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        if native_receipt != withdrawal.returned.native_receipt {
            return Err(SourceNeutralAthenaError::Body(
                "source-neutral returned-difference restoration changed its native receipt"
                    .to_owned(),
            ));
        }
        returned_deposits.push(withdrawal.returned);
        let body = SourceNeutralReturnedEcology::found(
            ecology,
            branches,
            predecessor_deposit_receipt,
            returned_deposits,
        )?;
        let successor = Self::found(body, granular, relational, realization, acoustic, optical)?;
        if successor.identity_sha256 != withdrawal.original_rest_identity_sha256 {
            return Err(SourceNeutralAthenaError::Body(
                "source-neutral returned-difference restoration did not recover its identity"
                    .to_owned(),
            ));
        }
        Ok(successor)
    }

    /// Return the source-neutral addresses which preceded every situated cultivation deposit.
    /// This is a structural difference of owned thread populations, not a name-pattern test.
    pub fn inherited_thread_addresses(&self) -> Vec<(String, String)> {
        let deposited = self
            .body
            .predecessor_deposit_receipt
            .placements
            .iter()
            .map(|placement| placement.thread_address.as_str())
            .chain(
                self.body
                    .returned_deposits
                    .iter()
                    .map(|deposit| deposit.native_receipt.thread_address.as_str()),
            )
            .collect::<BTreeSet<_>>();
        self.body
            .ecology
            .native()
            .spools
            .iter()
            .flat_map(|spool| {
                spool
                    .threads
                    .iter()
                    .filter(|thread| !deposited.contains(thread.address.as_str()))
                    .map(|thread| (spool.address.clone(), thread.address.clone()))
            })
            .collect()
    }

    /// Move one inherited carrier and every incident relation out of the continuing body. The
    /// ablated type cannot mount or radiate: it can only return the exact native insufficiency for
    /// a held later current and restore the moved carrier.
    pub fn withdraw_inherited_thread(
        self,
        spool_address: &str,
        thread_address: &str,
    ) -> Result<SourceNeutralInheritedThreadAblation, SourceNeutralAthenaError> {
        self.validate()?;
        if !self
            .inherited_thread_addresses()
            .iter()
            .any(|(spool, thread)| spool == spool_address && thread == thread_address)
        {
            return Err(SourceNeutralAthenaError::Body(
                "the requested carrier is not structurally inherited standing".to_owned(),
            ));
        }
        let SourceNeutralAthenaRest {
            body,
            granular,
            relational,
            realization,
            acoustic,
            optical,
            identity_sha256: original_rest_identity_sha256,
            ..
        } = self;
        let SourceNeutralReturnedEcology {
            ecology,
            branches,
            predecessor_deposit_receipt,
            returned_deposits,
            ..
        } = body;
        let (ecology, withdrawal) = ecology
            .withdraw_thread(spool_address, thread_address)
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        let receiver_insufficiency = ecology
            .native()
            .insufficiency_after_withdrawal(&withdrawal.native)
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        let ablated_body_identity_sha256 = digest(&(
            "soma-life.source-neutral-inherited-thread-ablation.v1",
            &ecology,
            &branches,
            &predecessor_deposit_receipt,
            &returned_deposits,
            granular.identity(),
            relational.identity(),
            realization.identity(),
            acoustic.identity(),
            optical.identity(),
        ));
        Ok(SourceNeutralInheritedThreadAblation {
            original_rest_identity_sha256,
            ablated_body_identity_sha256,
            spool_address: spool_address.to_owned(),
            thread_address: thread_address.to_owned(),
            ecology,
            branches,
            predecessor_deposit_receipt,
            returned_deposits,
            granular,
            relational,
            realization,
            acoustic,
            optical,
            withdrawal,
            receiver_insufficiency,
        })
    }

    /// Move one exact receiver-kernel direction out of the reconstruction body while retaining
    /// the complete native-radiation constitution.  The returned staged type is not another rest:
    /// it owns the one ablated ecology and the one reversible delta until restoration.
    pub fn withdraw_radical_direction(
        self,
        fibre_address: &str,
        direction_position: usize,
    ) -> Result<SourceNeutralRadicalDirectionAblation, SourceNeutralAthenaError> {
        self.validate()?;
        let original_rest_identity_sha256 = self.identity_sha256.clone();
        let fibre = self
            .body
            .ecology
            .exact_reconstruction_fibres()
            .iter()
            .find(|fibre| fibre.address == fibre_address)
            .ok_or_else(|| {
                SourceNeutralAthenaError::Body(format!(
                    "the requested radical fibre {fibre_address} is absent"
                ))
            })?;
        let direction = fibre
            .radical
            .get(direction_position)
            .cloned()
            .ok_or_else(|| {
                SourceNeutralAthenaError::Body(format!(
                    "the requested radical direction {direction_position} is absent"
                ))
            })?;
        let returned_covector_before = fibre.returned_covector.clone();
        let withdrawn_direction_return = fibre
            .return_operator
            .apply(&direction)
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        if withdrawn_direction_return
            .iter()
            .any(|coordinate| !coordinate.is_zero())
        {
            return Err(SourceNeutralAthenaError::Body(
                "the requested support-disjoint direction escaped its receiver radical".to_owned(),
            ));
        }

        let SourceNeutralAthenaRest {
            body:
                SourceNeutralReturnedEcology {
                    ecology,
                    branches,
                    predecessor_deposit_receipt,
                    returned_deposits,
                    ..
                },
            granular,
            relational,
            realization,
            acoustic,
            optical,
            ..
        } = self;
        let conduct_constitution_before_sha256 =
            source_neutral_native_conduct_constitution_identity(
                &ecology,
                &branches,
                &returned_deposits,
                &granular,
                &relational,
                &acoustic,
                &optical,
            );
        let (ecology, withdrawal) = ecology
            .withdraw_radical_direction(fibre_address, direction_position)
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        let returned_covector_after = ecology
            .exact_reconstruction_fibres()
            .iter()
            .find(|fibre| fibre.address == fibre_address)
            .map(|fibre| fibre.returned_covector.clone())
            .ok_or_else(|| {
                SourceNeutralAthenaError::Body(
                    "the radical withdrawal removed its reconstruction fibre".to_owned(),
                )
            })?;
        let conduct_constitution_after_sha256 = source_neutral_native_conduct_constitution_identity(
            &ecology,
            &branches,
            &returned_deposits,
            &granular,
            &relational,
            &acoustic,
            &optical,
        );
        if returned_covector_before != returned_covector_after
            || conduct_constitution_before_sha256 != conduct_constitution_after_sha256
            || withdrawal.direction != direction
        {
            return Err(SourceNeutralAthenaError::Body(
                "the radical withdrawal changed the admitted native-radiation constitution"
                    .to_owned(),
            ));
        }
        let ablated_body_identity_sha256 = digest(&(
            "soma-life.source-neutral-radical-direction-ablation.v1",
            &original_rest_identity_sha256,
            &ecology,
            &branches,
            &predecessor_deposit_receipt,
            &returned_deposits,
            granular.identity(),
            relational.identity(),
            realization.identity(),
            acoustic.identity(),
            optical.identity(),
            fibre_address,
            direction_position,
            &direction,
        ));
        Ok(SourceNeutralRadicalDirectionAblation {
            original_rest_identity_sha256,
            ablated_body_identity_sha256,
            fibre_address: fibre_address.to_owned(),
            direction_position,
            direction,
            returned_covector_before,
            returned_covector_after,
            withdrawn_direction_return,
            conduct_constitution_before_sha256,
            conduct_constitution_after_sha256,
            ecology,
            branches,
            predecessor_deposit_receipt,
            returned_deposits,
            granular,
            relational,
            realization,
            acoustic,
            optical,
            withdrawal,
        })
    }

    /// Move the complete source-neutral body onto one resident card.  The dense arrays are a
    /// one-time apparatus chart derived from the granular incidence and the exact situated
    /// Complex-Parametron families; no exterior occurrence or requested surface participates in
    /// their construction.
    pub fn mount_resident(self) -> Result<ResidentSourceNeutralAthena, SourceNeutralAthenaError> {
        self.validate()?;
        let realization_site_history = self
            .realization
            .found_site_history_quotient(&self.relational)
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!(
                "source-neutral-site-history-quotient source={} quotient={} fibre={} identity={}",
                realization_site_history.source_population(),
                realization_site_history.quotient_population(),
                realization_site_history.reconstruction_population(),
                &realization_site_history.identity()[..16],
            );
        }
        let constitution = self
            .granular
            .resident_constitution()
            .map_err(|error| SourceNeutralAthenaError::Granular(error.to_string()))?;
        let family_orientation = source_neutral_family_orientation(&self)?;
        let factor_capacity = constitution.factor_capacity.clone();
        let family_currents = self
            .body
            .ecology()
            .mixed_constitutive_families()
            .iter()
            .map(|family| family.returned_product.clone())
            .collect::<Vec<_>>();
        let mut resident = ResidentMembraneInteriorWord::mount(
            CudaRefineExecutor::new()
                .map_err(|error| SourceNeutralAthenaError::Apparatus(error.to_string()))?,
            &constitution.factor_capacity,
            &constitution.cell_offsets,
            &constitution.cell_factors,
            &constitution.cell_multiplicities,
            &constitution.cell_total_mass,
            &family_orientation,
            &family_currents,
        )
        .map_err(|error| SourceNeutralAthenaError::Apparatus(error.to_string()))?;
        let relational_current_atlas = self
            .relational
            .resident_current_atlas()
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        resident
            .mount_sparse_relational_current_atlas(&relational_current_atlas)
            .map_err(|error| SourceNeutralAthenaError::Apparatus(error.to_string()))?;
        let (mut receiver_ids, observations) = self
            .granular
            .resident_factor_receiver_chart()
            .map_err(|error| SourceNeutralAthenaError::Granular(error.to_string()))?;
        let inherited_receiver_count = receiver_ids.len();
        if inherited_receiver_count == 0
            || observations.len()
                != factor_capacity
                    .len()
                    .checked_mul(inherited_receiver_count)
                    .ok_or_else(|| {
                        SourceNeutralAthenaError::Body(
                            "the receiver constitution exceeded its extent".to_owned(),
                        )
                    })?
        {
            return Err(SourceNeutralAthenaError::Body(
                "the source-neutral receiver chart lost its factor incidence".to_owned(),
            ));
        }
        let relational_axes = self
            .relational
            .factor_receiver_axes()
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        if relational_axes.is_empty()
            || relational_axes
                .iter()
                .any(|axis| axis.len() != factor_capacity.len())
        {
            return Err(SourceNeutralAthenaError::Body(
                "the relational and Complex-Parametron factor bases do not meet".to_owned(),
            ));
        }
        for _ in &relational_axes {
            let relational_receiver = receiver_ids
                .last()
                .copied()
                .and_then(|receiver| receiver.checked_add(1))
                .ok_or_else(|| {
                    SourceNeutralAthenaError::Body(
                        "the relational receiver escaped its resident address".to_owned(),
                    )
                })?;
            receiver_ids.push(relational_receiver);
        }
        let receiver_count = receiver_ids.len();
        let mut observations_with_relational = Vec::with_capacity(
            factor_capacity
                .len()
                .checked_mul(receiver_count)
                .ok_or_else(|| {
                    SourceNeutralAthenaError::Body(
                        "the joined receiver chart exceeded its extent".to_owned(),
                    )
                })?,
        );
        for factor in 0..factor_capacity.len() {
            let from = factor * inherited_receiver_count;
            observations_with_relational
                .extend_from_slice(&observations[from..from + inherited_receiver_count]);
            observations_with_relational.extend(relational_axes.iter().map(|axis| axis[factor]));
        }
        let observations = observations_with_relational;
        let mut factor_receiver_classes = vec![0_u32; observations.len()];
        let mut receiver_class_counts = Vec::with_capacity(receiver_count);
        for receiver in 0..receiver_count {
            let mut classes = BTreeMap::<u64, u32>::new();
            for factor in 0..factor_capacity.len() {
                let at = factor * receiver_count + receiver;
                let observation = observations[at];
                let next = u32::try_from(classes.len()).map_err(|_| {
                    SourceNeutralAthenaError::Body(
                        "the receiver class population exceeded its address".to_owned(),
                    )
                })?;
                factor_receiver_classes[at] = *classes.entry(observation).or_insert(next);
            }
            receiver_class_counts.push(u32::try_from(classes.len()).map_err(|_| {
                SourceNeutralAthenaError::Body(
                    "the receiver class population exceeded its address".to_owned(),
                )
            })?);
        }
        let generator_ids = self.granular.receiver_history_generator_ids();
        let generators = self.granular.receiver_history_generator_targets();
        if generator_ids.len() != generators.len()
            || generators
                .iter()
                .any(|generator| generator.len() != factor_capacity.len())
        {
            return Err(SourceNeutralAthenaError::Body(
                "the source-neutral generator address population was not total".to_owned(),
            ));
        }
        resident
            .mount_factor_receiver_faces(&receiver_ids, &observations)
            .map_err(|error| SourceNeutralAthenaError::Apparatus(error.to_string()))?;
        let restrictions = self
            .granular
            .boundary_restriction_atlas()
            .map_err(|error| SourceNeutralAthenaError::Granular(error.to_string()))?;
        resident
            .mount_boundary_restriction_atlas(&restrictions)
            .map_err(|error| SourceNeutralAthenaError::Apparatus(error.to_string()))?;
        let factor_system = SourceNeutralFactorReceiverHistorySystem {
            items: (0..factor_capacity.len())
                .map(|factor| ItemId(factor as u64))
                .collect(),
            receivers: receiver_ids.iter().copied().map(ReceiverId).collect(),
            inputs: generator_ids.clone(),
            observations: observations.clone(),
            successors: generators.clone(),
        };
        let generator_targets = generators.iter().flatten().copied().collect::<Vec<_>>();
        let resident_compression = resident
            .mount_receiver_history_compression(
                &factor_system,
                u32::try_from(generators.len()).map_err(|_| {
                    SourceNeutralAthenaError::Body(
                        "the source-neutral generator population exceeded its address".to_owned(),
                    )
                })?,
                &generator_targets,
            )
            .map_err(|error| SourceNeutralAthenaError::Apparatus(error.to_string()))?;
        let compression = resident
            .receiver_history_compression()
            .cloned()
            .ok_or_else(|| {
                SourceNeutralAthenaError::Apparatus(
                    "the resident word did not retain its complete q/U/fibre owner".to_owned(),
                )
            })?;
        Ok(ResidentSourceNeutralAthena {
            rest: self,
            resident,
            realization_site_history,
            receiver_history: SourceNeutralReceiverHistoryConstitution {
                factor_capacity,
                generator_ids,
                generators,
                compression,
                resident_compression,
            },
        })
    }

    fn rederived_identity(&self) -> String {
        digest(&(
            SOURCE_NEUTRAL_ATHENA_REST_SCHEMA,
            self.body.identity(),
            self.granular.identity(),
            self.relational.identity(),
            self.realization.identity(),
            self.acoustic.identity(),
            self.optical.identity(),
        ))
    }
}

impl SourceNeutralInheritedThreadAblation {
    /// Pose the unchanged later current to the unchanged native-radiation receiver. Since its
    /// actual addressed carrying section has departed, the lawful return is the exact retained
    /// receiver insufficiency rather than rerouting through a sibling or exterior archive.
    pub fn obstruct_native_radiation(
        &self,
        projective: &GranularNativeProjectiveCurrent,
    ) -> Result<SourceNeutralNativeRadiationObstruction, SourceNeutralAthenaError> {
        if projective.standing_potential_identity_sha256 != self.granular.identity() {
            return Err(SourceNeutralAthenaError::Granular(
                "the held current belongs to another granular standing".to_owned(),
            ));
        }
        let identity_sha256 = digest(&(
            "soma-life.source-neutral-native-radiation-obstruction.v1",
            &self.original_rest_identity_sha256,
            &self.ablated_body_identity_sha256,
            &projective.identity_sha256,
            self.granular.identity(),
            &self.spool_address,
            &self.thread_address,
            &self.receiver_insufficiency,
        ));
        Ok(SourceNeutralNativeRadiationObstruction {
            schema: "soma-life.source-neutral-native-radiation-obstruction.v1".to_owned(),
            original_rest_identity_sha256: self.original_rest_identity_sha256.clone(),
            ablated_body_identity_sha256: self.ablated_body_identity_sha256.clone(),
            ingress_current_identity_sha256: projective.identity_sha256.clone(),
            standing_potential_identity_sha256: self.granular.identity().to_owned(),
            spool_address: self.spool_address.clone(),
            thread_address: self.thread_address.clone(),
            receiver_insufficiency: self.receiver_insufficiency.clone(),
            same_later_current_held: true,
            same_native_radiation_receiver_held: true,
            source_codec_consulted: false,
            exterior_reconstruction_fibre_reachable: false,
            identity_sha256,
        })
    }

    /// Consume the staged delta, restore every incident relation, and recover the exact original
    /// rested identity.
    pub fn restore(self) -> Result<SourceNeutralAthenaRest, SourceNeutralAthenaError> {
        let ecology = self
            .ecology
            .restore_thread(self.withdrawal)
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        let body = SourceNeutralReturnedEcology::found(
            ecology,
            self.branches,
            self.predecessor_deposit_receipt,
            self.returned_deposits,
        )?;
        let rest = SourceNeutralAthenaRest::found(
            body,
            self.granular,
            self.relational,
            self.realization,
            self.acoustic,
            self.optical,
        )?;
        if rest.identity() != self.original_rest_identity_sha256 {
            return Err(SourceNeutralAthenaError::Body(
                "the inherited carrier did not restore the exact Athena rest".to_owned(),
            ));
        }
        Ok(rest)
    }
}

impl SourceNeutralRadicalDirectionAblation {
    /// Return the exact D3 support-disjoint consequence for one already-measured child section.
    /// Equality follows from identical complete conduct constitution and annihilation of the moved
    /// direction, while the changed ablated-body identity retains the reconstruction difference.
    pub fn preserve_native_radiation(
        &self,
        projective: &GranularNativeProjectiveCurrent,
        child: &SourceNeutralResidentRadiationSection,
    ) -> Result<SourceNeutralRadicalConductPreservationReceipt, SourceNeutralAthenaError> {
        if projective.standing_potential_identity_sha256 != self.granular.identity()
            || child.rest_identity_sha256 != self.original_rest_identity_sha256
            || child.ingress_current_identity_sha256 != projective.identity_sha256
        {
            return Err(SourceNeutralAthenaError::Body(
                "the support-disjoint control did not retain the same child/current receiver"
                    .to_owned(),
            ));
        }
        let same_native_radiation_constitution =
            self.conduct_constitution_before_sha256 == self.conduct_constitution_after_sha256;
        let withdrawn_direction_in_receiver_radical =
            self.withdrawn_direction_return.iter().all(Zero::is_zero);
        let returned_covector_preserved =
            self.returned_covector_before == self.returned_covector_after;
        if !same_native_radiation_constitution
            || !withdrawn_direction_in_receiver_radical
            || !returned_covector_preserved
        {
            return Err(SourceNeutralAthenaError::Body(
                "the support-disjoint ablation failed its exact factorization law".to_owned(),
            ));
        }
        let child_receiver_consequence_identity_sha256 =
            source_neutral_native_receiver_consequence_identity(child);
        let preserved_receiver_consequence_identity_sha256 =
            child_receiver_consequence_identity_sha256.clone();
        let schema = "soma-life.source-neutral-radical-conduct-preservation-receipt.v1".to_owned();
        let identity_sha256 = digest(&(
            schema.as_str(),
            (
                &self.original_rest_identity_sha256,
                &self.ablated_body_identity_sha256,
                &self.fibre_address,
                self.direction_position,
                &self.direction,
                &self.returned_covector_before,
                &self.returned_covector_after,
                &self.withdrawn_direction_return,
                &self.conduct_constitution_before_sha256,
                &self.conduct_constitution_after_sha256,
            ),
            (
                &projective.identity_sha256,
                &child_receiver_consequence_identity_sha256,
                &preserved_receiver_consequence_identity_sha256,
                true,
                same_native_radiation_constitution,
                withdrawn_direction_in_receiver_radical,
                returned_covector_preserved,
                false,
                false,
            ),
        ));
        Ok(SourceNeutralRadicalConductPreservationReceipt {
            schema,
            original_rest_identity_sha256: self.original_rest_identity_sha256.clone(),
            ablated_body_identity_sha256: self.ablated_body_identity_sha256.clone(),
            fibre_address: self.fibre_address.clone(),
            direction_position: self.direction_position,
            direction: self.direction.clone(),
            returned_covector_before: self.returned_covector_before.clone(),
            returned_covector_after: self.returned_covector_after.clone(),
            withdrawn_direction_return: self.withdrawn_direction_return.clone(),
            conduct_constitution_before_sha256: self.conduct_constitution_before_sha256.clone(),
            conduct_constitution_after_sha256: self.conduct_constitution_after_sha256.clone(),
            held_later_current_identity_sha256: projective.identity_sha256.clone(),
            child_receiver_consequence_identity_sha256,
            preserved_receiver_consequence_identity_sha256,
            same_later_current_held: true,
            same_native_radiation_constitution,
            withdrawn_direction_in_receiver_radical,
            returned_covector_preserved,
            source_codec_consulted: false,
            exterior_reconstruction_fibre_reachable: false,
            identity_sha256,
        })
    }

    /// Consume the moved radical direction and recover the exact rested child identity.
    pub fn restore(self) -> Result<SourceNeutralAthenaRest, SourceNeutralAthenaError> {
        let ecology = self
            .ecology
            .restore_radical_direction(self.withdrawal)
            .map_err(|error| SourceNeutralAthenaError::Body(error.to_string()))?;
        let body = SourceNeutralReturnedEcology::found(
            ecology,
            self.branches,
            self.predecessor_deposit_receipt,
            self.returned_deposits,
        )?;
        let rest = SourceNeutralAthenaRest::found(
            body,
            self.granular,
            self.relational,
            self.realization,
            self.acoustic,
            self.optical,
        )?;
        if rest.identity() != self.original_rest_identity_sha256 {
            return Err(SourceNeutralAthenaError::Body(
                "the support-disjoint radical restoration changed the child identity".to_owned(),
            ));
        }
        Ok(rest)
    }
}
