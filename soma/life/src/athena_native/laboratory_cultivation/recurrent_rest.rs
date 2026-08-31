impl RecurrentReturnedAffineLaboratoryAthenaRest {
    pub fn read(bytes: &[u8]) -> Result<Self, LaboratoryCultivationError> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| LaboratoryCultivationError::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, LaboratoryCultivationError> {
        self.validate()?;
        serde_json::to_vec(self)
            .map_err(|error| LaboratoryCultivationError::Wire(error.to_string()))
    }

    pub fn identity(&self) -> &str {
        &self.identity_sha256
    }

    pub fn body(&self) -> &RecurrentLaboratoryCultivatedAthenaRest {
        &self.body
    }

    pub fn correspondences(&self) -> &[LaboratoryFactorCycleCorrespondence] {
        &self.correspondences
    }

    pub fn affine_cells(&self) -> &[LaboratoryCellAffineSection] {
        &self.affine_cells
    }

    pub(super) fn relational_potential(&self) -> &NativeRelationalPotentialComplex {
        &self.potential
    }

    pub(super) fn relational_codec(&self) -> &NativeRelationalCodec {
        &self.codec
    }

    /// Mount the recurrent body through the already admitted coupled-current, participant, and
    /// affine fronts. Returned differences enlarge the coupled incidence before the one card
    /// lease is founded; material transport remains the original rank-four local fibre carried by
    /// every affine landmark.
    pub fn mount_recurrent_integrated(
        self,
    ) -> Result<ResidentRecurrentAffineLaboratoryAthena, LaboratoryCultivationError> {
        self.validate()?;
        let participant_faces = self
            .potential
            .addressed_participant_subject_faces()
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        let mut participant_subject = Vec::with_capacity(self.potential.cells.len());
        let mut copular = Vec::with_capacity(self.potential.cells.len());
        let mut has_modality = Vec::with_capacity(self.potential.cells.len());
        let mut has_return = Vec::with_capacity(self.potential.cells.len());
        let mut landmark_support = Vec::with_capacity(self.potential.cells.len());
        let mut occurrence_mass = Vec::with_capacity(self.potential.cells.len());
        let mut last_occurrence = Vec::with_capacity(self.potential.cells.len());
        for cell in &self.potential.cells {
            participant_subject.push(u8::from(participant_faces.contains(&cell.subject)));
            copular.push(u8::from(cell.copular));
            has_modality.push(u8::from(cell.modality.is_some()));
            has_return.push(u8::from(
                cell.occurrences
                    .iter()
                    .any(|occurrence| occurrence.phase == NativeDeliveryPhase::Return),
            ));
            landmark_support.push(u32::try_from(cell.factor_support.len()).map_err(|_| {
                LaboratoryCultivationError::Correspondence(
                    "a recurrent participant cell support escaped the card address line".to_owned(),
                )
            })?);
            occurrence_mass.push(
                cell.occurrence_population()
                    .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?,
            );
            last_occurrence.push(cell.last_delivery_order().ok_or_else(|| {
                LaboratoryCultivationError::Correspondence(
                    "a recurrent participant cell lost its causal chronology".to_owned(),
                )
            })?);
        }
        let mut cell_offsets = Vec::with_capacity(self.affine_cells.len() + 1);
        let mut cell_factors = Vec::new();
        let mut multiplicities = Vec::new();
        let mut cell_total_mass = Vec::with_capacity(self.affine_cells.len());
        cell_offsets.push(0u64);
        for cell in &self.affine_cells {
            if cell.landmark_factors.len() != cell.occurrence_multiplicities.len() {
                return Err(LaboratoryCultivationError::Correspondence(
                    "a recurrent resident affine cell lost its factor/multiplicity incidence"
                        .to_owned(),
                ));
            }
            let total = cell
                .occurrence_multiplicities
                .iter()
                .try_fold(0u64, |sum, mass| sum.checked_add(*mass))
                .ok_or_else(|| {
                    LaboratoryCultivationError::Correspondence(
                        "the recurrent resident affine mass overflowed".to_owned(),
                    )
                })?;
            cell_factors.extend(cell.landmark_factors.iter().copied());
            multiplicities.extend(cell.occurrence_multiplicities.iter().copied());
            cell_total_mass.push(total);
            cell_offsets.push(u64::try_from(multiplicities.len()).map_err(|_| {
                LaboratoryCultivationError::Correspondence(
                    "the recurrent affine support escaped the resident offset chart".to_owned(),
                )
            })?);
        }
        let (incidence, front, interactions, factors, expected) =
            derive_recurrent_resident_coupling(&self.body)
                .map_err(|error| LaboratoryCultivationError::Situated(error.to_string()))?;
        let resident = ResidentAthenaIntegratedFront::mount(
            CudaRefineExecutor::new()
                .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?,
            format!(
                "recurrent-affine-laboratory-coupled/{}",
                self.identity_sha256
            ),
            incidence,
            front,
            interactions,
            &participant_subject,
            &copular,
            &has_modality,
            &has_return,
            &landmark_support,
            &occurrence_mass,
            &last_occurrence,
            &cell_offsets,
            &cell_factors,
            &multiplicities,
            &cell_total_mass,
        )
        .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        Ok(ResidentRecurrentAffineLaboratoryAthena {
            rest: self,
            factors,
            expected,
            resident,
        })
    }

    /// Return the incidence-founded participant/disjoint partition after recurrent returns. No
    /// name, prompt, or requested surface participates in the partition.
    pub fn ablation_atlas(
        &self,
    ) -> Result<AffineLaboratoryAblationAtlas, LaboratoryCultivationError> {
        let participants = self
            .potential
            .addressed_participant_subject_faces()
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        let mut participant_incident_cells = Vec::new();
        let mut participant_disjoint_cells = Vec::new();
        for cell in &self.potential.cells {
            if participants.contains(&cell.subject) {
                participant_incident_cells.push(cell.address.clone());
            } else {
                participant_disjoint_cells.push(cell.address.clone());
            }
        }
        if participant_incident_cells.is_empty() || participant_disjoint_cells.is_empty() {
            return Err(LaboratoryCultivationError::Correspondence(
                "the recurrent affine ecology does not expose both participant and disjoint cells"
                    .to_owned(),
            ));
        }
        Ok(AffineLaboratoryAblationAtlas {
            participant_incident_cells,
            participant_disjoint_cells,
        })
    }

    pub fn validate(&self) -> Result<(), LaboratoryCultivationError> {
        self.body
            .validate()
            .map_err(|error| LaboratoryCultivationError::Situated(error.to_string()))?;
        self.potential
            .validate()
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        self.codec
            .validate(&self.potential)
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        validate_returned_correspondences(
            self.body.ecology(),
            self.body.branches(),
            &self.potential,
            &self.correspondences,
        )?;
        if self.schema != RECURRENT_RETURNED_REST_SCHEMA
            || self.rest_identity_history.len() + 1 != self.body.returned_deposits().len()
            || self
                .rest_identity_history
                .iter()
                .any(|identity| !is_digest(identity))
            || !is_digest(&self.origin_predecessor_rest_identity_sha256)
            || self.origin_predecessor_body_identity_sha256
                != self.body.origin_predecessor_identity()
            || self.affine_cells != affine_cell_sections(&self.potential)?
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(LaboratoryCultivationError::Wire(
                "the recurrent affine rest lost its one-body return lineage".to_owned(),
            ));
        }
        Ok(())
    }

    pub fn deposit_additional_returned_difference(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<Self, LaboratoryCultivationError> {
        self.validate()?;
        let rest = self.deposit_additional_returned_difference_admitted(difference)?;
        rest.validate()?;
        Ok(rest)
    }

    pub(super) fn deposit_additional_returned_difference_admitted(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<Self, LaboratoryCultivationError> {
        let Self {
            schema,
            mut rest_identity_history,
            origin_predecessor_rest_identity_sha256,
            origin_predecessor_body_identity_sha256,
            body,
            potential,
            codec,
            correspondences,
            affine_cells,
            identity_sha256,
        } = self;
        let body = body
            .deposit_additional_returned_difference_admitted(difference)
            .map_err(|error| LaboratoryCultivationError::Situated(error.to_string()))?;
        rest_identity_history.push(identity_sha256);
        let mut rest = Self {
            schema,
            rest_identity_history,
            origin_predecessor_rest_identity_sha256,
            origin_predecessor_body_identity_sha256,
            body,
            potential,
            codec,
            correspondences,
            affine_cells,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        Ok(rest)
    }

    /// Remove one support-local relational cell while every returned native thread remains in
    /// the one body. This is the recurrent-state sibling control.
    pub fn withdraw_relational_cell(
        self,
        cell_address: &str,
    ) -> Result<(Self, AffineLaboratoryCellWithdrawal), LaboratoryCultivationError> {
        self.validate()?;
        let (rest, withdrawal) = self.withdraw_relational_cell_from_admitted(cell_address)?;
        rest.validate()?;
        Ok((rest, withdrawal))
    }

    pub(super) fn withdraw_relational_cell_from_admitted(
        mut self,
        cell_address: &str,
    ) -> Result<(Self, AffineLaboratoryCellWithdrawal), LaboratoryCultivationError> {
        if self.potential.cells.len() <= 1 {
            return Err(LaboratoryCultivationError::Correspondence(
                "the local ablation would remove the complete relational population".to_owned(),
            ));
        }
        let original_position = self
            .potential
            .cells
            .iter()
            .position(|cell| cell.address == cell_address)
            .ok_or_else(|| {
                LaboratoryCultivationError::Correspondence(
                    "the requested recurrent sibling cell is absent".to_owned(),
                )
            })?;
        let original_rest_identity_sha256 = self.identity_sha256.clone();
        let cell = self.potential.cells.remove(original_position);
        self.affine_cells = affine_cell_sections(&self.potential)?;
        self.identity_sha256 = self.rederived_identity()?;
        let ablated_rest_identity_sha256 = self.identity_sha256.clone();
        Ok((
            self,
            AffineLaboratoryCellWithdrawal {
                original_rest_identity_sha256,
                ablated_rest_identity_sha256,
                original_position,
                cell,
            },
        ))
    }

    pub fn restore_relational_cell(
        self,
        withdrawal: AffineLaboratoryCellWithdrawal,
    ) -> Result<Self, LaboratoryCultivationError> {
        self.validate()?;
        let rest = self.restore_relational_cell_from_admitted(withdrawal)?;
        rest.validate()?;
        Ok(rest)
    }

    pub(super) fn restore_relational_cell_from_admitted(
        mut self,
        withdrawal: AffineLaboratoryCellWithdrawal,
    ) -> Result<Self, LaboratoryCultivationError> {
        if self.identity_sha256 != withdrawal.ablated_rest_identity_sha256
            || withdrawal.original_position > self.potential.cells.len()
            || self
                .potential
                .cells
                .iter()
                .any(|cell| cell.address == withdrawal.cell.address)
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the moved affine cell was offered to a different recurrent body".to_owned(),
            ));
        }
        self.potential
            .cells
            .insert(withdrawal.original_position, withdrawal.cell);
        self.affine_cells = affine_cell_sections(&self.potential)?;
        self.identity_sha256 = self.rederived_identity()?;
        if self.identity_sha256 != withdrawal.original_rest_identity_sha256 {
            return Err(LaboratoryCultivationError::Wire(
                "recurrent sibling restoration did not recover the exact successor".to_owned(),
            ));
        }
        Ok(self)
    }

    pub fn withdraw_latest_returned_difference(
        self,
    ) -> Result<
        (
            RecurrentReturnedAffinePredecessor,
            RecurrentReturnedAffineDifferenceWithdrawal,
        ),
        LaboratoryCultivationError,
    > {
        self.validate()?;
        let (predecessor, withdrawal) = self.withdraw_latest_returned_difference_from_admitted()?;
        match &predecessor {
            RecurrentReturnedAffinePredecessor::First(rest) => rest.validate()?,
            RecurrentReturnedAffinePredecessor::Recurrent(rest) => rest.validate()?,
        }
        Ok((predecessor, withdrawal))
    }

    pub(super) fn withdraw_latest_returned_difference_from_admitted(
        self,
    ) -> Result<
        (
            RecurrentReturnedAffinePredecessor,
            RecurrentReturnedAffineDifferenceWithdrawal,
        ),
        LaboratoryCultivationError,
    > {
        let Self {
            schema,
            mut rest_identity_history,
            origin_predecessor_rest_identity_sha256,
            origin_predecessor_body_identity_sha256,
            body,
            potential,
            codec,
            correspondences,
            affine_cells,
            identity_sha256,
        } = self;
        let expected_predecessor_identity = rest_identity_history.pop().ok_or_else(|| {
            LaboratoryCultivationError::Wire("recurrent affine history is empty".to_owned())
        })?;
        let (body, situated) = body
            .withdraw_latest_returned_difference_from_admitted()
            .map_err(|error| LaboratoryCultivationError::Situated(error.to_string()))?;
        let predecessor = match body {
            RecurrentLaboratoryPredecessor::First(body) => {
                let rest = ReturnedAffineLaboratoryAthenaRest {
                    schema: RETURNED_REST_SCHEMA.to_owned(),
                    predecessor_rest_identity_sha256: origin_predecessor_rest_identity_sha256,
                    predecessor_body_identity_sha256: origin_predecessor_body_identity_sha256,
                    body,
                    potential,
                    codec,
                    correspondences,
                    affine_cells,
                    identity_sha256: expected_predecessor_identity.clone(),
                };
                RecurrentReturnedAffinePredecessor::First(rest)
            }
            RecurrentLaboratoryPredecessor::Recurrent(body) => {
                let rest = Self {
                    schema,
                    rest_identity_history,
                    origin_predecessor_rest_identity_sha256,
                    origin_predecessor_body_identity_sha256,
                    body,
                    potential,
                    codec,
                    correspondences,
                    affine_cells,
                    identity_sha256: expected_predecessor_identity.clone(),
                };
                RecurrentReturnedAffinePredecessor::Recurrent(rest)
            }
        };
        Ok((
            predecessor,
            RecurrentReturnedAffineDifferenceWithdrawal {
                original_rest_identity_sha256: identity_sha256,
                predecessor_rest_identity_sha256: expected_predecessor_identity,
                situated,
            },
        ))
    }

    pub fn restore_latest_returned_difference(
        predecessor: RecurrentReturnedAffinePredecessor,
        withdrawal: RecurrentReturnedAffineDifferenceWithdrawal,
    ) -> Result<Self, LaboratoryCultivationError> {
        let rest = Self::restore_latest_returned_difference_from_admitted(predecessor, withdrawal)?;
        rest.validate()?;
        Ok(rest)
    }

    pub(super) fn restore_latest_returned_difference_from_admitted(
        predecessor: RecurrentReturnedAffinePredecessor,
        withdrawal: RecurrentReturnedAffineDifferenceWithdrawal,
    ) -> Result<Self, LaboratoryCultivationError> {
        if predecessor.identity() != withdrawal.predecessor_rest_identity_sha256 {
            return Err(LaboratoryCultivationError::Wire(
                "the recurrent affine return was offered to another predecessor".to_owned(),
            ));
        }
        let predecessor_identity = predecessor.identity().to_owned();
        let (
            origin_predecessor_rest_identity_sha256,
            origin_predecessor_body_identity_sha256,
            body,
            potential,
            codec,
            correspondences,
            affine_cells,
            mut rest_identity_history,
        ) = match predecessor {
            RecurrentReturnedAffinePredecessor::First(rest) => {
                let ReturnedAffineLaboratoryAthenaRest {
                    schema: _,
                    predecessor_rest_identity_sha256,
                    predecessor_body_identity_sha256,
                    body,
                    potential,
                    codec,
                    correspondences,
                    affine_cells,
                    identity_sha256: _,
                } = rest;
                (
                    predecessor_rest_identity_sha256,
                    predecessor_body_identity_sha256,
                    RecurrentLaboratoryPredecessor::First(body),
                    potential,
                    codec,
                    correspondences,
                    affine_cells,
                    Vec::new(),
                )
            }
            RecurrentReturnedAffinePredecessor::Recurrent(rest) => {
                let Self {
                    schema: _,
                    rest_identity_history,
                    origin_predecessor_rest_identity_sha256,
                    origin_predecessor_body_identity_sha256,
                    body,
                    potential,
                    codec,
                    correspondences,
                    affine_cells,
                    identity_sha256: _,
                } = rest;
                (
                    origin_predecessor_rest_identity_sha256,
                    origin_predecessor_body_identity_sha256,
                    RecurrentLaboratoryPredecessor::Recurrent(body),
                    potential,
                    codec,
                    correspondences,
                    affine_cells,
                    rest_identity_history,
                )
            }
        };
        let body = RecurrentLaboratoryCultivatedAthenaRest::
            restore_latest_returned_difference_from_admitted(body, withdrawal.situated)
        .map_err(|error| LaboratoryCultivationError::Situated(error.to_string()))?;
        rest_identity_history.push(predecessor_identity);
        let rest = Self {
            schema: RECURRENT_RETURNED_REST_SCHEMA.to_owned(),
            rest_identity_history,
            origin_predecessor_rest_identity_sha256,
            origin_predecessor_body_identity_sha256,
            body,
            potential,
            codec,
            correspondences,
            affine_cells,
            identity_sha256: withdrawal.original_rest_identity_sha256,
        };
        Ok(rest)
    }

    fn rederived_identity(&self) -> Result<String, LaboratoryCultivationError> {
        let potential = self
            .potential
            .canonical_bytes()
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        let codec = self
            .codec
            .canonical_bytes(&self.potential)
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        digest_json(&(
            RECURRENT_RETURNED_REST_SCHEMA,
            &self.rest_identity_history,
            &self.origin_predecessor_rest_identity_sha256,
            &self.origin_predecessor_body_identity_sha256,
            self.body.identity(),
            Sha256::digest(&potential).as_slice(),
            Sha256::digest(&codec).as_slice(),
            &self.correspondences,
            &self.affine_cells,
        ))
    }
}
