impl ReturnedAffineLaboratoryRest {
    pub fn read(bytes: &[u8]) -> Result<Self, LaboratoryCultivationError> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| LaboratoryCultivationError::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn read_admitted(
        bytes: &[u8],
        witness: &AdmittedReturnedAffineLaboratoryRestWitness,
    ) -> Result<Self, LaboratoryCultivationError> {
        witness.validate()?;
        let measured_wire = render_hex(&Sha256::digest(bytes));
        if measured_wire != witness.rest_wire_sha256 {
            return Err(LaboratoryCultivationError::Wire(
                "the returned affine rest wire differs from its admitted occurrence".to_owned(),
            ));
        }
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| LaboratoryCultivationError::Wire(error.to_string()))?;
        if rest.schema != RETURNED_REST_SCHEMA
            || rest.identity_sha256 != witness.rest_identity_sha256
            || rest.predecessor_body_identity_sha256 != rest.body.predecessor_identity()
        {
            return Err(LaboratoryCultivationError::Wire(
                "the admitted returned affine rest lost its top-level lineage".to_owned(),
            ));
        }
        Ok(rest)
    }

    /// Move one exactly admitted returned wire into the membrane without replaying its complete
    /// cold chart validation at every resident contact.
    pub fn read_admitted_membrane(
        bytes: &[u8],
        witness: &AdmittedReturnedAffineLaboratoryRestWitness,
    ) -> Result<super::AdmittedMembraneStanding<Self>, LaboratoryCultivationError> {
        let rest = Self::read_admitted(bytes, witness)?;
        super::AdmittedMembraneStanding::from_validated_wire(
            rest,
            witness.rest_identity_sha256.clone(),
            witness.complete_validation_receipt_sha256.clone(),
        )
        .map_err(LaboratoryCultivationError::Wire)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, LaboratoryCultivationError> {
        self.validate()?;
        serde_json::to_vec(self)
            .map_err(|error| LaboratoryCultivationError::Wire(error.to_string()))
    }

    pub fn identity(&self) -> &str {
        &self.identity_sha256
    }

    pub fn predecessor_identity(&self) -> &str {
        &self.predecessor_rest_identity_sha256
    }

    pub fn body(&self) -> &LaboratoryCultivatedRest {
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
        if self.schema != RETURNED_REST_SCHEMA {
            return Err(LaboratoryCultivationError::Wire(
                "the returned affine rest has the wrong schema".to_owned(),
            ));
        }
        if self.predecessor_body_identity_sha256 != self.body.predecessor_identity() {
            return Err(LaboratoryCultivationError::Wire(format!(
                "the returned body predecessor identity differs: held {}, reconstructed {}",
                self.predecessor_body_identity_sha256,
                self.body.predecessor_identity()
            )));
        }
        if !is_digest(&self.predecessor_rest_identity_sha256) {
            return Err(LaboratoryCultivationError::Wire(
                "the returned affine predecessor address is not a digest".to_owned(),
            ));
        }
        if self.affine_cells != affine_cell_sections(&self.potential)? {
            return Err(LaboratoryCultivationError::Wire(
                "the returned affine sections do not reconstruct from the retained organ"
                    .to_owned(),
            ));
        }
        if !is_digest(&self.identity_sha256) {
            return Err(LaboratoryCultivationError::Wire(
                "the returned affine identity is not a digest".to_owned(),
            ));
        }
        let expected_identity = self.rederived_identity()?;
        if self.identity_sha256 != expected_identity {
            return Err(LaboratoryCultivationError::Wire(format!(
                "the returned affine identity differs: held {}, reconstructed {}",
                self.identity_sha256, expected_identity
            )));
        }
        Ok(())
    }

    /// Run the complete coupled successor and return the same rested owner after the card releases
    /// it.  This is used by a receiver, never to duplicate the continuing ecology.
    pub fn conduct_native_body(
        self,
    ) -> Result<(Self, SituatedCultivatedConductReturn), LaboratoryCultivationError> {
        self.validate()?;
        let Self {
            schema,
            predecessor_rest_identity_sha256,
            predecessor_body_identity_sha256,
            body,
            potential,
            codec,
            correspondences,
            affine_cells,
            identity_sha256,
        } = self;
        let mut resident = body
            .mount()
            .map_err(|error| LaboratoryCultivationError::Situated(error.to_string()))?;
        let returned = resident
            .conduct()
            .map_err(|error| LaboratoryCultivationError::Situated(error.to_string()))?;
        let body = resident.into_rest();
        let rest = Self {
            schema,
            predecessor_rest_identity_sha256,
            predecessor_body_identity_sha256,
            body,
            potential,
            codec,
            correspondences,
            affine_cells,
            identity_sha256,
        };
        rest.validate()?;
        Ok((rest, returned))
    }

    /// Remove the returned passage and recover the exact affine predecessor.  The move-owned
    /// withdrawal is the complete reconstruction fibre for the removed local morphology.
    pub fn withdraw_returned_difference(
        self,
    ) -> Result<
        (
            AffineLaboratoryCultivatedRest,
            ReturnedAffineLaboratoryDifferenceWithdrawal,
        ),
        LaboratoryCultivationError,
    > {
        self.validate()?;
        let Self {
            schema: _,
            predecessor_rest_identity_sha256,
            predecessor_body_identity_sha256,
            body,
            potential,
            codec,
            correspondences,
            affine_cells,
            identity_sha256,
        } = self;
        let (body, situated) = body
            .withdraw_returned_difference()
            .map_err(|error| LaboratoryCultivationError::Situated(error.to_string()))?;
        let mut predecessor = AffineLaboratoryCultivatedRest {
            schema: REST_SCHEMA.to_owned(),
            predecessor_rest_identity_sha256: body.identity().to_owned(),
            body,
            potential,
            codec,
            correspondences,
            affine_cells,
            identity_sha256: String::new(),
        };
        predecessor.identity_sha256 = predecessor.rederived_identity()?;
        if predecessor.identity_sha256 != predecessor_rest_identity_sha256 {
            return Err(LaboratoryCultivationError::Wire(
                "returned-difference withdrawal did not recover the exact affine predecessor"
                    .to_owned(),
            ));
        }
        predecessor.validate()?;
        Ok((
            predecessor,
            ReturnedAffineLaboratoryDifferenceWithdrawal {
                original_rest_identity_sha256: identity_sha256,
                predecessor_rest_identity_sha256,
                predecessor_body_identity_sha256,
                situated,
            },
        ))
    }

    pub fn restore_returned_difference(
        predecessor: AffineLaboratoryCultivatedRest,
        withdrawal: ReturnedAffineLaboratoryDifferenceWithdrawal,
    ) -> Result<Self, LaboratoryCultivationError> {
        predecessor.validate()?;
        if predecessor.identity() != withdrawal.predecessor_rest_identity_sha256 {
            return Err(LaboratoryCultivationError::Wire(
                "the returned passage was offered to a different affine predecessor".to_owned(),
            ));
        }
        let AffineLaboratoryCultivatedRest {
            schema: _,
            predecessor_rest_identity_sha256: _,
            body,
            potential,
            codec,
            correspondences,
            affine_cells,
            identity_sha256: _,
        } = predecessor;
        let body =
            LaboratoryCultivatedRest::restore_returned_difference(body, withdrawal.situated)
                .map_err(|error| LaboratoryCultivationError::Situated(error.to_string()))?;
        if body.predecessor_identity() != withdrawal.predecessor_body_identity_sha256 {
            return Err(LaboratoryCultivationError::Wire(
                "returned passage restoration changed the inherited body address".to_owned(),
            ));
        }
        let mut rest = Self {
            schema: RETURNED_REST_SCHEMA.to_owned(),
            predecessor_rest_identity_sha256: withdrawal.predecessor_rest_identity_sha256,
            predecessor_body_identity_sha256: withdrawal.predecessor_body_identity_sha256,
            body,
            potential,
            codec,
            correspondences,
            affine_cells,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        if rest.identity_sha256 != withdrawal.original_rest_identity_sha256 {
            return Err(LaboratoryCultivationError::Wire(
                "returned passage restoration did not recover the exact successor".to_owned(),
            ));
        }
        rest.validate()?;
        Ok(rest)
    }

    /// Remove one relation cell while preserving the complete returned native passage.  This is
    /// the support-disjoint sibling control for the morphology delta.
    pub fn withdraw_relational_cell(
        mut self,
        cell_address: &str,
    ) -> Result<(Self, AffineLaboratoryCellWithdrawal), LaboratoryCultivationError> {
        self.validate()?;
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
                    "the requested local ablation cell is absent".to_owned(),
                )
            })?;
        let original_rest_identity_sha256 = self.identity_sha256.clone();
        let cell = self.potential.cells.remove(original_position);
        self.affine_cells = affine_cell_sections(&self.potential)?;
        self.identity_sha256 = self.rederived_identity()?;
        let ablated_rest_identity_sha256 = self.identity_sha256.clone();
        self.validate()?;
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
        mut self,
        withdrawal: AffineLaboratoryCellWithdrawal,
    ) -> Result<Self, LaboratoryCultivationError> {
        self.validate()?;
        if self.identity_sha256 != withdrawal.ablated_rest_identity_sha256
            || withdrawal.original_position > self.potential.cells.len()
            || self
                .potential
                .cells
                .iter()
                .any(|cell| cell.address == withdrawal.cell.address)
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the moved affine cell was offered to a different returned body".to_owned(),
            ));
        }
        self.potential
            .cells
            .insert(withdrawal.original_position, withdrawal.cell);
        self.affine_cells = affine_cell_sections(&self.potential)?;
        self.identity_sha256 = self.rederived_identity()?;
        if self.identity_sha256 != withdrawal.original_rest_identity_sha256 {
            return Err(LaboratoryCultivationError::Wire(
                "returned-body cell restoration did not recover the exact successor".to_owned(),
            ));
        }
        self.validate()?;
        Ok(self)
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
            RETURNED_REST_SCHEMA,
            &self.predecessor_rest_identity_sha256,
            &self.predecessor_body_identity_sha256,
            self.body.identity(),
            Sha256::digest(&potential).as_slice(),
            Sha256::digest(&codec).as_slice(),
            &self.correspondences,
            &self.affine_cells,
        ))
    }

    /// Carry the existing affine organ across one later world return. No second relational body
    /// is founded and no exterior source face survives in the successor.
    pub fn deposit_additional_returned_difference(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<RecurrentReturnedAffineLaboratoryRest, LaboratoryCultivationError> {
        self.validate()?;
        let rest = self.deposit_additional_returned_difference_admitted(difference)?;
        rest.validate()?;
        Ok(rest)
    }

    pub(super) fn deposit_additional_returned_difference_admitted(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<RecurrentReturnedAffineLaboratoryRest, LaboratoryCultivationError> {
        let Self {
            schema: _,
            predecessor_rest_identity_sha256: origin_predecessor_rest_identity_sha256,
            predecessor_body_identity_sha256: origin_predecessor_body_identity_sha256,
            body,
            potential,
            codec,
            correspondences,
            affine_cells,
            identity_sha256: predecessor_identity,
        } = self;
        let body = body
            .deposit_additional_returned_difference_admitted(difference)
            .map_err(|error| LaboratoryCultivationError::Situated(error.to_string()))?;
        let mut rest = RecurrentReturnedAffineLaboratoryRest {
            schema: RECURRENT_RETURNED_REST_SCHEMA.to_owned(),
            rest_identity_history: vec![predecessor_identity],
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
}
