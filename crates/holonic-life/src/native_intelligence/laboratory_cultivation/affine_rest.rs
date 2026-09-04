impl AffineLaboratoryCultivatedRest {
    /// Consume the complete L2 body and use L1 plus the exchange projection only as mounted
    /// cultivation testimony.  Neither source object is retained in the returned rest.
    pub fn cultivate(
        body: SituatedCultivatedEcologyRest,
        product: ExchangeSituatedProduct,
        aperture: &ContinuationAperture,
        world: &VisibleMessageProjection,
    ) -> Result<(Self, LaboratoryCultivationReceipt), LaboratoryCultivationError> {
        body.validate()
            .map_err(|error| LaboratoryCultivationError::Situated(error.to_string()))?;
        product
            .validate()
            .map_err(|error| LaboratoryCultivationError::Product(error.to_string()))?;
        validate_exchange_projection(aperture, world)?;
        if body.predecessor_wire_sha256() != product.predecessor_rest_wire_sha256 {
            return Err(LaboratoryCultivationError::Product(
                "the L1 product and L2 body descend from different predecessor rests".to_owned(),
            ));
        }

        let correspondences = factor_correspondences(&body, &product)?;
        let factor_addresses = correspondences
            .iter()
            .map(|factor| factor.factor_address.clone())
            .collect::<Vec<_>>();
        let source_factors = source_factor_map(&product)?;
        let mut builder = NativeRelationalPotentialBuilder::new(factor_addresses)
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        let mut prior_by_container = BTreeMap::<u32, usize>::new();
        for (source_at, family) in ordered_families(aperture) {
            let source = ItemId(u64::try_from(source_at).map_err(display_correspondence)?);
            let factor = *source_factors.get(&source).ok_or_else(|| {
                LaboratoryCultivationError::Correspondence(format!(
                    "exchange source {} has no L2 affine landmark",
                    source.0
                ))
            })?;
            if let Some(prior) = prior_by_container.insert(family.prompt.container, factor) {
                if prior != factor {
                    builder.join_factors(prior, factor).map_err(|error| {
                        LaboratoryCultivationError::Relational(error.to_string())
                    })?;
                }
            }
            receive_message(
                &mut builder,
                factor,
                NativeDeliveryPhase::Ingress,
                world,
                &family.prompt,
                "user",
            )?;
            for response in &family.response {
                receive_message(
                    &mut builder,
                    factor,
                    NativeDeliveryPhase::Emanation,
                    world,
                    response,
                    "assistant",
                )?;
            }
            if let Some(later) = &family.later_operator_return {
                receive_message(
                    &mut builder,
                    factor,
                    NativeDeliveryPhase::Return,
                    world,
                    later,
                    "user",
                )?;
            }
        }
        let (codec, potential, relational) = builder
            .finish()
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        let affine_cells = affine_cell_sections(&potential)?;
        let predecessor_rest_identity_sha256 = body.identity().to_owned();
        let mut rest = Self {
            schema: REST_SCHEMA.to_owned(),
            predecessor_rest_identity_sha256: predecessor_rest_identity_sha256.clone(),
            body,
            potential,
            codec,
            correspondences,
            affine_cells,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        rest.validate()?;
        let receipt = LaboratoryCultivationReceipt {
            predecessor_rest_identity_sha256,
            cultivated_rest_identity_sha256: rest.identity_sha256.clone(),
            addressed_factor_population: rest.correspondences.len(),
            cycle_coordinate_population_per_factor: rest.body.branches().len(),
            exact_cycle_fibre_population: rest
                .correspondences
                .iter()
                .map(|factor| factor.cycle_fibres.len())
                .sum(),
            delivered_occurrence_population: relational.delivered_occurrence_population,
            relational_clause_population: relational.relational_clause_population,
            native_face_population: relational.native_face_population,
            native_cell_population: relational.native_cell_population,
            affine_cell_population: rest.affine_cells.len(),
            factor_world_line_join_population: relational.factor_world_line_join_population,
            aggregate_count_coordinate_population: 0,
            additional_winding_thread_population: 0,
            complete_source_occurrence_lineage_retained: true,
            barycentric_reconstruction_population_retained: true,
        };
        Ok((rest, receipt))
    }

    pub fn read(bytes: &[u8]) -> Result<Self, LaboratoryCultivationError> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| LaboratoryCultivationError::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    /// Remount the complete body against an earlier exact validation receipt.
    ///
    /// This path verifies the whole immutable wire and its internal top-level identities; it does
    /// not claim that a digest can validate a novel rest.  Novel or changed wires must use
    /// [`Self::read`] and replay the complete proof before an admission witness can be founded.
    pub fn read_admitted(
        bytes: &[u8],
        witness: &AdmittedAffineLaboratoryRestWitness,
    ) -> Result<Self, LaboratoryCultivationError> {
        witness.validate()?;
        let measured_wire = render_hex(&Sha256::digest(bytes));
        if measured_wire != witness.rest_wire_sha256 {
            return Err(LaboratoryCultivationError::Wire(
                "the affine rest wire differs from its admitted validated occurrence".to_owned(),
            ));
        }
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| LaboratoryCultivationError::Wire(error.to_string()))?;
        if rest.schema != REST_SCHEMA
            || rest.identity_sha256 != witness.rest_identity_sha256
            || rest.predecessor_rest_identity_sha256 != rest.body.identity()
        {
            return Err(LaboratoryCultivationError::Wire(
                "the admitted affine rest lost its top-level addressed identity".to_owned(),
            ));
        }
        Ok(rest)
    }

    /// Admit this exact previously validated wire directly to membrane constitution without
    /// replaying the complete 431 MB exterior chart inside every subsequent hot operation.
    pub fn read_admitted_membrane(
        bytes: &[u8],
        witness: &AdmittedAffineLaboratoryRestWitness,
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

    pub fn body(&self) -> &SituatedCultivatedEcologyRest {
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

    pub fn native_face_population(&self) -> usize {
        self.potential.faces.len()
    }

    pub fn native_cell_population(&self) -> usize {
        self.potential.cells.len()
    }

    /// Consume this exact affine predecessor and cultivate one complete situated return in its
    /// native ecology.  The affine organ is carried across the type-state transition; no source
    /// occurrence, lookup table, or independently live predecessor is retained.
    pub fn deposit_returned_difference(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<ReturnedAffineLaboratoryRest, LaboratoryCultivationError> {
        self.validate()?;
        let Self {
            schema: _,
            predecessor_rest_identity_sha256: _,
            body,
            potential,
            codec,
            correspondences,
            affine_cells,
            identity_sha256: predecessor_rest_identity_sha256,
        } = self;
        let predecessor_body_identity_sha256 = body.identity().to_owned();
        let body = body
            .deposit_returned_difference(difference)
            .map_err(|error| LaboratoryCultivationError::Situated(error.to_string()))?;
        let mut rest = ReturnedAffineLaboratoryRest {
            schema: RETURNED_REST_SCHEMA.to_owned(),
            predecessor_rest_identity_sha256,
            predecessor_body_identity_sha256,
            body,
            potential,
            codec,
            correspondences,
            affine_cells,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        rest.validate()?;
        Ok(rest)
    }

    /// Run the inherited native body and recover this exact affine owner after resident release.
    /// The relational organ remains move-owned beside the run and cannot act as a second ecology.
    pub fn conduct_native_body(
        self,
    ) -> Result<(Self, SituatedCultivatedConductReturn), LaboratoryCultivationError> {
        self.validate()?;
        let Self {
            schema,
            predecessor_rest_identity_sha256,
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

    /// Return the native target/sibling partition used by an ablation receiver.  This reads the
    /// existing participant incidence and never performs lexical or query-conditioned selection.
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
                "the cultivated affine ecology does not expose both target and disjoint sibling cells"
                    .to_owned(),
            ));
        }
        Ok(AffineLaboratoryAblationAtlas {
            participant_incident_cells,
            participant_disjoint_cells,
        })
    }

    /// Move one exact relational cell out of the continuing ecology.  The returned rest owns all
    /// remaining cells; the withdrawal owns the missing cell and is the only lawful restoration
    /// passage.
    pub fn withdraw_relational_cell(
        self,
        cell_address: &str,
    ) -> Result<(Self, AffineLaboratoryCellWithdrawal), LaboratoryCultivationError> {
        self.validate()?;
        let (rest, withdrawal) = self.withdraw_relational_cell_from_admitted(cell_address)?;
        rest.validate()?;
        Ok((rest, withdrawal))
    }

    /// Apply the support-local move to a rest which has already crossed an exact admission
    /// boundary.  The fields of this type are private and every public wire entrance validates;
    /// this path prevents a nested owner from serially revalidating the complete native ecology.
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
                    "the requested local ablation cell is absent".to_owned(),
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

    /// Consume a moved cell and recover the exact pre-ablation affine rest identity.
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
                "the moved affine cell was offered to a different local ablation body".to_owned(),
            ));
        }
        self.potential
            .cells
            .insert(withdrawal.original_position, withdrawal.cell);
        self.affine_cells = affine_cell_sections(&self.potential)?;
        self.identity_sha256 = self.rederived_identity()?;
        if self.identity_sha256 != withdrawal.original_rest_identity_sha256 {
            return Err(LaboratoryCultivationError::Wire(
                "local cell restoration did not recover the exact cultivated rest".to_owned(),
            ));
        }
        Ok(self)
    }

    /// Mount the complete participant/deed contact atlas once. Surface words and later proper
    /// names do not cross this boundary.
    pub fn mount(self) -> Result<ResidentAffineLaboratoryEcology, LaboratoryCultivationError> {
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
                    "a participant cell support escaped the card address line".to_owned(),
                )
            })?);
            occurrence_mass.push(
                cell.occurrence_population()
                    .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?,
            );
            last_occurrence.push(cell.last_delivery_order().ok_or_else(|| {
                LaboratoryCultivationError::Correspondence(
                    "a participant cell lost its causal chronology".to_owned(),
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
                    "a resident affine cell lost its factor/multiplicity incidence".to_owned(),
                ));
            }
            let total = cell
                .occurrence_multiplicities
                .iter()
                .try_fold(0u64, |sum, mass| sum.checked_add(*mass))
                .ok_or_else(|| {
                    LaboratoryCultivationError::Correspondence(
                        "the resident affine mass overflowed".to_owned(),
                    )
                })?;
            cell_factors.extend(cell.landmark_factors.iter().copied());
            multiplicities.extend(cell.occurrence_multiplicities.iter().copied());
            cell_total_mass.push(total);
            cell_offsets.push(u64::try_from(multiplicities.len()).map_err(|_| {
                LaboratoryCultivationError::Correspondence(
                    "the affine support escaped the resident offset chart".to_owned(),
                )
            })?);
        }
        let Self {
            schema,
            predecessor_rest_identity_sha256,
            body,
            potential,
            codec,
            correspondences,
            affine_cells,
            identity_sha256,
        } = self;
        let (incidence, front, interactions, factors, expected) =
            derive_resident_coupling(&body)
                .map_err(|error| LaboratoryCultivationError::Situated(error.to_string()))?;
        let resident = ResidentIntegratedFront::mount(
            CudaRefineExecutor::new()
                .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?,
            format!("affine-laboratory-coupled/{identity_sha256}"),
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
        Ok(ResidentAffineLaboratoryEcology {
            schema,
            predecessor_rest_identity_sha256,
            body,
            factors,
            expected,
            potential,
            codec,
            correspondences,
            affine_cells,
            identity_sha256,
            participant_faces,
            resident,
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
        validate_correspondences(&self.body, &self.potential, &self.correspondences)?;
        if self.schema != REST_SCHEMA
            || self.predecessor_rest_identity_sha256 != self.body.identity()
            || self.affine_cells != affine_cell_sections(&self.potential)?
            || !is_digest(&self.identity_sha256)
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(LaboratoryCultivationError::Wire(
                "the affine laboratory rest does not reconstruct from its singular body".to_owned(),
            ));
        }
        Ok(())
    }

    pub fn withdraw_relational_organ(
        self,
    ) -> Result<
        (
            SituatedCultivatedEcologyRest,
            AffineLaboratoryCultivationWithdrawal,
        ),
        LaboratoryCultivationError,
    > {
        self.validate()?;
        let Self {
            schema: _,
            predecessor_rest_identity_sha256,
            body,
            potential,
            codec,
            correspondences,
            affine_cells,
            identity_sha256,
        } = self;
        let withdrawal = AffineLaboratoryCultivationWithdrawal {
            original_rest_identity_sha256: identity_sha256,
            predecessor_rest_identity_sha256: predecessor_rest_identity_sha256.clone(),
            potential,
            codec,
            correspondences,
            affine_cells,
        };
        if body.identity() != predecessor_rest_identity_sha256 {
            return Err(LaboratoryCultivationError::Wire(
                "relational withdrawal did not recover the exact L2 identity".to_owned(),
            ));
        }
        Ok((body, withdrawal))
    }

    pub fn restore_relational_organ(
        body: SituatedCultivatedEcologyRest,
        withdrawal: AffineLaboratoryCultivationWithdrawal,
    ) -> Result<Self, LaboratoryCultivationError> {
        if body.identity() != withdrawal.predecessor_rest_identity_sha256 {
            return Err(LaboratoryCultivationError::Wire(
                "the withdrawn organ was offered to a different L2 body".to_owned(),
            ));
        }
        let mut rest = Self {
            schema: REST_SCHEMA.to_owned(),
            predecessor_rest_identity_sha256: withdrawal.predecessor_rest_identity_sha256,
            body,
            potential: withdrawal.potential,
            codec: withdrawal.codec,
            correspondences: withdrawal.correspondences,
            affine_cells: withdrawal.affine_cells,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        if rest.identity_sha256 != withdrawal.original_rest_identity_sha256 {
            return Err(LaboratoryCultivationError::Wire(
                "relational restoration did not recover the original rest identity".to_owned(),
            ));
        }
        rest.validate()?;
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
            REST_SCHEMA,
            self.body.identity(),
            Sha256::digest(&potential).as_slice(),
            Sha256::digest(&codec).as_slice(),
            &self.correspondences,
            &self.affine_cells,
        ))
    }
}
