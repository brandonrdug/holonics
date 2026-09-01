impl super::MembraneStanding for AffineLaboratoryCultivatedRest {
    fn validate_membrane_standing(&self) -> Result<(), String> {
        self.validate().map_err(|error| error.to_string())
    }

    fn membrane_identity(&self) -> &str {
        self.identity()
    }

    fn membrane_ecology(&self) -> &holonic_engine::native_spool::NativeSituatedSpoolBundle {
        self.body.ecology()
    }

    fn membrane_realization(&self) -> &super::ReceiverHistoryRealizationPassage {
        self.body.realization()
    }

    fn membrane_branches(&self) -> &[SituatedCultivationBranch] {
        self.body.branches()
    }

    fn membrane_correspondences(&self) -> &[LaboratoryFactorCycleCorrespondence] {
        &self.correspondences
    }

    fn membrane_affine_cells(&self) -> &[LaboratoryCellAffineSection] {
        &self.affine_cells
    }
}

impl super::MembraneStanding for ReturnedAffineLaboratoryRest {
    fn validate_membrane_standing(&self) -> Result<(), String> {
        self.validate().map_err(|error| error.to_string())
    }

    fn membrane_identity(&self) -> &str {
        self.identity()
    }

    fn membrane_ecology(&self) -> &holonic_engine::native_spool::NativeSituatedSpoolBundle {
        self.body.ecology()
    }

    fn membrane_realization(&self) -> &super::ReceiverHistoryRealizationPassage {
        self.body.realization()
    }

    fn membrane_branches(&self) -> &[SituatedCultivationBranch] {
        self.body.branches()
    }

    fn membrane_correspondences(&self) -> &[LaboratoryFactorCycleCorrespondence] {
        &self.correspondences
    }

    fn membrane_affine_cells(&self) -> &[LaboratoryCellAffineSection] {
        &self.affine_cells
    }
}

impl super::MembraneStanding for RecurrentReturnedAffineLaboratoryRest {
    fn validate_membrane_standing(&self) -> Result<(), String> {
        self.validate().map_err(|error| error.to_string())
    }

    fn membrane_identity(&self) -> &str {
        self.identity()
    }

    fn membrane_ecology(&self) -> &holonic_engine::native_spool::NativeSituatedSpoolBundle {
        self.body.ecology()
    }

    fn membrane_realization(&self) -> &super::ReceiverHistoryRealizationPassage {
        self.body.realization()
    }

    fn membrane_branches(&self) -> &[SituatedCultivationBranch] {
        self.body.branches()
    }

    fn membrane_correspondences(&self) -> &[LaboratoryFactorCycleCorrespondence] {
        &self.correspondences
    }

    fn membrane_affine_cells(&self) -> &[LaboratoryCellAffineSection] {
        &self.affine_cells
    }
}

impl MaterialFactorizationStanding for AffineLaboratoryCultivatedRest {
    fn validate_material_standing(&self) -> Result<(), String> {
        self.validate().map_err(|error| error.to_string())
    }

    fn material_standing_identity(&self) -> &str {
        self.identity()
    }

    fn material_standing_branches(&self) -> &[SituatedCultivationBranch] {
        self.body.branches()
    }

    fn material_standing_ecology(
        &self,
    ) -> &holonic_engine::native_spool::NativeSituatedSpoolBundle {
        self.body.ecology()
    }

    fn material_standing_realization(&self) -> &super::ReceiverHistoryRealizationPassage {
        self.body.realization()
    }

    fn material_affine_transport(
        &self,
        entering_section: &[i64],
    ) -> Result<Option<MaterialAffineTransportReceipt>, String> {
        // `MaterialFactorizationAperture::found` has already validated this exact borrowed rest.
        // Revalidating its complete nested morphology for every exterior presentation would
        // serialize cross-codec circulation over an unchanged body.
        material_affine_transport_from_parts(
            self.identity(),
            self.body.branches().len(),
            &self.correspondences,
            &self.affine_cells,
            entering_section,
        )
    }
}

impl MaterialFactorizationStanding for ReturnedAffineLaboratoryRest {
    fn validate_material_standing(&self) -> Result<(), String> {
        self.validate().map_err(|error| error.to_string())
    }

    fn material_standing_identity(&self) -> &str {
        self.identity()
    }

    fn material_standing_branches(&self) -> &[SituatedCultivationBranch] {
        self.body.branches()
    }

    fn material_standing_ecology(
        &self,
    ) -> &holonic_engine::native_spool::NativeSituatedSpoolBundle {
        self.body.ecology()
    }

    fn material_standing_realization(&self) -> &super::ReceiverHistoryRealizationPassage {
        self.body.realization()
    }

    fn material_affine_transport(
        &self,
        entering_section: &[i64],
    ) -> Result<Option<MaterialAffineTransportReceipt>, String> {
        // The owning material aperture validated this exact borrowed rest before factorization.
        material_affine_transport_from_parts(
            self.identity(),
            self.body.branches().len(),
            &self.correspondences,
            &self.affine_cells,
            entering_section,
        )
    }
}

impl MaterialFactorizationStanding for RecurrentReturnedAffineLaboratoryRest {
    fn validate_material_standing(&self) -> Result<(), String> {
        self.validate().map_err(|error| error.to_string())
    }

    fn material_standing_identity(&self) -> &str {
        self.identity()
    }

    fn material_standing_branches(&self) -> &[SituatedCultivationBranch] {
        self.body.branches()
    }

    fn material_standing_ecology(
        &self,
    ) -> &holonic_engine::native_spool::NativeSituatedSpoolBundle {
        self.body.ecology()
    }

    fn material_standing_realization(&self) -> &super::ReceiverHistoryRealizationPassage {
        self.body.realization()
    }

    fn material_affine_transport(
        &self,
        entering_section: &[i64],
    ) -> Result<Option<MaterialAffineTransportReceipt>, String> {
        // The owning material aperture validated this exact borrowed rest before factorization.
        material_affine_transport_from_parts(
            self.identity(),
            self.body.branches().len(),
            &self.correspondences,
            &self.affine_cells,
            entering_section,
        )
    }
}
