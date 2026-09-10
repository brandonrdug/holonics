//! Assembly of the existing constitutive field, independent of an exterior medium.
//! The field owns occurrence lineage, current, learned material and its one successor.
//! This recipe is immutable apparatus/law data, not another model state or learner.

use super::NativeSessionError;
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        NativeConstitutiveField, NativeFieldJunctionRepresentation, NativeFieldJunctionSolver,
        NativeJunctionSeed, NativeMaterialTarget, NativeMaterialTransportSource,
    },
    resident_section::{ResidentGrain, ResidentSurface},
};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeFieldJunctionSpec {
    pub representation: NativeFieldJunctionRepresentation,
    pub solver: NativeFieldJunctionSolver,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeFieldMaterialSpec {
    pub source: NativeMaterialTransportSource,
    pub target: NativeMaterialTarget,
}

/// A declared finite assembly. Port extent follows the supplied material, not a codec name.
/// Learned incidence and current belong to the founded field, never this seed description.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeFieldModelSpec {
    pub material: Vec<NativeJunctionSeed>,
    pub junction: Option<NativeFieldJunctionSpec>,
    pub material_transport: Option<NativeFieldMaterialSpec>,
}

impl NativeFieldModelSpec {
    /// Found on an existing resident surface, so a larger application can share its apparatus.
    pub fn found_on<'c>(
        &self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<NativeConstitutiveField<'c>, NativeSessionError> {
        let mut field = match self.junction.as_ref().map(|j| j.representation) {
            None => NativeConstitutiveField::found(surface, self.material.clone())?,
            Some(NativeFieldJunctionRepresentation::RationalWords) => {
                NativeConstitutiveField::found_with_paired_junction(surface, self.material.clone())?
            }
            Some(NativeFieldJunctionRepresentation::EnclosedDyadic { fractional_bits }) => {
                NativeConstitutiveField::found_with_enclosed_junction(
                    surface,
                    self.material.clone(),
                    ResidentGrain(fractional_bits),
                )?
            }
        };
        if let Some(material) = &self.material_transport {
            field.enable_material_transport_chart(material.source, material.target)?;
        }
        if let Some(junction) = &self.junction {
            // Operative material has its own supported solver. An incompatible recipe must
            // refuse, not silently replace the requested numerical realization.
            if field.junction_solver() != Some(junction.solver) {
                field.set_junction_solver(junction.solver)?;
            }
        }
        Ok(field)
    }
}

/// One device mount and one field for the callback. Holon source/receiver capabilities remain
/// the engine's actual types; this boundary supplies no text, acoustic or visual topology.
pub fn with_native_field<R, E>(
    spec: &NativeFieldModelSpec,
    operation: impl FnOnce(&mut NativeConstitutiveField<'_>) -> Result<R, E>,
) -> Result<R, E>
where
    E: From<NativeSessionError>,
{
    let readout = ResidentReadout::new()
        .map_err(|e| E::from(NativeSessionError::Application(e.to_string())))?;
    let surface = ResidentSurface::on(&readout)
        .map_err(|e| E::from(NativeSessionError::Application(e.to_string())))?;
    let mut field = spec.found_on(&surface).map_err(E::from)?;
    operation(&mut field)
}

#[cfg(test)]
mod tests;
