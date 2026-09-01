//! The morphology-derived interior constitution of the singular Athena membrane.
//!
//! The cultivated body already owns the incidence, capacities, exact mixed response and affine
//! sections needed for contact.  This module rotates those owners into one compact cellular-sheaf
//! chart.  It does not add a media class, semantic route, authored width, global affine origin or
//! second ecology.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::{
    cuda_refine::{CudaRefineExecutor, ResidentMembraneInteriorWord},
    CausalCellId, CausalChain, CellularRestriction, ComparativeMultiplicity, EventId,
    ExactCellularSheaf, ExactComplexWaveCurrent, ExactLinearMap, ExactRatMatrix,
    GradedCausalComplex,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::Serialize;
use sha2::{Digest, Sha256};
use thiserror::Error;

use super::{LaboratoryCellAffineSection, LaboratoryFactorCycleCorrespondence, MembraneStanding};

pub const MEMBRANE_INTERIOR_SCHEMA: &str = "soma-life.morphology-derived-native-interior.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct InteriorConstitutionReceipt {
    pub schema: String,
    pub rested_identity_sha256: String,
    pub exact_sheaf_sha256: String,
    pub factor_cell_population: usize,
    pub constitutive_cell_population: usize,
    pub restriction_population: usize,
    pub affine_cochain_population: usize,
    pub derived_stalk_rank: usize,
    pub total_cultivated_capacity: u64,
    pub fixed_behavioral_capacity_supplied: bool,
    pub global_affine_origin_supplied: bool,
    pub semantic_topology_supplied: bool,
    pub all_to_all_affine_edges_materialized: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AffineMembraneCochain {
    pub cell_address: String,
    pub coefficients: Vec<(u32, Rat)>,
    pub occurrence_multiplicities: Vec<(u32, u64)>,
    pub source_occurrence_identities_sha256: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ConstitutiveFamilyContact {
    pub family_address: String,
    pub left_coordinate: Option<usize>,
    pub right_coordinate: Option<usize>,
    pub left_winding_section: Vec<Rat>,
    pub right_winding_section: Vec<Rat>,
    pub storage: Rat,
    pub oriented_overlap: Rat,
    pub returned_product: ExactComplexWaveCurrent,
    pub weighted_response: ExactComplexWaveCurrent,
}

/// Exact constitutive current across one receiver-history support passage.
///
/// The context and target populations come from the recurrent carrier.  Their common factors
/// found contact; their signed set difference is retained as the oriented exterior boundary.
/// Recurrence is a caused population multiplier, never a selector or probability.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct FactorSupportBoundaryCurrent {
    pub schema: String,
    pub rested_identity_sha256: String,
    pub context_factors: Vec<u32>,
    pub target_factors: Vec<u32>,
    pub shared_factors: Vec<u32>,
    pub oriented_factor_boundary: Vec<(u32, i8)>,
    pub recurrence_multiplicity: u64,
    pub capacity_weighted_overlap: Rat,
    pub family_contacts: Vec<ConstitutiveFamilyContact>,
    pub returned_response: ExactComplexWaveCurrent,
    pub opposite_returned_response: ExactComplexWaveCurrent,
    pub exact_exchange_balance: ExactComplexWaveCurrent,
    pub response_is_in_constitutive_radical: bool,
    pub complete_support_fibre_retained: bool,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ExactLocalReconstructionFibre {
    pub coordinate_factors: Vec<u32>,
    pub receiver_functional: Vec<Rat>,
    pub returned_overlap: Rat,
    pub local_pivot_factor: u32,
    pub particular: Vec<Rat>,
    pub presented_partner_section: Vec<Rat>,
    pub hidden_difference: Vec<Rat>,
    pub radical: Vec<Vec<Rat>>,
    pub functional_on_hidden_difference: Rat,
    pub no_global_origin_was_introduced: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct FoundedInteriorContact {
    pub schema: String,
    pub rested_identity_sha256: String,
    pub left: AffineMembraneCochain,
    pub right: AffineMembraneCochain,
    pub shared_factors: Vec<u32>,
    pub capacity_weighted_overlap: Rat,
    pub family_contacts: Vec<ConstitutiveFamilyContact>,
    pub returned_response: ExactComplexWaveCurrent,
    pub opposite_returned_response: ExactComplexWaveCurrent,
    pub exact_exchange_balance: ExactComplexWaveCurrent,
    pub simultaneously_reoriented_overlap: Rat,
    pub simultaneously_reoriented_response: ExactComplexWaveCurrent,
    pub reconstruction_fibre: ExactLocalReconstructionFibre,
    pub directional_withdrawal_fibre_retained: bool,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SharedSupportObstruction {
    pub schema: String,
    pub rested_identity_sha256: String,
    pub left: AffineMembraneCochain,
    pub right: AffineMembraneCochain,
    pub shared_factors: Vec<u32>,
    pub returned_response: ExactComplexWaveCurrent,
    pub reason: String,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case", tag = "disposition", content = "return")]
pub enum InteriorContactConsequence {
    Founded(FoundedInteriorContact),
    Obstructed(SharedSupportObstruction),
}

#[derive(Clone, Debug)]
struct ConstitutiveCellAddress {
    family_at: usize,
    cell: CausalCellId,
    left_coordinate: Option<usize>,
    right_coordinate: Option<usize>,
    left_winding_section: Vec<Rat>,
    right_winding_section: Vec<Rat>,
    factor_orientations: BTreeMap<u32, i8>,
}

/// A compiled constitutive view of the one move-owned rest.
///
/// The sheaf and indexes are derived apparatus.  Source cells and mixed current remain owned only
/// by the rest inside [`super::NativeCausalMembrane`].
pub struct MorphologyDerivedInterior {
    sheaf: ExactCellularSheaf,
    factor_cells: BTreeMap<u32, CausalCellId>,
    factor_capacities: BTreeMap<u32, u64>,
    affine_cells: BTreeMap<String, usize>,
    constitutive_cells: Vec<ConstitutiveCellAddress>,
    receipt: InteriorConstitutionReceipt,
}

impl MorphologyDerivedInterior {
    /// Return the exact factor capacities and constitutive orientations in the same dense factor
    /// chart used by the resident word.  These are mounted standing, not a second semantic view;
    /// the receiver-history quotient consumes them once while founding its invariant image.
    pub(crate) fn receiver_history_constitution(&self) -> (Vec<u64>, Vec<i8>) {
        let factor_capacity = self
            .factor_cells
            .keys()
            .map(|factor| self.factor_capacities[factor])
            .collect::<Vec<_>>();
        let family_orientation = self
            .constitutive_cells
            .iter()
            .flat_map(|family| {
                self.factor_cells
                    .keys()
                    .map(move |factor| family.factor_orientations.get(factor).copied().unwrap_or(0))
            })
            .collect::<Vec<_>>();
        (factor_capacity, family_orientation)
    }

    pub fn derive(rest: &impl MembraneStanding) -> Result<Self, MembraneInteriorError> {
        rest.validate_membrane_standing()
            .map_err(MembraneInteriorError::MalformedStanding)?;
        let rank = rest.membrane_branches().len();
        if rank == 0
            || rest.membrane_correspondences().is_empty()
            || rest.membrane_affine_cells().is_empty()
        {
            return Err(MembraneInteriorError::MalformedStanding(
                "the membrane interior lost its cultivated base or local fibre rank".to_owned(),
            ));
        }

        let exact_fibres = rest.membrane_ecology().exact_reconstruction_fibres();
        let fibre_by_address = exact_fibres
            .iter()
            .map(|fibre| (fibre.address.as_str(), fibre))
            .collect::<BTreeMap<_, _>>();
        // Capacity is the complete local caused population.  Every base factor first contributes
        // the union of its exact cycle-fibre occurrences; affine incidence then contributes the
        // later cultivated population.  A factor absent from one relational chart therefore does
        // not disappear, and no caller supplies a replacement extent.
        let mut capacities = BTreeMap::new();
        for factor in rest.membrane_correspondences() {
            let mut base_occurrences = BTreeSet::new();
            for fibre_address in &factor.cycle_fibres {
                let fibre = fibre_by_address
                    .get(fibre_address.exact_fibre_address.as_str())
                    .ok_or_else(|| {
                        MembraneInteriorError::MissingFibre(
                            fibre_address.exact_fibre_address.clone(),
                        )
                    })?;
                base_occurrences.extend(fibre.occurrences.iter().copied());
            }
            let base_capacity = u64::try_from(base_occurrences.len())
                .map_err(|_| MembraneInteriorError::CapacityOverflow)?;
            capacities.insert(factor.factor, base_capacity);
        }
        let mut affine_index = BTreeMap::new();
        for (at, cell) in rest.membrane_affine_cells().iter().enumerate() {
            validate_affine_cell(cell)?;
            if affine_index.insert(cell.cell_address.clone(), at).is_some() {
                return Err(MembraneInteriorError::MalformedStanding(format!(
                    "affine cell {} occurs twice",
                    cell.cell_address
                )));
            }
            for (factor, population) in cell
                .landmark_factors
                .iter()
                .copied()
                .zip(cell.occurrence_multiplicities.iter().copied())
            {
                let capacity = capacities
                    .get_mut(&factor)
                    .ok_or(MembraneInteriorError::MissingFactor(factor))?;
                *capacity = capacity
                    .checked_add(population)
                    .ok_or(MembraneInteriorError::CapacityOverflow)?;
            }
        }
        if capacities.values().any(|capacity| *capacity == 0) {
            return Err(MembraneInteriorError::MalformedStanding(
                "a cultivated factor has no incident occurrence capacity".to_owned(),
            ));
        }

        let mut complex = GradedCausalComplex::default();
        let mut factor_cells = BTreeMap::new();
        let mut orientations = BTreeMap::<(u32, usize), i8>::new();
        let mut stalk_dimensions = BTreeMap::new();
        let mut native_to_factor = BTreeMap::new();
        for correspondence in rest.membrane_correspondences() {
            validate_correspondence(correspondence, rank)?;
            let mut source_events = BTreeSet::new();
            for fibre_address in &correspondence.cycle_fibres {
                let fibre = fibre_by_address
                    .get(fibre_address.exact_fibre_address.as_str())
                    .ok_or_else(|| {
                        MembraneInteriorError::MissingFibre(
                            fibre_address.exact_fibre_address.clone(),
                        )
                    })?;
                if fibre.thread != fibre_address.thread_address
                    || fibre.dependent_receiver_fibre != BTreeSet::from([correspondence.native])
                {
                    return Err(MembraneInteriorError::MalformedStanding(format!(
                        "factor {} lost its exact local fibre incidence",
                        correspondence.factor
                    )));
                }
                source_events.extend(fibre.occurrences.iter().copied());
                orientations.insert(
                    (correspondence.factor, fibre_address.coordinate),
                    exact_fibre_orientation(&fibre.returned_covector).ok_or_else(|| {
                        MembraneInteriorError::UnorientedFibre(
                            fibre_address.exact_fibre_address.clone(),
                        )
                    })?,
                );
            }
            let cell = complex
                .found_cell(
                    format!("native-factor/{}", correspondence.factor_address),
                    source_events,
                    0,
                    CausalChain::default(),
                )
                .map_err(display_algebraic)?;
            factor_cells.insert(correspondence.factor, cell);
            stalk_dimensions.insert(cell, rank);
            if native_to_factor
                .insert(correspondence.native, correspondence.factor)
                .is_some()
            {
                return Err(MembraneInteriorError::MalformedStanding(
                    "one native landmark entered two factor cells".to_owned(),
                ));
            }
        }

        let branch_coordinates = rest
            .membrane_branches()
            .iter()
            .map(|branch| (branch.thread_address.as_str(), branch.branch))
            .collect::<BTreeMap<_, _>>();
        let families = rest.membrane_ecology().mixed_constitutive_families();
        if families.is_empty() {
            return Err(MembraneInteriorError::MalformedStanding(
                "the exact mixed constitutive family is absent".to_owned(),
            ));
        }
        let correspondence_by_factor = rest
            .membrane_correspondences()
            .iter()
            .map(|factor| (factor.factor, factor))
            .collect::<BTreeMap<_, _>>();
        let mut thread_sections = branch_coordinates
            .iter()
            .map(|(thread, coordinate)| {
                let mut section = vec![rat(0); rank];
                section[*coordinate] = rat(1);
                ((*thread).to_owned(), section)
            })
            .collect::<BTreeMap<_, _>>();
        for thread in families
            .iter()
            .flat_map(|family| [&family.left_thread, &family.right_thread])
        {
            if thread_sections.contains_key(thread) {
                continue;
            }
            let sections = exact_fibres
                .iter()
                .filter(|fibre| &fibre.thread == thread)
                .map(|fibre| fibre.returned_covector.clone())
                .collect::<BTreeSet<_>>();
            if sections.len() != 1 {
                return Err(MembraneInteriorError::MissingThread(thread.clone()));
            }
            let section = sections.into_iter().next().expect("one exact section");
            if section.len() != rank || section.iter().all(|coefficient| coefficient == &rat(0)) {
                return Err(MembraneInteriorError::MalformedStanding(format!(
                    "thread {thread} does not inhabit the standing winding chart"
                )));
            }
            thread_sections.insert(thread.clone(), section);
        }
        let mut restrictions = Vec::new();
        let mut constitutive_cells = Vec::with_capacity(families.len());
        for (family_at, family) in families.iter().enumerate() {
            let left_coordinate = branch_coordinates.get(family.left_thread.as_str()).copied();
            let right_coordinate = branch_coordinates
                .get(family.right_thread.as_str())
                .copied();
            let left_winding_section = thread_sections[&family.left_thread].clone();
            let right_winding_section = thread_sections[&family.right_thread].clone();
            let mut boundary = CausalChain::default();
            let mut source_events = BTreeSet::<EventId>::new();
            let mut support_factors = Vec::with_capacity(family.dependent_receiver_support.len());
            let mut factor_orientations = BTreeMap::new();
            for native in &family.dependent_receiver_support {
                let factor = *native_to_factor
                    .get(native)
                    .ok_or(MembraneInteriorError::MissingNativeSupport(native.0))?;
                let correspondence = correspondence_by_factor[&factor];
                for (thread, section) in [
                    (&family.left_thread, &left_winding_section),
                    (&family.right_thread, &right_winding_section),
                ] {
                    if branch_coordinates.contains_key(thread.as_str()) {
                        for (coordinate, coefficient) in section.iter().enumerate() {
                            if coefficient == &rat(0) {
                                continue;
                            }
                            let fibre_address = &correspondence.cycle_fibres[coordinate];
                            let fibre =
                                fibre_by_address[fibre_address.exact_fibre_address.as_str()];
                            source_events.extend(fibre.occurrences.iter().copied());
                        }
                    } else {
                        for fibre in exact_fibres.iter().filter(|fibre| {
                            &fibre.thread == thread
                                && fibre.dependent_receiver_fibre.contains(native)
                        }) {
                            source_events.extend(fibre.occurrences.iter().copied());
                        }
                    }
                }
                let left_hand = section_orientation(factor, &left_winding_section, &orientations)?;
                let right_hand =
                    section_orientation(factor, &right_winding_section, &orientations)?;
                let hand = left_hand.checked_mul(right_hand).ok_or_else(|| {
                    MembraneInteriorError::MalformedStanding(
                        "the tensor-product orientation overflowed".to_owned(),
                    )
                })?;
                if hand != 0 {
                    boundary.add_term(
                        factor_cells[&factor],
                        ComparativeMultiplicity::from_hand(hand, 1_u8)
                            .map_err(display_algebraic)?,
                    );
                }
                factor_orientations.insert(factor, hand);
                support_factors.push(factor);
            }
            let upper = complex
                .found_cell(
                    format!("native-constitutive/{}", family.address),
                    source_events,
                    1,
                    boundary,
                )
                .map_err(display_algebraic)?;
            stalk_dimensions.insert(upper, rank);
            for factor in support_factors {
                let entries = constitutive_section_operator(
                    rank,
                    &family.storage,
                    &left_winding_section,
                    &right_winding_section,
                );
                restrictions.push(CellularRestriction {
                    lower: factor_cells[&factor],
                    upper,
                    map: ExactLinearMap::new(rank, rank, entries).map_err(display_sheaf)?,
                });
            }
            constitutive_cells.push(ConstitutiveCellAddress {
                family_at,
                cell: upper,
                left_coordinate,
                right_coordinate,
                left_winding_section,
                right_winding_section,
                factor_orientations,
            });
        }

        let sheaf = ExactCellularSheaf::new(complex, stalk_dimensions, restrictions)
            .map_err(display_sheaf)?;
        // JSON cannot use a pair of cell IDs as an object key.  The witness therefore presents
        // every ordered map entry as a sequence while retaining the same exact values.
        let cells = sheaf.complex().cells().iter().collect::<Vec<_>>();
        let stalks = sheaf.stalk_dimensions().iter().collect::<Vec<_>>();
        let restriction_witness = sheaf
            .restrictions()
            .iter()
            .map(|((lower, upper), map)| (lower, upper, map))
            .collect::<Vec<_>>();
        let exact_sheaf_sha256 = sha256(
            &serde_json::to_vec(&(MEMBRANE_INTERIOR_SCHEMA, cells, stalks, restriction_witness))
                .map_err(|error| MembraneInteriorError::Serialization(error.to_string()))?,
        );
        let total_cultivated_capacity = capacities.values().try_fold(0_u64, |sum, value| {
            sum.checked_add(*value)
                .ok_or(MembraneInteriorError::CapacityOverflow)
        })?;
        let receipt = InteriorConstitutionReceipt {
            schema: MEMBRANE_INTERIOR_SCHEMA.to_owned(),
            rested_identity_sha256: rest.membrane_identity().to_owned(),
            exact_sheaf_sha256,
            factor_cell_population: factor_cells.len(),
            constitutive_cell_population: constitutive_cells.len(),
            restriction_population: sheaf.restrictions().len(),
            affine_cochain_population: affine_index.len(),
            derived_stalk_rank: rank,
            total_cultivated_capacity,
            fixed_behavioral_capacity_supplied: false,
            global_affine_origin_supplied: false,
            semantic_topology_supplied: false,
            all_to_all_affine_edges_materialized: false,
        };
        Ok(Self {
            sheaf,
            factor_cells,
            factor_capacities: capacities,
            affine_cells: affine_index,
            constitutive_cells,
            receipt,
        })
    }

    pub fn receipt(&self) -> &InteriorConstitutionReceipt {
        &self.receipt
    }

    pub fn sheaf(&self) -> &ExactCellularSheaf {
        &self.sheaf
    }

    pub fn factor_cells(&self) -> &BTreeMap<u32, CausalCellId> {
        &self.factor_cells
    }

    pub fn affine_cell_index(&self, address: &str) -> Option<&usize> {
        self.affine_cells.get(address)
    }

    /// Return the exact rank inherited from the continuing ecology.  It is a receiver chart over
    /// the constitutive carrier, not a caller-selected behavioral width.
    pub fn winding_rank(&self) -> usize {
        self.receipt.derived_stalk_rank
    }

    /// Conduct one recurrent context/target support through the existing Complex-Parametron
    /// constitutive families.  No affine cell, word, semantic role, or response candidate is
    /// selected: the complete factor supports are the addressed local cochains.
    pub fn factor_support_boundary_current(
        &self,
        rest: &impl MembraneStanding,
        context_factors: &[u32],
        target_factors: &[u32],
        recurrence_multiplicity: u64,
    ) -> Result<FactorSupportBoundaryCurrent, MembraneInteriorError> {
        if rest.membrane_identity() != self.receipt.rested_identity_sha256 {
            return Err(MembraneInteriorError::RestIdentity);
        }
        if recurrence_multiplicity == 0
            || context_factors.windows(2).any(|pair| pair[0] >= pair[1])
            || target_factors.windows(2).any(|pair| pair[0] >= pair[1])
            || context_factors
                .iter()
                .chain(target_factors)
                .any(|factor| !self.factor_capacities.contains_key(factor))
        {
            return Err(MembraneInteriorError::MalformedStanding(
                "a granular boundary support is not an addressed factor population".to_owned(),
            ));
        }
        let context = context_factors.iter().copied().collect::<BTreeSet<_>>();
        let target = target_factors.iter().copied().collect::<BTreeSet<_>>();
        let shared_factors = context.intersection(&target).copied().collect::<Vec<_>>();
        let mut oriented_factor_boundary = context
            .difference(&target)
            .copied()
            .map(|factor| (factor, -1))
            .chain(
                target
                    .difference(&context)
                    .copied()
                    .map(|factor| (factor, 1)),
            )
            .collect::<Vec<_>>();
        oriented_factor_boundary.sort_by_key(|(factor, _)| *factor);
        let recurrence = rat_i(recurrence_multiplicity);
        let capacity_weighted_overlap = shared_factors.iter().fold(rat(0), |sum, factor| {
            sum + &recurrence * rat_i(self.factor_capacities[factor])
        });
        let families = rest.membrane_ecology().mixed_constitutive_families();
        let mut returned_response = ExactComplexWaveCurrent::zero();
        let mut family_contacts = Vec::with_capacity(self.constitutive_cells.len());
        for address in &self.constitutive_cells {
            let family = families.get(address.family_at).ok_or_else(|| {
                MembraneInteriorError::MalformedStanding(
                    "the mixed family index escaped the rested ecology".to_owned(),
                )
            })?;
            let oriented_overlap = shared_factors.iter().fold(rat(0), |sum, factor| {
                let orientation = rat(i64::from(
                    address
                        .factor_orientations
                        .get(factor)
                        .copied()
                        .unwrap_or(0),
                ));
                sum + &recurrence * orientation * rat_i(self.factor_capacities[factor])
            });
            let response = family.returned_product.scaled(&oriented_overlap);
            returned_response = returned_response.add(&response);
            family_contacts.push(ConstitutiveFamilyContact {
                family_address: family.address.clone(),
                left_coordinate: address.left_coordinate,
                right_coordinate: address.right_coordinate,
                left_winding_section: address.left_winding_section.clone(),
                right_winding_section: address.right_winding_section.clone(),
                storage: family.storage.clone(),
                oriented_overlap,
                returned_product: family.returned_product.clone(),
                weighted_response: response,
            });
        }
        let opposite_returned_response = returned_response.negated();
        let exact_exchange_balance = returned_response.add(&opposite_returned_response);
        if !exact_exchange_balance.is_zero() {
            return Err(MembraneInteriorError::Balance);
        }
        let response_is_in_constitutive_radical = returned_response.is_zero();
        let open_exterior = if shared_factors.is_empty() {
            vec!["the context and target supports have no founded common factor contact".to_owned()]
        } else if response_is_in_constitutive_radical {
            vec![
                "the complete support passage lies in the current constitutive receiver radical"
                    .to_owned(),
            ]
        } else {
            Vec::new()
        };
        Ok(FactorSupportBoundaryCurrent {
            schema: MEMBRANE_INTERIOR_SCHEMA.to_owned(),
            rested_identity_sha256: rest.membrane_identity().to_owned(),
            context_factors: context_factors.to_vec(),
            target_factors: target_factors.to_vec(),
            shared_factors,
            oriented_factor_boundary,
            recurrence_multiplicity,
            capacity_weighted_overlap,
            family_contacts,
            returned_response,
            opposite_returned_response,
            exact_exchange_balance,
            response_is_in_constitutive_radical,
            complete_support_fibre_retained: true,
            open_exterior,
        })
    }

    /// Pull one resident family-current return back into the standing winding chart.  Every
    /// coordinate is accumulated only from constitutive families incident to it; no media label,
    /// surface word, or fixed response extent enters this action section.
    pub fn returned_winding_section(
        &self,
        rest: &impl MembraneStanding,
        family_overlaps: &[Rat],
    ) -> Result<Vec<Rat>, MembraneInteriorError> {
        if rest.membrane_identity() != self.receipt.rested_identity_sha256 {
            return Err(MembraneInteriorError::RestIdentity);
        }
        if family_overlaps.len() != self.constitutive_cells.len() {
            return Err(MembraneInteriorError::MalformedStanding(
                "the resident family current does not cover the constituted interior".to_owned(),
            ));
        }
        let families = rest.membrane_ecology().mixed_constitutive_families();
        let mut section = vec![rat(0); self.winding_rank()];
        for (address, overlap) in self.constitutive_cells.iter().zip(family_overlaps) {
            let family = families.get(address.family_at).ok_or_else(|| {
                MembraneInteriorError::MalformedStanding(
                    "the constitutive family escaped the rested ecology".to_owned(),
                )
            })?;
            let returned_action = &family.storage * overlap;
            add_scaled_section(
                &mut section,
                &address.left_winding_section,
                &returned_action,
            )?;
            if address.right_winding_section != address.left_winding_section {
                add_scaled_section(
                    &mut section,
                    &address.right_winding_section,
                    &returned_action,
                )?;
            }
        }
        if section.iter().all(|coefficient| coefficient == &rat(0)) {
            return Err(MembraneInteriorError::ZeroFoundedResponse);
        }
        Ok(section)
    }

    /// The receiver constitutive form on the winding chart.  Its positive diagonal is the sum of
    /// squared incident storage terms and is therefore derived from the same exact families that
    /// generated the returned action section.
    pub fn winding_metric(
        &self,
        rest: &impl MembraneStanding,
    ) -> Result<ExactRatMatrix, MembraneInteriorError> {
        let trace = holonic_engine::cuda_refine::trace_configuration().holonics_phase_trace;
        let began = std::time::Instant::now();
        if rest.membrane_identity() != self.receipt.rested_identity_sha256 {
            return Err(MembraneInteriorError::RestIdentity);
        }
        let families = rest.membrane_ecology().mixed_constitutive_families();
        let rank = self.winding_rank();
        let mut entries = vec![vec![rat(0); rank]; rank];
        for address in &self.constitutive_cells {
            let family = families.get(address.family_at).ok_or_else(|| {
                MembraneInteriorError::MalformedStanding(
                    "the constitutive family escaped the rested ecology".to_owned(),
                )
            })?;
            let storage_square = &family.storage * &family.storage;
            add_outer_product(&mut entries, &address.left_winding_section, &storage_square)?;
            if address.right_winding_section != address.left_winding_section {
                add_outer_product(
                    &mut entries,
                    &address.right_winding_section,
                    &storage_square,
                )?;
            }
        }
        if trace {
            eprintln!("sens6-winding-metric gram-formed {:?}", began.elapsed());
        }
        // The causal adjoint below uses this same metric on both sides. Its global positive
        // content is therefore gauge: G and aG return the same adjoint, while the rested
        // constitutive families retain `a` and reconstruct the physical Gram form exactly. Keep
        // the primitive projective representative here so an inherited current scale cannot
        // inflate a four-direction receiver into an enormous exact-inversion bill.
        let entries = primitive_positive_metric(entries)?;
        let metric = ExactRatMatrix::new(entries)
            .map_err(|error| MembraneInteriorError::Sheaf(error.to_string()))?;
        if trace {
            eprintln!("sens6-winding-metric matrix-mounted {:?}", began.elapsed());
        }
        if metric.inverse().is_err() {
            return Err(MembraneInteriorError::MalformedStanding(
                "the winding receiver metric is degenerate".to_owned(),
            ));
        }
        if trace {
            eprintln!(
                "sens6-winding-metric inverse-certified {:?}",
                began.elapsed()
            );
        }
        Ok(metric)
    }

    /// Mount the exact compiled interior on the strongest admitted resident surface.  The dense
    /// apparatus coordinates below are derived bijectively from addressed factors and never
    /// become their native identity.
    pub fn mount_resident(
        &self,
        rest: &impl MembraneStanding,
    ) -> Result<ResidentMembraneInteriorWord, MembraneInteriorError> {
        if rest.membrane_identity() != self.receipt.rested_identity_sha256 {
            return Err(MembraneInteriorError::RestIdentity);
        }
        let dense_factor = self
            .factor_cells
            .keys()
            .copied()
            .enumerate()
            .map(|(dense, factor)| {
                u32::try_from(dense)
                    .map(|dense| (factor, dense))
                    .map_err(|_| {
                        MembraneInteriorError::Apparatus(
                            "the factor population escaped the card address line".to_owned(),
                        )
                    })
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        let factor_capacity = self
            .factor_cells
            .keys()
            .map(|factor| self.factor_capacities[factor])
            .collect::<Vec<_>>();
        let mut cell_offsets = Vec::with_capacity(rest.membrane_affine_cells().len() + 1);
        let mut cell_factors = Vec::new();
        let mut cell_multiplicities = Vec::new();
        let mut cell_total_mass = Vec::with_capacity(rest.membrane_affine_cells().len());
        cell_offsets.push(0_u64);
        for cell in rest.membrane_affine_cells() {
            let mut local = cell
                .landmark_factors
                .iter()
                .copied()
                .zip(cell.occurrence_multiplicities.iter().copied())
                .map(|(factor, multiplicity)| {
                    dense_factor
                        .get(&factor)
                        .copied()
                        .map(|dense| (dense, multiplicity))
                        .ok_or(MembraneInteriorError::MissingFactor(factor))
                })
                .collect::<Result<Vec<_>, _>>()?;
            local.sort_by_key(|(factor, _)| *factor);
            let total = local.iter().try_fold(0_u64, |sum, (_, population)| {
                sum.checked_add(*population)
                    .ok_or(MembraneInteriorError::CapacityOverflow)
            })?;
            cell_factors.extend(local.iter().map(|(factor, _)| *factor));
            cell_multiplicities.extend(local.iter().map(|(_, population)| *population));
            cell_total_mass.push(total);
            cell_offsets.push(
                u64::try_from(cell_factors.len())
                    .map_err(|_| MembraneInteriorError::CapacityOverflow)?,
            );
        }
        let mut family_orientation = Vec::with_capacity(
            self.constitutive_cells
                .len()
                .saturating_mul(self.factor_cells.len()),
        );
        for family in &self.constitutive_cells {
            for factor in self.factor_cells.keys() {
                // Absence is exact disjoint support.  The dense CUDA chart retains it as zero;
                // only founded factor incidences carry an orientation.
                family_orientation
                    .push(family.factor_orientations.get(factor).copied().unwrap_or(0));
            }
        }
        let family_currents = rest
            .membrane_ecology()
            .mixed_constitutive_families()
            .iter()
            .map(|family| family.returned_product.clone())
            .collect::<Vec<_>>();
        ResidentMembraneInteriorWord::mount(
            CudaRefineExecutor::new()
                .map_err(|error| MembraneInteriorError::Apparatus(error.to_string()))?,
            &factor_capacity,
            &cell_offsets,
            &cell_factors,
            &cell_multiplicities,
            &cell_total_mass,
            &family_orientation,
            &family_currents,
        )
        .map_err(|error| MembraneInteriorError::Apparatus(error.to_string()))
    }

    pub fn contact(
        &self,
        rest: &impl MembraneStanding,
        left_address: &str,
        right_address: &str,
    ) -> Result<InteriorContactConsequence, MembraneInteriorError> {
        if rest.membrane_identity() != self.receipt.rested_identity_sha256 {
            return Err(MembraneInteriorError::RestIdentity);
        }
        let left =
            rest.membrane_affine_cells()
                .get(*self.affine_cells.get(left_address).ok_or_else(|| {
                    MembraneInteriorError::MissingAffineCell(left_address.to_owned())
                })?)
                .ok_or_else(|| MembraneInteriorError::MissingAffineCell(left_address.to_owned()))?;
        let right = rest
            .membrane_affine_cells()
            .get(*self.affine_cells.get(right_address).ok_or_else(|| {
                MembraneInteriorError::MissingAffineCell(right_address.to_owned())
            })?)
            .ok_or_else(|| MembraneInteriorError::MissingAffineCell(right_address.to_owned()))?;
        let left_section = affine_cochain(left);
        let right_section = affine_cochain(right);
        let left_map = left_section
            .coefficients
            .iter()
            .cloned()
            .collect::<BTreeMap<_, _>>();
        let right_map = right_section
            .coefficients
            .iter()
            .cloned()
            .collect::<BTreeMap<_, _>>();
        let shared_factors = left_map
            .keys()
            .filter(|factor| right_map.contains_key(factor))
            .copied()
            .collect::<Vec<_>>();
        if shared_factors.is_empty() {
            return Ok(InteriorContactConsequence::Obstructed(
                SharedSupportObstruction {
                    schema: MEMBRANE_INTERIOR_SCHEMA.to_owned(),
                    rested_identity_sha256: rest.membrane_identity().to_owned(),
                    left: left_section,
                    right: right_section,
                    shared_factors,
                    returned_response: ExactComplexWaveCurrent::zero(),
                    reason: "the two local sections have no founded shared factor support"
                        .to_owned(),
                    open_exterior: vec![
                        "a later returned passage may found incidence; the membrane does not smooth across the absent contact"
                            .to_owned(),
                    ],
                },
            ));
        }

        let overlap = shared_factors.iter().fold(rat(0), |sum, factor| {
            let capacity = rat_i(self.factor_capacities[factor]);
            sum + capacity * &left_map[factor] * &right_map[factor]
        });
        let reoriented_overlap = shared_factors.iter().fold(rat(0), |sum, factor| {
            let capacity = rat_i(self.factor_capacities[factor]);
            sum + capacity * (-&left_map[factor]) * (-&right_map[factor])
        });
        let families = rest.membrane_ecology().mixed_constitutive_families();
        let mut returned_response = ExactComplexWaveCurrent::zero();
        let mut reoriented_response = ExactComplexWaveCurrent::zero();
        let mut family_contacts = Vec::with_capacity(self.constitutive_cells.len());
        for address in &self.constitutive_cells {
            let family = families.get(address.family_at).ok_or_else(|| {
                MembraneInteriorError::MalformedStanding(
                    "the mixed family index escaped the rested ecology".to_owned(),
                )
            })?;
            let _constitutive_cell = address.cell;
            let oriented_overlap = shared_factors.iter().fold(rat(0), |sum, factor| {
                let capacity = rat_i(self.factor_capacities[factor]);
                let orientation = rat(i64::from(
                    address
                        .factor_orientations
                        .get(factor)
                        .copied()
                        .unwrap_or(0),
                ));
                sum + orientation * capacity * &left_map[factor] * &right_map[factor]
            });
            let reoriented_family_overlap = shared_factors.iter().fold(rat(0), |sum, factor| {
                let capacity = rat_i(self.factor_capacities[factor]);
                let orientation = rat(i64::from(
                    address
                        .factor_orientations
                        .get(factor)
                        .copied()
                        .unwrap_or(0),
                ));
                sum + orientation * capacity * (-&left_map[factor]) * (-&right_map[factor])
            });
            if oriented_overlap != reoriented_family_overlap {
                return Err(MembraneInteriorError::ReorientationCovariance);
            }
            let response = family.returned_product.scaled(&oriented_overlap);
            returned_response = returned_response.add(&response);
            reoriented_response = reoriented_response
                .add(&family.returned_product.scaled(&reoriented_family_overlap));
            family_contacts.push(ConstitutiveFamilyContact {
                family_address: family.address.clone(),
                left_coordinate: address.left_coordinate,
                right_coordinate: address.right_coordinate,
                left_winding_section: address.left_winding_section.clone(),
                right_winding_section: address.right_winding_section.clone(),
                storage: family.storage.clone(),
                oriented_overlap,
                returned_product: family.returned_product.clone(),
                weighted_response: response,
            });
        }
        if returned_response.is_zero() {
            return Err(MembraneInteriorError::ZeroFoundedResponse);
        }
        if overlap != reoriented_overlap || returned_response != reoriented_response {
            return Err(MembraneInteriorError::ReorientationCovariance);
        }
        let reconstruction_fibre =
            reconstruction_fibre(&left_map, &right_map, &self.factor_capacities, &overlap)?;
        let opposite = returned_response.negated();
        let balance = returned_response.add(&opposite);
        if !balance.is_zero() {
            return Err(MembraneInteriorError::Balance);
        }
        Ok(InteriorContactConsequence::Founded(FoundedInteriorContact {
            schema: MEMBRANE_INTERIOR_SCHEMA.to_owned(),
            rested_identity_sha256: rest.membrane_identity().to_owned(),
            left: left_section,
            right: right_section,
            shared_factors,
            capacity_weighted_overlap: overlap,
            family_contacts,
            returned_response,
            opposite_returned_response: opposite,
            exact_exchange_balance: balance,
            simultaneously_reoriented_overlap: reoriented_overlap,
            simultaneously_reoriented_response: reoriented_response,
            reconstruction_fibre,
            directional_withdrawal_fibre_retained: true,
            open_exterior: vec![
                "receiver histories beyond the admitted mixed family retain their reconstruction fibre"
                    .to_owned(),
            ],
        }))
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum MembraneInteriorError {
    #[error("the membrane interior has not been constituted")]
    InteriorAbsent,
    #[error("the constituted membrane interior has not been mounted on a resident card")]
    ResidentInteriorAbsent,
    #[error("the rested ecology does not match the constituted interior")]
    RestIdentity,
    #[error("the cultivated standing is malformed: {0}")]
    MalformedStanding(String),
    #[error("factor {0} is absent from the cultivated base")]
    MissingFactor(u32),
    #[error("native support {0} has no cultivated factor")]
    MissingNativeSupport(u64),
    #[error("exact reconstruction fibre {0} is absent")]
    MissingFibre(String),
    #[error("thread {0} is absent from the local cycle chart")]
    MissingThread(String),
    #[error("affine cell {0} is absent")]
    MissingAffineCell(String),
    #[error("exact fibre {0} carries no oriented returned section")]
    UnorientedFibre(String),
    #[error("cultivated capacity overflowed its exact population carrier")]
    CapacityOverflow,
    #[error("a founded shared contact returned the zero constitutive response")]
    ZeroFoundedResponse,
    #[error("simultaneous source reorientation changed the constitutive response")]
    ReorientationCovariance,
    #[error("the returned exchange pair failed exact balance")]
    Balance,
    #[error("the local reconstruction fibre failed its exact kernel law")]
    ReconstructionFibre,
    #[error("the causal complex refused: {0}")]
    Algebraic(String),
    #[error("the exact sheaf refused: {0}")]
    Sheaf(String),
    #[error("the exact membrane receipt could not be serialized: {0}")]
    Serialization(String),
    #[error("the resident membrane apparatus refused: {0}")]
    Apparatus(String),
}

fn section_orientation(
    factor: u32,
    section: &[Rat],
    orientations: &BTreeMap<(u32, usize), i8>,
) -> Result<i8, MembraneInteriorError> {
    let pairing =
        section
            .iter()
            .enumerate()
            .try_fold(rat(0), |sum, (coordinate, coefficient)| {
                orientations
                    .get(&(factor, coordinate))
                    .map(|hand| sum + coefficient * rat(i64::from(*hand)))
                    .ok_or_else(|| {
                        MembraneInteriorError::MalformedStanding(
                            "a section escaped the factor orientation chart".to_owned(),
                        )
                    })
            })?;
    Ok(if pairing > rat(0) {
        1
    } else if pairing < rat(0) {
        -1
    } else {
        0
    })
}

fn constitutive_section_operator(
    rank: usize,
    storage: &Rat,
    left: &[Rat],
    right: &[Rat],
) -> Vec<Vec<Rat>> {
    let mut entries = vec![vec![rat(0); rank]; rank];
    for section in [left, right] {
        for row in 0..rank {
            for column in 0..rank {
                entries[row][column] += storage * &section[row] * &section[column];
            }
        }
        if left == right {
            break;
        }
    }
    entries
}

fn add_scaled_section(
    target: &mut [Rat],
    section: &[Rat],
    scale: &Rat,
) -> Result<(), MembraneInteriorError> {
    if target.len() != section.len() {
        return Err(MembraneInteriorError::MalformedStanding(
            "a returned section escaped the winding chart".to_owned(),
        ));
    }
    for (target, coefficient) in target.iter_mut().zip(section) {
        *target += scale * coefficient;
    }
    Ok(())
}

fn add_outer_product(
    target: &mut [Vec<Rat>],
    section: &[Rat],
    scale: &Rat,
) -> Result<(), MembraneInteriorError> {
    if target.len() != section.len() || target.iter().any(|row| row.len() != section.len()) {
        return Err(MembraneInteriorError::MalformedStanding(
            "a constitutive section escaped the receiver metric chart".to_owned(),
        ));
    }
    for row in 0..section.len() {
        for column in 0..section.len() {
            target[row][column] += scale * &section[row] * &section[column];
        }
    }
    Ok(())
}

fn primitive_positive_metric(
    entries: Vec<Vec<Rat>>,
) -> Result<Vec<Vec<Rat>>, MembraneInteriorError> {
    let mut common_denominator = BigInt::from(1);
    for entry in entries.iter().flatten() {
        common_denominator = lcm_positive(&common_denominator, entry.denom());
    }
    let mut integral = Vec::with_capacity(entries.len());
    let mut content = BigInt::from(0);
    for row in entries {
        let mut integral_row = Vec::with_capacity(row.len());
        for entry in row {
            let coefficient = entry.numer() * (&common_denominator / entry.denom());
            if coefficient != BigInt::from(0) {
                content = if content == BigInt::from(0) {
                    if coefficient < BigInt::from(0) {
                        -coefficient.clone()
                    } else {
                        coefficient.clone()
                    }
                } else {
                    gcd_positive(content, coefficient.clone())
                };
            }
            integral_row.push(coefficient);
        }
        integral.push(integral_row);
    }
    if content == BigInt::from(0) {
        return Err(MembraneInteriorError::MalformedStanding(
            "the winding receiver metric vanished".to_owned(),
        ));
    }
    Ok(integral
        .into_iter()
        .map(|row| {
            row.into_iter()
                .map(|coefficient| Rat::from_integer(coefficient / &content))
                .collect()
        })
        .collect())
}

fn lcm_positive(left: &BigInt, right: &BigInt) -> BigInt {
    (left / gcd_positive(left.clone(), right.clone())) * right
}

fn gcd_positive(mut left: BigInt, mut right: BigInt) -> BigInt {
    if left < BigInt::from(0) {
        left = -left;
    }
    if right < BigInt::from(0) {
        right = -right;
    }
    while right != BigInt::from(0) {
        let remainder = left % &right;
        left = right;
        right = remainder;
    }
    if left == BigInt::from(0) {
        BigInt::from(1)
    } else {
        left
    }
}

fn validate_affine_cell(cell: &LaboratoryCellAffineSection) -> Result<(), MembraneInteriorError> {
    if cell.cell_address.is_empty()
        || cell.landmark_factors.is_empty()
        || cell.landmark_factors.len() != cell.occurrence_multiplicities.len()
        || cell.landmark_factors.len() != cell.barycentric_weights.len()
        || cell
            .occurrence_multiplicities
            .iter()
            .any(|value| *value == 0)
        || cell.source_occurrence_identities_sha256.is_empty()
    {
        return Err(MembraneInteriorError::MalformedStanding(format!(
            "affine cell {} lost its complete local section",
            cell.cell_address
        )));
    }
    let total = cell
        .barycentric_weights
        .iter()
        .fold(rat(0), |sum, weight| sum + weight);
    if total != rat(1) {
        return Err(MembraneInteriorError::MalformedStanding(format!(
            "affine cell {} is not a barycentric section",
            cell.cell_address
        )));
    }
    Ok(())
}

fn validate_correspondence(
    correspondence: &LaboratoryFactorCycleCorrespondence,
    rank: usize,
) -> Result<(), MembraneInteriorError> {
    if correspondence.factor_address.is_empty()
        || correspondence.cycle_fibres.len() != rank
        || correspondence
            .cycle_fibres
            .iter()
            .enumerate()
            .any(|(coordinate, fibre)| {
                fibre.coordinate != coordinate
                    || fibre.thread_address.is_empty()
                    || fibre.exact_fibre_address.is_empty()
            })
    {
        return Err(MembraneInteriorError::MalformedStanding(format!(
            "factor {} lost its local cycle chart",
            correspondence.factor
        )));
    }
    Ok(())
}

fn exact_fibre_orientation(returned_covector: &[Rat]) -> Option<i8> {
    let total = returned_covector
        .iter()
        .fold(rat(0), |sum, coefficient| sum + coefficient);
    if total > rat(0) {
        Some(1)
    } else if total < rat(0) {
        Some(-1)
    } else {
        None
    }
}

fn affine_cochain(cell: &LaboratoryCellAffineSection) -> AffineMembraneCochain {
    AffineMembraneCochain {
        cell_address: cell.cell_address.clone(),
        coefficients: cell
            .landmark_factors
            .iter()
            .copied()
            .zip(cell.barycentric_weights.iter().cloned())
            .collect(),
        occurrence_multiplicities: cell
            .landmark_factors
            .iter()
            .copied()
            .zip(cell.occurrence_multiplicities.iter().copied())
            .collect(),
        source_occurrence_identities_sha256: cell.source_occurrence_identities_sha256.clone(),
    }
}

fn reconstruction_fibre(
    left: &BTreeMap<u32, Rat>,
    right: &BTreeMap<u32, Rat>,
    capacities: &BTreeMap<u32, u64>,
    overlap: &Rat,
) -> Result<ExactLocalReconstructionFibre, MembraneInteriorError> {
    let factors = left
        .keys()
        .chain(right.keys())
        .copied()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let functional = factors
        .iter()
        .map(|factor| {
            let coefficient = left.get(factor).cloned().unwrap_or_else(|| rat(0));
            rat_i(capacities[factor]) * coefficient
        })
        .collect::<Vec<_>>();
    let partner = factors
        .iter()
        .map(|factor| right.get(factor).cloned().unwrap_or_else(|| rat(0)))
        .collect::<Vec<_>>();
    let pivot = functional
        .iter()
        .position(|coefficient| coefficient != &rat(0))
        .ok_or(MembraneInteriorError::ReconstructionFibre)?;
    let mut particular = vec![rat(0); factors.len()];
    particular[pivot] = overlap / &functional[pivot];
    let hidden = partner
        .iter()
        .zip(&particular)
        .map(|(actual, visible)| actual - visible)
        .collect::<Vec<_>>();
    let mut radical = Vec::with_capacity(factors.len().saturating_sub(1));
    for coordinate in 0..factors.len() {
        if coordinate == pivot {
            continue;
        }
        let mut direction = vec![rat(0); factors.len()];
        direction[coordinate] = rat(1);
        direction[pivot] = -&functional[coordinate] / &functional[pivot];
        radical.push(direction);
    }
    let functional_on_hidden_difference = dot(&functional, &hidden)?;
    if functional_on_hidden_difference != rat(0)
        || radical
            .iter()
            .any(|direction| dot(&functional, direction).ok() != Some(rat(0)))
        || dot(&functional, &particular)? != *overlap
        || dot(&functional, &partner)? != *overlap
    {
        return Err(MembraneInteriorError::ReconstructionFibre);
    }
    Ok(ExactLocalReconstructionFibre {
        coordinate_factors: factors.clone(),
        receiver_functional: functional,
        returned_overlap: overlap.clone(),
        local_pivot_factor: factors[pivot],
        particular,
        presented_partner_section: partner,
        hidden_difference: hidden,
        radical,
        functional_on_hidden_difference,
        no_global_origin_was_introduced: true,
    })
}

fn dot(left: &[Rat], right: &[Rat]) -> Result<Rat, MembraneInteriorError> {
    if left.len() != right.len() {
        return Err(MembraneInteriorError::ReconstructionFibre);
    }
    Ok(left
        .iter()
        .zip(right)
        .fold(rat(0), |sum, (left, right)| sum + left * right))
}

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn rat_i(value: u64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn display_algebraic(error: impl std::fmt::Display) -> MembraneInteriorError {
    MembraneInteriorError::Algebraic(error.to_string())
}

fn display_sheaf(error: impl std::fmt::Display) -> MembraneInteriorError {
    MembraneInteriorError::Sheaf(error.to_string())
}
