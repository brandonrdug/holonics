//! The partition refinement shell, enacted on the card.
//!
//! **GPU-first, not GPU-later.** Brandon, 2026-08-10: *"the card's integration is so fucking
//! important and you can't just keep punting it… every time we have to go from it not being
//! integrated to integrating it, you risk contamination. It's GPU first."* This module exists so
//! that the front `token_invariance` walks is enacted on the device from the beginning, with the
//! cpu law standing beside it as the exact reference rather than as the implementation.
//!
//! # What crosses, and why it is small
//!
//! A receiver's reading of a surface is `[kind, weight, density, conduct token]`. Two occurrences
//! agree at an offset exactly when those four words agree, so the cpu assigns each **distinct
//! reading** a dense identity once over the whole corpus — [`ReadingIdentities`] — and the device
//! compares identities. Equality of identities is equality of readings, exactly.
//!
//! Identity `0` is reserved before any reading is assigned one, and stands for an offset that has
//! run off the end of its whole. That is not a sentinel of convenience: a terminus is
//! family-invariant — deleting a receiver never merges *"the whole ended"* with a reading — so it
//! must be a value no reading can take.
//!
//! So a shell key is one `u64`, and the corpus crosses once as three `u32` arrays plus the stream.
//!
//! # The quotient is a hash join and the table cannot fill
//!
//! An occurrence's new class is the identity of `(current class, shell key)`, claimed by
//! `atomicCAS` in an open-addressed table. The atomic is on the **claim**, never on the reading.
//! Distinct pairs are at most occupied occurrences, so a capacity strictly above the occurrence
//! count always leaves an empty slot and every probe terminates. The cpu sizes it as the next power
//! of two above the site count — **derived from the material, no load factor, no number chosen.**
//!
//! # Launch geometry
//!
//! Read off the device and the kernel, as `cuda_aperture` and `cuda_relation` now do:
//! `block = min(function max, device max)` taken down to a whole warp, grid refused by name past
//! the device's own `MAX_GRID_DIM_X`.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::c_void;
use std::ptr;

mod cuda_executor;
pub use cuda_executor::CudaRefineExecutor;
mod partition_refinement;
pub use partition_refinement::{DeviceCorpus, ReadingIdentities};

mod affine_barycentric_transport;
mod athena_integrated_front;
mod complex_parametron;
mod cuda_driver;
mod device_contact;
mod device_ecology_types;
mod device_fixed_sections;
mod device_inference_world;
mod device_media;
mod device_recurrence;
mod interval_potential;
mod membrane_addressed_current;
mod membrane_boundary_interval;
mod membrane_boundary_plan;
mod membrane_boundary_return;
mod membrane_boundary_support_phase;
mod membrane_boundary_workspace;
mod membrane_conduct;
mod membrane_factored_coordinates;
mod membrane_factored_descent;
mod membrane_factored_receivers;
mod membrane_factored_transport;
mod membrane_foundation;
mod membrane_generated_condition;
mod membrane_generated_transport;
mod membrane_inspection;
mod membrane_joint_boundary;
mod membrane_moment_plan;
mod membrane_moment_workspace;
mod membrane_mount;
mod membrane_native_boundary;
mod membrane_projective_stream;
mod membrane_receiver_completion;
mod membrane_receiver_mount;
mod membrane_returned_restriction;
mod membrane_sparse_completion;
mod membrane_state;
mod membrane_transport_setup;
mod membrane_types;
mod participant_causal_front;
#[cfg(test)]
mod tests;
mod trace_config;
use crate::is_sha256_digest as is_digest;
pub use affine_barycentric_transport::{
    ResidentAffineBarycentricTransport, ResidentAffineBarycentricTransportReturn,
};
pub use athena_integrated_front::{
    ResidentAthenaIntegratedFront, ResidentAthenaIntegratedReturn,
    ResidentSituatedCurrentCausalFrontReturn,
};
#[cfg(test)]
use complex_parametron::derive_coupled_limb_chart;
pub use complex_parametron::{
    CausalAdjointPulledIncidence, CoupledComplexInteraction, ResidentComplexIncidence,
    ResidentComplexIncidenceReturn, ResidentCoupledComplexParametron,
    ResidentCoupledComplexParametronReturn, ResidentNativeWord, ResidentNativeWordReturn,
};
use complex_parametron::{
    common_real_denominator, decode_component, decode_signed_magnitude, derive_word_prime_family,
    derive_word_prime_rank_witness, encode_component, encode_integer, encode_integral_form_factors,
    factored_moment_section_identity, lcm_positive,
};
pub use device_ecology_types::{
    DeviceCondensedRecurrences, DeviceContactPassage, DeviceDynamicMorphology,
    DeviceFixedSectionFamilies, DeviceHeterogeneousFusion, DeviceInferenceEcology,
    DeviceJointMediaTransport, DeviceMaterialOperationWorldTube, DeviceMediaCandidateCounts,
    DeviceNativeFixedSectionFamilies, DeviceNativeTrace, DeviceOpticalIncidencePassage,
    DeviceProductionAperture, DeviceQuadraticSectionTransport, DeviceRaggedNativeTrace,
    DeviceReturnedRecurrences, DeviceSaturation, Quotient, QuotientCarrier, quotient_on_cpu,
};
pub use interval_potential::{ResidentIntervalPotentialReceiver, ResidentIntervalPotentialReturn};
use membrane_boundary_plan::BoundaryCompletionPlan;
use membrane_boundary_support_phase::BoundarySupportPhaseReceipt;
use membrane_boundary_workspace::BoundaryCompletionWorkspace;
use membrane_state::{
    ResidentAddressedFactoredReceiverMount, ResidentBoundaryRestrictionAtlasMount,
    ResidentCompletedTargetObservationAperture, ResidentCompletedTargetObserverWorkspace,
    ResidentExactRationalMatrix, ResidentFactoredConstitutiveSpine, ResidentFactoredCurrentState,
    ResidentFactoredHistoryQuotientPassage, ResidentFactoredMomentCandidate,
    ResidentFactoredMomentCoordinateAtlas, ResidentFactoredMomentRankAtlas,
    ResidentFactoredMomentReceiverState, ResidentFactoredMomentState,
    ResidentFactoredReceiverHistoryMount, ResidentFactorizedRelationalWorkspace,
    ResidentIntegralMatrix, ResidentObservableIntegralFormMount, ResidentQuadraticActionMount,
    ResidentReceiverHistoryCompressionMount, ResidentSparseQuadraticBoundaryConditionerMount,
    ResidentSparseQuadraticConditionedCurrent, ResidentSparseQuadraticMomentState,
    ResidentSparseQuadraticNativeBoundary, ResidentSparseQuadraticReceiverMount,
    ResidentSparseRelationalBoundaryReceiver, ResidentSparseRelationalConditionedCurrent,
    ResidentSparseRelationalCurrentAtlasMount, ResidentSparseRelationalCurrentState,
    ResidentSparseRelationalGeneratorTransport, ResidentTransportedConstitutiveSpine,
    ResidentTransportedFactoredHistory, ResidentTransportedFactoredMomentIncidence,
    SparsePairActionIngress,
};
pub use membrane_types::{
    ResidentAddressedCurrentPassageReturn, ResidentAddressedFactoredReceiverFrameReturn,
    ResidentBoundaryChainPortReturn, ResidentBoundaryChainSupport,
    ResidentBoundaryChainSupportReturn, ResidentBoundaryRestrictionAtlas,
    ResidentBoundaryRestrictionFront, ResidentCurrentAddress, ResidentFactorSupportBoundaryReturn,
    ResidentFactoredMomentAddress, ResidentFactoredMomentBoundaryReturn,
    ResidentFactoredMomentCoordinateAddress, ResidentFactoredMomentCoordinateReturn,
    ResidentFactoredMomentDescentAddress, ResidentFactoredMomentDescentReturn,
    ResidentFactoredMomentFoundationReturn, ResidentFactoredMomentRankAddress,
    ResidentFactoredMomentRankReturn, ResidentFactoredMomentReceiverAddress,
    ResidentFactoredMomentReceiverReturn, ResidentFactoredMomentTransportAddress,
    ResidentFactoredMomentTransportOccurrence, ResidentFactoredMomentTransportReturn,
    ResidentFactoredReceiverHistoryReceipt, ResidentGeneratedPortCurrentPassageReturn,
    ResidentGeneratedPortLocalCurrent, ResidentJointBoundaryChainReturn,
    ResidentMembraneInteriorReturn, ResidentObservableIntegralFormReturn,
    ResidentQuadraticMomentFront, ResidentQuadraticMomentPortReturn,
    ResidentQuadraticMomentRestriction, ResidentQuadraticMomentRestrictionSource,
    ResidentQuadraticMomentReturn, ResidentReceiverHistoryCompressionReceipt,
    ResidentSituatedReceiverPairingReturn, ResidentSparseQuadraticChronologyFoundationReturn,
    ResidentSparseQuadraticMomentFoundationReturn, ResidentSparseRelationalCurrentAtlas,
    ResidentSparseRelationalCurrentReceipt,
};
pub use participant_causal_front::{
    DeviceNativeWord, ResidentParticipantCausalFront, ResidentParticipantCausalFrontReturn,
};
pub use trace_config::{TraceConfiguration, trace_configuration};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};
use relational_geometry::Rat;
use sha2::{Digest, Sha256};

use crate::ExactComplexWaveCurrent;
use crate::addressed_current::{
    AddressedCurrentOccurrence, AddressedCurrentPassage, AddressedCurrentSection,
    AddressedGeneratedPortJunctionOccurrence, AddressedGeneratedPortJunctionPassage,
    AddressedGeneratedPortSlot,
};
use crate::corpus_census::CorpusCensus;
use crate::exact_linear::ExactRatMatrix;
use crate::factored_moment::{
    AddressedDiagonalCurrentStep, FactoredMomentSection, SparseQuadraticMomentAction,
    SparseQuadraticMomentFoundation, SparseQuadraticPairReceiverFrame, WeightedIntegralCurrent,
};
use crate::receiver_exact_compression::{ObservedSystem, compress_on_device};
use crate::receiver_history_compression::{
    AddressedFactoredIntegralReceiverComplex, AddressedPrimitiveReceiverFrame,
    IntegralFormFrameFactor, ObservableIntegralFormFrame, ReceiverHistoryCompression,
};
use crate::token_invariance::ConductAtlas;
pub use cuda_driver::CudaRefineError;
use cuda_driver::{
    Buffer, CuDevicePtr, cuCtxSetCurrent, cuCtxSynchronize, cuLaunchKernel, cuMemcpyDtoDAsync_v2,
    cuMemcpyHtoD_v2, cuMemsetD8_v2, cuModuleGetFunction, driver,
};

const PTX: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/refine_shell.ptx"));
const CUDA_SUCCESS: i32 = 0;

/// The identity reserved for an offset past the end of a whole, mirroring `refine_shell.cu`.
pub const ABSENT: u32 = 0;

/// `CUdevice_attribute` / `CUfunction_attribute` selectors from `cuda.h` — ABI.
const DEVICE_MAX_THREADS_PER_BLOCK: i32 = 1;
const DEVICE_MAX_GRID_DIM_X: i32 = 5;
const DEVICE_WARP_SIZE: i32 = 10;
const FUNCTION_MAX_THREADS_PER_BLOCK: i32 = 0;

pub const CAUSAL_ADJOINT_PULLED_INCIDENCE_SCHEMA: &str =
    "holonic-engine.causal-adjoint-pulled-incidence.v1";

/// One resident enactment of a morphology-derived membrane interior.
///
/// All invariant incidence, factor capacity, affine support and constitutive current cross once at
/// mount.  A later occurrence supplies only two addressed local sections and one exact complex
/// boundary current.  Three kernels form one default-stream word with two device-buffer
/// dependencies and one terminal synchronization.
pub struct ResidentMembraneInteriorWord {
    cell_offsets: Buffer,
    cell_factors: Buffer,
    cell_multiplicities: Buffer,
    cell_total_mass: Buffer,
    factor_capacity: Buffer,
    family_orientation: Buffer,
    family_real_sign: Buffer,
    family_real_limbs: Buffer,
    family_imaginary_sign: Buffer,
    family_imaginary_limbs: Buffer,
    factor_receiver_observations: Option<Buffer>,
    factor_receiver_classes: Option<Vec<u32>>,
    receiver_class_counts: Option<Vec<u32>>,
    receiver_count: u32,
    receiver_face_identity_sha256: Option<String>,
    quadratic_action: Option<ResidentQuadraticActionMount>,
    boundary_restriction_atlas: Option<ResidentBoundaryRestrictionAtlasMount>,
    factored_receiver_history: Option<ResidentFactoredReceiverHistoryMount>,
    observable_integral_form_frame: Option<ResidentObservableIntegralFormMount>,
    addressed_factored_receiver_frame: Option<ResidentAddressedFactoredReceiverMount>,
    sparse_relational_atlas: Option<ResidentSparseRelationalCurrentAtlasMount>,
    sparse_relational_current: Option<ResidentSparseRelationalCurrentState>,
    card: CudaRefineExecutor,
    cells: u32,
    factors: u32,
    families: u32,
    family_limb_count: u32,
    family_common_denominator: BigInt,
    maximal_family_numerator: BigInt,
    constitutive_family_identity_sha256: String,
    mount_host_ingress_octets: u64,
    maximal_overlap_magnitude: u64,
    total_factor_capacity: u64,
}

fn derive_sparse_pair_action_ingress(
    action: &SparseQuadraticMomentAction,
) -> Result<SparsePairActionIngress, CudaRefineError> {
    action
        .validate()
        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
    let pair_population = action.pairs.len();
    let generator_population = action.generator_population as usize;
    let action_population = generator_population
        .checked_mul(pair_population)
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    if pair_population == 0
        || action.target_pair_coordinates.len() != action_population
        || action.multiplicities.len() != action_population
    {
        return Err(CudaRefineError::MembraneInteriorWordShape);
    }

    let pair_factors = action
        .pairs
        .iter()
        .flat_map(|pair| [pair.left, pair.right])
        .collect::<Vec<_>>();
    let mut pair_row_offsets = vec![0_u64; action.factor_population as usize + 1];
    let mut pair_cursor = 0_usize;
    for left in 0..action.factor_population as usize {
        pair_row_offsets[left] = u64::try_from(pair_cursor)
            .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        while pair_cursor < pair_population && action.pairs[pair_cursor].left as usize == left {
            pair_cursor += 1;
        }
    }
    pair_row_offsets[action.factor_population as usize] = u64::try_from(pair_cursor)
        .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    if pair_cursor != pair_population {
        return Err(CudaRefineError::MembraneInteriorWordShape);
    }

    let mut aggregate_counts = vec![0_usize; pair_population];
    let mut aggregate_multiplicities = vec![0_u64; pair_population];
    for (target, multiplicity) in action
        .target_pair_coordinates
        .iter()
        .zip(&action.multiplicities)
    {
        let target = *target as usize;
        aggregate_counts[target] = aggregate_counts[target]
            .checked_add(1)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        aggregate_multiplicities[target] = aggregate_multiplicities[target]
            .checked_add(u64::from(*multiplicity))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    }
    let maximal_incoming_multiplicity = aggregate_multiplicities
        .into_iter()
        .max()
        .map(BigUint::from)
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
    let mut target_offsets = Vec::with_capacity(pair_population + 1);
    target_offsets.push(0_u64);
    for count in &aggregate_counts {
        let next = target_offsets
            .last()
            .copied()
            .and_then(|offset| offset.checked_add(*count as u64))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        target_offsets.push(next);
    }
    let mut aggregate_cursors = target_offsets[..pair_population]
        .iter()
        .map(|offset| *offset as usize)
        .collect::<Vec<_>>();
    let mut source_pairs = vec![0_u32; action_population];
    let mut multiplicities = vec![0_u8; action_population];
    for action_at in 0..action_population {
        let target = action.target_pair_coordinates[action_at] as usize;
        let destination = aggregate_cursors[target];
        aggregate_cursors[target] += 1;
        source_pairs[destination] = (action_at % pair_population) as u32;
        multiplicities[destination] = action.multiplicities[action_at];
    }

    let generator_offset_population = generator_population
        .checked_mul(pair_population + 1)
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    let mut generator_target_offsets = Vec::with_capacity(generator_offset_population);
    let mut generator_source_pairs = vec![0_u32; action_population];
    let mut generator_multiplicities = vec![0_u8; action_population];
    let mut counts = vec![0_usize; pair_population];
    let mut cursors = vec![0_usize; pair_population];
    for generator in 0..generator_population {
        counts.fill(0);
        let action_base = generator * pair_population;
        for source in 0..pair_population {
            let target = action.target_pair_coordinates[action_base + source] as usize;
            counts[target] += 1;
        }
        let edge_base = action_base;
        generator_target_offsets.push(edge_base as u64);
        let mut local = 0_usize;
        for target in 0..pair_population {
            cursors[target] = edge_base + local;
            local = local
                .checked_add(counts[target])
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            generator_target_offsets.push((edge_base + local) as u64);
        }
        if local != pair_population {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        for source in 0..pair_population {
            let action_at = action_base + source;
            let target = action.target_pair_coordinates[action_at] as usize;
            let destination = cursors[target];
            cursors[target] += 1;
            generator_source_pairs[destination] = source as u32;
            generator_multiplicities[destination] = action.multiplicities[action_at];
        }
    }
    if generator_target_offsets.len() != generator_offset_population {
        return Err(CudaRefineError::MembraneInteriorWordShape);
    }

    Ok(SparsePairActionIngress {
        pair_factors,
        pair_row_offsets,
        target_offsets,
        source_pairs,
        multiplicities,
        generator_target_offsets,
        generator_source_pairs,
        generator_multiplicities,
        maximal_incoming_multiplicity,
    })
}

impl ResidentMembraneInteriorWord {
    /// Complete the same exact image passage while its receiver coordinates remain device-owned,
    /// and feed those coordinates directly through the standing boundary radiation, phase, and
    /// balance laws before the one terminal synchronization.  This is the productive image-rest
    /// route: no `Rat`, source rank-one family, or host semantic continuation stands between the
    /// descended image and its returned exterior consequence.
    pub fn complete_resident_factored_moment_boundary_receivers(
        &mut self,
        address: &ResidentFactoredMomentReceiverAddress,
        port_population: usize,
        entering_current: &ExactComplexWaveCurrent,
    ) -> Result<ResidentFactoredMomentBoundaryReturn, CudaRefineError> {
        let completion_plan = membrane_boundary_plan::prepare_boundary_completion(
            self,
            address,
            port_population,
            entering_current,
        )?;
        let buffer_octets = membrane_boundary_workspace::buffer_octets;
        let workspace = BoundaryCompletionWorkspace::allocate(self, &completion_plan)?;
        let support_phase = membrane_boundary_support_phase::enqueue_support_radiation_phase(
            self,
            &completion_plan,
            &workspace,
        )?;
        let BoundaryCompletionPlan {
            port_population: _plan_port_population,
            support_count,
            primitive_receiver_count: _primitive_receiver_count,
            family_count,
            opaque_receiver_count,
            generator_count,
            support_ports: ref _support_ports,
            support_port_pointer: _support_port_pointer,
            support_receiver_class_pointer: _support_receiver_class_pointer,
            support_quadratic_scale_pointer: _support_quadratic_scale_pointer,
            support_quadratic_scale_limb_count: _support_quadratic_scale_limb_count,
            maximal_support_quadratic_scale: ref _maximal_support_quadratic_scale,
            receiver_output_population: _receiver_output_population,
            receiver_limb_count: _receiver_limb_count,
            receiver_output_bound: ref _receiver_output_bound,
            ref receiver_denominator,
            receiver_sign_pointer: _receiver_sign_pointer,
            receiver_limbs_pointer: _receiver_limbs_pointer,
            rooted_completion,
            sparse_pair_completion,
            ref native_sparse_boundary,
            ref native_sparse_situated_aperture,
            ref native_sparse_relational_receiver,
            situated_population,
            ref situated_face_source_states,
            ref situated_face_ports,
            ref situated_face_generators,
            ref sparse_situated_current,
            support_family_population,
            support_receiver_population,
            port_family_population,
            port_receiver_population,
            component_count: _component_count,
            component_population,
            phase_pair_population,
            situated_pair_population,
            overlap_limb_count,
            contact_limb_count,
            radiation_limb_count,
            compatibility_limb_count,
            norm_limb_count,
            square_limb_count,
            cross_limb_count,
            ref returned_denominator,
            ref balance_denominator,
            joint_scale,
            incoming_real_bound: ref _incoming_real_bound,
            incoming_imaginary_bound: ref _incoming_imaginary_bound,
            situated_pairing_limb_count,
            ref situated_projective_dimensions,
            ref relational_projective_dimensions,
            stored_limb_count,
            incoming_real_sign: _incoming_real_sign,
            ref incoming_real_limbs,
            incoming_imaginary_sign: _incoming_imaginary_sign,
            ref incoming_imaginary_limbs,
        } = completion_plan;
        let BoundaryCompletionWorkspace {
            obstruction,
            action_sign: _action_sign,
            action_limbs: _action_limbs,
            reflected_sign: _reflected_sign,
            reflected_limbs: _reflected_limbs,
            opaque_receiver_sign: _opaque_receiver_sign,
            opaque_receiver_limbs: _opaque_receiver_limbs,
            receiver_norm_sign: _receiver_norm_sign,
            receiver_norm_limbs: _receiver_norm_limbs,
            contact_real_sign: _contact_real_sign,
            contact_real_limbs: _contact_real_limbs,
            contact_imaginary_sign: _contact_imaginary_sign,
            contact_imaginary_limbs: _contact_imaginary_limbs,
            support_real_sign: _support_real_sign,
            support_real_limbs: _support_real_limbs,
            support_imaginary_sign: _support_imaginary_sign,
            support_imaginary_limbs: _support_imaginary_limbs,
            port_real_sign,
            port_real_limbs,
            port_imaginary_sign,
            port_imaginary_limbs,
            joint_real_sign,
            joint_real_limbs,
            joint_imaginary_sign,
            joint_imaginary_limbs,
            port_action_sign,
            port_action_limbs,
            port_reflected_sign,
            port_reflected_limbs,
            port_receiver_sign,
            port_receiver_limbs,
            port_receiver_norm_sign,
            port_receiver_norm_limbs,
            compatibility_sign: _compatibility_sign,
            compatibility_limbs: _compatibility_limbs,
            phase_norm_limbs: _phase_norm_limbs,
            phase_locked,
            phase_pair_dominates: _phase_pair_dominates,
            phase_square_scratch: _phase_square_scratch,
            phase_left_cross_scratch: _phase_left_cross_scratch,
            phase_right_cross_scratch: _phase_right_cross_scratch,
            situated_pairing_sign,
            situated_pairing_limbs,
            situated_pairing_imaginary_scratch,
            situated_pairing_front,
            situated_native_phase_front,
            situated_projective_norm_product,
            situated_projective_current_self,
            situated_projective_ingress_self,
            incoming_real_sign_device,
            incoming_real_limbs_device,
            incoming_imaginary_sign_device,
            incoming_imaginary_limbs_device,
            stored_real_sign,
            stored_real_limbs,
            stored_imaginary_sign,
            stored_imaginary_limbs,
            balance_scratch,
        } = workspace;
        let BoundarySupportPhaseReceipt {
            complete_native_successor_front,
            mut complete_successor_launches,
            mut situated_phase_locked_pointer,
            mut situated_count_wire,
            situated_phase_select_grid,
            situated_phase_pair_grid,
        } = support_phase;
        let mut obstruction_pointer = obstruction.pointer;
        let mut port_real_sign_pointer = port_real_sign.pointer;
        let mut port_real_limbs_pointer = port_real_limbs.pointer;
        let mut port_imaginary_sign_pointer = port_imaginary_sign.pointer;
        let mut port_imaginary_limbs_pointer = port_imaginary_limbs.pointer;
        let mut joint_real_sign_pointer = joint_real_sign.pointer;
        let mut joint_real_limbs_pointer = joint_real_limbs.pointer;
        let mut joint_imaginary_sign_pointer = joint_imaginary_sign.pointer;
        let mut joint_imaginary_limbs_pointer = joint_imaginary_limbs.pointer;
        let mut radiation_limb_count_wire = radiation_limb_count as u32;
        let interval_stage = membrane_boundary_interval::stage_projective_interval(
            self,
            &completion_plan,
            situated_phase_locked_pointer,
            situated_phase_select_grid,
            situated_phase_pair_grid,
        )?;
        let _projective_interval_workspace = interval_stage.workspace;
        let projective_interval_workspace_octets = interval_stage.workspace_octets;
        let projective_interval_launches = interval_stage.launches;
        let projective_candidate_front = interval_stage.candidate_front;
        let projective_interval_obstruction = interval_stage.obstruction;
        situated_phase_locked_pointer = interval_stage.phase_locked_pointer;

        // Only interval-undefeated addressed faces now pay the exact projective contraction.
        // Other faces remain present in the native phase reconstruction fibre; the zeroed
        // situated coordinate is non-observation, not an identification with the form radical.
        let mut situated_front_workspace = Vec::<Buffer>::new();
        let mut situated_front_workspace_octets = 0_u64;
        let mut situated_front_launches = 0_u64;
        if native_sparse_situated_aperture.is_some() && trace_configuration().holonics_profile_sync
        {
            let began = std::time::Instant::now();
            driver(
                unsafe { cuCtxSynchronize() },
                "cuCtxSynchronize(profile native phase)",
            )?;
            eprintln!(
                "uar2-profile-native-phase-sync milliseconds={}",
                began.elapsed().as_millis(),
            );
        }
        if let Some((
            source_state_population,
            source_port_population,
            pair_population,
            pair_factors,
            current,
            current_limb_count,
            ingress_receiver,
            ingress_receiver_limb_count,
            restrictions,
            restriction_present,
            restriction_limb_count,
            situated_signs,
            situated_limbs,
            situated_current_norm_limbs,
            situated_ingress_norm_limbs,
            output_limb_count,
        )) = native_sparse_situated_aperture.as_ref()
        {
            const SITUATED_PROJECTIVE_PAIR_CHUNK: usize = 1024;
            const SITUATED_PROJECTIVE_FACE_WINDOW: usize = 32;
            let chunk_count = pair_population.div_ceil(SITUATED_PROJECTIVE_PAIR_CHUNK);
            let face_window_population = situated_population.min(SITUATED_PROJECTIVE_FACE_WINDOW);
            let section_capacity = face_window_population
                .checked_mul(3)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let partial_population = section_capacity
                .checked_mul(chunk_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let work_population = face_window_population
                .checked_mul(chunk_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let reduce_population = section_capacity
                .checked_mul(chunk_count.div_ceil(1024).max(1))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let partial_signs = Buffer::alloc(partial_population)?;
            let partial_limbs =
                Buffer::alloc(buffer_octets(partial_population, *output_limb_count)?)?;
            let reduce_signs = Buffer::alloc(reduce_population)?;
            let reduce_limbs =
                Buffer::alloc(buffer_octets(reduce_population, *output_limb_count)?)?;
            let final_signs = Buffer::alloc(section_capacity)?;
            let final_limbs = Buffer::alloc(buffer_octets(section_capacity, *output_limb_count)?)?;
            let first_scratch = Buffer::alloc(buffer_octets(work_population, *output_limb_count)?)?;
            let second_scratch =
                Buffer::alloc(buffer_octets(work_population, *output_limb_count)?)?;
            let mut phase_front_pointer = situated_phase_locked_pointer;
            let mut pair_factors_pointer = *pair_factors;
            let mut current_pointer = *current;
            let mut ingress_receiver_pointer = *ingress_receiver;
            let mut restrictions_pointer = *restrictions;
            let mut restriction_present_pointer = *restriction_present;
            let mut partial_sign_pointer = partial_signs.pointer;
            let mut partial_limb_pointer = partial_limbs.pointer;
            let mut first_scratch_pointer = first_scratch.pointer;
            let mut second_scratch_pointer = second_scratch.pointer;
            let mut pair_count_wire = *pair_population as u32;
            let mut factor_count_wire = self.factors;
            let mut source_state_count_wire = *source_state_population as u32;
            let mut source_port_count_wire = *source_port_population as u32;
            let mut face_count_wire = situated_population as u32;
            let mut generator_count_wire = generator_count as u32;
            let mut chunk_count_wire = chunk_count as u32;
            let mut chunk_size_wire = SITUATED_PROJECTIVE_PAIR_CHUNK as u32;
            let mut current_limb_count_wire = *current_limb_count as u32;
            let mut ingress_receiver_limb_count_wire = *ingress_receiver_limb_count as u32;
            let mut restriction_limb_count_wire = *restriction_limb_count as u32;
            let mut output_limb_count_wire = *output_limb_count as u32;
            let mut final_sign_pointer = final_signs.pointer;
            let mut final_limb_pointer = final_limbs.pointer;
            let mut situated_sign_pointer = *situated_signs;
            let mut situated_limb_pointer = *situated_limbs;
            let mut current_norm_pointer = *situated_current_norm_limbs;
            let mut ingress_norm_pointer = *situated_ingress_norm_limbs;
            let mut face_offset = 0_usize;
            let mut face_window_count = 0_usize;
            while face_offset < situated_population {
                let current_face_population =
                    face_window_population.min(situated_population - face_offset);
                let current_section_count = current_face_population
                    .checked_mul(3)
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
                let current_work_population = current_face_population
                    .checked_mul(chunk_count)
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
                let mut face_offset_wire = face_offset as u32;
                let mut window_face_count_wire = current_face_population as u32;
                let mut arguments: [*mut c_void; 25] = [
                    &mut phase_front_pointer as *mut u64 as *mut c_void,
                    &mut pair_factors_pointer as *mut u64 as *mut c_void,
                    &mut current_pointer as *mut u64 as *mut c_void,
                    &mut ingress_receiver_pointer as *mut u64 as *mut c_void,
                    &mut restrictions_pointer as *mut u64 as *mut c_void,
                    &mut restriction_present_pointer as *mut u64 as *mut c_void,
                    &mut partial_sign_pointer as *mut u64 as *mut c_void,
                    &mut partial_limb_pointer as *mut u64 as *mut c_void,
                    &mut first_scratch_pointer as *mut u64 as *mut c_void,
                    &mut second_scratch_pointer as *mut u64 as *mut c_void,
                    &mut pair_count_wire as *mut u32 as *mut c_void,
                    &mut factor_count_wire as *mut u32 as *mut c_void,
                    &mut source_state_count_wire as *mut u32 as *mut c_void,
                    &mut source_port_count_wire as *mut u32 as *mut c_void,
                    &mut face_count_wire as *mut u32 as *mut c_void,
                    &mut face_offset_wire as *mut u32 as *mut c_void,
                    &mut window_face_count_wire as *mut u32 as *mut c_void,
                    &mut generator_count_wire as *mut u32 as *mut c_void,
                    &mut chunk_count_wire as *mut u32 as *mut c_void,
                    &mut chunk_size_wire as *mut u32 as *mut c_void,
                    &mut current_limb_count_wire as *mut u32 as *mut c_void,
                    &mut ingress_receiver_limb_count_wire as *mut u32 as *mut c_void,
                    &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
                    &mut output_limb_count_wire as *mut u32 as *mut c_void,
                    &mut obstruction_pointer as *mut u64 as *mut c_void,
                ];
                driver(
                    unsafe {
                        cuLaunchKernel(
                            self.card
                                .membrane_sparse_quadratic_state_situated_front_chunks,
                            self.card.grid_for(current_work_population as u64)?,
                            1,
                            1,
                            self.card.block_x,
                            1,
                            1,
                            0,
                            ptr::null_mut(),
                            arguments.as_mut_ptr(),
                            ptr::null_mut(),
                        )
                    },
                    "cuLaunchKernel(form membrane sparse quadratic situated face window)",
                )?;
                let reduction_launches = self.reduce_sparse_quadratic_signed_sections(
                    &partial_signs,
                    &partial_limbs,
                    &reduce_signs,
                    &reduce_limbs,
                    &final_signs,
                    &final_limbs,
                    current_section_count,
                    chunk_count,
                    *output_limb_count,
                )?;
                let mut scatter_arguments: [*mut c_void; 10] = [
                    &mut final_sign_pointer as *mut u64 as *mut c_void,
                    &mut final_limb_pointer as *mut u64 as *mut c_void,
                    &mut situated_sign_pointer as *mut u64 as *mut c_void,
                    &mut situated_limb_pointer as *mut u64 as *mut c_void,
                    &mut current_norm_pointer as *mut u64 as *mut c_void,
                    &mut ingress_norm_pointer as *mut u64 as *mut c_void,
                    &mut face_offset_wire as *mut u32 as *mut c_void,
                    &mut window_face_count_wire as *mut u32 as *mut c_void,
                    &mut generator_count_wire as *mut u32 as *mut c_void,
                    &mut output_limb_count_wire as *mut u32 as *mut c_void,
                ];
                driver(
                    unsafe {
                        cuLaunchKernel(
                            self.card.membrane_sparse_quadratic_situated_front_scatter,
                            self.card.grid_for(current_face_population as u64)?,
                            1,
                            1,
                            self.card.block_x,
                            1,
                            1,
                            0,
                            ptr::null_mut(),
                            scatter_arguments.as_mut_ptr(),
                            ptr::null_mut(),
                        )
                    },
                    "cuLaunchKernel(scatter membrane sparse quadratic situated face window)",
                )?;
                situated_front_launches = situated_front_launches
                    .saturating_add(reduction_launches)
                    .saturating_add(2);
                face_window_count = face_window_count.saturating_add(1);
                face_offset = face_offset.saturating_add(current_face_population);
            }
            situated_front_workspace_octets = [
                partial_population,
                buffer_octets(partial_population, *output_limb_count)?,
                reduce_population,
                buffer_octets(reduce_population, *output_limb_count)?,
                section_capacity,
                buffer_octets(section_capacity, *output_limb_count)?,
                buffer_octets(work_population, *output_limb_count)?,
                buffer_octets(work_population, *output_limb_count)?,
            ]
            .into_iter()
            .try_fold(0_u64, |sum, octets| {
                sum.checked_add(u64::try_from(octets).ok()?)
            })
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            situated_front_workspace.extend([
                partial_signs,
                partial_limbs,
                reduce_signs,
                reduce_limbs,
                final_signs,
                final_limbs,
                first_scratch,
                second_scratch,
            ]);
            if trace_configuration().holonics_phase_trace {
                eprintln!(
                    "uar2-situated-front-staged faces={} face-windows={} face-window={} pairs={} chunks={} limbs={}",
                    situated_population,
                    face_window_count,
                    face_window_population,
                    pair_population,
                    chunk_count,
                    output_limb_count,
                );
            }
            if trace_configuration().holonics_profile_sync {
                let began = std::time::Instant::now();
                driver(
                    unsafe { cuCtxSynchronize() },
                    "cuCtxSynchronize(profile situated front)",
                )?;
                eprintln!(
                    "uar2-profile-situated-front-sync milliseconds={}",
                    began.elapsed().as_millis(),
                );
            }
        }

        let mut incoming_real_sign_pointer = incoming_real_sign_device.pointer;
        let mut incoming_real_limbs_pointer = incoming_real_limbs_device.pointer;
        let mut incoming_imaginary_sign_pointer = incoming_imaginary_sign_device.pointer;
        let mut incoming_imaginary_limbs_pointer = incoming_imaginary_limbs_device.pointer;
        let mut situated_pairing_sign_pointer = situated_pairing_sign.pointer;
        let mut situated_pairing_limbs_pointer = situated_pairing_limbs.pointer;
        let mut situated_pairing_imaginary_scratch_pointer =
            situated_pairing_imaginary_scratch.pointer;
        let mut situated_pairing_front_pointer = situated_pairing_front.pointer;
        let mut incoming_limb_count_wire = stored_limb_count as u32;
        let mut situated_pairing_limb_count_wire = situated_pairing_limb_count as u32;
        let mut situated_pairing_workspace = Vec::<Buffer>::new();
        let mut situated_pairing_workspace_octets = 0_u64;
        let mut situated_formation_launches = 1_u64;
        if let Some((
            native_signs,
            native_limbs,
            native_limb_count,
            _,
            native_current_norm_limbs,
            _,
            native_ingress_norm_limbs,
            _,
            _,
            _,
        )) = &native_sparse_boundary
        {
            let mut native_sign_pointer = *native_signs;
            let mut native_limb_pointer = *native_limbs;
            let mut native_section_count_wire = situated_population as u32;
            let mut native_input_count_wire = 1_u32;
            let mut native_output_count_wire = 1_u32;
            let mut native_reduction_chunk_wire = 1_u32;
            let mut native_copy_arguments: [*mut c_void; 9] = [
                &mut native_sign_pointer as *mut u64 as *mut c_void,
                &mut native_limb_pointer as *mut u64 as *mut c_void,
                &mut situated_pairing_sign_pointer as *mut u64 as *mut c_void,
                &mut situated_pairing_limbs_pointer as *mut u64 as *mut c_void,
                &mut native_section_count_wire as *mut u32 as *mut c_void,
                &mut native_input_count_wire as *mut u32 as *mut c_void,
                &mut native_output_count_wire as *mut u32 as *mut c_void,
                &mut native_reduction_chunk_wire as *mut u32 as *mut c_void,
                &mut situated_pairing_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_sparse_quadratic_signed_reduce,
                        situated_phase_select_grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        native_copy_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(copy_membrane_sparse_quadratic_native_situated_section)",
            )?;
            let (_, norm_product_limb_count, _, _) = situated_projective_dimensions
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let norm_product = situated_projective_norm_product
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let mut current_norm_pointer = *native_current_norm_limbs;
            let mut ingress_norm_pointer = *native_ingress_norm_limbs;
            let mut norm_product_pointer = norm_product.pointer;
            let mut returned_current_norm_pointer = situated_projective_current_self
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?
                .pointer;
            let mut returned_ingress_norm_pointer = situated_projective_ingress_self
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?
                .pointer;
            let mut native_norm_limb_count_wire = *native_limb_count as u32;
            let mut norm_product_limb_count_wire = *norm_product_limb_count as u32;
            let mut norm_product_arguments: [*mut c_void; 8] = [
                &mut current_norm_pointer as *mut u64 as *mut c_void,
                &mut ingress_norm_pointer as *mut u64 as *mut c_void,
                &mut norm_product_pointer as *mut u64 as *mut c_void,
                &mut returned_current_norm_pointer as *mut u64 as *mut c_void,
                &mut returned_ingress_norm_pointer as *mut u64 as *mut c_void,
                &mut situated_count_wire as *mut u32 as *mut c_void,
                &mut native_norm_limb_count_wire as *mut u32 as *mut c_void,
                &mut norm_product_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_sparse_quadratic_situated_norm_products,
                        situated_phase_select_grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        norm_product_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(form_membrane_sparse_quadratic_situated_norm_products)",
            )?;
            situated_formation_launches = situated_formation_launches.saturating_add(1);
        } else if let Some((
            pair_population,
            pair_factors_pointer,
            current_pointer,
            current_limb_count,
            _,
            ingress_receiver_pointer,
            ingress_receiver_limb_count,
            _,
            restriction_pointer,
            restriction_limb_count,
            _,
        )) = &sparse_situated_current
        {
            const SITUATED_CURRENT_PAIR_CHUNK: usize = 256;
            let chunk_count = pair_population
                .checked_add(SITUATED_CURRENT_PAIR_CHUNK - 1)
                .map(|held| held / SITUATED_CURRENT_PAIR_CHUNK)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let partial_population = situated_population
                .checked_mul(chunk_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let partial_octets = buffer_octets(partial_population, situated_pairing_limb_count)?;
            situated_pairing_workspace_octets = u64::try_from(partial_octets)
                .ok()
                .and_then(|octets| octets.checked_mul(4))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            for _ in 0..4 {
                situated_pairing_workspace.push(Buffer::alloc(partial_octets)?);
            }
            let mut partial_a_pointer = situated_pairing_workspace[0].pointer;
            let partial_b_pointer = situated_pairing_workspace[1].pointer;
            let mut product_first_pointer = situated_pairing_workspace[2].pointer;
            let mut product_second_pointer = situated_pairing_workspace[3].pointer;
            let mut pair_factors_pointer = *pair_factors_pointer;
            let mut current_pointer = *current_pointer;
            let mut ingress_receiver_pointer = *ingress_receiver_pointer;
            let mut restriction_pointer = *restriction_pointer;
            let mut pair_population_wire = *pair_population as u32;
            let mut factor_count_wire = self.factors;
            let mut chunk_count_wire = chunk_count as u32;
            let mut chunk_size_wire = SITUATED_CURRENT_PAIR_CHUNK as u32;
            let mut current_limb_count_wire = *current_limb_count as u32;
            let mut ingress_receiver_limb_count_wire = *ingress_receiver_limb_count as u32;
            let mut restriction_limb_count_wire = *restriction_limb_count as u32;
            let mut situated_pairing_arguments: [*mut c_void; 16] = [
                &mut pair_factors_pointer as *mut u64 as *mut c_void,
                &mut current_pointer as *mut u64 as *mut c_void,
                &mut ingress_receiver_pointer as *mut u64 as *mut c_void,
                &mut restriction_pointer as *mut u64 as *mut c_void,
                &mut partial_a_pointer as *mut u64 as *mut c_void,
                &mut product_first_pointer as *mut u64 as *mut c_void,
                &mut product_second_pointer as *mut u64 as *mut c_void,
                &mut pair_population_wire as *mut u32 as *mut c_void,
                &mut factor_count_wire as *mut u32 as *mut c_void,
                &mut situated_count_wire as *mut u32 as *mut c_void,
                &mut chunk_count_wire as *mut u32 as *mut c_void,
                &mut chunk_size_wire as *mut u32 as *mut c_void,
                &mut current_limb_count_wire as *mut u32 as *mut c_void,
                &mut ingress_receiver_limb_count_wire as *mut u32 as *mut c_void,
                &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
                &mut situated_pairing_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_sparse_quadratic_situated_chunks,
                        self.card.grid_for(partial_population as u64)?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        situated_pairing_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(form_membrane_sparse_quadratic_situated_chunks)",
            )?;
            situated_formation_launches = 1;

            let mut input_pointer = partial_a_pointer;
            let mut input_count = chunk_count;
            while input_count > 1 {
                let output_count = input_count
                    .checked_add(SITUATED_CURRENT_PAIR_CHUNK - 1)
                    .map(|held| held / SITUATED_CURRENT_PAIR_CHUNK)
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
                let mut output_pointer = if input_pointer == partial_a_pointer {
                    partial_b_pointer
                } else {
                    partial_a_pointer
                };
                let mut input_count_wire = input_count as u32;
                let mut output_count_wire = output_count as u32;
                let mut reduction_arguments: [*mut c_void; 7] = [
                    &mut input_pointer as *mut u64 as *mut c_void,
                    &mut output_pointer as *mut u64 as *mut c_void,
                    &mut situated_count_wire as *mut u32 as *mut c_void,
                    &mut input_count_wire as *mut u32 as *mut c_void,
                    &mut output_count_wire as *mut u32 as *mut c_void,
                    &mut chunk_size_wire as *mut u32 as *mut c_void,
                    &mut situated_pairing_limb_count_wire as *mut u32 as *mut c_void,
                ];
                driver(
                    unsafe {
                        cuLaunchKernel(
                            self.card.membrane_sparse_quadratic_situated_reduce,
                            self.card.grid_for(
                                situated_population.checked_mul(output_count).ok_or(
                                    CudaRefineError::MembraneInteriorCurrentOutsideApparatus,
                                )? as u64,
                            )?,
                            1,
                            1,
                            self.card.block_x,
                            1,
                            1,
                            0,
                            ptr::null_mut(),
                            reduction_arguments.as_mut_ptr(),
                            ptr::null_mut(),
                        )
                    },
                    "cuLaunchKernel(reduce_membrane_sparse_quadratic_situated_chunks)",
                )?;
                situated_formation_launches = situated_formation_launches.saturating_add(1);
                input_pointer = output_pointer;
                input_count = output_count;
            }

            let mut final_input_count_wire = 1_u32;
            let mut final_output_count_wire = 1_u32;
            let mut final_chunk_size_wire = 1_u32;
            let mut final_copy_arguments: [*mut c_void; 7] = [
                &mut input_pointer as *mut u64 as *mut c_void,
                &mut situated_pairing_limbs_pointer as *mut u64 as *mut c_void,
                &mut situated_count_wire as *mut u32 as *mut c_void,
                &mut final_input_count_wire as *mut u32 as *mut c_void,
                &mut final_output_count_wire as *mut u32 as *mut c_void,
                &mut final_chunk_size_wire as *mut u32 as *mut c_void,
                &mut situated_pairing_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_sparse_quadratic_situated_reduce,
                        situated_phase_select_grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        final_copy_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(copy_membrane_sparse_quadratic_situated_return)",
            )?;
            situated_formation_launches = situated_formation_launches.saturating_add(1);
            let mut situated_sign_arguments: [*mut c_void; 4] = [
                &mut situated_pairing_limbs_pointer as *mut u64 as *mut c_void,
                &mut situated_pairing_sign_pointer as *mut u64 as *mut c_void,
                &mut situated_count_wire as *mut u32 as *mut c_void,
                &mut situated_pairing_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_sparse_quadratic_situated_signs,
                        situated_phase_select_grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        situated_sign_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(mark_membrane_sparse_quadratic_situated_signs)",
            )?;
            situated_formation_launches = situated_formation_launches.saturating_add(1);
        } else {
            let mut situated_pairing_arguments: [*mut c_void; 16] = [
                &mut port_real_sign_pointer as *mut u64 as *mut c_void,
                &mut port_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut port_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut port_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut incoming_real_sign_pointer as *mut u64 as *mut c_void,
                &mut incoming_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut incoming_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut incoming_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut situated_phase_locked_pointer as *mut u64 as *mut c_void,
                &mut situated_pairing_sign_pointer as *mut u64 as *mut c_void,
                &mut situated_pairing_limbs_pointer as *mut u64 as *mut c_void,
                &mut situated_pairing_imaginary_scratch_pointer as *mut u64 as *mut c_void,
                &mut situated_count_wire as *mut u32 as *mut c_void,
                &mut radiation_limb_count_wire as *mut u32 as *mut c_void,
                &mut incoming_limb_count_wire as *mut u32 as *mut c_void,
                &mut situated_pairing_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_situated_output_pairing,
                        situated_phase_select_grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        situated_pairing_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(form_membrane_factored_image_situated_output_pairing)",
            )?;
        }
        let mut _projective_stream_workspace = Vec::<Buffer>::new();
        let mut projective_stream_workspace_octets = 0_u64;
        let mut projective_stream_launches = 0_u64;
        if let Some((
            _,
            norm_product_limb_count,
            projective_square_limb_count,
            projective_cross_limb_count,
        )) = &situated_projective_dimensions
        {
            // When a second independent receiver is present, selection is deferred until both
            // coordinate sections exist so their Pareto product can be streamed in one passage.
            if native_sparse_relational_receiver.is_none() {
                let norm_product_pointer = situated_projective_norm_product
                    .as_ref()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?
                    .pointer;
                let (workspace, launches, octets, window_population) = self
                    .stage_streamed_sparse_projective_front(
                        situated_phase_locked_pointer,
                        situated_pairing_sign_pointer,
                        situated_pairing_limbs_pointer,
                        situated_pairing_limb_count,
                        norm_product_pointer,
                        *norm_product_limb_count,
                        *projective_square_limb_count,
                        *projective_cross_limb_count,
                        None,
                        situated_pairing_front_pointer,
                        situated_population,
                    )?;
                _projective_stream_workspace = workspace;
                projective_stream_launches = launches;
                projective_stream_workspace_octets = octets;
                if trace_configuration().holonics_phase_trace {
                    eprintln!(
                        "uar2-projective-streamed pairs={} window={} launches={}",
                        situated_pair_population, window_population, launches,
                    );
                }
            }
        } else {
            let mut situated_select_direct = ptr::null_mut();
            driver(
                unsafe {
                    cuModuleGetFunction(
                        &mut situated_select_direct,
                        self.card.module,
                        c"select_membrane_situated_output_pairing_front_direct".as_ptr(),
                    )
                },
                "cuModuleGetFunction(select_membrane_situated_output_pairing_front_direct)",
            )?;
            let mut situated_chart_count_wire = 1_u32;
            let mut situated_select_arguments: [*mut c_void; 7] = [
                &mut situated_phase_locked_pointer as *mut u64 as *mut c_void,
                &mut situated_pairing_sign_pointer as *mut u64 as *mut c_void,
                &mut situated_pairing_limbs_pointer as *mut u64 as *mut c_void,
                &mut situated_pairing_front_pointer as *mut u64 as *mut c_void,
                &mut situated_count_wire as *mut u32 as *mut c_void,
                &mut situated_chart_count_wire as *mut u32 as *mut c_void,
                &mut situated_pairing_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        situated_select_direct,
                        situated_phase_select_grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        situated_select_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(select_membrane_situated_output_pairing_front_direct)",
            )?;
            projective_stream_launches = 1;
        }
        // The quadratic projective front is a receiver shadow, not complete native equality.
        // When `B^dagger K B` is present, its independent signed Complex-Parametron receiver is
        // composed with the quadratic receiver over the complete native phase front below.  No
        // scalar sum, lexical feature, or positive collapse joins the two currents.
        let mut relational_projective_front = None::<Buffer>;
        let mut relational_projective_workspace = Vec::<Buffer>::new();
        let mut relational_projective_workspace_octets = 0_u64;
        let mut relational_projective_launches = 0_u64;
        if let (
            Some((
                _,
                relational_signs,
                relational_limbs,
                relational_limb_count,
                _,
                relational_transported_norm,
                _,
                relational_ingress_norm,
                _,
            )),
            Some((norm_product_limb_count, square_limb_count, cross_limb_count)),
        ) = (
            native_sparse_relational_receiver.as_ref(),
            relational_projective_dimensions.as_ref(),
        ) {
            let norm_product = Buffer::alloc(buffer_octets(
                situated_population,
                *norm_product_limb_count,
            )?)?;
            let returned_transported_norm =
                Buffer::alloc(buffer_octets(situated_population, *relational_limb_count)?)?;
            let returned_ingress_norm =
                Buffer::alloc(buffer_octets(situated_population, *relational_limb_count)?)?;
            let selected_front = Buffer::alloc(situated_population)?;

            let mut relational_transported_norm_pointer = *relational_transported_norm;
            let mut relational_ingress_norm_pointer = *relational_ingress_norm;
            let mut norm_product_pointer = norm_product.pointer;
            let mut returned_transported_norm_pointer = returned_transported_norm.pointer;
            let mut returned_ingress_norm_pointer = returned_ingress_norm.pointer;
            let mut relational_face_count_wire = situated_population as u32;
            let mut relational_limb_count_wire = *relational_limb_count as u32;
            let mut norm_product_limb_count_wire = *norm_product_limb_count as u32;
            let mut norm_arguments: [*mut c_void; 8] = [
                &mut relational_transported_norm_pointer as *mut u64 as *mut c_void,
                &mut relational_ingress_norm_pointer as *mut u64 as *mut c_void,
                &mut norm_product_pointer as *mut u64 as *mut c_void,
                &mut returned_transported_norm_pointer as *mut u64 as *mut c_void,
                &mut returned_ingress_norm_pointer as *mut u64 as *mut c_void,
                &mut relational_face_count_wire as *mut u32 as *mut c_void,
                &mut relational_limb_count_wire as *mut u32 as *mut c_void,
                &mut norm_product_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_sparse_quadratic_situated_norm_products,
                        situated_phase_select_grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        norm_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(form_membrane_sparse_relational_situated_norm_products)",
            )?;
            let (
                _,
                quadratic_norm_limb_count,
                quadratic_square_limb_count,
                quadratic_cross_limb_count,
            ) = situated_projective_dimensions
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let quadratic_norm_pointer = situated_projective_norm_product
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?
                .pointer;
            let (mut streamed_workspace, streamed_launches, streamed_octets, window_population) =
                self.stage_streamed_sparse_projective_front(
                    situated_phase_locked_pointer,
                    situated_pairing_sign_pointer,
                    situated_pairing_limbs_pointer,
                    situated_pairing_limb_count,
                    quadratic_norm_pointer,
                    *quadratic_norm_limb_count,
                    *quadratic_square_limb_count,
                    *quadratic_cross_limb_count,
                    Some((
                        *relational_signs,
                        *relational_limbs,
                        *relational_limb_count,
                        norm_product.pointer,
                        *norm_product_limb_count,
                        *square_limb_count,
                        *cross_limb_count,
                    )),
                    selected_front.pointer,
                    situated_population,
                )?;
            relational_projective_launches = streamed_launches.saturating_add(1);
            relational_projective_workspace_octets = [
                buffer_octets(situated_population, *norm_product_limb_count)?,
                buffer_octets(situated_population, *relational_limb_count)?,
                buffer_octets(situated_population, *relational_limb_count)?,
                situated_population,
            ]
            .into_iter()
            .try_fold(0_u64, |sum, octets| {
                sum.checked_add(u64::try_from(octets).ok()?)
            })
            .and_then(|held| held.checked_add(streamed_octets))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            relational_projective_workspace.extend([
                norm_product,
                returned_transported_norm,
                returned_ingress_norm,
            ]);
            relational_projective_workspace.append(&mut streamed_workspace);
            relational_projective_front = Some(selected_front);
            if trace_configuration().holonics_phase_trace {
                eprintln!(
                    "uar2-projective-streamed pairs={} window={} launches={}",
                    situated_pair_population, window_population, streamed_launches,
                );
            }
        }
        if sparse_pair_completion {
            // Found the full state-addressed local-current successor before observation.  The
            // situated/projective fronts below may observe or realize this state, but cannot
            // remove an occurrence from its next-order carrier.
            let mut mark_productive = ptr::null_mut();
            driver(
                unsafe {
                    cuModuleGetFunction(
                        &mut mark_productive,
                        self.card.module,
                        c"mark_membrane_productive_current_front".as_ptr(),
                    )
                },
                "cuModuleGetFunction(mark_membrane_productive_current_front)",
            )?;
            let mut current_self_pointer = situated_projective_current_self
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?
                .pointer;
            let mut productive_front_pointer = complete_native_successor_front.pointer;
            let mut face_count_wire = situated_population as u32;
            let mut component_count_wire = 1_u32;
            let mut current_self_limb_count_wire = native_sparse_boundary
                .as_ref()
                .map(|(_, _, limb_count, _, _, _, _, _, _, _)| *limb_count as u32)
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let mut productive_arguments: [*mut c_void; 5] = [
                &mut current_self_pointer as *mut u64 as *mut c_void,
                &mut productive_front_pointer as *mut u64 as *mut c_void,
                &mut face_count_wire as *mut u32 as *mut c_void,
                &mut component_count_wire as *mut u32 as *mut c_void,
                &mut current_self_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        mark_productive,
                        self.card.grid_for(situated_population as u64)?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        productive_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(mark_membrane_productive_current_front)",
            )?;
            complete_successor_launches = 1;
            self.stage_resident_sparse_quadratic_returned_restriction(
                complete_native_successor_front.pointer,
                situated_population,
            )?;
        }

        // Sparse completion consumes `transported_image` and thereby drops its native boundary.
        // Keep the relational boundary owner alive until its terminal testimony has crossed the
        // host return below.  Retaining raw CUdeviceptr values alone is not ownership: after the
        // completion move those addresses may already have been released or reused.  The receiver
        // does not continue into the next native state; only its exact returned coordinates do.
        let completed_relational_receiver = if native_sparse_relational_receiver.is_some() {
            self.factored_receiver_history
                .as_mut()
                .and_then(|mount| mount.transported_image.as_mut())
                .and_then(|transport| transport.sparse_native_boundary.as_mut())
                .and_then(|boundary| boundary.relational_receiver.take())
        } else {
            None
        };
        let mut stored_real_sign_pointer = stored_real_sign.pointer;
        let mut stored_real_limbs_pointer = stored_real_limbs.pointer;
        let mut stored_imaginary_sign_pointer = stored_imaginary_sign.pointer;
        let mut stored_imaginary_limbs_pointer = stored_imaginary_limbs.pointer;
        let mut balance_scratch_pointer = balance_scratch.pointer;
        let mut joint_scale_wire = joint_scale;
        let mut stored_limb_count_wire = stored_limb_count as u32;
        let mut balance_arguments: [*mut c_void; 16] = [
            &mut joint_real_sign_pointer as *mut u64 as *mut c_void,
            &mut joint_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut joint_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut joint_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut incoming_real_sign_pointer as *mut u64 as *mut c_void,
            &mut incoming_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut incoming_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut incoming_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut joint_scale_wire as *mut u64 as *mut c_void,
            &mut stored_real_sign_pointer as *mut u64 as *mut c_void,
            &mut stored_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut stored_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut stored_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut balance_scratch_pointer as *mut u64 as *mut c_void,
            &mut radiation_limb_count_wire as *mut u32 as *mut c_void,
            &mut stored_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_boundary_chain_balance,
                    1,
                    1,
                    1,
                    1,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    balance_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(balance_membrane_factored_image_chain)",
        )?;
        self.card.launches = self
            .card
            .launches
            .checked_add(
                6_u64
                    .saturating_add(projective_interval_launches)
                    .saturating_add(situated_front_launches)
                    .saturating_add(situated_formation_launches)
                    .saturating_add(projective_stream_launches)
                    .saturating_add(relational_projective_launches)
                    .saturating_add(complete_successor_launches),
            )
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;

        membrane_boundary_return::complete_boundary_return(
            membrane_boundary_return::BoundaryReturnState {
                interior: self,
                address,
                sparse_pair_completion,
                rooted_completion,
                entering_current,
                obstruction,
                port_action_sign,
                port_action_limbs,
                port_reflected_sign,
                port_reflected_limbs,
                port_receiver_sign,
                port_receiver_limbs,
                port_receiver_norm_sign,
                port_receiver_norm_limbs,
                port_real_sign,
                port_real_limbs,
                port_imaginary_sign,
                port_imaginary_limbs,
                phase_locked,
                situated_pairing_sign,
                situated_pairing_limbs,
                situated_pairing_front,
                complete_native_successor_front,
                situated_native_phase_front,
                projective_candidate_front,
                projective_interval_obstruction,
                situated_projective_norm_product,
                situated_projective_current_self,
                situated_projective_ingress_self,
                relational_projective_front,
                joint_real_sign,
                joint_real_limbs,
                joint_imaginary_sign,
                joint_imaginary_limbs,
                stored_real_sign,
                stored_real_limbs,
                stored_imaginary_sign,
                stored_imaginary_limbs,
                completed_relational_receiver,
                native_sparse_boundary,
                native_sparse_relational_receiver,
                situated_projective_dimensions,
                situated_face_source_states,
                situated_face_ports,
                situated_face_generators,
                receiver_denominator,
                returned_denominator,
                balance_denominator,
                incoming_real_limbs,
                incoming_imaginary_limbs,
                port_population,
                support_count,
                family_count,
                opaque_receiver_count,
                generator_count,
                situated_population,
                support_family_population,
                support_receiver_population,
                port_family_population,
                port_receiver_population,
                component_population,
                phase_pair_population,
                overlap_limb_count,
                contact_limb_count,
                radiation_limb_count,
                compatibility_limb_count,
                norm_limb_count,
                square_limb_count,
                cross_limb_count,
                situated_pairing_limb_count,
                stored_limb_count,
                situated_pairing_workspace_octets,
                projective_interval_workspace_octets,
                situated_front_workspace_octets,
                projective_stream_workspace_octets,
                relational_projective_workspace_octets,
                projective_interval_launches,
                situated_front_launches,
                situated_formation_launches,
                projective_stream_launches,
                relational_projective_launches,
            },
        )
    }

    /// Form and contract the complete per-port quadratic moment without materializing the
    /// context-by-restriction-by-generator support product on the host.  The sparse axes cross
    /// once; both tensor formation and every declared quadratic receiver remain resident until
    /// the exact moment and contraction testimony returns.
    pub fn conduct_quadratic_moment_front(
        &mut self,
        front: &ResidentQuadraticMomentFront,
        port_population: usize,
        entering_current: &ExactComplexWaveCurrent,
        materialize_moment_field: bool,
    ) -> Result<ResidentQuadraticMomentReturn, CudaRefineError> {
        self.conduct_quadratic_moment_front_inner(
            front,
            port_population,
            entering_current,
            materialize_moment_field,
            None,
        )
    }

    /// Internal observer half of the resident HNN word.  `completed_step` is present only after
    /// the complete target-site direct sum has atomically replaced its source; consequently no
    /// receiver code in this method can author the state which it observes.
    // Chunk coordinates and terminal flags are consumed through retained CUDA argument pointers.
    #[allow(unused_assignments)]
    fn conduct_quadratic_moment_front_inner(
        &mut self,
        front: &ResidentQuadraticMomentFront,
        port_population: usize,
        entering_current: &ExactComplexWaveCurrent,
        materialize_moment_field: bool,
        completed_step: Option<ResidentCompletedTargetObservationAperture>,
    ) -> Result<ResidentQuadraticMomentReturn, CudaRefineError> {
        let resident_began = std::time::Instant::now();
        let post_target_observer = completed_step.is_some();
        let admission = membrane_moment_plan::admit_moment_front(
            self,
            front,
            port_population,
            entering_current,
        )?;
        let resident_rectangular_restrictions = admission.resident_rectangular_restrictions;
        if let Some(observed) = membrane_moment_plan::observe_completed_target(
            self,
            &admission,
            front,
            port_population,
            entering_current,
            materialize_moment_field,
            completed_step.as_ref(),
        )? {
            return Ok(observed);
        }

        let plan = admission.complete(
            self,
            front,
            port_population,
            entering_current,
            materialize_moment_field,
            completed_step.as_ref(),
        )?;

        let factor_receiver_observations = self
            .factor_receiver_observations
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let quadratic_action = self
            .quadratic_action
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let resident_atlas = if resident_rectangular_restrictions {
            Some(
                self.boundary_restriction_atlas
                    .as_ref()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
            )
        } else {
            None
        };
        let cuda_profile = trace_configuration().mem6_cuda_profile;
        let octets = |population: usize, limbs: usize| {
            population
                .checked_mul(limbs)
                .and_then(|words| words.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)
        };

        let allocation_began = std::time::Instant::now();
        let workspace = membrane_moment_workspace::allocate(
            self,
            &plan,
            post_target_observer,
            materialize_moment_field,
        )?;
        if cuda_profile {
            eprintln!(
                "mem6-cuda allocation_ms={} product_limbs={} moment_limbs={} overlap_limbs={}",
                allocation_began.elapsed().as_millis(),
                plan.product_limb_count,
                plan.moment_limb_count,
                plan.overlap_limb_count,
            );
        }
        let membrane_moment_workspace::MomentFrontWorkspace {
            context_current,
            context_weight,
            context_state_present,
            context_states,
            restriction_port,
            port_restriction_offset,
            restriction_current,
            restriction_present,
            restriction_target_states,
            boundary_states_device,
            universal_ports_device,
            active_factor_chart,
            generator_targets,
            generator_local_targets,
            moment,
            left_scratch,
            right_scratch,
            quadratic_scratch,
            term_scratch,
            action_sign,
            action_limbs,
            reflected_sign,
            reflected_limbs,
            receiver_sign,
            receiver_limbs,
            receiver_norm_sign,
            receiver_norm_limbs,
            contact_real_sign,
            contact_real_limbs,
            contact_imaginary_sign,
            contact_imaginary_limbs,
            overlap_scratch,
            contribution_action_sign,
            contribution_action_limbs,
            contribution_reflected_sign,
            contribution_reflected_limbs,
            contribution_receiver_sign,
            contribution_receiver_limbs,
            contribution_receiver_norm_sign,
            contribution_receiver_norm_limbs,
            factorized_left_scratch,
            factorized_right_scratch,
            factorized_bucket_scratch,
            factorized_quadratic_scratch,
            factorized_term_scratch,
            factorized_overlap_scratch,
            support_port,
            support_real_sign,
            support_real_limbs,
            support_imaginary_sign,
            support_imaginary_limbs,
            port_real_sign,
            port_real_limbs,
            port_imaginary_sign,
            port_imaginary_limbs,
            joint_real_sign,
            joint_real_limbs,
            joint_imaginary_sign,
            joint_imaginary_limbs,
            port_action_sign,
            port_action_limbs,
            port_reflected_sign,
            port_reflected_limbs,
            port_receiver_sign,
            port_receiver_limbs,
            port_receiver_norm_sign,
            port_receiver_norm_limbs,
            compatibility_sign,
            compatibility_limbs,
            phase_norm_limbs,
            phase_locked,
            phase_square_scratch,
            phase_left_cross_scratch,
            phase_right_cross_scratch,
            situated_pairing_sign,
            situated_pairing_limbs,
            situated_pairing_imaginary_scratch,
            situated_pairing_front,
            complete_native_successor_front,
            incoming_real_sign_device,
            incoming_real_limbs_device,
            incoming_imaginary_sign_device,
            incoming_imaginary_limbs_device,
            stored_real_sign,
            stored_real_limbs,
            stored_imaginary_sign,
            stored_imaginary_limbs,
            balance_scratch,
            factorized_relational_workspace,
        } = workspace;
        let membrane_moment_plan::MomentFrontPlan {
            factored_receiver_history,
            resident_current,
            resident_boundary,
            resident_rectangular_restrictions,
            restriction_count,
            resident_context_state,
            native_factors,
            factors,
            generator_count,
            port_restriction_offsets,
            context_count,
            active_factors,
            active_generator_targets,
            active_generator_local_targets,
            context_limb_count,
            restriction_limb_count,
            weight_limb_count,
            current_factor_population,
            context_current_limbs,
            restriction_current_limbs,
            context_weight_limbs,
            restriction_ports,
            maximal_context,
            relational_current_aperture,
            moment_limb_count,
            overlap_limb_count,
            contact_limb_count,
            radiation_limb_count,
            compatibility_limb_count,
            norm_limb_count,
            square_limb_count,
            cross_limb_count,
            situated_pairing_limb_count,
            stored_limb_count,
            joint_scale,
            balance_denominator,
            product_limb_count,
            quadratic_limb_count,
            component_count,
            descend_boundary_state_receiver,
            local_response_population,
            response_population,
            component_population,
            moment_population,
            axis_count,
            contraction_work,
            context_chunk_size,
            context_chunk_count,
            incidence_chunk_size,
            incidence_chunk_count,
            legacy_restriction_allocation_count,
            contribution_work,
            family_population,
            receiver_population,
            ..
        } = plan;

        let mut context_current_pointer = resident_context_state
            .as_ref()
            .map(|state| state.current_limbs_pointer)
            .or_else(|| context_current.as_ref().map(|buffer| buffer.pointer))
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut context_weight_pointer = resident_context_state
            .as_ref()
            .map(|state| state.weight_limbs_pointer)
            .or_else(|| context_weight.as_ref().map(|buffer| buffer.pointer))
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut context_state_present_pointer = resident_context_state
            .as_ref()
            .map(|state| state.boundary_state_present_pointer)
            .or_else(|| context_state_present.as_ref().map(|buffer| buffer.pointer))
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut context_states_pointer = resident_context_state
            .as_ref()
            .map(|state| state.boundary_states_pointer)
            .or_else(|| context_states.as_ref().map(|buffer| buffer.pointer))
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut restriction_port_pointer = restriction_port.pointer;
        let mut restriction_current_pointer = restriction_current.pointer;
        let mut moment_pointer = moment.pointer;
        let mut left_scratch_pointer = left_scratch.pointer;
        let mut right_scratch_pointer = right_scratch.pointer;
        let mut quadratic_scratch_pointer = quadratic_scratch.pointer;
        let mut term_scratch_pointer = term_scratch.pointer;
        let mut context_count_wire = context_count as u32;
        let mut restriction_count_wire = restriction_count as u32;
        let mut port_count_wire = port_population as u32;
        let mut factor_count_wire = factors as u32;
        let mut context_limb_count_wire = context_limb_count as u32;
        let mut restriction_limb_count_wire = restriction_limb_count as u32;
        let mut weight_limb_count_wire = weight_limb_count as u32;
        let mut product_limb_count_wire = product_limb_count as u32;
        let mut quadratic_limb_count_wire = quadratic_limb_count as u32;
        let mut moment_limb_count_wire = moment_limb_count as u32;
        let mut resident_gather_launches = 0_u64;
        if !post_target_observer {
            if let (Some(boundary), Some(atlas)) = (resident_boundary, resident_atlas) {
                let mut state_port_transition_pointer = atlas.state_port_transition.pointer;
                let mut transition_targets_pointer = atlas.transition_targets.pointer;
                let mut transition_factor_offset_pointer = atlas.transition_factor_offsets.pointer;
                let mut transition_factor_pointer = atlas.transition_factors.pointer;
                let mut transition_current_pointer = atlas.transition_current_limbs.pointer;
                let mut boundary_states_pointer = boundary_states_device.pointer;
                let mut universal_ports_pointer = universal_ports_device.pointer;
                let mut restriction_present_pointer = restriction_present.pointer;
                let mut restriction_target_states_pointer = restriction_target_states.pointer;
                let mut boundary_state_count_wire = boundary.boundary_states.len() as u32;
                let mut atlas_state_count_wire = atlas.state_count;
                let mut universal_port_count_wire = atlas.universal_port_count;
                let mut native_factor_count_wire = self.factors;
                let mut gather_arguments: [*mut c_void; 16] = [
                    &mut state_port_transition_pointer as *mut u64 as *mut c_void,
                    &mut transition_targets_pointer as *mut u64 as *mut c_void,
                    &mut transition_factor_offset_pointer as *mut u64 as *mut c_void,
                    &mut transition_factor_pointer as *mut u64 as *mut c_void,
                    &mut transition_current_pointer as *mut u64 as *mut c_void,
                    &mut boundary_states_pointer as *mut u64 as *mut c_void,
                    &mut universal_ports_pointer as *mut u64 as *mut c_void,
                    &mut restriction_current_pointer as *mut u64 as *mut c_void,
                    &mut restriction_present_pointer as *mut u64 as *mut c_void,
                    &mut restriction_target_states_pointer as *mut u64 as *mut c_void,
                    &mut boundary_state_count_wire as *mut u32 as *mut c_void,
                    &mut port_count_wire as *mut u32 as *mut c_void,
                    &mut atlas_state_count_wire as *mut u32 as *mut c_void,
                    &mut universal_port_count_wire as *mut u32 as *mut c_void,
                    &mut native_factor_count_wire as *mut u32 as *mut c_void,
                    &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
                ];
                let gather_grid = self.card.grid_for(restriction_count as u64)?;
                driver(
                    unsafe {
                        cuLaunchKernel(
                            self.card.membrane_resident_boundary_restriction_gather,
                            gather_grid,
                            1,
                            1,
                            self.card.block_x,
                            1,
                            1,
                            0,
                            ptr::null_mut(),
                            gather_arguments.as_mut_ptr(),
                            ptr::null_mut(),
                        )
                    },
                    "cuLaunchKernel(gather_membrane_resident_boundary_restrictions)",
                )?;
                resident_gather_launches = 1;
            }
        }
        let mut form_arguments: [*mut c_void; 19] = [
            &mut context_current_pointer as *mut u64 as *mut c_void,
            &mut context_weight_pointer as *mut u64 as *mut c_void,
            &mut restriction_port_pointer as *mut u64 as *mut c_void,
            &mut restriction_current_pointer as *mut u64 as *mut c_void,
            &mut moment_pointer as *mut u64 as *mut c_void,
            &mut left_scratch_pointer as *mut u64 as *mut c_void,
            &mut right_scratch_pointer as *mut u64 as *mut c_void,
            &mut quadratic_scratch_pointer as *mut u64 as *mut c_void,
            &mut term_scratch_pointer as *mut u64 as *mut c_void,
            &mut context_count_wire as *mut u32 as *mut c_void,
            &mut restriction_count_wire as *mut u32 as *mut c_void,
            &mut port_count_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut context_limb_count_wire as *mut u32 as *mut c_void,
            &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
            &mut weight_limb_count_wire as *mut u32 as *mut c_void,
            &mut product_limb_count_wire as *mut u32 as *mut c_void,
            &mut quadratic_limb_count_wire as *mut u32 as *mut c_void,
            &mut moment_limb_count_wire as *mut u32 as *mut c_void,
        ];
        if materialize_moment_field {
            let moment_grid = self.card.grid_for(moment_population as u64)?;
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_quadratic_moment_form,
                        moment_grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        form_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(form_membrane_quadratic_moments)",
            )?;
        }

        let mut active_factor_chart_pointer = active_factor_chart.pointer;
        let mut generator_targets_pointer = generator_targets.pointer;
        let mut generator_local_targets_pointer = generator_local_targets.pointer;
        let mut factor_receiver_observations_pointer = factor_receiver_observations.pointer;
        let mut factor_capacity_pointer = self.factor_capacity.pointer;
        let mut family_orientation_pointer = self.family_orientation.pointer;
        let mut family_real_sign_pointer = self.family_real_sign.pointer;
        let mut family_real_limbs_pointer = self.family_real_limbs.pointer;
        let mut family_imaginary_sign_pointer = self.family_imaginary_sign.pointer;
        let mut family_imaginary_limbs_pointer = self.family_imaginary_limbs.pointer;
        let mut action_sign_pointer = action_sign.pointer;
        let mut action_limbs_pointer = action_limbs.pointer;
        let mut reflected_sign_pointer = reflected_sign.pointer;
        let mut reflected_limbs_pointer = reflected_limbs.pointer;
        let mut receiver_sign_pointer = receiver_sign.pointer;
        let mut receiver_limbs_pointer = receiver_limbs.pointer;
        let mut receiver_norm_sign_pointer = receiver_norm_sign.pointer;
        let mut receiver_norm_limbs_pointer = receiver_norm_limbs.pointer;
        let mut contact_real_sign_pointer = contact_real_sign.pointer;
        let mut contact_real_limbs_pointer = contact_real_limbs.pointer;
        let mut contact_imaginary_sign_pointer = contact_imaginary_sign.pointer;
        let mut contact_imaginary_limbs_pointer = contact_imaginary_limbs.pointer;
        let mut overlap_scratch_pointer = overlap_scratch.pointer;
        let mut generator_count_wire = front.generator_count;
        let mut native_factor_count_wire = self.factors;
        let mut family_count_wire = self.families;
        let mut receiver_count_wire = self.receiver_count;
        let mut overlap_limb_count_wire = overlap_limb_count as u32;
        let mut family_limb_count_wire = self.family_limb_count;
        let mut contact_limb_count_wire = contact_limb_count as u32;
        let mut contract_arguments: [*mut c_void; 34] = [
            &mut moment_pointer as *mut u64 as *mut c_void,
            &mut active_factor_chart_pointer as *mut u64 as *mut c_void,
            &mut generator_targets_pointer as *mut u64 as *mut c_void,
            &mut generator_local_targets_pointer as *mut u64 as *mut c_void,
            &mut factor_receiver_observations_pointer as *mut u64 as *mut c_void,
            &mut factor_capacity_pointer as *mut u64 as *mut c_void,
            &mut family_orientation_pointer as *mut u64 as *mut c_void,
            &mut family_real_sign_pointer as *mut u64 as *mut c_void,
            &mut family_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut family_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut family_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut action_sign_pointer as *mut u64 as *mut c_void,
            &mut action_limbs_pointer as *mut u64 as *mut c_void,
            &mut reflected_sign_pointer as *mut u64 as *mut c_void,
            &mut reflected_limbs_pointer as *mut u64 as *mut c_void,
            &mut receiver_sign_pointer as *mut u64 as *mut c_void,
            &mut receiver_limbs_pointer as *mut u64 as *mut c_void,
            &mut receiver_norm_sign_pointer as *mut u64 as *mut c_void,
            &mut receiver_norm_limbs_pointer as *mut u64 as *mut c_void,
            &mut contact_real_sign_pointer as *mut u64 as *mut c_void,
            &mut contact_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut contact_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut contact_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut overlap_scratch_pointer as *mut u64 as *mut c_void,
            &mut port_count_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut native_factor_count_wire as *mut u32 as *mut c_void,
            &mut generator_count_wire as *mut u32 as *mut c_void,
            &mut family_count_wire as *mut u32 as *mut c_void,
            &mut receiver_count_wire as *mut u32 as *mut c_void,
            &mut moment_limb_count_wire as *mut u32 as *mut c_void,
            &mut overlap_limb_count_wire as *mut u32 as *mut c_void,
            &mut family_limb_count_wire as *mut u32 as *mut c_void,
            &mut contact_limb_count_wire as *mut u32 as *mut c_void,
        ];
        let contract_grid = self.card.grid_for(contraction_work as u64)?;
        let mut completed_target_observer_workspace = None;
        if post_target_observer {
            let aperture = completed_step
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let (
                _,
                _,
                _,
                target_relational_state_count,
                target_relational_real_sign_pointer,
                target_relational_real_limbs_pointer,
                target_relational_imaginary_sign_pointer,
                target_relational_imaginary_limbs_pointer,
                target_relational_limb_count,
                returned_relational_bound,
            ) = relational_current_aperture
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            if aperture.local_face_population != response_population
                || *target_relational_state_count != context_count
                || aperture.candidate_count == 0
                || aperture.selected_slot_count == 0
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            let face_current_bound = &maximal_context * BigUint::from(aperture.candidate_count);
            let face_relational_bound =
                returned_relational_bound * BigUint::from(aperture.candidate_count);
            let face_current_limb_count = face_current_bound.to_u32_digits().len().max(1);
            let face_relational_limb_count = face_relational_bound.to_u32_digits().len().max(1);
            let observer_limb_count = compatibility_limb_count;
            let face_factor_population = response_population
                .checked_mul(native_factors)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let observer_work = response_population
                .checked_mul(axis_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            let membrane_moment_workspace::MomentCompletedTargetObserverBuffers {
                face_current,
                face_relational_real_sign,
                face_relational_real_limbs,
                face_relational_imaginary_sign,
                face_relational_imaginary_limbs,
                relational_dot_real_sign,
                relational_dot_real_limbs,
                relational_dot_imaginary_sign,
                relational_dot_imaginary_limbs,
                target_norm_limbs,
                relational_norm_limbs,
                norm_product_limbs,
                first_scratch,
                second_scratch,
                third_scratch,
                obstruction,
            } = membrane_moment_workspace::allocate_completed_target_observer(
                response_population,
                face_factor_population,
                face_current_limb_count,
                face_relational_limb_count,
                observer_limb_count,
                observer_work,
            )?;

            let mut pushforward = ptr::null_mut();
            driver(
                unsafe {
                    cuModuleGetFunction(
                        &mut pushforward,
                        self.card.module,
                        c"pushforward_membrane_completed_target_observer_current".as_ptr(),
                    )
                },
                "cuModuleGetFunction(pushforward_membrane_completed_target_observer_current)",
            )?;
            let mut selected_faces_pointer = aperture.selected_faces.pointer;
            let mut target_relational_real_sign_pointer = *target_relational_real_sign_pointer;
            let mut target_relational_real_limbs_pointer = *target_relational_real_limbs_pointer;
            let mut target_relational_imaginary_sign_pointer =
                *target_relational_imaginary_sign_pointer;
            let mut target_relational_imaginary_limbs_pointer =
                *target_relational_imaginary_limbs_pointer;
            let mut candidate_selected_slots_pointer = aperture.candidate_selected_slots.pointer;
            let mut candidate_to_target_pointer = aperture.candidate_to_target.pointer;
            let mut face_current_pointer = face_current.pointer;
            let mut face_relational_real_sign_pointer = face_relational_real_sign.pointer;
            let mut face_relational_real_limbs_pointer = face_relational_real_limbs.pointer;
            let mut face_relational_imaginary_sign_pointer = face_relational_imaginary_sign.pointer;
            let mut face_relational_imaginary_limbs_pointer =
                face_relational_imaginary_limbs.pointer;
            let mut observer_obstruction_pointer = obstruction.pointer;
            let mut target_count_wire = context_count as u32;
            let mut selected_slot_count_wire = aperture.selected_slot_count as u32;
            let mut candidate_count_wire = aperture.candidate_count as u32;
            let mut observer_face_count_wire = response_population as u32;
            let mut target_relational_limb_count_wire = *target_relational_limb_count as u32;
            let mut face_current_limb_count_wire = face_current_limb_count as u32;
            let mut face_relational_limb_count_wire = face_relational_limb_count as u32;
            let mut pushforward_arguments: [*mut c_void; 23] = [
                &mut context_current_pointer as *mut u64 as *mut c_void,
                &mut target_relational_real_sign_pointer as *mut u64 as *mut c_void,
                &mut target_relational_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut target_relational_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut target_relational_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut selected_faces_pointer as *mut u64 as *mut c_void,
                &mut candidate_selected_slots_pointer as *mut u64 as *mut c_void,
                &mut candidate_to_target_pointer as *mut u64 as *mut c_void,
                &mut face_current_pointer as *mut u64 as *mut c_void,
                &mut face_relational_real_sign_pointer as *mut u64 as *mut c_void,
                &mut face_relational_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut face_relational_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut face_relational_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut observer_obstruction_pointer as *mut u64 as *mut c_void,
                &mut target_count_wire as *mut u32 as *mut c_void,
                &mut native_factor_count_wire as *mut u32 as *mut c_void,
                &mut selected_slot_count_wire as *mut u32 as *mut c_void,
                &mut candidate_count_wire as *mut u32 as *mut c_void,
                &mut observer_face_count_wire as *mut u32 as *mut c_void,
                &mut context_limb_count_wire as *mut u32 as *mut c_void,
                &mut target_relational_limb_count_wire as *mut u32 as *mut c_void,
                &mut face_current_limb_count_wire as *mut u32 as *mut c_void,
                &mut face_relational_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        pushforward,
                        self.card.grid_for(face_factor_population as u64)?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        pushforward_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(pushforward_membrane_completed_target_observer_current)",
            )?;

            let mut contract_completed = ptr::null_mut();
            driver(
                unsafe {
                    cuModuleGetFunction(
                        &mut contract_completed,
                        self.card.module,
                        c"contract_membrane_completed_target_observer".as_ptr(),
                    )
                },
                "cuModuleGetFunction(contract_membrane_completed_target_observer)",
            )?;
            let mut receiver_class_base_pointer = quadratic_action.receiver_class_bases.pointer;
            let mut source_class_factor_offset_pointer =
                quadratic_action.source_class_factor_offsets.pointer;
            let mut source_class_factor_pointer = quadratic_action.source_class_factors.pointer;
            let mut relational_dot_real_sign_pointer = relational_dot_real_sign.pointer;
            let mut relational_dot_real_limbs_pointer = relational_dot_real_limbs.pointer;
            let mut relational_dot_imaginary_sign_pointer = relational_dot_imaginary_sign.pointer;
            let mut relational_dot_imaginary_limbs_pointer = relational_dot_imaginary_limbs.pointer;
            let mut target_norm_pointer = target_norm_limbs.pointer;
            let mut relational_norm_pointer = relational_norm_limbs.pointer;
            let mut first_scratch_pointer = first_scratch.pointer;
            let mut second_scratch_pointer = second_scratch.pointer;
            let mut third_scratch_pointer = third_scratch.pointer;
            let mut axis_count_wire = axis_count as u32;
            let mut observer_limb_count_wire = observer_limb_count as u32;
            let mut direct_arguments: [*mut c_void; 47] = [
                &mut face_current_pointer as *mut u64 as *mut c_void,
                &mut face_relational_real_sign_pointer as *mut u64 as *mut c_void,
                &mut face_relational_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut face_relational_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut face_relational_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut receiver_class_base_pointer as *mut u64 as *mut c_void,
                &mut source_class_factor_offset_pointer as *mut u64 as *mut c_void,
                &mut source_class_factor_pointer as *mut u64 as *mut c_void,
                &mut factor_capacity_pointer as *mut u64 as *mut c_void,
                &mut family_orientation_pointer as *mut u64 as *mut c_void,
                &mut family_real_sign_pointer as *mut u64 as *mut c_void,
                &mut family_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut family_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut family_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut action_sign_pointer as *mut u64 as *mut c_void,
                &mut action_limbs_pointer as *mut u64 as *mut c_void,
                &mut reflected_sign_pointer as *mut u64 as *mut c_void,
                &mut reflected_limbs_pointer as *mut u64 as *mut c_void,
                &mut receiver_sign_pointer as *mut u64 as *mut c_void,
                &mut receiver_limbs_pointer as *mut u64 as *mut c_void,
                &mut receiver_norm_sign_pointer as *mut u64 as *mut c_void,
                &mut receiver_norm_limbs_pointer as *mut u64 as *mut c_void,
                &mut contact_real_sign_pointer as *mut u64 as *mut c_void,
                &mut contact_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut contact_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut contact_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut relational_dot_real_sign_pointer as *mut u64 as *mut c_void,
                &mut relational_dot_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut relational_dot_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut relational_dot_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut target_norm_pointer as *mut u64 as *mut c_void,
                &mut relational_norm_pointer as *mut u64 as *mut c_void,
                &mut first_scratch_pointer as *mut u64 as *mut c_void,
                &mut second_scratch_pointer as *mut u64 as *mut c_void,
                &mut third_scratch_pointer as *mut u64 as *mut c_void,
                &mut observer_obstruction_pointer as *mut u64 as *mut c_void,
                &mut observer_face_count_wire as *mut u32 as *mut c_void,
                &mut native_factor_count_wire as *mut u32 as *mut c_void,
                &mut family_count_wire as *mut u32 as *mut c_void,
                &mut receiver_count_wire as *mut u32 as *mut c_void,
                &mut axis_count_wire as *mut u32 as *mut c_void,
                &mut face_current_limb_count_wire as *mut u32 as *mut c_void,
                &mut face_relational_limb_count_wire as *mut u32 as *mut c_void,
                &mut family_limb_count_wire as *mut u32 as *mut c_void,
                &mut overlap_limb_count_wire as *mut u32 as *mut c_void,
                &mut observer_limb_count_wire as *mut u32 as *mut c_void,
                &mut contact_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        contract_completed,
                        self.card.grid_for(observer_work as u64)?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        direct_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(contract_membrane_completed_target_observer)",
            )?;
            let resident_working_octets = [
                octets(face_factor_population, face_current_limb_count)?,
                octets(face_factor_population, face_relational_limb_count)?
                    .checked_mul(2)
                    .and_then(|octets| octets.checked_add(face_factor_population * 2))
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
                octets(response_population, observer_limb_count)?
                    .checked_mul(7)
                    .and_then(|octets| octets.checked_add(response_population * 2))
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
                octets(observer_work, observer_limb_count)?
                    .checked_mul(3)
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
                std::mem::size_of::<u32>(),
            ]
            .into_iter()
            .try_fold(0_u64, |sum, octets| {
                sum.checked_add(u64::try_from(octets).ok()?)
            })
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
            completed_target_observer_workspace = Some(ResidentCompletedTargetObserverWorkspace {
                face_current,
                face_relational_real_sign,
                face_relational_real_limbs,
                face_relational_imaginary_sign,
                face_relational_imaginary_limbs,
                relational_dot_real_sign,
                relational_dot_real_limbs,
                relational_dot_imaginary_sign,
                relational_dot_imaginary_limbs,
                target_norm_limbs,
                relational_norm_limbs,
                norm_product_limbs,
                first_scratch,
                second_scratch,
                third_scratch,
                limb_count: observer_limb_count,
                obstruction,
                resident_working_octets,
            });
        } else if materialize_moment_field {
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_quadratic_moment_contract,
                        contract_grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        contract_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(contract_membrane_quadratic_moments)",
            )?;
        } else {
            let mut port_restriction_offset_pointer = port_restriction_offset.pointer;
            let mut native_generator_targets_pointer =
                quadratic_action.native_generator_targets.pointer;
            let mut receiver_class_base_pointer = quadratic_action.receiver_class_bases.pointer;
            let mut source_class_factor_offset_pointer =
                quadratic_action.source_class_factor_offsets.pointer;
            let mut source_class_factor_pointer = quadratic_action.source_class_factors.pointer;
            let mut generator_class_factor_offset_pointer =
                quadratic_action.generator_class_factor_offsets.pointer;
            let mut generator_class_factor_pointer =
                quadratic_action.generator_class_factors.pointer;
            let mut factorized_left_scratch_pointer = factorized_left_scratch.pointer;
            let mut factorized_right_scratch_pointer = factorized_right_scratch.pointer;
            let mut factorized_bucket_scratch_pointer = factorized_bucket_scratch.pointer;
            let mut factorized_quadratic_scratch_pointer = factorized_quadratic_scratch.pointer;
            let mut factorized_term_scratch_pointer = factorized_term_scratch.pointer;
            let mut factorized_overlap_scratch_pointer = factorized_overlap_scratch.pointer;
            let mut contribution_action_sign_pointer = contribution_action_sign.pointer;
            let mut contribution_action_limbs_pointer = contribution_action_limbs.pointer;
            let mut contribution_reflected_sign_pointer = contribution_reflected_sign.pointer;
            let mut contribution_reflected_limbs_pointer = contribution_reflected_limbs.pointer;
            let mut contribution_receiver_sign_pointer = contribution_receiver_sign.pointer;
            let mut contribution_receiver_limbs_pointer = contribution_receiver_limbs.pointer;
            let mut contribution_receiver_norm_sign_pointer =
                contribution_receiver_norm_sign.pointer;
            let mut contribution_receiver_norm_limbs_pointer =
                contribution_receiver_norm_limbs.pointer;
            let mut context_chunk_count_wire = context_chunk_count as u32;
            let mut context_chunk_size_wire = context_chunk_size as u32;
            let mut incidence_chunk_count_wire = incidence_chunk_count as u32;
            let mut incidence_chunk_size_wire = incidence_chunk_size as u32;
            let mut selected_context_chunk_wire = 0_u32;
            let mut selected_incidence_chunk_wire = 0_u32;
            let mut resident_rectangular_for_contract =
                u32::from(resident_rectangular_restrictions);
            let mut resident_boundary_state_count_for_contract = resident_boundary
                .map(|boundary| boundary.boundary_states.len() as u32)
                .unwrap_or(0);
            let mut boundary_states_for_contract_pointer = boundary_states_device.pointer;
            let mut factorized_arguments: [*mut c_void; 50] = [
                &mut context_current_pointer as *mut u64 as *mut c_void,
                &mut context_weight_pointer as *mut u64 as *mut c_void,
                &mut context_state_present_pointer as *mut u64 as *mut c_void,
                &mut context_states_pointer as *mut u64 as *mut c_void,
                &mut restriction_current_pointer as *mut u64 as *mut c_void,
                &mut boundary_states_for_contract_pointer as *mut u64 as *mut c_void,
                &mut native_generator_targets_pointer as *mut u64 as *mut c_void,
                &mut receiver_class_base_pointer as *mut u64 as *mut c_void,
                &mut source_class_factor_offset_pointer as *mut u64 as *mut c_void,
                &mut source_class_factor_pointer as *mut u64 as *mut c_void,
                &mut generator_class_factor_offset_pointer as *mut u64 as *mut c_void,
                &mut generator_class_factor_pointer as *mut u64 as *mut c_void,
                &mut factor_capacity_pointer as *mut u64 as *mut c_void,
                &mut family_orientation_pointer as *mut u64 as *mut c_void,
                &mut contribution_action_sign_pointer as *mut u64 as *mut c_void,
                &mut contribution_action_limbs_pointer as *mut u64 as *mut c_void,
                &mut contribution_reflected_sign_pointer as *mut u64 as *mut c_void,
                &mut contribution_reflected_limbs_pointer as *mut u64 as *mut c_void,
                &mut contribution_receiver_sign_pointer as *mut u64 as *mut c_void,
                &mut contribution_receiver_limbs_pointer as *mut u64 as *mut c_void,
                &mut contribution_receiver_norm_sign_pointer as *mut u64 as *mut c_void,
                &mut contribution_receiver_norm_limbs_pointer as *mut u64 as *mut c_void,
                &mut factorized_left_scratch_pointer as *mut u64 as *mut c_void,
                &mut factorized_right_scratch_pointer as *mut u64 as *mut c_void,
                &mut factorized_bucket_scratch_pointer as *mut u64 as *mut c_void,
                &mut factorized_quadratic_scratch_pointer as *mut u64 as *mut c_void,
                &mut factorized_term_scratch_pointer as *mut u64 as *mut c_void,
                &mut factorized_overlap_scratch_pointer as *mut u64 as *mut c_void,
                &mut context_count_wire as *mut u32 as *mut c_void,
                &mut restriction_count_wire as *mut u32 as *mut c_void,
                &mut port_count_wire as *mut u32 as *mut c_void,
                &mut native_factor_count_wire as *mut u32 as *mut c_void,
                &mut generator_count_wire as *mut u32 as *mut c_void,
                &mut family_count_wire as *mut u32 as *mut c_void,
                &mut receiver_count_wire as *mut u32 as *mut c_void,
                &mut context_chunk_count_wire as *mut u32 as *mut c_void,
                &mut context_chunk_size_wire as *mut u32 as *mut c_void,
                &mut incidence_chunk_count_wire as *mut u32 as *mut c_void,
                &mut incidence_chunk_size_wire as *mut u32 as *mut c_void,
                &mut selected_context_chunk_wire as *mut u32 as *mut c_void,
                &mut selected_incidence_chunk_wire as *mut u32 as *mut c_void,
                &mut context_limb_count_wire as *mut u32 as *mut c_void,
                &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
                &mut weight_limb_count_wire as *mut u32 as *mut c_void,
                &mut product_limb_count_wire as *mut u32 as *mut c_void,
                &mut quadratic_limb_count_wire as *mut u32 as *mut c_void,
                &mut moment_limb_count_wire as *mut u32 as *mut c_void,
                &mut overlap_limb_count_wire as *mut u32 as *mut c_void,
                &mut resident_rectangular_for_contract as *mut u32 as *mut c_void,
                &mut resident_boundary_state_count_for_contract as *mut u32 as *mut c_void,
            ];
            let contribution_grid = self.card.grid_for(contribution_work as u64)?;
            let mut axis_count_wire = axis_count as u32;
            let mut resident_rectangular_wire = u32::from(resident_rectangular_restrictions);
            let mut resident_boundary_state_count_wire = resident_boundary
                .map(|boundary| boundary.boundary_states.len() as u32)
                .unwrap_or(0);
            let mut clear_output_wire = 1_u32;
            let mut finalize_contact_wire = 0_u32;
            let mut descend_boundary_state_receiver_wire =
                u32::from(descend_boundary_state_receiver);
            let mut reduce_arguments: [*mut c_void; 40] = [
                &mut contribution_action_sign_pointer as *mut u64 as *mut c_void,
                &mut contribution_action_limbs_pointer as *mut u64 as *mut c_void,
                &mut contribution_reflected_sign_pointer as *mut u64 as *mut c_void,
                &mut contribution_reflected_limbs_pointer as *mut u64 as *mut c_void,
                &mut contribution_receiver_sign_pointer as *mut u64 as *mut c_void,
                &mut contribution_receiver_limbs_pointer as *mut u64 as *mut c_void,
                &mut contribution_receiver_norm_sign_pointer as *mut u64 as *mut c_void,
                &mut contribution_receiver_norm_limbs_pointer as *mut u64 as *mut c_void,
                &mut port_restriction_offset_pointer as *mut u64 as *mut c_void,
                &mut family_real_sign_pointer as *mut u64 as *mut c_void,
                &mut family_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut family_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut family_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut action_sign_pointer as *mut u64 as *mut c_void,
                &mut action_limbs_pointer as *mut u64 as *mut c_void,
                &mut reflected_sign_pointer as *mut u64 as *mut c_void,
                &mut reflected_limbs_pointer as *mut u64 as *mut c_void,
                &mut receiver_sign_pointer as *mut u64 as *mut c_void,
                &mut receiver_limbs_pointer as *mut u64 as *mut c_void,
                &mut receiver_norm_sign_pointer as *mut u64 as *mut c_void,
                &mut receiver_norm_limbs_pointer as *mut u64 as *mut c_void,
                &mut contact_real_sign_pointer as *mut u64 as *mut c_void,
                &mut contact_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut contact_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut contact_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut context_chunk_count_wire as *mut u32 as *mut c_void,
                &mut incidence_chunk_count_wire as *mut u32 as *mut c_void,
                &mut port_count_wire as *mut u32 as *mut c_void,
                &mut generator_count_wire as *mut u32 as *mut c_void,
                &mut family_count_wire as *mut u32 as *mut c_void,
                &mut receiver_count_wire as *mut u32 as *mut c_void,
                &mut axis_count_wire as *mut u32 as *mut c_void,
                &mut overlap_limb_count_wire as *mut u32 as *mut c_void,
                &mut family_limb_count_wire as *mut u32 as *mut c_void,
                &mut contact_limb_count_wire as *mut u32 as *mut c_void,
                &mut resident_rectangular_wire as *mut u32 as *mut c_void,
                &mut resident_boundary_state_count_wire as *mut u32 as *mut c_void,
                &mut descend_boundary_state_receiver_wire as *mut u32 as *mut c_void,
                &mut clear_output_wire as *mut u32 as *mut c_void,
                &mut finalize_contact_wire as *mut u32 as *mut c_void,
            ];
            let contraction_began = std::time::Instant::now();
            for context_chunk in 0..context_chunk_count {
                selected_context_chunk_wire = context_chunk as u32;
                for incidence_chunk in 0..incidence_chunk_count {
                    selected_incidence_chunk_wire = incidence_chunk as u32;
                    clear_output_wire = u32::from(context_chunk == 0 && incidence_chunk == 0);
                    finalize_contact_wire = u32::from(
                        context_chunk + 1 == context_chunk_count
                            && incidence_chunk + 1 == incidence_chunk_count,
                    );
                    driver(
                        unsafe {
                            cuLaunchKernel(
                                self.card.membrane_factorized_moment_contract,
                                contribution_grid,
                                1,
                                1,
                                self.card.block_x,
                                1,
                                1,
                                0,
                                ptr::null_mut(),
                                factorized_arguments.as_mut_ptr(),
                                ptr::null_mut(),
                            )
                        },
                        "cuLaunchKernel(contract_membrane_factorized_quadratic_moments)",
                    )?;
                    driver(
                        unsafe {
                            cuLaunchKernel(
                                self.card.membrane_factorized_moment_reduce,
                                contract_grid,
                                1,
                                1,
                                self.card.block_x,
                                1,
                                1,
                                0,
                                ptr::null_mut(),
                                reduce_arguments.as_mut_ptr(),
                                ptr::null_mut(),
                            )
                        },
                        "cuLaunchKernel(reduce_membrane_factorized_quadratic_moments)",
                    )?;
                }
            }
            if cuda_profile {
                driver(
                    unsafe { cuCtxSynchronize() },
                    "cuCtxSynchronize(factorized-cover-profile)",
                )?;
                eprintln!(
                    "mem6-cuda contract-reduce-ms={} resident-contributions={} context-chunks={} context-chunk-size={} incidence-chunks={} incidence-chunk-size={} addressed-faces={}",
                    contraction_began.elapsed().as_millis(),
                    contribution_work,
                    context_chunk_count,
                    context_chunk_size,
                    incidence_chunk_count,
                    incidence_chunk_size,
                    response_population,
                );
            }
        }

        let mut factorized_relational_launches = 0_u64;
        if let (
            Some(workspace),
            Some((
                _,
                source_relational_state_present,
                source_relational_states,
                source_relational_state_count,
                source_relational_real_sign,
                source_relational_real_limbs,
                source_relational_imaginary_sign,
                source_relational_imaginary_limbs,
                source_relational_limb_count,
                _,
            )),
        ) = (
            factorized_relational_workspace.as_ref(),
            relational_current_aperture.as_ref(),
        ) {
            let boundary = resident_boundary.ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let mut transported_current_pointer = workspace.transported_current.pointer;
            let mut transported_state_present_pointer = workspace.transported_state_present.pointer;
            let mut transported_states_pointer = workspace.transported_states.pointer;
            let mut transported_limb_count_wire = workspace.transported_limb_count as u32;
            let mut relational_generator_targets_pointer =
                quadratic_action.native_generator_targets.pointer;
            let mut source_relational_state_present_pointer = *source_relational_state_present;
            let mut source_relational_states_pointer = *source_relational_states;
            let mut source_relational_real_sign_pointer = *source_relational_real_sign;
            let mut source_relational_real_limbs_pointer = *source_relational_real_limbs;
            let mut source_relational_imaginary_sign_pointer = *source_relational_imaginary_sign;
            let mut source_relational_imaginary_limbs_pointer = *source_relational_imaginary_limbs;
            let mut transported_relational_real_sign_pointer =
                workspace.transported_relational_real_sign.pointer;
            let mut transported_relational_real_limbs_pointer =
                workspace.transported_relational_real_limbs.pointer;
            let mut transported_relational_imaginary_sign_pointer =
                workspace.transported_relational_imaginary_sign.pointer;
            let mut transported_relational_imaginary_limbs_pointer =
                workspace.transported_relational_imaginary_limbs.pointer;
            let mut relational_obstruction_pointer = workspace.obstruction.pointer;
            let mut relational_factor_count_wire = self.factors;
            let mut relational_generator_count_wire = front.generator_count;
            let mut source_relational_state_count_wire = *source_relational_state_count as u32;
            let mut source_relational_limb_count_wire = *source_relational_limb_count as u32;
            let mut transported_relational_limb_count_wire =
                workspace.transported_relational_limb_count as u32;
            let mut relational_transport = ptr::null_mut();
            let mut relational_partial = ptr::null_mut();
            let mut relational_norm = ptr::null_mut();
            driver(
                unsafe {
                    cuModuleGetFunction(
                        &mut relational_transport,
                        self.card.module,
                        c"transport_membrane_sparse_relational_generator_limbs".as_ptr(),
                    )
                },
                "cuModuleGetFunction(transport_membrane_sparse_relational_generator_limbs)",
            )?;
            driver(
                unsafe {
                    cuModuleGetFunction(
                        &mut relational_partial,
                        self.card.module,
                        c"form_membrane_factorized_relational_moment_partials".as_ptr(),
                    )
                },
                "cuModuleGetFunction(form_membrane_factorized_relational_moment_partials)",
            )?;
            driver(
                unsafe {
                    cuModuleGetFunction(
                        &mut relational_norm,
                        self.card.module,
                        c"form_membrane_factorized_relational_current_norms".as_ptr(),
                    )
                },
                "cuModuleGetFunction(form_membrane_factorized_relational_current_norms)",
            )?;

            let mut current_transport_arguments: [*mut c_void; 12] = [
                &mut context_current_pointer as *mut u64 as *mut c_void,
                &mut context_state_present_pointer as *mut u64 as *mut c_void,
                &mut context_states_pointer as *mut u64 as *mut c_void,
                &mut relational_generator_targets_pointer as *mut u64 as *mut c_void,
                &mut transported_current_pointer as *mut u64 as *mut c_void,
                &mut transported_state_present_pointer as *mut u64 as *mut c_void,
                &mut transported_states_pointer as *mut u64 as *mut c_void,
                &mut context_count_wire as *mut u32 as *mut c_void,
                &mut native_factor_count_wire as *mut u32 as *mut c_void,
                &mut generator_count_wire as *mut u32 as *mut c_void,
                &mut context_limb_count_wire as *mut u32 as *mut c_void,
                &mut transported_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.membrane_factor_current_transport,
                        self.card.grid_for(
                            u64::try_from(context_count.saturating_mul(generator_count))
                                .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
                        )?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        current_transport_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(transport_membrane_factorized_relational_source_currents)",
            )?;
            let mut relational_transport_arguments: [*mut c_void; 16] = [
                &mut relational_generator_targets_pointer as *mut u64 as *mut c_void,
                &mut source_relational_state_present_pointer as *mut u64 as *mut c_void,
                &mut source_relational_real_sign_pointer as *mut u64 as *mut c_void,
                &mut source_relational_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut source_relational_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut source_relational_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_real_sign_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut relational_factor_count_wire as *mut u32 as *mut c_void,
                &mut relational_generator_count_wire as *mut u32 as *mut c_void,
                &mut source_relational_state_count_wire as *mut u32 as *mut c_void,
                &mut source_relational_limb_count_wire as *mut u32 as *mut c_void,
                &mut transported_relational_limb_count_wire as *mut u32 as *mut c_void,
                &mut relational_obstruction_pointer as *mut u64 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        relational_transport,
                        self.card.grid_for(
                            u64::from(self.factors)
                                * u64::from(front.generator_count)
                                * u64::try_from(*source_relational_state_count)
                                    .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
                        )?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        relational_transport_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(transport_membrane_sparse_relational_generator_limbs)",
            )?;

            let mut relational_restriction_pointer = restriction_current.pointer;
            let mut relational_restriction_present_pointer = restriction_present.pointer;
            let mut relational_boundary_states_pointer = boundary_states_device.pointer;
            let mut partial_overlap_pointer = workspace.partial_overlap.pointer;
            let mut partial_target_norm_pointer = workspace.partial_target_norm.pointer;
            let mut dot_real_sign_pointer = workspace.dot_real_signs.pointer;
            let mut dot_real_pointer = workspace.dot_real.pointer;
            let mut dot_imaginary_sign_pointer = workspace.dot_imaginary_signs.pointer;
            let mut dot_imaginary_pointer = workspace.dot_imaginary.pointer;
            let mut partial_first_scratch_pointer = workspace.partial_first_scratch.pointer;
            let mut partial_second_scratch_pointer = workspace.partial_second_scratch.pointer;
            let mut partial_third_scratch_pointer = workspace.partial_third_scratch.pointer;
            let mut relational_port_count_wire = port_population as u32;
            let mut relational_boundary_state_count_wire = boundary.boundary_states.len() as u32;
            let mut relational_output_limb_count_wire = workspace.limb_count as u32;
            let mut relational_partial_arguments: [*mut c_void; 33] = [
                &mut transported_current_pointer as *mut u64 as *mut c_void,
                &mut transported_state_present_pointer as *mut u64 as *mut c_void,
                &mut transported_states_pointer as *mut u64 as *mut c_void,
                &mut context_weight_pointer as *mut u64 as *mut c_void,
                &mut relational_restriction_pointer as *mut u64 as *mut c_void,
                &mut relational_restriction_present_pointer as *mut u64 as *mut c_void,
                &mut relational_boundary_states_pointer as *mut u64 as *mut c_void,
                &mut source_relational_state_present_pointer as *mut u64 as *mut c_void,
                &mut source_relational_states_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_real_sign_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut partial_overlap_pointer as *mut u64 as *mut c_void,
                &mut partial_target_norm_pointer as *mut u64 as *mut c_void,
                &mut dot_real_sign_pointer as *mut u64 as *mut c_void,
                &mut dot_real_pointer as *mut u64 as *mut c_void,
                &mut dot_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut dot_imaginary_pointer as *mut u64 as *mut c_void,
                &mut partial_first_scratch_pointer as *mut u64 as *mut c_void,
                &mut partial_second_scratch_pointer as *mut u64 as *mut c_void,
                &mut partial_third_scratch_pointer as *mut u64 as *mut c_void,
                &mut context_count_wire as *mut u32 as *mut c_void,
                &mut relational_factor_count_wire as *mut u32 as *mut c_void,
                &mut relational_port_count_wire as *mut u32 as *mut c_void,
                &mut relational_generator_count_wire as *mut u32 as *mut c_void,
                &mut relational_boundary_state_count_wire as *mut u32 as *mut c_void,
                &mut source_relational_state_count_wire as *mut u32 as *mut c_void,
                &mut transported_limb_count_wire as *mut u32 as *mut c_void,
                &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
                &mut transported_relational_limb_count_wire as *mut u32 as *mut c_void,
                &mut weight_limb_count_wire as *mut u32 as *mut c_void,
                &mut relational_output_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        relational_partial,
                        self.card.grid_for(
                            u64::try_from(local_response_population.saturating_mul(context_count))
                                .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?,
                        )?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        relational_partial_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(form_membrane_factorized_relational_moment_partials)",
            )?;

            let mut relational_norm_pointer = workspace.relational_norm.pointer;
            let mut norm_first_scratch_pointer = workspace.norm_first_scratch.pointer;
            let mut norm_second_scratch_pointer = workspace.norm_second_scratch.pointer;
            let mut descend_relational_receiver_wire = u32::from(descend_boundary_state_receiver);
            let mut relational_norm_arguments: [*mut c_void; 21] = [
                &mut relational_restriction_pointer as *mut u64 as *mut c_void,
                &mut relational_restriction_present_pointer as *mut u64 as *mut c_void,
                &mut relational_boundary_states_pointer as *mut u64 as *mut c_void,
                &mut source_relational_state_present_pointer as *mut u64 as *mut c_void,
                &mut source_relational_states_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_real_sign_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_imaginary_sign_pointer as *mut u64 as *mut c_void,
                &mut transported_relational_imaginary_limbs_pointer as *mut u64 as *mut c_void,
                &mut relational_norm_pointer as *mut u64 as *mut c_void,
                &mut norm_first_scratch_pointer as *mut u64 as *mut c_void,
                &mut norm_second_scratch_pointer as *mut u64 as *mut c_void,
                &mut relational_port_count_wire as *mut u32 as *mut c_void,
                &mut relational_factor_count_wire as *mut u32 as *mut c_void,
                &mut relational_generator_count_wire as *mut u32 as *mut c_void,
                &mut relational_boundary_state_count_wire as *mut u32 as *mut c_void,
                &mut source_relational_state_count_wire as *mut u32 as *mut c_void,
                &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
                &mut transported_relational_limb_count_wire as *mut u32 as *mut c_void,
                &mut relational_output_limb_count_wire as *mut u32 as *mut c_void,
                &mut descend_relational_receiver_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        relational_norm,
                        self.card.grid_for(response_population as u64)?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        relational_norm_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(form_membrane_factorized_relational_current_norms)",
            )?;
            factorized_relational_launches = 4;
        }

        // Every successor below receives the complete addressed higher-face population.  The
        // physical port count remains only in the cold reconstruction chart above.
        port_count_wire = response_population as u32;

        let mut support_port_pointer = support_port.pointer;
        let mut support_real_sign_pointer = support_real_sign.pointer;
        let mut support_real_limbs_pointer = support_real_limbs.pointer;
        let mut support_imaginary_sign_pointer = support_imaginary_sign.pointer;
        let mut support_imaginary_limbs_pointer = support_imaginary_limbs.pointer;
        let mut port_real_sign_pointer = port_real_sign.pointer;
        let mut port_real_limbs_pointer = port_real_limbs.pointer;
        let mut port_imaginary_sign_pointer = port_imaginary_sign.pointer;
        let mut port_imaginary_limbs_pointer = port_imaginary_limbs.pointer;
        let mut joint_real_sign_pointer = joint_real_sign.pointer;
        let mut joint_real_limbs_pointer = joint_real_limbs.pointer;
        let mut joint_imaginary_sign_pointer = joint_imaginary_sign.pointer;
        let mut joint_imaginary_limbs_pointer = joint_imaginary_limbs.pointer;
        let mut port_action_sign_pointer = port_action_sign.pointer;
        let mut port_action_limbs_pointer = port_action_limbs.pointer;
        let mut port_reflected_sign_pointer = port_reflected_sign.pointer;
        let mut port_reflected_limbs_pointer = port_reflected_limbs.pointer;
        let mut port_receiver_sign_pointer = port_receiver_sign.pointer;
        let mut port_receiver_limbs_pointer = port_receiver_limbs.pointer;
        let mut port_receiver_norm_sign_pointer = port_receiver_norm_sign.pointer;
        let mut port_receiver_norm_limbs_pointer = port_receiver_norm_limbs.pointer;
        let mut support_count_wire = response_population as u32;
        let mut radiation_limb_count_wire = radiation_limb_count as u32;
        let mut radiation_arguments: [*mut c_void; 40] = [
            &mut support_port_pointer as *mut u64 as *mut c_void,
            &mut action_sign_pointer as *mut u64 as *mut c_void,
            &mut action_limbs_pointer as *mut u64 as *mut c_void,
            &mut reflected_sign_pointer as *mut u64 as *mut c_void,
            &mut reflected_limbs_pointer as *mut u64 as *mut c_void,
            &mut receiver_sign_pointer as *mut u64 as *mut c_void,
            &mut receiver_limbs_pointer as *mut u64 as *mut c_void,
            &mut receiver_norm_sign_pointer as *mut u64 as *mut c_void,
            &mut receiver_norm_limbs_pointer as *mut u64 as *mut c_void,
            &mut contact_real_sign_pointer as *mut u64 as *mut c_void,
            &mut contact_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut contact_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut contact_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut support_real_sign_pointer as *mut u64 as *mut c_void,
            &mut support_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut support_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut support_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_real_sign_pointer as *mut u64 as *mut c_void,
            &mut port_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut port_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut joint_real_sign_pointer as *mut u64 as *mut c_void,
            &mut joint_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut joint_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut joint_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_action_sign_pointer as *mut u64 as *mut c_void,
            &mut port_action_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_reflected_sign_pointer as *mut u64 as *mut c_void,
            &mut port_reflected_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_receiver_sign_pointer as *mut u64 as *mut c_void,
            &mut port_receiver_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_receiver_norm_sign_pointer as *mut u64 as *mut c_void,
            &mut port_receiver_norm_limbs_pointer as *mut u64 as *mut c_void,
            &mut support_count_wire as *mut u32 as *mut c_void,
            &mut port_count_wire as *mut u32 as *mut c_void,
            &mut family_count_wire as *mut u32 as *mut c_void,
            &mut receiver_count_wire as *mut u32 as *mut c_void,
            &mut overlap_limb_count_wire as *mut u32 as *mut c_void,
            &mut contact_limb_count_wire as *mut u32 as *mut c_void,
            &mut radiation_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_boundary_chain_radiation,
                    1,
                    1,
                    1,
                    1,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    radiation_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(gather_membrane_quadratic_moment_radiation)",
        )?;

        let mut compatibility_sign_pointer = compatibility_sign.pointer;
        let mut compatibility_limbs_pointer = compatibility_limbs.pointer;
        let mut phase_norm_limbs_pointer = phase_norm_limbs.pointer;
        let mut phase_locked_pointer = phase_locked.pointer;
        let mut phase_square_scratch_pointer = phase_square_scratch.pointer;
        let mut phase_left_cross_scratch_pointer = phase_left_cross_scratch.pointer;
        let mut phase_right_cross_scratch_pointer = phase_right_cross_scratch.pointer;
        let mut compatibility_limb_count_wire = compatibility_limb_count as u32;
        let mut norm_limb_count_wire = norm_limb_count as u32;
        let mut square_limb_count_wire = square_limb_count as u32;
        let mut cross_limb_count_wire = cross_limb_count as u32;
        let mut component_count_wire = component_count;
        let mut phase_component_arguments: [*mut c_void; 20] = [
            &mut family_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut family_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_action_sign_pointer as *mut u64 as *mut c_void,
            &mut port_action_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_reflected_sign_pointer as *mut u64 as *mut c_void,
            &mut port_reflected_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_receiver_sign_pointer as *mut u64 as *mut c_void,
            &mut port_receiver_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_receiver_norm_limbs_pointer as *mut u64 as *mut c_void,
            &mut compatibility_sign_pointer as *mut u64 as *mut c_void,
            &mut compatibility_limbs_pointer as *mut u64 as *mut c_void,
            &mut phase_norm_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_count_wire as *mut u32 as *mut c_void,
            &mut family_count_wire as *mut u32 as *mut c_void,
            &mut receiver_count_wire as *mut u32 as *mut c_void,
            &mut component_count_wire as *mut u32 as *mut c_void,
            &mut family_limb_count_wire as *mut u32 as *mut c_void,
            &mut overlap_limb_count_wire as *mut u32 as *mut c_void,
            &mut compatibility_limb_count_wire as *mut u32 as *mut c_void,
            &mut norm_limb_count_wire as *mut u32 as *mut c_void,
        ];
        let phase_component_grid = self.card.grid_for(component_population as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_boundary_phase_components,
                    phase_component_grid,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    phase_component_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(form_membrane_quadratic_moment_phase_components)",
        )?;
        if let Some(workspace) = factorized_relational_workspace.as_ref() {
            let mut relational_reduce = ptr::null_mut();
            driver(
                unsafe {
                    cuModuleGetFunction(
                        &mut relational_reduce,
                        self.card.module,
                        c"reduce_membrane_factorized_relational_moment_components".as_ptr(),
                    )
                },
                "cuModuleGetFunction(reduce_membrane_factorized_relational_moment_components)",
            )?;
            let mut partial_overlap_pointer = workspace.partial_overlap.pointer;
            let mut partial_target_norm_pointer = workspace.partial_target_norm.pointer;
            let mut relational_norm_pointer = workspace.relational_norm.pointer;
            let mut reduce_first_scratch_pointer = workspace.reduce_first_scratch.pointer;
            let mut reduce_second_scratch_pointer = workspace.reduce_second_scratch.pointer;
            let mut reduce_third_scratch_pointer = workspace.reduce_third_scratch.pointer;
            let mut relational_face_count_wire = response_population as u32;
            let mut relational_context_count_wire = context_count as u32;
            let mut relational_port_count_wire = port_population as u32;
            let mut relational_generator_count_wire = generator_count as u32;
            let mut relational_boundary_state_count_wire = resident_boundary
                .map(|boundary| boundary.boundary_states.len() as u32)
                .unwrap_or(1);
            let mut relational_reduce_boundary_states_pointer = boundary_states_device.pointer;
            let mut relational_component_wire = self
                .families
                .checked_add(self.receiver_count)
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let mut relational_limb_count_wire = workspace.limb_count as u32;
            let mut descend_relational_reduce_wire = u32::from(descend_boundary_state_receiver);
            let mut relational_reduce_arguments: [*mut c_void; 21] = [
                &mut partial_overlap_pointer as *mut u64 as *mut c_void,
                &mut partial_target_norm_pointer as *mut u64 as *mut c_void,
                &mut relational_norm_pointer as *mut u64 as *mut c_void,
                &mut context_state_present_pointer as *mut u64 as *mut c_void,
                &mut context_states_pointer as *mut u64 as *mut c_void,
                &mut relational_reduce_boundary_states_pointer as *mut u64 as *mut c_void,
                &mut compatibility_sign_pointer as *mut u64 as *mut c_void,
                &mut compatibility_limbs_pointer as *mut u64 as *mut c_void,
                &mut phase_norm_limbs_pointer as *mut u64 as *mut c_void,
                &mut reduce_first_scratch_pointer as *mut u64 as *mut c_void,
                &mut reduce_second_scratch_pointer as *mut u64 as *mut c_void,
                &mut reduce_third_scratch_pointer as *mut u64 as *mut c_void,
                &mut relational_face_count_wire as *mut u32 as *mut c_void,
                &mut relational_context_count_wire as *mut u32 as *mut c_void,
                &mut relational_port_count_wire as *mut u32 as *mut c_void,
                &mut relational_generator_count_wire as *mut u32 as *mut c_void,
                &mut relational_boundary_state_count_wire as *mut u32 as *mut c_void,
                &mut component_count_wire as *mut u32 as *mut c_void,
                &mut relational_component_wire as *mut u32 as *mut c_void,
                &mut relational_limb_count_wire as *mut u32 as *mut c_void,
                &mut descend_relational_reduce_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        relational_reduce,
                        self.card.grid_for(response_population as u64)?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        relational_reduce_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(reduce_membrane_factorized_relational_moment_components)",
            )?;
            factorized_relational_launches = factorized_relational_launches.saturating_add(1);
        } else if let Some(workspace) = completed_target_observer_workspace.as_ref() {
            let mut append_relational = ptr::null_mut();
            driver(
                unsafe {
                    cuModuleGetFunction(
                        &mut append_relational,
                        self.card.module,
                        c"append_membrane_completed_target_oriented_relational_component".as_ptr(),
                    )
                },
                "cuModuleGetFunction(append_membrane_completed_target_oriented_relational_component)",
            )?;
            let mut dot_real_sign_pointer = workspace.relational_dot_real_sign.pointer;
            let mut dot_real_limbs_pointer = workspace.relational_dot_real_limbs.pointer;
            let mut target_norm_pointer = workspace.target_norm_limbs.pointer;
            let mut relational_norm_pointer = workspace.relational_norm_limbs.pointer;
            let mut norm_product_pointer = workspace.norm_product_limbs.pointer;
            let mut first_scratch_pointer = workspace.first_scratch.pointer;
            let mut relational_face_count_wire = response_population as u32;
            let mut relational_component_wire = self
                .families
                .checked_add(self.receiver_count)
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let mut relational_limb_count_wire = workspace.limb_count as u32;
            let mut append_arguments: [*mut c_void; 13] = [
                &mut dot_real_sign_pointer as *mut u64 as *mut c_void,
                &mut dot_real_limbs_pointer as *mut u64 as *mut c_void,
                &mut target_norm_pointer as *mut u64 as *mut c_void,
                &mut relational_norm_pointer as *mut u64 as *mut c_void,
                &mut compatibility_sign_pointer as *mut u64 as *mut c_void,
                &mut compatibility_limbs_pointer as *mut u64 as *mut c_void,
                &mut phase_norm_limbs_pointer as *mut u64 as *mut c_void,
                &mut norm_product_pointer as *mut u64 as *mut c_void,
                &mut first_scratch_pointer as *mut u64 as *mut c_void,
                &mut relational_face_count_wire as *mut u32 as *mut c_void,
                &mut component_count_wire as *mut u32 as *mut c_void,
                &mut relational_component_wire as *mut u32 as *mut c_void,
                &mut relational_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        append_relational,
                        self.card.grid_for(response_population as u64)?,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        append_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(append_membrane_completed_target_oriented_relational_component)",
            )?;
            factorized_relational_launches = factorized_relational_launches.saturating_add(3);
        }
        let mut mark_productive = ptr::null_mut();
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut mark_productive,
                    self.card.module,
                    c"mark_membrane_productive_current_front".as_ptr(),
                )
            },
            "cuModuleGetFunction(mark_membrane_productive_current_front)",
        )?;
        let (
            mut productive_norm_pointer,
            mut productive_component_count_wire,
            mut productive_limb_count_wire,
        ) = if let Some(workspace) = factorized_relational_workspace.as_ref() {
            (
                workspace.reduce_first_scratch.pointer,
                1_u32,
                workspace.limb_count as u32,
            )
        } else if let Some(workspace) = completed_target_observer_workspace.as_ref() {
            (
                workspace.target_norm_limbs.pointer,
                1_u32,
                workspace.limb_count as u32,
            )
        } else {
            (
                phase_norm_limbs.pointer,
                component_count,
                norm_limb_count as u32,
            )
        };
        let mut productive_front_pointer = complete_native_successor_front.pointer;
        let mut productive_face_count_wire = response_population as u32;
        let mut productive_arguments: [*mut c_void; 5] = [
            &mut productive_norm_pointer as *mut u64 as *mut c_void,
            &mut productive_front_pointer as *mut u64 as *mut c_void,
            &mut productive_face_count_wire as *mut u32 as *mut c_void,
            &mut productive_component_count_wire as *mut u32 as *mut c_void,
            &mut productive_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    mark_productive,
                    self.card.grid_for(response_population as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    productive_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(mark_membrane_productive_current_front)",
        )?;
        let mut phase_select_direct = ptr::null_mut();
        // `selectedStateAddressedSum` applies the receiver-selected predicate before it forms the
        // target-state direct sum.  The complete component section below is that common receiver
        // family, so all productive addressed faces are commensurable here; target state remains
        // an output address and reconstruction coordinate, not a wall around alternative answers.
        // Partitioning this comparison by prospective target state retained one nondominated face
        // per successor and inverted the proved order of selection and target addressing.
        let relational_observer_present = factorized_relational_workspace.is_some()
            || completed_target_observer_workspace.is_some();
        let phase_select_name = if relational_observer_present {
            c"select_membrane_boundary_phase_front_complete_receiver_direct"
        } else {
            c"select_membrane_boundary_phase_front_direct"
        };
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut phase_select_direct,
                    self.card.module,
                    phase_select_name.as_ptr(),
                )
            },
            "cuModuleGetFunction(select_membrane_boundary_phase_front_target_state_direct)",
        )?;
        let phase_select_grid = self.card.grid_for(response_population as u64)?;
        let mut complete_native_face_population_wire = response_population as u32;
        if relational_observer_present {
            let (mut productive_target_norm_pointer, mut productive_limb_count_wire) =
                if let Some(workspace) = factorized_relational_workspace.as_ref() {
                    (
                        workspace.reduce_first_scratch.pointer,
                        workspace.limb_count as u32,
                    )
                } else {
                    let workspace = completed_target_observer_workspace
                        .as_ref()
                        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
                    (
                        workspace.target_norm_limbs.pointer,
                        workspace.limb_count as u32,
                    )
                };
            let mut phase_select_arguments: [*mut c_void; 15] = [
                &mut compatibility_sign_pointer as *mut u64 as *mut c_void,
                &mut compatibility_limbs_pointer as *mut u64 as *mut c_void,
                &mut phase_norm_limbs_pointer as *mut u64 as *mut c_void,
                &mut productive_target_norm_pointer as *mut u64 as *mut c_void,
                &mut phase_locked_pointer as *mut u64 as *mut c_void,
                &mut phase_square_scratch_pointer as *mut u64 as *mut c_void,
                &mut phase_left_cross_scratch_pointer as *mut u64 as *mut c_void,
                &mut phase_right_cross_scratch_pointer as *mut u64 as *mut c_void,
                &mut complete_native_face_population_wire as *mut u32 as *mut c_void,
                &mut component_count_wire as *mut u32 as *mut c_void,
                &mut compatibility_limb_count_wire as *mut u32 as *mut c_void,
                &mut norm_limb_count_wire as *mut u32 as *mut c_void,
                &mut productive_limb_count_wire as *mut u32 as *mut c_void,
                &mut square_limb_count_wire as *mut u32 as *mut c_void,
                &mut cross_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        phase_select_direct,
                        phase_select_grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        phase_select_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(select_membrane_boundary_phase_front_complete_receiver_direct)",
            )?;
        } else {
            let mut one_complete_receiver_chart_wire = 1_u32;
            let mut phase_select_arguments: [*mut c_void; 14] = [
                &mut compatibility_sign_pointer as *mut u64 as *mut c_void,
                &mut compatibility_limbs_pointer as *mut u64 as *mut c_void,
                &mut phase_norm_limbs_pointer as *mut u64 as *mut c_void,
                &mut phase_locked_pointer as *mut u64 as *mut c_void,
                &mut phase_square_scratch_pointer as *mut u64 as *mut c_void,
                &mut phase_left_cross_scratch_pointer as *mut u64 as *mut c_void,
                &mut phase_right_cross_scratch_pointer as *mut u64 as *mut c_void,
                &mut complete_native_face_population_wire as *mut u32 as *mut c_void,
                &mut one_complete_receiver_chart_wire as *mut u32 as *mut c_void,
                &mut component_count_wire as *mut u32 as *mut c_void,
                &mut compatibility_limb_count_wire as *mut u32 as *mut c_void,
                &mut norm_limb_count_wire as *mut u32 as *mut c_void,
                &mut square_limb_count_wire as *mut u32 as *mut c_void,
                &mut cross_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        phase_select_direct,
                        phase_select_grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        phase_select_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(select_membrane_boundary_phase_front_direct)",
            )?;
        }

        let mut incoming_real_sign_pointer = incoming_real_sign_device.pointer;
        let mut incoming_real_limbs_pointer = incoming_real_limbs_device.pointer;
        let mut incoming_imaginary_sign_pointer = incoming_imaginary_sign_device.pointer;
        let mut incoming_imaginary_limbs_pointer = incoming_imaginary_limbs_device.pointer;
        let mut situated_pairing_sign_pointer = situated_pairing_sign.pointer;
        let mut situated_pairing_limbs_pointer = situated_pairing_limbs.pointer;
        let mut situated_pairing_imaginary_scratch_pointer =
            situated_pairing_imaginary_scratch.pointer;
        let mut situated_pairing_front_pointer = situated_pairing_front.pointer;
        let mut incoming_limb_count_wire = stored_limb_count as u32;
        let mut situated_pairing_limb_count_wire = situated_pairing_limb_count as u32;
        let mut situated_pairing_arguments: [*mut c_void; 16] = [
            &mut port_real_sign_pointer as *mut u64 as *mut c_void,
            &mut port_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut port_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut port_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut incoming_real_sign_pointer as *mut u64 as *mut c_void,
            &mut incoming_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut incoming_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut incoming_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut phase_locked_pointer as *mut u64 as *mut c_void,
            &mut situated_pairing_sign_pointer as *mut u64 as *mut c_void,
            &mut situated_pairing_limbs_pointer as *mut u64 as *mut c_void,
            &mut situated_pairing_imaginary_scratch_pointer as *mut u64 as *mut c_void,
            &mut port_count_wire as *mut u32 as *mut c_void,
            &mut radiation_limb_count_wire as *mut u32 as *mut c_void,
            &mut incoming_limb_count_wire as *mut u32 as *mut c_void,
            &mut situated_pairing_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_situated_output_pairing,
                    phase_select_grid,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    situated_pairing_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(form_membrane_situated_output_pairing)",
        )?;
        let mut situated_select_direct = ptr::null_mut();
        // The native phase section retains its addressed target-state direct sum, but the
        // presented exterior current is precisely the receiver which makes those otherwise
        // incomparable alternatives commensurable: every `Re(conj(J) R_face)` occupies the same
        // signed quantity line.  Comparing that returned line separately inside each prospective
        // successor state would preserve one winner *per answer state* and therefore prevent the
        // receiver from ever selecting an answer.  Keep every native phase face and its target
        // address as reconstruction testimony, then take the maximum fibre of this one declared
        // exterior receiver over the complete native population.
        let situated_select_name = if relational_observer_present {
            c"select_membrane_situated_relational_then_output_front_direct"
        } else {
            c"select_membrane_situated_output_pairing_front_direct"
        };
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut situated_select_direct,
                    self.card.module,
                    situated_select_name.as_ptr(),
                )
            },
            "cuModuleGetFunction(select_membrane_situated_output_pairing_front_target_state_direct)",
        )?;
        let mut complete_response_population_wire = response_population as u32;
        if relational_observer_present {
            let mut relational_component_wire = self
                .families
                .checked_add(self.receiver_count)
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            let mut situated_select_arguments: [*mut c_void; 18] = [
                &mut phase_locked_pointer as *mut u64 as *mut c_void,
                &mut compatibility_sign_pointer as *mut u64 as *mut c_void,
                &mut compatibility_limbs_pointer as *mut u64 as *mut c_void,
                &mut phase_norm_limbs_pointer as *mut u64 as *mut c_void,
                &mut situated_pairing_sign_pointer as *mut u64 as *mut c_void,
                &mut situated_pairing_limbs_pointer as *mut u64 as *mut c_void,
                &mut situated_pairing_front_pointer as *mut u64 as *mut c_void,
                &mut phase_square_scratch_pointer as *mut u64 as *mut c_void,
                &mut phase_left_cross_scratch_pointer as *mut u64 as *mut c_void,
                &mut phase_right_cross_scratch_pointer as *mut u64 as *mut c_void,
                &mut complete_response_population_wire as *mut u32 as *mut c_void,
                &mut component_count_wire as *mut u32 as *mut c_void,
                &mut relational_component_wire as *mut u32 as *mut c_void,
                &mut compatibility_limb_count_wire as *mut u32 as *mut c_void,
                &mut norm_limb_count_wire as *mut u32 as *mut c_void,
                &mut situated_pairing_limb_count_wire as *mut u32 as *mut c_void,
                &mut square_limb_count_wire as *mut u32 as *mut c_void,
                &mut cross_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        situated_select_direct,
                        phase_select_grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        situated_select_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(select_membrane_situated_relational_then_output_front_direct)",
            )?;
        } else {
            let mut one_exterior_receiver_chart_wire = 1_u32;
            let mut situated_select_arguments: [*mut c_void; 7] = [
                &mut phase_locked_pointer as *mut u64 as *mut c_void,
                &mut situated_pairing_sign_pointer as *mut u64 as *mut c_void,
                &mut situated_pairing_limbs_pointer as *mut u64 as *mut c_void,
                &mut situated_pairing_front_pointer as *mut u64 as *mut c_void,
                &mut complete_response_population_wire as *mut u32 as *mut c_void,
                &mut one_exterior_receiver_chart_wire as *mut u32 as *mut c_void,
                &mut situated_pairing_limb_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        situated_select_direct,
                        phase_select_grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        situated_select_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(select_membrane_situated_output_pairing_front_direct)",
            )?;
        }
        let mut stored_real_sign_pointer = stored_real_sign.pointer;
        let mut stored_real_limbs_pointer = stored_real_limbs.pointer;
        let mut stored_imaginary_sign_pointer = stored_imaginary_sign.pointer;
        let mut stored_imaginary_limbs_pointer = stored_imaginary_limbs.pointer;
        let mut balance_scratch_pointer = balance_scratch.pointer;
        let mut joint_scale_wire = joint_scale;
        let mut stored_limb_count_wire = stored_limb_count as u32;
        let mut balance_arguments: [*mut c_void; 16] = [
            &mut joint_real_sign_pointer as *mut u64 as *mut c_void,
            &mut joint_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut joint_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut joint_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut incoming_real_sign_pointer as *mut u64 as *mut c_void,
            &mut incoming_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut incoming_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut incoming_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut joint_scale_wire as *mut u64 as *mut c_void,
            &mut stored_real_sign_pointer as *mut u64 as *mut c_void,
            &mut stored_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut stored_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut stored_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut balance_scratch_pointer as *mut u64 as *mut c_void,
            &mut radiation_limb_count_wire as *mut u32 as *mut c_void,
            &mut stored_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_boundary_chain_balance,
                    1,
                    1,
                    1,
                    1,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    balance_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(balance_membrane_quadratic_moment_chain)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        if cuda_profile {
            eprintln!(
                "mem6-cuda through_terminal_sync_ms={}",
                resident_began.elapsed().as_millis(),
            );
        }
        let moment_transport_launches = if post_target_observer {
            // The completed target is observed through the sparse inverse-incidence
            // passage above.  Re-running either moment transport would enact a
            // second state transition instead of observing the committed one.
            0_u64
        } else if materialize_moment_field {
            2_u64
        } else {
            u64::try_from(context_chunk_count)
                .ok()
                .and_then(|contexts| {
                    contexts.checked_mul(u64::try_from(incidence_chunk_count).ok()?)
                })
                .and_then(|covers| covers.checked_mul(2))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
        };
        let launches = 6_u64
            .checked_add(moment_transport_launches)
            .and_then(|count| count.checked_add(resident_gather_launches))
            .and_then(|count| count.checked_add(factorized_relational_launches))
            .and_then(|count| count.checked_add(1))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        self.card.launches += launches;

        let restriction_population = if post_target_observer {
            // This receipt counts the retained caused incidences which carry the
            // completed target into its receiver chart.  It is not an outgoing
            // boundary-atlas population and therefore requires no fabricated
            // identity restriction at the target.
            completed_step
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?
                .selected_slot_count
        } else if resident_rectangular_restrictions {
            let mut present = vec![0_u8; restriction_count];
            restriction_present.read(&mut present)?;
            if trace_configuration().holonics_uar2_trace {
                eprintln!(
                    "post-target-observer-restrictions present={present:?} boundary-state-count={}",
                    resident_boundary
                        .expect("the resident presentation was established")
                        .boundary_states
                        .len(),
                );
            }
            if present.iter().any(|value| *value > 1)
                || present
                    .chunks_exact(
                        resident_boundary
                            .expect("the resident presentation was established")
                            .boundary_states
                            .len(),
                    )
                    .any(|port| !port.iter().any(|value| *value != 0))
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            present.iter().filter(|value| **value != 0).count()
        } else {
            restriction_count
        };

        let mut moment_host = vec![0_u32; moment_population * moment_limb_count];
        let mut action_sign_host = vec![0_u8; family_population];
        let mut action_limbs_host = vec![0_u32; family_population * overlap_limb_count];
        let mut reflected_sign_host = vec![0_u8; family_population];
        let mut reflected_limbs_host = vec![0_u32; family_population * overlap_limb_count];
        let mut receiver_sign_host = vec![0_u8; receiver_population];
        let mut receiver_limbs_host = vec![0_u32; receiver_population * overlap_limb_count];
        let mut receiver_norm_sign_host = vec![0_u8; receiver_population];
        let mut receiver_norm_limbs_host = vec![0_u32; receiver_population * overlap_limb_count];
        moment.read(&mut moment_host)?;
        action_sign.read(&mut action_sign_host)?;
        action_limbs.read(&mut action_limbs_host)?;
        reflected_sign.read(&mut reflected_sign_host)?;
        reflected_limbs.read(&mut reflected_limbs_host)?;
        receiver_sign.read(&mut receiver_sign_host)?;
        receiver_limbs.read(&mut receiver_limbs_host)?;
        receiver_norm_sign.read(&mut receiver_norm_sign_host)?;
        receiver_norm_limbs.read(&mut receiver_norm_limbs_host)?;
        let mut port_receiver_norm_sign_host = vec![0_u8; receiver_population];
        port_receiver_norm_sign.read(&mut port_receiver_norm_sign_host)?;
        if trace_configuration().holonics_uar2_trace {
            eprintln!(
                "post-target-observer-sign-ranges action={:?} reflected={:?} receiver={:?} receiver-norm={:?} port-receiver-norm={:?}",
                action_sign_host.iter().copied().max(),
                reflected_sign_host.iter().copied().max(),
                receiver_sign_host.iter().copied().max(),
                receiver_norm_sign_host.iter().copied().max(),
                port_receiver_norm_sign_host.iter().copied().max(),
            );
        }
        if action_sign_host.iter().any(|sign| *sign > 2)
            || reflected_sign_host.iter().any(|sign| *sign > 2)
            || receiver_sign_host.iter().any(|sign| *sign > 2)
            || receiver_norm_sign_host.iter().any(|sign| *sign > 1)
            || port_receiver_norm_sign_host.iter().any(|sign| *sign > 1)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut port_real_sign_host = vec![0_u8; response_population];
        let mut port_real_limbs_host = vec![0_u32; response_population * radiation_limb_count];
        let mut port_imaginary_sign_host = vec![0_u8; response_population];
        let mut port_imaginary_limbs_host = vec![0_u32; response_population * radiation_limb_count];
        let mut phase_locked_host = vec![0_u8; response_population];
        let mut situated_pairing_sign_host = vec![0_u8; response_population];
        let mut situated_pairing_limbs_host =
            vec![0_u32; response_population * situated_pairing_limb_count];
        let mut situated_pairing_front_host = vec![0_u8; response_population];
        let mut complete_native_successor_front_host = vec![0_u8; response_population];
        let mut joint_real_sign_host = [0_u8; 1];
        let mut joint_real_limbs_host = vec![0_u32; radiation_limb_count];
        let mut joint_imaginary_sign_host = [0_u8; 1];
        let mut joint_imaginary_limbs_host = vec![0_u32; radiation_limb_count];
        let mut stored_real_sign_host = [0_u8; 1];
        let mut stored_real_limbs_host = vec![0_u32; stored_limb_count];
        let mut stored_imaginary_sign_host = [0_u8; 1];
        let mut stored_imaginary_limbs_host = vec![0_u32; stored_limb_count];
        port_real_sign.read(&mut port_real_sign_host)?;
        port_real_limbs.read(&mut port_real_limbs_host)?;
        port_imaginary_sign.read(&mut port_imaginary_sign_host)?;
        port_imaginary_limbs.read(&mut port_imaginary_limbs_host)?;
        phase_locked.read(&mut phase_locked_host)?;
        situated_pairing_sign.read(&mut situated_pairing_sign_host)?;
        situated_pairing_limbs.read(&mut situated_pairing_limbs_host)?;
        situated_pairing_front.read(&mut situated_pairing_front_host)?;
        complete_native_successor_front.read(&mut complete_native_successor_front_host)?;
        joint_real_sign.read(&mut joint_real_sign_host)?;
        joint_real_limbs.read(&mut joint_real_limbs_host)?;
        joint_imaginary_sign.read(&mut joint_imaginary_sign_host)?;
        joint_imaginary_limbs.read(&mut joint_imaginary_limbs_host)?;
        stored_real_sign.read(&mut stored_real_sign_host)?;
        stored_real_limbs.read(&mut stored_real_limbs_host)?;
        stored_imaginary_sign.read(&mut stored_imaginary_sign_host)?;
        stored_imaginary_limbs.read(&mut stored_imaginary_limbs_host)?;
        let factorized_relational_host =
            if let Some(workspace) = factorized_relational_workspace.as_ref() {
                let mut compatibility_sign_host = vec![0_u8; component_population];
                let mut compatibility_limbs_host =
                    vec![0_u32; component_population * compatibility_limb_count];
                let mut target_norm_host = vec![0_u32; response_population * workspace.limb_count];
                let mut current_norm_host = vec![0_u32; response_population * workspace.limb_count];
                let mut norm_product_host = vec![0_u32; response_population * workspace.limb_count];
                let mut obstruction_host = [0_u32; 1];
                compatibility_sign.read(&mut compatibility_sign_host)?;
                compatibility_limbs.read(&mut compatibility_limbs_host)?;
                workspace.reduce_first_scratch.read(&mut target_norm_host)?;
                workspace.relational_norm.read(&mut current_norm_host)?;
                workspace
                    .reduce_second_scratch
                    .read(&mut norm_product_host)?;
                workspace.obstruction.read(&mut obstruction_host)?;
                Some((
                    compatibility_sign_host,
                    compatibility_limbs_host,
                    target_norm_host,
                    current_norm_host,
                    norm_product_host,
                    obstruction_host[0],
                ))
            } else if let Some(workspace) = completed_target_observer_workspace.as_ref() {
                let mut compatibility_sign_host = vec![0_u8; component_population];
                let mut compatibility_limbs_host =
                    vec![0_u32; component_population * compatibility_limb_count];
                let mut target_norm_host = vec![0_u32; response_population * workspace.limb_count];
                let mut current_norm_host = vec![0_u32; response_population * workspace.limb_count];
                let mut norm_product_host = vec![0_u32; response_population * workspace.limb_count];
                let mut obstruction_host = [0_u32; 1];
                compatibility_sign.read(&mut compatibility_sign_host)?;
                compatibility_limbs.read(&mut compatibility_limbs_host)?;
                workspace.target_norm_limbs.read(&mut target_norm_host)?;
                workspace
                    .relational_norm_limbs
                    .read(&mut current_norm_host)?;
                workspace.norm_product_limbs.read(&mut norm_product_host)?;
                workspace.obstruction.read(&mut obstruction_host)?;
                Some((
                    compatibility_sign_host,
                    compatibility_limbs_host,
                    target_norm_host,
                    current_norm_host,
                    norm_product_host,
                    obstruction_host[0],
                ))
            } else {
                None
            };
        let completed_oriented_relational_host =
            if let Some(workspace) = completed_target_observer_workspace.as_ref() {
                let mut real_signs = vec![0_u8; response_population];
                let mut real_limbs = vec![0_u32; response_population * workspace.limb_count];
                let mut imaginary_signs = vec![0_u8; response_population];
                let mut imaginary_limbs = vec![0_u32; response_population * workspace.limb_count];
                workspace.relational_dot_real_sign.read(&mut real_signs)?;
                workspace.relational_dot_real_limbs.read(&mut real_limbs)?;
                workspace
                    .relational_dot_imaginary_sign
                    .read(&mut imaginary_signs)?;
                workspace
                    .relational_dot_imaginary_limbs
                    .read(&mut imaginary_limbs)?;
                Some((
                    real_signs,
                    real_limbs,
                    imaginary_signs,
                    imaginary_limbs,
                    workspace.limb_count,
                ))
            } else {
                None
            };
        let phase_locked_port_population =
            phase_locked_host.iter().filter(|held| **held != 0).count();
        let situated_receiver_front_ports = situated_pairing_front_host
            .iter()
            .enumerate()
            .filter_map(|(port, held)| (*held != 0).then_some(port as u32))
            .collect::<Vec<_>>();
        if trace_configuration().holonics_uar2_trace {
            let complete_native_productive = complete_native_successor_front_host
                .iter()
                .filter(|held| **held != 0)
                .count();
            let phase_locked = phase_locked_host.iter().filter(|held| **held != 0).count();
            let invalid_relational = factorized_relational_host.as_ref().map(
                |(signs, _, target_norms, current_norms, products, obstruction)| {
                    (
                        *obstruction,
                        signs.iter().filter(|sign| **sign != 0).count(),
                        target_norms.iter().filter(|limb| **limb != 0).count(),
                        current_norms.iter().filter(|limb| **limb != 0).count(),
                        products.iter().filter(|limb| **limb != 0).count(),
                    )
                },
            );
            eprintln!(
                "post-target-observer-front native-productive={} phase-locked={} situated={} relational={invalid_relational:?}",
                complete_native_productive,
                phase_locked,
                situated_receiver_front_ports.len(),
            );
        }
        if phase_locked_port_population == 0
            || phase_locked_host.iter().any(|held| *held > 1)
            || situated_pairing_sign_host.iter().any(|sign| *sign > 2)
            || situated_pairing_front_host.iter().any(|held| *held > 1)
            || complete_native_successor_front_host
                .iter()
                .any(|held| *held > 1)
            || complete_native_successor_front_host
                .iter()
                .all(|held| *held == 0)
            || situated_receiver_front_ports.is_empty()
            || situated_pairing_front_host
                .iter()
                .zip(&phase_locked_host)
                .any(|(situated, native)| *situated != 0 && *native == 0)
            || factorized_relational_host.as_ref().is_some_and(
                |(signs, _, _, _, _, obstruction)| {
                    *obstruction != 0 || signs.iter().any(|sign| *sign > 2)
                },
            )
            || completed_oriented_relational_host.as_ref().is_some_and(
                |(real_signs, _, imaginary_signs, _, _)| {
                    real_signs.iter().any(|sign| *sign > 2)
                        || imaginary_signs.iter().any(|sign| *sign > 2)
                },
            )
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let decode_integer = |sign: u8, limbs: &[u32]| -> Result<BigInt, CudaRefineError> {
            let value = decode_component(sign, limbs, &BigInt::one())?;
            Ok(value.numer().clone())
        };
        let situated_receiver_pairing_coordinates = (0..response_population)
            .map(|port| {
                let begin = port * situated_pairing_limb_count;
                decode_integer(
                    situated_pairing_sign_host[port],
                    &situated_pairing_limbs_host[begin..begin + situated_pairing_limb_count],
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let (
            receiver_relational_coordinates,
            relational_target_self_pairings,
            relational_current_self_pairings,
            relational_squared_norm_products,
        ) = if let Some((
            compatibility_sign_host,
            compatibility_limbs_host,
            target_norm_host,
            current_norm_host,
            norm_product_host,
            _,
        )) = factorized_relational_host.as_ref()
        {
            let relational_component =
                self.families
                    .checked_add(self.receiver_count)
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)? as usize;
            let mut coordinates = Vec::with_capacity(response_population);
            let mut target_norms = Vec::with_capacity(response_population);
            let mut current_norms = Vec::with_capacity(response_population);
            let mut norm_products = Vec::with_capacity(response_population);
            for face in 0..response_population {
                let component = face * component_count as usize + relational_component;
                let component_begin = component * compatibility_limb_count;
                coordinates.push(decode_integer(
                    compatibility_sign_host[component],
                    &compatibility_limbs_host
                        [component_begin..component_begin + compatibility_limb_count],
                )?);
                let begin = face * compatibility_limb_count;
                let target = BigUint::new(
                    target_norm_host[begin..begin + compatibility_limb_count].to_vec(),
                );
                let current = BigUint::new(
                    current_norm_host[begin..begin + compatibility_limb_count].to_vec(),
                );
                let product = BigUint::new(
                    norm_product_host[begin..begin + compatibility_limb_count].to_vec(),
                );
                if &target * &current != product {
                    if trace_configuration().holonics_uar2_trace {
                        eprintln!(
                            "post-target-observer-obstruction=relational-norm-product face={face}"
                        );
                    }
                    return Err(CudaRefineError::MembraneInteriorWordShape);
                }
                target_norms.push(target);
                current_norms.push(current);
                norm_products.push(product);
            }
            (coordinates, target_norms, current_norms, norm_products)
        } else {
            (Vec::new(), Vec::new(), Vec::new(), Vec::new())
        };
        let (
            relational_oriented_real_coordinates,
            relational_oriented_imaginary_coordinates,
            relational_modulus_squared_coordinates,
        ) = if let Some((real_signs, real_limbs, imaginary_signs, imaginary_limbs, limb_count)) =
            completed_oriented_relational_host.as_ref()
        {
            let mut real = Vec::with_capacity(response_population);
            let mut imaginary = Vec::with_capacity(response_population);
            let mut modulus_squared = Vec::with_capacity(response_population);
            for face in 0..response_population {
                let begin = face * *limb_count;
                let real_coordinate =
                    decode_integer(real_signs[face], &real_limbs[begin..begin + *limb_count])?;
                let imaginary_coordinate = decode_integer(
                    imaginary_signs[face],
                    &imaginary_limbs[begin..begin + *limb_count],
                )?;
                if receiver_relational_coordinates.get(face) != Some(&real_coordinate) {
                    if trace_configuration().holonics_uar2_trace {
                        eprintln!(
                            "post-target-observer-obstruction=oriented-real-projection face={face}"
                        );
                    }
                    return Err(CudaRefineError::MembraneInteriorWordShape);
                }
                modulus_squared.push(
                    real_coordinate.magnitude() * real_coordinate.magnitude()
                        + imaginary_coordinate.magnitude() * imaginary_coordinate.magnitude(),
                );
                real.push(real_coordinate);
                imaginary.push(imaginary_coordinate);
            }
            (real, imaginary, modulus_squared)
        } else {
            (
                Vec::new(),
                Vec::new(),
                receiver_relational_coordinates
                    .iter()
                    .map(|coordinate| coordinate.magnitude().clone())
                    .collect::<Vec<_>>(),
            )
        };
        let mut ports = Vec::with_capacity(response_population);
        for port in 0..response_population {
            let port_moment = if materialize_moment_field {
                let moment_begin = port * factors * factors * moment_limb_count;
                moment_host[moment_begin..moment_begin + factors * factors * moment_limb_count]
                    .chunks_exact(moment_limb_count)
                    .map(|limbs| BigUint::new(limbs.to_vec()))
                    .collect::<Vec<_>>()
            } else {
                Vec::new()
            };
            let family_begin = port * self.families as usize;
            let receiver_begin = port * self.receiver_count as usize;
            let decode_family = |signs: &[u8], limbs: &[u32]| {
                (family_begin..family_begin + self.families as usize)
                    .map(|at| {
                        let begin = at * overlap_limb_count;
                        decode_integer(signs[at], &limbs[begin..begin + overlap_limb_count])
                    })
                    .collect::<Result<Vec<_>, _>>()
            };
            ports.push(ResidentQuadraticMomentPortReturn {
                port: port as u32,
                moment: port_moment,
                reflected_family_overlaps: decode_family(
                    &reflected_sign_host,
                    &reflected_limbs_host,
                )?,
                family_overlaps: decode_family(&action_sign_host, &action_limbs_host)?,
                receiver_overlaps: (receiver_begin..receiver_begin + self.receiver_count as usize)
                    .map(|at| {
                        let begin = at * overlap_limb_count;
                        decode_integer(
                            receiver_sign_host[at],
                            &receiver_limbs_host[begin..begin + overlap_limb_count],
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                receiver_action_norms: (receiver_begin
                    ..receiver_begin + self.receiver_count as usize)
                    .map(|at| {
                        let begin = at * overlap_limb_count;
                        BigUint::new(
                            receiver_norm_limbs_host[begin..begin + overlap_limb_count].to_vec(),
                        )
                    })
                    .collect(),
            });
        }
        let decode_current = |real_sign: u8,
                              real_limbs: &[u32],
                              imaginary_sign: u8,
                              imaginary_limbs: &[u32],
                              denominator: &BigInt|
         -> Result<ExactComplexWaveCurrent, CudaRefineError> {
            Ok(ExactComplexWaveCurrent::new(
                decode_component(real_sign, real_limbs, denominator)?,
                decode_component(imaginary_sign, imaginary_limbs, denominator)?,
            ))
        };
        let port_returns = (0..response_population)
            .map(|port| {
                let begin = port * radiation_limb_count;
                let end = begin + radiation_limb_count;
                let returned_response = decode_current(
                    port_real_sign_host[port],
                    &port_real_limbs_host[begin..end],
                    port_imaginary_sign_host[port],
                    &port_imaginary_limbs_host[begin..end],
                    &self.family_common_denominator,
                )?;
                Ok(ResidentBoundaryChainPortReturn {
                    port: port as u32,
                    lies_in_joint_port_kernel: returned_response.is_zero(),
                    lies_in_receiver_phase_front: phase_locked_host[port] != 0,
                    returned_response,
                })
            })
            .collect::<Result<Vec<_>, CudaRefineError>>()?;
        let total_returned_current = decode_current(
            joint_real_sign_host[0],
            &joint_real_limbs_host,
            joint_imaginary_sign_host[0],
            &joint_imaginary_limbs_host,
            &self.family_common_denominator,
        )?;
        let stored_difference = decode_current(
            stored_real_sign_host[0],
            &stored_real_limbs_host,
            stored_imaginary_sign_host[0],
            &stored_imaginary_limbs_host,
            &balance_denominator,
        )?;
        let local_balance_closes =
            stored_difference.add(&total_returned_current) == *entering_current;
        if !local_balance_closes {
            if trace_configuration().holonics_uar2_trace {
                eprintln!("post-target-observer-obstruction=local-current-balance");
            }
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let situated_face_ports = (0..response_population)
            .map(|face| {
                if materialize_moment_field {
                    face as u32
                } else {
                    ((face % local_response_population) / generator_count) as u32
                }
            })
            .collect::<Vec<_>>();
        let situated_face_generators = (0..response_population)
            .map(|face| {
                if materialize_moment_field {
                    0
                } else {
                    ((face % local_response_population) % generator_count) as u32
                }
            })
            .collect::<Vec<_>>();
        let situated_face_source_states = if descend_boundary_state_receiver {
            vec![u32::MAX; response_population]
        } else if let Some(boundary) = resident_boundary {
            (0..response_population)
                .map(|face| boundary.boundary_states[face / local_response_population])
                .collect::<Vec<_>>()
        } else {
            vec![u32::MAX; response_population]
        };
        let situated_receiver_front_ports = situated_receiver_front_ports
            .iter()
            .map(|face| situated_face_ports[*face as usize])
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let situated_receiver_pairing = ResidentSituatedReceiverPairingReturn {
            receiver_chart: if completed_target_observer_workspace.is_some() {
                "completed-target-sparse-incidence-relational-and-exterior-current".to_owned()
            } else if factorized_relational_workspace.is_some() {
                "state-addressed-factorized-relational-and-exterior-current".to_owned()
            } else {
                "exterior-complex-current".to_owned()
            },
            coordinate_denominator: &self.family_common_denominator * &balance_denominator,
            coordinates: situated_receiver_pairing_coordinates,
            current_self_pairings: Vec::new(),
            ingress_self_pairings: Vec::new(),
            squared_norm_products: Vec::new(),
            relational_oriented_real_coordinates,
            relational_oriented_imaginary_coordinates,
            relational_modulus_squared_coordinates,
            relational_target_self_pairings,
            relational_current_self_pairings,
            relational_squared_norm_products,
            face_source_states: situated_face_source_states,
            face_ports: situated_face_ports,
            face_generators: situated_face_generators,
            front_faces: situated_pairing_front_host
                .iter()
                .enumerate()
                .filter_map(|(face, held)| (*held != 0).then_some(face as u32))
                .collect(),
            front_is_unique: situated_pairing_front_host
                .iter()
                .filter(|held| **held != 0)
                .count()
                == 1,
            front_ports: situated_receiver_front_ports,
            native_phase_front_faces: phase_locked_host
                .iter()
                .enumerate()
                .filter_map(|(face, held)| (*held != 0).then_some(face as u32))
                .collect(),
            projective_candidate_faces: Vec::new(),
            projective_interval_limb_count: 0,
            projective_interval_obstruction_reopened_front: false,
            complete_native_phase_front_retained: true,
            ingress_moment_reconstruction_fibre_retained: relational_observer_present,
        };
        let direct_restriction_ingress = if resident_rectangular_restrictions {
            0
        } else {
            std::mem::size_of_val(&restriction_ports[..])
                .checked_add(std::mem::size_of_val(&port_restriction_offsets[..]))
                .and_then(|octets| {
                    octets.checked_add(std::mem::size_of_val(&restriction_current_limbs[..]))
                })
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?
        };
        let resident_aperture_ingress = if let Some(boundary) = resident_boundary {
            std::mem::size_of_val(&boundary.boundary_states[..])
                .checked_add(std::mem::size_of_val(&boundary.universal_ports[..]))
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?
        } else {
            0
        };
        let materialized_chart_ingress = if materialize_moment_field {
            std::mem::size_of_val(&active_factors[..])
                .checked_add(std::mem::size_of_val(&active_generator_targets[..]))
                .and_then(|octets| {
                    octets.checked_add(std::mem::size_of_val(&active_generator_local_targets[..]))
                })
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?
        } else {
            0
        };
        let successor_host_ingress_octets = [
            std::mem::size_of_val(&context_current_limbs[..]),
            std::mem::size_of_val(&context_weight_limbs[..]),
            direct_restriction_ingress,
            resident_aperture_ingress,
            materialized_chart_ingress,
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let relational_host_egress_octets = factorized_relational_host
            .as_ref()
            .and_then(
                |(signs, coordinates, target_norms, current_norms, norm_products, _)| {
                    std::mem::size_of_val(&signs[..])
                        .checked_add(std::mem::size_of_val(&coordinates[..]))
                        .and_then(|held| held.checked_add(std::mem::size_of_val(&target_norms[..])))
                        .and_then(|held| {
                            held.checked_add(std::mem::size_of_val(&current_norms[..]))
                        })
                        .and_then(|held| {
                            held.checked_add(std::mem::size_of_val(&norm_products[..]))
                        })
                        .and_then(|held| held.checked_add(std::mem::size_of::<u32>()))
                },
            )
            .unwrap_or(0)
            .checked_add(
                completed_oriented_relational_host
                    .as_ref()
                    .and_then(
                        |(
                            real_signs,
                            real_coordinates,
                            imaginary_signs,
                            imaginary_coordinates,
                            _,
                        )| {
                            std::mem::size_of_val(&real_signs[..])
                                .checked_add(std::mem::size_of_val(&real_coordinates[..]))
                                .and_then(|held| {
                                    held.checked_add(std::mem::size_of_val(&imaginary_signs[..]))
                                })
                                .and_then(|held| {
                                    held.checked_add(std::mem::size_of_val(
                                        &imaginary_coordinates[..],
                                    ))
                                })
                        },
                    )
                    .unwrap_or(0),
            )
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let successor_host_egress_octets = std::mem::size_of_val(&moment_host[..])
            .checked_add(std::mem::size_of_val(&action_sign_host[..]))
            .and_then(|octets| octets.checked_add(std::mem::size_of_val(&action_limbs_host[..])))
            .and_then(|octets| octets.checked_add(std::mem::size_of_val(&reflected_sign_host[..])))
            .and_then(|octets| octets.checked_add(std::mem::size_of_val(&reflected_limbs_host[..])))
            .and_then(|octets| octets.checked_add(std::mem::size_of_val(&receiver_sign_host[..])))
            .and_then(|octets| octets.checked_add(std::mem::size_of_val(&receiver_limbs_host[..])))
            .and_then(|octets| {
                octets.checked_add(std::mem::size_of_val(&receiver_norm_sign_host[..]))
            })
            .and_then(|octets| {
                octets.checked_add(std::mem::size_of_val(&receiver_norm_limbs_host[..]))
            })
            .and_then(|octets| {
                octets.checked_add(std::mem::size_of_val(&situated_pairing_sign_host[..]))
            })
            .and_then(|octets| {
                octets.checked_add(std::mem::size_of_val(&situated_pairing_limbs_host[..]))
            })
            .and_then(|octets| {
                octets.checked_add(std::mem::size_of_val(&situated_pairing_front_host[..]))
            })
            .and_then(|octets| {
                octets.checked_add(
                    if resident_rectangular_restrictions && !post_target_observer {
                        restriction_count
                    } else {
                        0
                    },
                )
            })
            .and_then(|octets| octets.checked_add(relational_host_egress_octets))
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            as u64;
        let dense_working_octets = octets(moment_population, moment_limb_count)?
            .checked_add(octets(moment_population, product_limb_count)? * 2)
            .and_then(|held| {
                held.checked_add(octets(moment_population, quadratic_limb_count).ok()?)
            })
            .and_then(|held| held.checked_add(octets(moment_population, moment_limb_count).ok()?))
            .and_then(|held| held.checked_add(octets(contraction_work, overlap_limb_count).ok()?))
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let factorized_working_octets = octets(contribution_work, product_limb_count)?
            .checked_mul(3)
            .and_then(|held| {
                held.checked_add(octets(contribution_work, quadratic_limb_count).ok()?)
            })
            .and_then(|held| held.checked_add(octets(contribution_work, moment_limb_count).ok()?))
            .and_then(|held| {
                held.checked_add(
                    octets(contribution_work, overlap_limb_count)
                        .ok()?
                        .checked_mul(5)?,
                )
            })
            .and_then(|held| held.checked_add(contribution_work.checked_mul(4)?))
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let phase_working_octets = octets(component_population, compatibility_limb_count)?
            .checked_add(octets(component_population, norm_limb_count)?)
            .and_then(|held| held.checked_add(component_population))
            .and_then(|held| held.checked_add(response_population))
            .and_then(|held| held.checked_add(response_population))
            .and_then(|held| held.checked_add(octets(response_population, square_limb_count).ok()?))
            .and_then(|held| {
                held.checked_add(
                    octets(response_population, cross_limb_count)
                        .ok()?
                        .checked_mul(2)?,
                )
            })
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let situated_pairing_working_octets = response_population
            .checked_add(octets(response_population, situated_pairing_limb_count)?)
            .and_then(|held| {
                held.checked_add(octets(response_population, situated_pairing_limb_count).ok()?)
            })
            .and_then(|held| held.checked_add(response_population))
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let relational_working_octets =
            if let Some(workspace) = factorized_relational_workspace.as_ref() {
                usize::try_from(workspace.resident_working_octets)
                    .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
            } else if let Some(workspace) = completed_target_observer_workspace.as_ref() {
                usize::try_from(workspace.resident_working_octets)
                    .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
            } else {
                0
            };
        let resident_working_octets = (if materialize_moment_field {
            dense_working_octets
        } else {
            factorized_working_octets
        })
        .checked_add(phase_working_octets)
        .and_then(|held| held.checked_add(situated_pairing_working_octets))
        .and_then(|held| {
            held.checked_add(
                octets(
                    legacy_restriction_allocation_count.saturating_mul(current_factor_population),
                    restriction_limb_count,
                )
                .ok()?,
            )
        })
        .and_then(|held| held.checked_add(legacy_restriction_allocation_count))
        .and_then(|held| {
            held.checked_add(
                legacy_restriction_allocation_count.checked_mul(std::mem::size_of::<u32>())?,
            )
        })
        .and_then(|held| held.checked_add(relational_working_octets))
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            as u64;
        if cuda_profile {
            eprintln!(
                "mem6-cuda before_buffer_release_ms={} resident_working_octets={}",
                resident_began.elapsed().as_millis(),
                resident_working_octets,
            );
        }
        // The phase/current word has crossed its terminal synchronization and all of its cold
        // receiver testimony has already been reconstructed above.  Release that occurrence-
        // local apparatus before founding the successor current.  Keeping these buffers alive
        // across the successor allocation falsely made two causal orders co-resident; at the
        // plural state front that occupied nearly the complete card even though the direct-sum
        // successor retains only state-matched incidences.
        drop(context_current);
        drop(context_weight);
        drop(context_state_present);
        drop(context_states);
        drop(restriction_port);
        drop(port_restriction_offset);
        drop(boundary_states_device);
        drop(universal_ports_device);
        drop(active_factor_chart);
        drop(generator_targets);
        drop(generator_local_targets);
        drop(moment);
        drop(left_scratch);
        drop(right_scratch);
        drop(quadratic_scratch);
        drop(term_scratch);
        drop(action_sign);
        drop(action_limbs);
        drop(reflected_sign);
        drop(reflected_limbs);
        drop(receiver_sign);
        drop(receiver_limbs);
        drop(receiver_norm_sign);
        drop(receiver_norm_limbs);
        drop(contact_real_sign);
        drop(contact_real_limbs);
        drop(contact_imaginary_sign);
        drop(contact_imaginary_limbs);
        drop(overlap_scratch);
        drop(contribution_action_sign);
        drop(contribution_action_limbs);
        drop(contribution_reflected_sign);
        drop(contribution_reflected_limbs);
        drop(contribution_receiver_sign);
        drop(contribution_receiver_limbs);
        drop(contribution_receiver_norm_sign);
        drop(contribution_receiver_norm_limbs);
        drop(factorized_left_scratch);
        drop(factorized_right_scratch);
        drop(factorized_bucket_scratch);
        drop(factorized_quadratic_scratch);
        drop(factorized_term_scratch);
        drop(factorized_overlap_scratch);
        drop(support_port);
        drop(support_real_sign);
        drop(support_real_limbs);
        drop(support_imaginary_sign);
        drop(support_imaginary_limbs);
        drop(port_real_sign);
        drop(port_real_limbs);
        drop(port_imaginary_sign);
        drop(port_imaginary_limbs);
        drop(joint_real_sign);
        drop(joint_real_limbs);
        drop(joint_imaginary_sign);
        drop(joint_imaginary_limbs);
        drop(port_action_sign);
        drop(port_action_limbs);
        drop(port_reflected_sign);
        drop(port_reflected_limbs);
        drop(port_receiver_sign);
        drop(port_receiver_limbs);
        drop(port_receiver_norm_sign);
        drop(port_receiver_norm_limbs);
        drop(compatibility_sign);
        drop(compatibility_limbs);
        drop(phase_norm_limbs);
        drop(phase_locked);
        drop(phase_square_scratch);
        drop(phase_left_cross_scratch);
        drop(phase_right_cross_scratch);
        drop(situated_pairing_sign);
        drop(situated_pairing_limbs);
        drop(situated_pairing_imaginary_scratch);
        drop(incoming_real_sign_device);
        drop(incoming_real_limbs_device);
        drop(incoming_imaginary_sign_device);
        drop(incoming_imaginary_limbs_device);
        drop(stored_real_sign);
        drop(stored_real_limbs);
        drop(stored_imaginary_sign);
        drop(stored_imaginary_limbs);
        drop(balance_scratch);

        // The relational observer workspace belongs only to `observe_R(X')`.  The causal-adjoint
        // current which founded `X'` was already transported and committed by the early step.
        drop(factorized_relational_workspace);
        drop(completed_target_observer_workspace);
        let continuation_launches = completed_step
            .as_ref()
            .map_or(0, |aperture| aperture.returned.launches);
        let continuation_synchronizations = completed_step
            .as_ref()
            .map_or(0, |aperture| aperture.returned.synchronizations);
        let conditioned_current = completed_step.map(|aperture| aperture.returned);
        let relational_current = self
            .sparse_relational_current
            .as_ref()
            .map(|current| current.receipt.clone());
        Ok(ResidentQuadraticMomentReturn {
            factored_receiver_history,
            resident_current,
            conditioned_current,
            relational_current,
            receiver_coordinate_denominator: BigInt::one(),
            ports,
            port_returns,
            entering_current: entering_current.clone(),
            total_returned_current,
            stored_difference,
            local_balance_closes,
            phase_locked_port_population,
            phase_front_is_unique: phase_locked_port_population == 1,
            situated_receiver_pairing: Some(situated_receiver_pairing),
            complete_successor_faces: (0..response_population)
                .filter(|face| {
                    // The complete front is device-derived above and read only after the
                    // resident successor has committed.  This older returned-current chart has
                    // no addressed state axis, so its face index is its complete address.
                    complete_native_successor_front_host[*face] != 0
                })
                .map(|face| face as u32)
                .collect(),
            complete_successor_face_population: if descend_boundary_state_receiver {
                resident_boundary
                    .map(|boundary| boundary.boundary_states.len())
                    .unwrap_or(1)
                    .checked_mul(local_response_population)
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            } else {
                response_population
            },
            active_factor_population: factors,
            native_factor_population: native_factors,
            moment_field_materialized: materialize_moment_field,
            moment_factorization_retained: true,
            context_population: context_count,
            restriction_population,
            generator_population: generator_count,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            launches: launches + continuation_launches,
            device_dependency_edges: launches + continuation_launches - 1,
            synchronizations: 1 + continuation_synchronizations,
            block_threads: self.card.block_x,
            mount_host_ingress_octets: self.mount_host_ingress_octets,
            successor_host_ingress_octets,
            successor_host_egress_octets,
            intermediate_host_egress_octets: 0,
            resident_invariant_octets: self.mount_host_ingress_octets,
            resident_working_octets,
            invariant_transport_reuploaded: false,
            cpu_semantic_replay_after_device: false,
        })
    }
}
