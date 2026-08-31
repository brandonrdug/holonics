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
mod membrane_moment_contraction;
mod membrane_moment_execution;
mod membrane_moment_plan;
mod membrane_moment_readback;
mod membrane_moment_receiver;
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
        let cuda_profile = trace_configuration().mem6_cuda_profile;
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
        let execution = membrane_moment_execution::MomentFrontExecution {
            plan,
            workspace,
            post_target_observer,
            materialize_moment_field,
            resident_began,
            cuda_profile,
        };
        let mut contraction = membrane_moment_contraction::launch(
            self,
            front,
            port_population,
            completed_step.as_ref(),
            &execution,
        )?;
        membrane_moment_receiver::launch(self, port_population, &execution, &mut contraction)?;
        membrane_moment_readback::readback(
            self,
            entering_current,
            completed_step,
            execution,
            contraction,
        )
    }
}
