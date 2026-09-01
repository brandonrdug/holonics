//! Owner-local CUDA refinement surface.

use super::*;

pub struct ResidentIntegratedFront {
    coupled: ResidentCoupledComplexParametron,
    participant: ResidentParticipantCausalFront,
    affine: ResidentAffineBarycentricTransport,
    context_identity: usize,
    card: CudaRefineExecutor,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentIntegratedFrontReturn {
    pub coupled: ResidentCoupledComplexParametronReturn,
    pub participant: ResidentParticipantCausalFrontReturn,
    pub affine: ResidentAffineBarycentricTransportReturn,
    pub context_identity: usize,
    pub one_underlying_context: bool,
    pub launches: u64,
    pub synchronizations: u64,
    pub successor_host_ingress_octets: u64,
    pub successor_host_egress_octets: u64,
    pub intermediate_host_egress_octets: u64,
    pub resident_invariant_octets: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
}

/// The complete prompt-current/cultivated-cell overlap holon and its non-dominated returned front.
/// Every overlap coordinate remains exact; the selected mask is a receiver projection over that
/// tensorial section rather than a score or ranked candidate list.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentSituatedCurrentCausalFrontReturn {
    pub contexts: Vec<AddressedCurrentSection>,
    pub common_factor_current: Vec<(u32, BigUint)>,
    pub differentiated_factor_currents: Vec<Vec<(u32, BigUint)>>,
    pub cell_context_overlaps: Vec<Vec<BigUint>>,
    pub causal_candidate_front: Vec<u8>,
    pub causal_candidate_population: usize,
    pub selected: Vec<u8>,
    pub selected_population: usize,
    pub participant_only: bool,
    pub deed: u32,
    pub context_population: usize,
    pub cell_population: usize,
    pub current_limb_count: usize,
    pub overlap_limb_count: usize,
    pub overlap_identity_sha256: String,
    pub situated_difference_identity_sha256: String,
    pub device: String,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub successor_host_ingress_octets: u64,
    pub successor_host_egress_octets: u64,
    pub resident_invariant_octets: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
    pub scalar_score_present: bool,
    pub authored_output_extent_present: bool,
}

impl ResidentIntegratedFront {
    #[allow(clippy::too_many_arguments)]
    pub fn mount(
        card: CudaRefineExecutor,
        coupled_address: impl Into<String>,
        causal_adjoint_pulled_incidence: CausalAdjointPulledIncidence,
        standing_front: Vec<ExactComplexWaveCurrent>,
        interactions: Vec<CoupledComplexInteraction>,
        participant_subject: &[u8],
        copular: &[u8],
        has_modality: &[u8],
        has_return: &[u8],
        landmark_support: &[u32],
        occurrence_mass: &[u64],
        last_occurrence: &[u64],
        cell_offsets: &[u64],
        cell_factors: &[u32],
        multiplicities: &[u64],
        cell_total_mass: &[u64],
    ) -> Result<Self, CudaRefineError> {
        let context_identity = card.context as usize;
        let coupled = ResidentCoupledComplexParametron::mount(
            card.fork_same_context(),
            coupled_address,
            causal_adjoint_pulled_incidence,
            standing_front,
            interactions,
        )?;
        let participant = card.fork_same_context().mount_participant_causal_front(
            participant_subject,
            copular,
            has_modality,
            has_return,
            landmark_support,
            occurrence_mass,
            last_occurrence,
        )?;
        let affine = card
            .fork_same_context()
            .mount_affine_barycentric_transport(
                cell_offsets,
                cell_factors,
                multiplicities,
                cell_total_mass,
            )?;
        Ok(Self {
            coupled,
            participant,
            affine,
            context_identity,
            card,
        })
    }

    /// One fixed resident word.  The host supplies only the later material section, factor-active
    /// aperture, and receiver deed; it does not inspect one device return to select the next law.
    pub fn conduct(
        &mut self,
        active_factors: &[bool],
        entering_section: &[i64],
        deed: u32,
    ) -> Result<ResidentIntegratedFrontReturn, CudaRefineError> {
        let pending_coupled = self.coupled.enqueue(active_factors)?;
        let pending_affine = self.affine.enqueue(entering_section)?;
        let pending_participant = self.participant.enqueue(deed)?;
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        let coupled = self.coupled.finalize(pending_coupled, 0)?;
        let affine = self.affine.finalize(pending_affine, 0)?;
        let participant = self.participant.finalize(pending_participant, 0)?;
        let invariant_transport_reuploaded = coupled.invariant_transport_reuploaded
            || affine.invariant_transport_reuploaded
            || participant.invariant_transport_reuploaded;
        let cpu_semantic_replay_after_device = coupled.cpu_semantic_replay_after_device
            || affine.cpu_semantic_replay_after_device
            || participant.cpu_semantic_replay_after_device;
        let successor_host_ingress_octets = coupled
            .successor_host_ingress_octets
            .checked_add(affine.successor_host_ingress_octets)
            .and_then(|total| total.checked_add(participant.successor_host_ingress_octets))
            .ok_or(CudaRefineError::AffineBarycentricTransportShape)?;
        let successor_host_egress_octets = coupled
            .successor_host_egress_octets
            .checked_add(affine.successor_host_egress_octets)
            .and_then(|total| total.checked_add(participant.successor_host_egress_octets))
            .ok_or(CudaRefineError::AffineBarycentricTransportShape)?;
        let resident_invariant_octets = coupled
            .resident_invariant_octets
            .checked_add(affine.resident_invariant_octets)
            .and_then(|total| total.checked_add(participant.resident_invariant_octets))
            .ok_or(CudaRefineError::AffineBarycentricTransportShape)?;
        Ok(ResidentIntegratedFrontReturn {
            coupled,
            participant,
            affine,
            context_identity: self.context_identity,
            one_underlying_context: self.context_identity == self.card.context as usize,
            launches: 3,
            synchronizations: 1,
            successor_host_ingress_octets,
            successor_host_egress_octets,
            intermediate_host_egress_octets: 0,
            resident_invariant_octets,
            invariant_transport_reuploaded,
            cpu_semantic_replay_after_device,
        })
    }

    pub fn conduct_participant(
        &mut self,
        deed: u32,
    ) -> Result<ResidentParticipantCausalFrontReturn, CudaRefineError> {
        self.participant.conduct(deed)
    }

    /// Contract one exact current family with every cultivated affine cell and return the complete
    /// Pareto front in one default-stream word. The cell/context overlap tensor is the comparison
    /// object; no aggregate score, lexical label, or authored output extent is supplied.
    pub fn conduct_situated_current_front(
        &mut self,
        contexts: &[AddressedCurrentSection],
        participant_only: bool,
        deed: u32,
    ) -> Result<ResidentSituatedCurrentCausalFrontReturn, CudaRefineError> {
        let factor_count = self.affine.factor_population as usize;
        let context_count = contexts.len();
        let cell_count = self.affine.cells as usize;
        if factor_count == 0
            || context_count == 0
            || context_count > u32::MAX as usize
            || cell_count == 0
            || deed > 2
            || contexts.iter().any(|context| {
                context.quadratic_weight.is_zero()
                    || context.factor_current.is_empty()
                    || context
                        .factor_current
                        .windows(2)
                        .any(|pair| pair[0].0 >= pair[1].0)
                    || context.factor_current.iter().any(|(factor, coefficient)| {
                        *factor as usize >= factor_count || coefficient.is_zero()
                    })
            })
        {
            return Err(CudaRefineError::ParticipantCausalFrontShape);
        }
        let current_limb_count = contexts
            .iter()
            .flat_map(|context| &context.factor_current)
            .map(|(_, coefficient)| coefficient.to_u32_digits().len())
            .max()
            .unwrap_or(1)
            .max(1);
        let overlap_limb_count = current_limb_count
            .checked_add(2)
            .filter(|extent| *extent <= u32::MAX as usize)
            .ok_or(CudaRefineError::ParticipantCausalFrontShape)?;
        let current_population = context_count
            .checked_mul(factor_count)
            .and_then(|extent| extent.checked_mul(current_limb_count))
            .ok_or(CudaRefineError::ParticipantCausalFrontShape)?;
        let mut dense_current = vec![0_u32; current_population];
        for (context, section) in contexts.iter().enumerate() {
            for (factor, coefficient) in &section.factor_current {
                let mut limbs = coefficient.to_u32_digits();
                limbs.resize(current_limb_count, 0);
                let begin = (context * factor_count + *factor as usize) * current_limb_count;
                dense_current[begin..begin + current_limb_count].copy_from_slice(&limbs);
            }
        }
        let overlap_coordinate_population = cell_count
            .checked_mul(context_count)
            .ok_or(CudaRefineError::ParticipantCausalFrontShape)?;
        let overlap_limb_population = overlap_coordinate_population
            .checked_mul(overlap_limb_count)
            .ok_or(CudaRefineError::ParticipantCausalFrontShape)?;
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let current_device = Buffer::of(&dense_current)?;
        let common_limb_population = factor_count
            .checked_mul(current_limb_count)
            .ok_or(CudaRefineError::ParticipantCausalFrontShape)?;
        let common_device = Buffer::alloc(
            common_limb_population
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::ParticipantCausalFrontShape)?,
        )?;
        let residual_device = Buffer::alloc(
            current_population
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::ParticipantCausalFrontShape)?,
        )?;
        let overlaps_device = Buffer::alloc(
            overlap_limb_population
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::ParticipantCausalFrontShape)?,
        )?;
        let candidate_device = Buffer::alloc(cell_count)?;
        let selected_device = Buffer::alloc(cell_count)?;
        driver(
            unsafe { cuMemsetD8_v2(selected_device.pointer, 0, cell_count) },
            "cuMemsetD8_v2(situated_current_selected)",
        )?;
        let overflow = Buffer::of(&[0_u32])?;

        let mut source_current_pointer = current_device.pointer;
        let mut common_pointer = common_device.pointer;
        let mut residual_pointer = residual_device.pointer;
        let mut factors_wire = self.affine.factor_population;
        let mut contexts_wire = context_count as u32;
        let mut current_limbs_wire = current_limb_count as u32;
        let mut difference_arguments: [*mut c_void; 6] = [
            &mut source_current_pointer as *mut u64 as *mut c_void,
            &mut common_pointer as *mut u64 as *mut c_void,
            &mut residual_pointer as *mut u64 as *mut c_void,
            &mut factors_wire as *mut u32 as *mut c_void,
            &mut contexts_wire as *mut u32 as *mut c_void,
            &mut current_limbs_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.situated_current_difference,
                    self.card.grid_for(factor_count as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    difference_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(differentiate_situated_current_contexts)",
        )?;

        let mut cell_offsets_pointer = self.affine.cell_offsets.pointer;
        let mut cell_factors_pointer = self.affine.cell_factors.pointer;
        let mut multiplicities_pointer = self.affine.multiplicities.pointer;
        let mut current_pointer = residual_device.pointer;
        let mut overlaps_pointer = overlaps_device.pointer;
        let mut overflow_pointer = overflow.pointer;
        let mut cells_wire = self.affine.cells;
        let mut overlap_limbs_wire = overlap_limb_count as u32;
        let mut contract_arguments: [*mut c_void; 11] = [
            &mut cell_offsets_pointer as *mut u64 as *mut c_void,
            &mut cell_factors_pointer as *mut u64 as *mut c_void,
            &mut multiplicities_pointer as *mut u64 as *mut c_void,
            &mut current_pointer as *mut u64 as *mut c_void,
            &mut overlaps_pointer as *mut u64 as *mut c_void,
            &mut overflow_pointer as *mut u64 as *mut c_void,
            &mut cells_wire as *mut u32 as *mut c_void,
            &mut factors_wire as *mut u32 as *mut c_void,
            &mut contexts_wire as *mut u32 as *mut c_void,
            &mut current_limbs_wire as *mut u32 as *mut c_void,
            &mut overlap_limbs_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.situated_current_affine_cells,
                    self.card.grid_for(overlap_coordinate_population as u64)?,
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
            "cuLaunchKernel(contract_situated_current_affine_cells)",
        )?;

        let mut participant_subject_pointer = self.participant.participant_subject.pointer;
        let mut copular_pointer = self.participant.copular.pointer;
        let mut has_modality_pointer = self.participant.has_modality.pointer;
        let mut has_return_pointer = self.participant.has_return.pointer;
        let mut landmark_support_pointer = self.participant.landmark_support.pointer;
        let mut occurrence_mass_pointer = self.participant.occurrence_mass.pointer;
        let mut last_occurrence_pointer = self.participant.last_occurrence.pointer;
        let mut candidate_pointer = candidate_device.pointer;
        let mut participant_only_wire = u32::from(participant_only);
        let mut deed_wire = deed;
        let mut structural_arguments: [*mut c_void; 14] = [
            &mut participant_subject_pointer as *mut u64 as *mut c_void,
            &mut copular_pointer as *mut u64 as *mut c_void,
            &mut has_modality_pointer as *mut u64 as *mut c_void,
            &mut has_return_pointer as *mut u64 as *mut c_void,
            &mut landmark_support_pointer as *mut u64 as *mut c_void,
            &mut occurrence_mass_pointer as *mut u64 as *mut c_void,
            &mut last_occurrence_pointer as *mut u64 as *mut c_void,
            &mut overlaps_pointer as *mut u64 as *mut c_void,
            &mut candidate_pointer as *mut u64 as *mut c_void,
            &mut cells_wire as *mut u32 as *mut c_void,
            &mut contexts_wire as *mut u32 as *mut c_void,
            &mut overlap_limbs_wire as *mut u32 as *mut c_void,
            &mut participant_only_wire as *mut u32 as *mut c_void,
            &mut deed_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.situated_current_structural_front,
                    self.card.grid_for(cell_count as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    structural_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(select_situated_current_structural_front)",
        )?;

        let mut cell_total_mass_pointer = self.affine.cell_total_mass.pointer;
        let mut selected_pointer = selected_device.pointer;
        let mut select_arguments: [*mut c_void; 13] = [
            &mut participant_subject_pointer as *mut u64 as *mut c_void,
            &mut copular_pointer as *mut u64 as *mut c_void,
            &mut has_modality_pointer as *mut u64 as *mut c_void,
            &mut has_return_pointer as *mut u64 as *mut c_void,
            &mut candidate_pointer as *mut u64 as *mut c_void,
            &mut cell_total_mass_pointer as *mut u64 as *mut c_void,
            &mut overlaps_pointer as *mut u64 as *mut c_void,
            &mut selected_pointer as *mut u64 as *mut c_void,
            &mut cells_wire as *mut u32 as *mut c_void,
            &mut contexts_wire as *mut u32 as *mut c_void,
            &mut overlap_limbs_wire as *mut u32 as *mut c_void,
            &mut participant_only_wire as *mut u32 as *mut c_void,
            &mut deed_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.situated_current_causal_front,
                    self.card.grid_for(context_count as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    select_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(select_situated_current_causal_front)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.card.launches += 4;
        let mut overflow_host = [0_u32; 1];
        overflow.read(&mut overflow_host)?;
        if overflow_host[0] != 0 {
            return Err(CudaRefineError::ParticipantCausalFrontShape);
        }
        let mut causal_candidate_front = vec![0_u8; cell_count];
        candidate_device.read(&mut causal_candidate_front)?;
        let mut selected = vec![0_u8; cell_count];
        selected_device.read(&mut selected)?;
        let mut overlap_limbs = vec![0_u32; overlap_limb_population];
        overlaps_device.read(&mut overlap_limbs)?;
        let mut common_limbs = vec![0_u32; common_limb_population];
        common_device.read(&mut common_limbs)?;
        let mut residual_limbs = vec![0_u32; current_population];
        residual_device.read(&mut residual_limbs)?;
        let common_factor_current = common_limbs
            .chunks_exact(current_limb_count)
            .enumerate()
            .filter_map(|(factor, limbs)| {
                let coefficient = BigUint::new(limbs.to_vec());
                (!coefficient.is_zero()).then_some((factor as u32, coefficient))
            })
            .collect::<Vec<_>>();
        let differentiated_factor_currents = residual_limbs
            .chunks_exact(factor_count * current_limb_count)
            .map(|context| {
                context
                    .chunks_exact(current_limb_count)
                    .enumerate()
                    .filter_map(|(factor, limbs)| {
                        let coefficient = BigUint::new(limbs.to_vec());
                        (!coefficient.is_zero()).then_some((factor as u32, coefficient))
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        if differentiated_factor_currents.iter().all(Vec::is_empty) {
            return Err(CudaRefineError::ParticipantCausalFrontShape);
        }
        let cell_context_overlaps = overlap_limbs
            .chunks_exact(overlap_limb_count)
            .map(|limbs| BigUint::new(limbs.to_vec()))
            .collect::<Vec<_>>()
            .chunks_exact(context_count)
            .map(|cell| cell.to_vec())
            .collect::<Vec<_>>();
        let overlap_identity_sha256 = Sha256::digest(
            overlap_limbs
                .iter()
                .flat_map(|limb| limb.to_le_bytes())
                .chain(causal_candidate_front.iter().copied())
                .chain(selected.iter().copied())
                .collect::<Vec<_>>(),
        )
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect::<String>();
        let situated_difference_identity_sha256 = Sha256::digest(
            common_limbs
                .iter()
                .chain(&residual_limbs)
                .flat_map(|limb| limb.to_le_bytes())
                .collect::<Vec<_>>(),
        )
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect::<String>();
        let successor_host_ingress_octets =
            u64::try_from(std::mem::size_of_val(&dense_current[..]))
                .map_err(|_| CudaRefineError::ParticipantCausalFrontShape)?;
        let successor_host_egress_octets = u64::try_from(
            std::mem::size_of_val(&overlap_limbs[..])
                .checked_add(std::mem::size_of_val(&selected[..]))
                .and_then(|total| {
                    total.checked_add(std::mem::size_of_val(&causal_candidate_front[..]))
                })
                .and_then(|total| total.checked_add(std::mem::size_of_val(&common_limbs[..])))
                .and_then(|total| total.checked_add(std::mem::size_of_val(&residual_limbs[..])))
                .ok_or(CudaRefineError::ParticipantCausalFrontShape)?,
        )
        .map_err(|_| CudaRefineError::ParticipantCausalFrontShape)?;
        Ok(ResidentSituatedCurrentCausalFrontReturn {
            contexts: contexts.to_vec(),
            common_factor_current,
            differentiated_factor_currents,
            cell_context_overlaps,
            causal_candidate_population: causal_candidate_front
                .iter()
                .filter(|value| **value != 0)
                .count(),
            causal_candidate_front,
            selected_population: selected.iter().filter(|value| **value != 0).count(),
            selected,
            participant_only,
            deed,
            context_population: context_count,
            cell_population: cell_count,
            current_limb_count,
            overlap_limb_count,
            overlap_identity_sha256,
            situated_difference_identity_sha256,
            device: self.card.device_name.clone(),
            launches: 4,
            synchronizations: 1,
            block_threads: self.card.block_x,
            successor_host_ingress_octets,
            successor_host_egress_octets,
            resident_invariant_octets: self.participant.resident_invariant_octets
                + self.affine.mount_host_ingress_octets,
            invariant_transport_reuploaded: false,
            cpu_semantic_replay_after_device: false,
            scalar_score_present: false,
            authored_output_extent_present: false,
        })
    }
}
