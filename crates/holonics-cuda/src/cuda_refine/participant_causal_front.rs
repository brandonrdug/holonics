//! Owner-local CUDA refinement surface.

use super::*;

pub struct DeviceNativeWord {
    pub native_end: Vec<u32>,
    pub launches: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// One participant/deed causal atlas retained on the card across receiver projections.  All
/// arrays are native structural coordinates; no surface words, queries, scores, or answer extents
/// enter this owner.
pub struct ResidentParticipantCausalFront {
    pub(super) participant_subject: Buffer,
    pub(super) copular: Buffer,
    pub(super) has_modality: Buffer,
    pub(super) has_return: Buffer,
    pub(super) landmark_support: Buffer,
    pub(super) occurrence_mass: Buffer,
    pub(super) last_occurrence: Buffer,
    card: CudaRefineExecutor,
    cells: u32,
    participant_subject_population: u64,
    pub(super) resident_invariant_octets: u64,
    mount_host_ingress_octets: u64,
}

/// The complete terminal mask returned by one typed participant deed.  Equal terminal sections
/// remain plural; the caller receives the full mask and its reconstruction extent.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentParticipantCausalFrontReturn {
    pub deed: u32,
    pub selected: Vec<u8>,
    pub selected_population: usize,
    pub participant_subject_population: u64,
    pub device: String,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub mount_host_ingress_octets: u64,
    pub successor_host_ingress_octets: u64,
    pub successor_host_egress_octets: u64,
    pub resident_invariant_octets: u64,
    pub resident_working_octets: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
    pub authored_output_extent_present: bool,
}

pub(super) struct PendingParticipantCausalFront {
    deed: u32,
    selected_device: Buffer,
}

impl CudaRefineExecutor {
    /// Mount one complete participant incidence/chart body.  Every array has one entry per native
    /// relational cell and remains resident across all later describe/identify/infer deeds.
    #[allow(clippy::too_many_arguments)]
    pub fn mount_participant_causal_front(
        self,
        participant_subject: &[u8],
        copular: &[u8],
        has_modality: &[u8],
        has_return: &[u8],
        landmark_support: &[u32],
        occurrence_mass: &[u64],
        last_occurrence: &[u64],
    ) -> Result<ResidentParticipantCausalFront, CudaRefineError> {
        let cells = participant_subject.len();
        if cells == 0
            || cells > u32::MAX as usize
            || [
                copular.len(),
                has_modality.len(),
                has_return.len(),
                landmark_support.len(),
                occurrence_mass.len(),
                last_occurrence.len(),
            ]
            .iter()
            .any(|extent| *extent != cells)
            || participant_subject.iter().all(|value| *value == 0)
        {
            return Err(CudaRefineError::ParticipantCausalFrontShape);
        }
        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let participant_subject_population = participant_subject
            .iter()
            .map(|value| u64::from(*value != 0))
            .sum();
        let mount_host_ingress_octets = std::mem::size_of_val(participant_subject)
            .checked_add(std::mem::size_of_val(copular))
            .and_then(|total| total.checked_add(std::mem::size_of_val(has_modality)))
            .and_then(|total| total.checked_add(std::mem::size_of_val(has_return)))
            .and_then(|total| total.checked_add(std::mem::size_of_val(landmark_support)))
            .and_then(|total| total.checked_add(std::mem::size_of_val(occurrence_mass)))
            .and_then(|total| total.checked_add(std::mem::size_of_val(last_occurrence)))
            .ok_or(CudaRefineError::ParticipantCausalFrontShape)?
            as u64;
        Ok(ResidentParticipantCausalFront {
            participant_subject: Buffer::of(participant_subject)?,
            copular: Buffer::of(copular)?,
            has_modality: Buffer::of(has_modality)?,
            has_return: Buffer::of(has_return)?,
            landmark_support: Buffer::of(landmark_support)?,
            occurrence_mass: Buffer::of(occurrence_mass)?,
            last_occurrence: Buffer::of(last_occurrence)?,
            card: self,
            cells: cells as u32,
            participant_subject_population,
            resident_invariant_octets: mount_host_ingress_octets,
            mount_host_ingress_octets,
        })
    }
}

impl ResidentParticipantCausalFront {
    /// Return one typed causal front.  `deed` is 0=describe, 1=identify, 2=infer; no surface
    /// parsing occurs here and every selected equality class is returned.
    pub fn conduct(
        &mut self,
        deed: u32,
    ) -> Result<ResidentParticipantCausalFrontReturn, CudaRefineError> {
        let pending = self.enqueue(deed)?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.finalize(pending, 1)
    }

    pub(super) fn enqueue(
        &mut self,
        deed: u32,
    ) -> Result<PendingParticipantCausalFront, CudaRefineError> {
        if deed > 2 {
            return Err(CudaRefineError::ParticipantCausalFrontShape);
        }
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )
        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        let selected_device = Buffer::alloc(self.cells as usize)?;
        let grid = self.card.grid_for(u64::from(self.cells))?;
        let mut participant_subject_pointer = self.participant_subject.pointer;
        let mut copular_pointer = self.copular.pointer;
        let mut has_modality_pointer = self.has_modality.pointer;
        let mut has_return_pointer = self.has_return.pointer;
        let mut landmark_support_pointer = self.landmark_support.pointer;
        let mut occurrence_mass_pointer = self.occurrence_mass.pointer;
        let mut last_occurrence_pointer = self.last_occurrence.pointer;
        let mut selected_pointer = selected_device.pointer;
        let mut cells = self.cells;
        let mut deed = deed;
        let mut arguments: [*mut c_void; 10] = [
            &mut participant_subject_pointer as *mut u64 as *mut c_void,
            &mut copular_pointer as *mut u64 as *mut c_void,
            &mut has_modality_pointer as *mut u64 as *mut c_void,
            &mut has_return_pointer as *mut u64 as *mut c_void,
            &mut landmark_support_pointer as *mut u64 as *mut c_void,
            &mut occurrence_mass_pointer as *mut u64 as *mut c_void,
            &mut last_occurrence_pointer as *mut u64 as *mut c_void,
            &mut selected_pointer as *mut u64 as *mut c_void,
            &mut cells as *mut u32 as *mut c_void,
            &mut deed as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.participant_causal_front,
                    grid,
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
            "cuLaunchKernel(select_participant_causal_front)",
        )?;
        self.card.launches += 1;
        Ok(PendingParticipantCausalFront {
            deed,
            selected_device,
        })
    }

    pub(super) fn finalize(
        &mut self,
        pending: PendingParticipantCausalFront,
        synchronizations: u64,
    ) -> Result<ResidentParticipantCausalFrontReturn, CudaRefineError> {
        let PendingParticipantCausalFront {
            deed,
            selected_device,
        } = pending;
        let mut selected = vec![0u8; self.cells as usize];
        selected_device.read(&mut selected)?;
        let selected_population = selected.iter().filter(|value| **value != 0).count();
        Ok(ResidentParticipantCausalFrontReturn {
            deed,
            selected,
            selected_population,
            participant_subject_population: self.participant_subject_population,
            device: self.card.device_name.clone(),
            launches: 1,
            synchronizations,
            block_threads: self.card.block_x,
            mount_host_ingress_octets: self.mount_host_ingress_octets,
            successor_host_ingress_octets: std::mem::size_of::<u32>() as u64,
            successor_host_egress_octets: u64::from(self.cells),
            resident_invariant_octets: self.resident_invariant_octets,
            resident_working_octets: u64::from(self.cells),
            invariant_transport_reuploaded: false,
            cpu_semantic_replay_after_device: false,
            authored_output_extent_present: false,
        })
    }
}
