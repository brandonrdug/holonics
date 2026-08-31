//! Owner-local CUDA refinement surface.

use super::*;

pub struct ResidentAffineBarycentricTransport {
    pub(super) cell_offsets: Buffer,
    pub(super) cell_factors: Buffer,
    pub(super) multiplicities: Buffer,
    pub(super) cell_total_mass: Buffer,
    card: CudaRefineExecutor,
    pub(super) cells: u32,
    pub(super) factor_population: u32,
    support_terms: u64,
    greatest_total_mass: u64,
    pub(super) mount_host_ingress_octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentAffineBarycentricTransportReturn {
    pub entering_section: Vec<i64>,
    pub addressed_cell_population: usize,
    pub support_term_population: usize,
    pub local_fibre_term_population: usize,
    pub exact_reconstruction_cell_population: usize,
    pub augmented_numerators_sha256: String,
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
    pub cell_selected_or_ranked: bool,
}

pub(super) struct PendingAffineBarycentricTransport {
    entering_section: Vec<i64>,
    section: Buffer,
    augmented: Buffer,
    exact: Buffer,
    output_population: usize,
}

impl CudaRefineExecutor {
    pub fn mount_affine_barycentric_transport(
        self,
        cell_offsets: &[u64],
        cell_factors: &[u32],
        multiplicities: &[u64],
        cell_total_mass: &[u64],
    ) -> Result<ResidentAffineBarycentricTransport, CudaRefineError> {
        let cells = cell_total_mass.len();
        if cells == 0
            || cells > u32::MAX as usize
            || cell_offsets.len() != cells + 1
            || cell_offsets.first() != Some(&0)
            || cell_offsets.last().copied() != Some(multiplicities.len() as u64)
            || cell_factors.len() != multiplicities.len()
            || cell_offsets.windows(2).any(|pair| pair[0] >= pair[1])
            || cell_total_mass.iter().any(|mass| *mass == 0)
        {
            return Err(CudaRefineError::AffineBarycentricTransportShape);
        }
        for (cell, offsets) in cell_offsets.windows(2).enumerate() {
            let returned = multiplicities[offsets[0] as usize..offsets[1] as usize]
                .iter()
                .try_fold(0u64, |sum, mass| sum.checked_add(*mass))
                .ok_or(CudaRefineError::AffineBarycentricTransportShape)?;
            if returned != cell_total_mass[cell] {
                return Err(CudaRefineError::AffineBarycentricTransportShape);
            }
        }
        let factor_population = cell_factors
            .iter()
            .copied()
            .max()
            .and_then(|factor| factor.checked_add(1))
            .ok_or(CudaRefineError::AffineBarycentricTransportShape)?;
        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let mount_host_ingress_octets = std::mem::size_of_val(cell_offsets)
            .checked_add(std::mem::size_of_val(cell_factors))
            .and_then(|total| total.checked_add(std::mem::size_of_val(multiplicities)))
            .and_then(|total| total.checked_add(std::mem::size_of_val(cell_total_mass)))
            .ok_or(CudaRefineError::AffineBarycentricTransportShape)?
            as u64;
        Ok(ResidentAffineBarycentricTransport {
            cell_offsets: Buffer::of(cell_offsets)?,
            cell_factors: Buffer::of(cell_factors)?,
            multiplicities: Buffer::of(multiplicities)?,
            cell_total_mass: Buffer::of(cell_total_mass)?,
            card: self,
            cells: cells as u32,
            factor_population,
            support_terms: multiplicities.len() as u64,
            greatest_total_mass: cell_total_mass.iter().copied().max().unwrap_or(0),
            mount_host_ingress_octets,
        })
    }
}

impl ResidentAffineBarycentricTransport {
    pub fn conduct(
        &mut self,
        entering_section: &[i64],
    ) -> Result<ResidentAffineBarycentricTransportReturn, CudaRefineError> {
        let pending = self.enqueue(entering_section)?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.finalize(pending, 1)
    }

    pub(super) fn enqueue(
        &mut self,
        entering_section: &[i64],
    ) -> Result<PendingAffineBarycentricTransport, CudaRefineError> {
        if entering_section.is_empty()
            || entering_section.len() > u32::MAX as usize
            || entering_section.iter().any(|coefficient| {
                u128::from(self.greatest_total_mass)
                    .checked_mul(u128::from(coefficient.unsigned_abs()))
                    .is_none_or(|bound| bound > i64::MAX as u128)
            })
        {
            return Err(CudaRefineError::AffineBarycentricTransportShape);
        }
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let section = Buffer::of(entering_section)?;
        let output_population = (self.cells as usize)
            .checked_mul(entering_section.len())
            .ok_or(CudaRefineError::AffineBarycentricTransportShape)?;
        let augmented = Buffer::alloc(
            output_population
                .checked_mul(std::mem::size_of::<i64>())
                .ok_or(CudaRefineError::AffineBarycentricTransportShape)?,
        )?;
        let exact = Buffer::alloc(self.cells as usize)?;
        let grid = self.card.grid_for(u64::from(self.cells))?;
        let mut offsets_pointer = self.cell_offsets.pointer;
        let mut multiplicities_pointer = self.multiplicities.pointer;
        let mut total_mass_pointer = self.cell_total_mass.pointer;
        let mut section_pointer = section.pointer;
        let mut augmented_pointer = augmented.pointer;
        let mut exact_pointer = exact.pointer;
        let mut cells = self.cells;
        let mut rank = entering_section.len() as u32;
        let mut arguments: [*mut c_void; 8] = [
            &mut offsets_pointer as *mut u64 as *mut c_void,
            &mut multiplicities_pointer as *mut u64 as *mut c_void,
            &mut total_mass_pointer as *mut u64 as *mut c_void,
            &mut section_pointer as *mut u64 as *mut c_void,
            &mut augmented_pointer as *mut u64 as *mut c_void,
            &mut exact_pointer as *mut u64 as *mut c_void,
            &mut cells as *mut u32 as *mut c_void,
            &mut rank as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.affine_barycentric_transport,
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
            "cuLaunchKernel(conduct_affine_barycentric_transport)",
        )?;
        self.card.launches += 1;
        Ok(PendingAffineBarycentricTransport {
            entering_section: entering_section.to_vec(),
            section,
            augmented,
            exact,
            output_population,
        })
    }

    pub(super) fn finalize(
        &mut self,
        pending: PendingAffineBarycentricTransport,
        synchronizations: u64,
    ) -> Result<ResidentAffineBarycentricTransportReturn, CudaRefineError> {
        let PendingAffineBarycentricTransport {
            entering_section,
            section,
            augmented,
            exact,
            output_population,
        } = pending;
        let _section_lifetime = section;
        let mut returned = vec![0i64; output_population];
        augmented.read(&mut returned)?;
        let mut exact_cells = vec![0u8; self.cells as usize];
        exact.read(&mut exact_cells)?;
        let exact_reconstruction_cell_population =
            exact_cells.iter().filter(|value| **value != 0).count();
        if exact_reconstruction_cell_population != self.cells as usize {
            return Err(CudaRefineError::AffineBarycentricTransportShape);
        }
        let mut digest = Sha256::new();
        for value in &returned {
            digest.update(value.to_le_bytes());
        }
        let augmented_numerators_sha256 = digest
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect();
        let successor_host_ingress_octets =
            std::mem::size_of_val(entering_section.as_slice()) as u64;
        let successor_host_egress_octets = std::mem::size_of_val(returned.as_slice())
            .checked_add(std::mem::size_of_val(exact_cells.as_slice()))
            .ok_or(CudaRefineError::AffineBarycentricTransportShape)?
            as u64;
        let local_fibre_term_population = (self.support_terms as usize)
            .checked_mul(entering_section.len())
            .ok_or(CudaRefineError::AffineBarycentricTransportShape)?;
        Ok(ResidentAffineBarycentricTransportReturn {
            entering_section,
            addressed_cell_population: self.cells as usize,
            support_term_population: self.support_terms as usize,
            local_fibre_term_population,
            exact_reconstruction_cell_population,
            augmented_numerators_sha256,
            device: self.card.device_name.clone(),
            launches: 1,
            synchronizations,
            block_threads: self.card.block_x,
            mount_host_ingress_octets: self.mount_host_ingress_octets,
            successor_host_ingress_octets,
            successor_host_egress_octets,
            resident_invariant_octets: self.mount_host_ingress_octets,
            resident_working_octets: successor_host_ingress_octets + successor_host_egress_octets,
            invariant_transport_reuploaded: false,
            cpu_semantic_replay_after_device: false,
            cell_selected_or_ranked: false,
        })
    }
}
