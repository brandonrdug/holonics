use super::*;

use crate::cuda_refine::membrane_boundary_plan::BoundaryCompletionPlan;

/// Checked byte extent for a resident unsigned-limb section.
pub(super) fn buffer_octets(population: usize, limbs: usize) -> Result<usize, CudaRefineError> {
    population
        .checked_mul(limbs)
        .and_then(|held| held.checked_mul(std::mem::size_of::<u32>()))
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)
}

/// Device workspace for one boundary completion.
///
/// The fields are deliberately named after the kernel sections they own. Keeping every
/// allocation in this owner preserves the resident lifetime across all default-stream launches
/// and the terminal image completion.
pub(super) struct BoundaryCompletionWorkspace {
    pub(super) obstruction: Buffer,
    pub(super) action_sign: Buffer,
    pub(super) action_limbs: Buffer,
    pub(super) reflected_sign: Buffer,
    pub(super) reflected_limbs: Buffer,
    pub(super) opaque_receiver_sign: Buffer,
    pub(super) opaque_receiver_limbs: Buffer,
    pub(super) receiver_norm_sign: Buffer,
    pub(super) receiver_norm_limbs: Buffer,
    pub(super) contact_real_sign: Buffer,
    pub(super) contact_real_limbs: Buffer,
    pub(super) contact_imaginary_sign: Buffer,
    pub(super) contact_imaginary_limbs: Buffer,
    pub(super) support_real_sign: Buffer,
    pub(super) support_real_limbs: Buffer,
    pub(super) support_imaginary_sign: Buffer,
    pub(super) support_imaginary_limbs: Buffer,
    pub(super) port_real_sign: Buffer,
    pub(super) port_real_limbs: Buffer,
    pub(super) port_imaginary_sign: Buffer,
    pub(super) port_imaginary_limbs: Buffer,
    pub(super) joint_real_sign: Buffer,
    pub(super) joint_real_limbs: Buffer,
    pub(super) joint_imaginary_sign: Buffer,
    pub(super) joint_imaginary_limbs: Buffer,
    pub(super) port_action_sign: Buffer,
    pub(super) port_action_limbs: Buffer,
    pub(super) port_reflected_sign: Buffer,
    pub(super) port_reflected_limbs: Buffer,
    pub(super) port_receiver_sign: Buffer,
    pub(super) port_receiver_limbs: Buffer,
    pub(super) port_receiver_norm_sign: Buffer,
    pub(super) port_receiver_norm_limbs: Buffer,
    pub(super) compatibility_sign: Buffer,
    pub(super) compatibility_limbs: Buffer,
    pub(super) phase_norm_limbs: Buffer,
    pub(super) phase_locked: Buffer,
    pub(super) phase_pair_dominates: Buffer,
    pub(super) phase_square_scratch: Buffer,
    pub(super) phase_left_cross_scratch: Buffer,
    pub(super) phase_right_cross_scratch: Buffer,
    pub(super) situated_pairing_sign: Buffer,
    pub(super) situated_pairing_limbs: Buffer,
    pub(super) situated_pairing_imaginary_scratch: Buffer,
    pub(super) situated_pairing_front: Buffer,
    pub(super) situated_native_phase_front: Option<Buffer>,
    pub(super) situated_projective_norm_product: Option<Buffer>,
    pub(super) situated_projective_current_self: Option<Buffer>,
    pub(super) situated_projective_ingress_self: Option<Buffer>,
    pub(super) incoming_real_sign_device: Buffer,
    pub(super) incoming_real_limbs_device: Buffer,
    pub(super) incoming_imaginary_sign_device: Buffer,
    pub(super) incoming_imaginary_limbs_device: Buffer,
    pub(super) stored_real_sign: Buffer,
    pub(super) stored_real_limbs: Buffer,
    pub(super) stored_imaginary_sign: Buffer,
    pub(super) stored_imaginary_limbs: Buffer,
    pub(super) balance_scratch: Buffer,
}

impl BoundaryCompletionWorkspace {
    pub(super) fn allocate(
        word: &ResidentMembraneInteriorWord,
        plan: &BoundaryCompletionPlan,
    ) -> Result<Self, CudaRefineError> {
        driver(
            unsafe { cuCtxSetCurrent(word.card.context) },
            "cuCtxSetCurrent",
        )?;
        let obstruction = Buffer::of(&[0_u32])?;
        let action_sign = Buffer::alloc(plan.support_family_population)?;
        let action_limbs = Buffer::alloc(buffer_octets(
            plan.support_family_population,
            plan.overlap_limb_count,
        )?)?;
        let reflected_sign = Buffer::alloc(plan.support_family_population)?;
        let reflected_limbs = Buffer::alloc(buffer_octets(
            plan.support_family_population,
            plan.overlap_limb_count,
        )?)?;
        let opaque_receiver_sign = Buffer::alloc(plan.support_receiver_population)?;
        let opaque_receiver_limbs = Buffer::alloc(buffer_octets(
            plan.support_receiver_population,
            plan.overlap_limb_count,
        )?)?;
        let receiver_norm_sign = Buffer::alloc(plan.support_receiver_population)?;
        let receiver_norm_limbs = Buffer::alloc(buffer_octets(
            plan.support_receiver_population,
            plan.overlap_limb_count,
        )?)?;
        let contact_real_sign = Buffer::alloc(plan.support_family_population)?;
        let contact_real_limbs = Buffer::alloc(buffer_octets(
            plan.support_family_population,
            plan.contact_limb_count,
        )?)?;
        let contact_imaginary_sign = Buffer::alloc(plan.support_family_population)?;
        let contact_imaginary_limbs = Buffer::alloc(buffer_octets(
            plan.support_family_population,
            plan.contact_limb_count,
        )?)?;
        let support_real_sign = Buffer::alloc(plan.support_count)?;
        let support_real_limbs = Buffer::alloc(buffer_octets(
            plan.support_count,
            plan.radiation_limb_count,
        )?)?;
        let support_imaginary_sign = Buffer::alloc(plan.support_count)?;
        let support_imaginary_limbs = Buffer::alloc(buffer_octets(
            plan.support_count,
            plan.radiation_limb_count,
        )?)?;
        let port_real_sign = Buffer::alloc(plan.port_population)?;
        let port_real_limbs = Buffer::alloc(buffer_octets(
            plan.port_population,
            plan.radiation_limb_count,
        )?)?;
        let port_imaginary_sign = Buffer::alloc(plan.port_population)?;
        let port_imaginary_limbs = Buffer::alloc(buffer_octets(
            plan.port_population,
            plan.radiation_limb_count,
        )?)?;
        let joint_real_sign = Buffer::alloc(1)?;
        let joint_real_limbs = Buffer::alloc(buffer_octets(1, plan.radiation_limb_count)?)?;
        let joint_imaginary_sign = Buffer::alloc(1)?;
        let joint_imaginary_limbs = Buffer::alloc(buffer_octets(1, plan.radiation_limb_count)?)?;
        let port_action_sign = Buffer::alloc(plan.port_family_population)?;
        let port_action_limbs = Buffer::alloc(buffer_octets(
            plan.port_family_population,
            plan.overlap_limb_count,
        )?)?;
        let port_reflected_sign = Buffer::alloc(plan.port_family_population)?;
        let port_reflected_limbs = Buffer::alloc(buffer_octets(
            plan.port_family_population,
            plan.overlap_limb_count,
        )?)?;
        let port_receiver_sign = Buffer::alloc(plan.port_receiver_population)?;
        let port_receiver_limbs = Buffer::alloc(buffer_octets(
            plan.port_receiver_population,
            plan.overlap_limb_count,
        )?)?;
        let port_receiver_norm_sign = Buffer::alloc(plan.port_receiver_population)?;
        let port_receiver_norm_limbs = Buffer::alloc(buffer_octets(
            plan.port_receiver_population,
            plan.overlap_limb_count,
        )?)?;
        let compatibility_sign = Buffer::alloc(plan.component_population)?;
        let compatibility_limbs = Buffer::alloc(buffer_octets(
            plan.component_population,
            plan.compatibility_limb_count,
        )?)?;
        let phase_norm_limbs = Buffer::alloc(buffer_octets(
            plan.component_population,
            plan.norm_limb_count,
        )?)?;
        let phase_locked = Buffer::alloc(plan.port_population)?;
        let phase_pair_dominates = Buffer::alloc(plan.phase_pair_population)?;
        let phase_square_scratch = Buffer::alloc(buffer_octets(
            plan.phase_pair_population,
            plan.square_limb_count,
        )?)?;
        let phase_left_cross_scratch = Buffer::alloc(buffer_octets(
            plan.phase_pair_population,
            plan.cross_limb_count,
        )?)?;
        let phase_right_cross_scratch = Buffer::alloc(buffer_octets(
            plan.phase_pair_population,
            plan.cross_limb_count,
        )?)?;
        let situated_pairing_sign = Buffer::alloc(plan.situated_population)?;
        let situated_pairing_limbs = Buffer::alloc(buffer_octets(
            plan.situated_population,
            plan.situated_pairing_limb_count,
        )?)?;
        let situated_pairing_imaginary_scratch = Buffer::alloc(buffer_octets(
            plan.situated_population,
            plan.situated_pairing_limb_count,
        )?)?;
        let situated_pairing_front = Buffer::alloc(plan.situated_population)?;
        let situated_native_phase_front = plan
            .native_sparse_boundary
            .as_ref()
            .map(|_| Buffer::alloc(plan.situated_population))
            .transpose()?;
        let situated_projective_norm_product = plan
            .situated_projective_dimensions
            .as_ref()
            .map(|(_, limbs, _, _)| Buffer::alloc(buffer_octets(plan.situated_population, *limbs)?))
            .transpose()?;
        let situated_projective_current_self = plan
            .situated_projective_dimensions
            .as_ref()
            .map(|_| {
                Buffer::alloc(buffer_octets(
                    plan.situated_population,
                    plan.situated_pairing_limb_count,
                )?)
            })
            .transpose()?;
        let situated_projective_ingress_self = plan
            .situated_projective_dimensions
            .as_ref()
            .map(|_| {
                Buffer::alloc(buffer_octets(
                    plan.situated_population,
                    plan.situated_pairing_limb_count,
                )?)
            })
            .transpose()?;
        let incoming_real_sign_device = Buffer::of(&[plan.incoming_real_sign])?;
        let incoming_real_limbs_device = Buffer::of(&plan.incoming_real_limbs)?;
        let incoming_imaginary_sign_device = Buffer::of(&[plan.incoming_imaginary_sign])?;
        let incoming_imaginary_limbs_device = Buffer::of(&plan.incoming_imaginary_limbs)?;
        let stored_real_sign = Buffer::alloc(1)?;
        let stored_real_limbs = Buffer::alloc(buffer_octets(1, plan.stored_limb_count)?)?;
        let stored_imaginary_sign = Buffer::alloc(1)?;
        let stored_imaginary_limbs = Buffer::alloc(buffer_octets(1, plan.stored_limb_count)?)?;
        let balance_scratch = Buffer::alloc(buffer_octets(1, plan.stored_limb_count)?)?;
        if trace_configuration().holonics_phase_trace {
            eprintln!("uar2-boundary-workspace-admitted");
        }
        Ok(Self {
            obstruction,
            action_sign,
            action_limbs,
            reflected_sign,
            reflected_limbs,
            opaque_receiver_sign,
            opaque_receiver_limbs,
            receiver_norm_sign,
            receiver_norm_limbs,
            contact_real_sign,
            contact_real_limbs,
            contact_imaginary_sign,
            contact_imaginary_limbs,
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
            phase_pair_dominates,
            phase_square_scratch,
            phase_left_cross_scratch,
            phase_right_cross_scratch,
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
        })
    }
}
