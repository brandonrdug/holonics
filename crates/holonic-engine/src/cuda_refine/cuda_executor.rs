#[cfg(target_os = "linux")]
use std::ffi::{CStr, c_char};
#[cfg(target_os = "linux")]
use std::ptr;

use super::CudaRefineError;
#[cfg(target_os = "linux")]
use super::PTX;
use super::cuda_driver::{CuContext, CuFunction, CuModule};
#[cfg(target_os = "linux")]
use super::cuda_driver::{
    cuCtxCreate_v2, cuCtxDestroy_v2, cuDeviceGet, cuDeviceGetAttribute, cuDeviceGetCount,
    cuDeviceGetName, cuFuncGetAttribute, cuInit, cuModuleGetFunction, cuModuleLoadData,
    cuModuleUnload, driver,
};
#[cfg(target_os = "linux")]
use super::{
    DEVICE_MAX_GRID_DIM_X, DEVICE_MAX_THREADS_PER_BLOCK, DEVICE_WARP_SIZE,
    FUNCTION_MAX_THREADS_PER_BLOCK,
};

/// **Every distinct reading in the corpus, given a dense identity.**
///
/// Identity `0` is reserved for a terminus before any reading is assigned one, so no reading can
/// collide with it. Built once per `(census, atlas)`; the device compares identities and never
/// reconstructs a reading.
/// The card, mounted once, with the refinement law resident.
pub struct CudaRefineExecutor {
    pub(super) context: CuContext,
    pub(super) module: CuModule,
    pub(super) refine: CuFunction,
    /// The LAW: the material-free quotient every organ with a front shares.
    pub(super) claim: CuFunction,
    pub(super) native_word: CuFunction,
    pub(super) complex_incidence: CuFunction,
    pub(super) addressed_complex_junction: CuFunction,
    pub(super) coupled_complex_parametron: CuFunction,
    pub(super) interval_potential_receiver: CuFunction,
    pub(super) native_trace: CuFunction,
    pub(super) native_ragged_trace: CuFunction,
    pub(super) returned_recurrence: CuFunction,
    pub(super) dynamic_morphology: CuFunction,
    pub(super) condensed_recurrence: CuFunction,
    pub(super) heterogeneous_fusion: CuFunction,
    pub(super) media_candidate_counts: CuFunction,
    pub(super) joint_media_transport: CuFunction,
    pub(super) production_aperture_fronts: CuFunction,
    pub(super) production_aperture_reduction: CuFunction,
    pub(super) quadratic_section_transport: CuFunction,
    pub(super) fixed_section_families: CuFunction,
    pub(super) native_fixed_section_families: CuFunction,
    pub(super) fixed_section_family_reduction: CuFunction,
    pub(super) inference_ecology: CuFunction,
    pub(super) material_operation_world_tube: CuFunction,
    pub(super) contact_pairs: CuFunction,
    pub(super) contact_compare: CuFunction,
    pub(super) optical_incidence: CuFunction,
    pub(super) participant_causal_front: CuFunction,
    pub(super) situated_current_difference: CuFunction,
    pub(super) situated_current_affine_cells: CuFunction,
    pub(super) situated_current_structural_front: CuFunction,
    pub(super) situated_current_causal_front: CuFunction,
    pub(super) affine_barycentric_transport: CuFunction,
    pub(super) membrane_local_contacts: CuFunction,
    pub(super) membrane_radiation: CuFunction,
    pub(super) membrane_boundary_injection: CuFunction,
    pub(super) membrane_boundary_chain_contacts: CuFunction,
    pub(super) membrane_quadratic_moment_form: CuFunction,
    pub(super) membrane_quadratic_moment_contract: CuFunction,
    pub(super) membrane_resident_boundary_restriction_gather: CuFunction,
    pub(super) membrane_observable_form_contract: CuFunction,
    pub(super) membrane_observable_form_transport: CuFunction,
    pub(super) membrane_factored_moment_incidence_transport: CuFunction,
    pub(super) membrane_factored_history_identify: CuFunction,
    pub(super) membrane_factored_history_compact: CuFunction,
    pub(super) membrane_factored_moment_modular_rank: CuFunction,
    pub(super) membrane_factored_moment_modular_rank_select: CuFunction,
    pub(super) membrane_factored_moment_coordinate_residues: CuFunction,
    pub(super) membrane_factored_moment_crt_prepare: CuFunction,
    pub(super) membrane_factored_moment_crt_accumulate: CuFunction,
    pub(super) membrane_factored_moment_crt_advance: CuFunction,
    pub(super) membrane_factored_moment_crt_close: CuFunction,
    pub(super) membrane_factored_moment_signed_crt: CuFunction,
    pub(super) membrane_factored_moment_square_source_projection: CuFunction,
    pub(super) membrane_factored_moment_square_verify: CuFunction,
    pub(super) membrane_factored_moment_target_gather: CuFunction,
    pub(super) membrane_factored_moment_candidate_receivers: CuFunction,
    pub(super) membrane_factored_moment_functional_projection: CuFunction,
    pub(super) membrane_factored_moment_constitutive_aperture: CuFunction,
    pub(super) membrane_factored_moment_functional_dualization: CuFunction,
    pub(super) membrane_factored_moment_functional_pairs: CuFunction,
    pub(super) membrane_factored_moment_functional_receiver_factors: CuFunction,
    pub(super) membrane_factored_moment_functional_receiver_reduce: CuFunction,
    pub(super) membrane_sparse_quadratic_pair_transport: CuFunction,
    pub(super) membrane_sparse_quadratic_diagonal_chronology: CuFunction,
    pub(super) membrane_sparse_quadratic_generator_pair_transport: CuFunction,
    pub(super) membrane_sparse_quadratic_state_generator_pair_transport: CuFunction,
    pub(super) membrane_sparse_quadratic_state_face_restriction_gather: CuFunction,
    pub(super) membrane_sparse_quadratic_state_situated_front_chunks: CuFunction,
    pub(super) membrane_sparse_quadratic_state_returned_face_index: CuFunction,
    pub(super) membrane_sparse_quadratic_state_returned_faces_condition: CuFunction,
    pub(super) membrane_sparse_quadratic_phase_front_lift: CuFunction,
    pub(super) membrane_sparse_quadratic_returned_port_resolve: CuFunction,
    pub(super) membrane_sparse_quadratic_returned_port_condition: CuFunction,
    pub(super) membrane_sparse_quadratic_returned_faces_condition: CuFunction,
    pub(super) membrane_sparse_quadratic_pair_receivers: CuFunction,
    pub(super) membrane_sparse_quadratic_situated_chunks: CuFunction,
    pub(super) membrane_sparse_quadratic_situated_reduce: CuFunction,
    pub(super) membrane_sparse_quadratic_situated_signs: CuFunction,
    pub(super) membrane_sparse_quadratic_native_family_chunks: CuFunction,
    pub(super) membrane_sparse_quadratic_native_potential_chunks: CuFunction,
    pub(super) membrane_sparse_quadratic_situated_front_chunks: CuFunction,
    pub(super) membrane_sparse_quadratic_situated_front_scatter: CuFunction,
    pub(super) membrane_sparse_quadratic_projective_interval_chunks: CuFunction,
    pub(super) membrane_sparse_quadratic_unsigned_interval_reduce: CuFunction,
    pub(super) membrane_sparse_quadratic_projective_interval_pairs: CuFunction,
    pub(super) membrane_sparse_quadratic_projective_interval_select: CuFunction,
    pub(super) membrane_sparse_quadratic_projective_interval_ensure: CuFunction,
    pub(super) membrane_sparse_quadratic_signed_reduce: CuFunction,
    pub(super) membrane_sparse_quadratic_native_receiver_scatter: CuFunction,
    pub(super) membrane_sparse_quadratic_situated_norm_products: CuFunction,
    pub(super) membrane_sparse_quadratic_situated_projective_pairs: CuFunction,
    pub(super) membrane_sparse_quadratic_situated_projective_front_join: CuFunction,
    pub(super) membrane_factor_current_transport: CuFunction,
    pub(super) membrane_generated_port_restriction_collect: CuFunction,
    pub(super) membrane_generated_port_current_condition: CuFunction,
    pub(super) membrane_factor_current_identify: CuFunction,
    pub(super) membrane_factor_current_compact: CuFunction,
    pub(super) membrane_factorized_moment_contract: CuFunction,
    pub(super) membrane_factorized_moment_reduce: CuFunction,
    pub(super) membrane_factored_receiver_boundary_supports: CuFunction,
    pub(super) membrane_boundary_chain_radiation: CuFunction,
    pub(super) membrane_boundary_phase_components: CuFunction,
    pub(super) membrane_boundary_phase_pairs: CuFunction,
    pub(super) membrane_boundary_phase_select: CuFunction,
    pub(super) membrane_situated_output_pairing: CuFunction,
    pub(super) membrane_situated_output_pairing_pairs: CuFunction,
    pub(super) membrane_situated_output_pairing_select: CuFunction,
    pub(super) membrane_boundary_chain_balance: CuFunction,
    pub(super) device_name: String,
    pub(super) block_x: u32,
    pub(super) max_grid_x: u32,
    pub(super) warp: u32,
    pub(super) launches: u64,
    pub(super) owns_context: bool,
}

impl CudaRefineExecutor {
    pub fn new() -> Result<Self, CudaRefineError> {
        #[cfg(not(target_os = "linux"))]
        {
            return Err(CudaRefineError::UnsupportedDevice);
        }
        #[cfg(target_os = "linux")]
        unsafe {
            driver(cuInit(0), "cuInit")?;
            let mut count = 0;
            driver(cuDeviceGetCount(&mut count), "cuDeviceGetCount")?;
            if count <= 0 {
                return Err(CudaRefineError::NoDevice);
            }
            let mut device = 0;
            driver(cuDeviceGet(&mut device, 0), "cuDeviceGet")?;
            let mut raw = [0 as c_char; 256];
            driver(
                cuDeviceGetName(raw.as_mut_ptr(), raw.len() as i32, device),
                "cuDeviceGetName",
            )?;
            let device_name = CStr::from_ptr(raw.as_ptr()).to_string_lossy().into_owned();

            let attribute =
                |selector: i32, operation: &'static str| -> Result<u32, CudaRefineError> {
                    let mut value = 0i32;
                    driver(
                        cuDeviceGetAttribute(&mut value, selector, device),
                        operation,
                    )?;
                    Ok(value.max(0) as u32)
                };
            let device_block = attribute(
                DEVICE_MAX_THREADS_PER_BLOCK,
                "cuDeviceGetAttribute(MAX_THREADS_PER_BLOCK)",
            )?;
            let max_grid_x = attribute(
                DEVICE_MAX_GRID_DIM_X,
                "cuDeviceGetAttribute(MAX_GRID_DIM_X)",
            )?;
            let warp = attribute(DEVICE_WARP_SIZE, "cuDeviceGetAttribute(WARP_SIZE)")?.max(1);

            let mut context = ptr::null_mut();
            driver(cuCtxCreate_v2(&mut context, 0, device), "cuCtxCreate_v2")?;

            let mut image = PTX.to_vec();
            if !image.ends_with(&[0]) {
                image.push(0);
            }
            let mut module = ptr::null_mut();
            if let Err(error) = driver(
                cuModuleLoadData(&mut module, image.as_ptr().cast()),
                "cuModuleLoadData",
            ) {
                let _ = cuCtxDestroy_v2(context);
                return Err(error);
            }
            let mut refine = ptr::null_mut();
            let mut claim = ptr::null_mut();
            let mut native_word = ptr::null_mut();
            let mut complex_incidence = ptr::null_mut();
            let mut addressed_complex_junction = ptr::null_mut();
            let mut coupled_complex_parametron = ptr::null_mut();
            let mut interval_potential_receiver = ptr::null_mut();
            let mut native_trace = ptr::null_mut();
            let mut native_ragged_trace = ptr::null_mut();
            let mut returned_recurrence = ptr::null_mut();
            let mut dynamic_morphology = ptr::null_mut();
            let mut condensed_recurrence = ptr::null_mut();
            let mut heterogeneous_fusion = ptr::null_mut();
            let mut media_candidate_counts = ptr::null_mut();
            let mut joint_media_transport = ptr::null_mut();
            let mut production_aperture_fronts = ptr::null_mut();
            let mut production_aperture_reduction = ptr::null_mut();
            let mut quadratic_section_transport = ptr::null_mut();
            let mut fixed_section_families = ptr::null_mut();
            let mut native_fixed_section_families = ptr::null_mut();
            let mut fixed_section_family_reduction = ptr::null_mut();
            let mut inference_ecology = ptr::null_mut();
            let mut material_operation_world_tube = ptr::null_mut();
            let mut contact_pairs = ptr::null_mut();
            let mut contact_compare = ptr::null_mut();
            let mut optical_incidence = ptr::null_mut();
            let mut participant_causal_front = ptr::null_mut();
            let mut situated_current_difference = ptr::null_mut();
            let mut situated_current_affine_cells = ptr::null_mut();
            let mut situated_current_structural_front = ptr::null_mut();
            let mut situated_current_causal_front = ptr::null_mut();
            let mut affine_barycentric_transport = ptr::null_mut();
            let mut membrane_local_contacts = ptr::null_mut();
            let mut membrane_radiation = ptr::null_mut();
            let mut membrane_boundary_injection = ptr::null_mut();
            let mut membrane_boundary_chain_contacts = ptr::null_mut();
            let mut membrane_quadratic_moment_form = ptr::null_mut();
            let mut membrane_quadratic_moment_contract = ptr::null_mut();
            let mut membrane_resident_boundary_restriction_gather = ptr::null_mut();
            let mut membrane_observable_form_contract = ptr::null_mut();
            let mut membrane_observable_form_transport = ptr::null_mut();
            let mut membrane_factored_moment_incidence_transport = ptr::null_mut();
            let mut membrane_factored_history_identify = ptr::null_mut();
            let mut membrane_factored_history_compact = ptr::null_mut();
            let mut membrane_factored_moment_modular_rank = ptr::null_mut();
            let mut membrane_factored_moment_modular_rank_select = ptr::null_mut();
            let mut membrane_factored_moment_coordinate_residues = ptr::null_mut();
            let mut membrane_factored_moment_crt_prepare = ptr::null_mut();
            let mut membrane_factored_moment_crt_accumulate = ptr::null_mut();
            let mut membrane_factored_moment_crt_advance = ptr::null_mut();
            let mut membrane_factored_moment_crt_close = ptr::null_mut();
            let mut membrane_factored_moment_signed_crt = ptr::null_mut();
            let mut membrane_factored_moment_square_source_projection = ptr::null_mut();
            let mut membrane_factored_moment_square_verify = ptr::null_mut();
            let mut membrane_factored_moment_target_gather = ptr::null_mut();
            let mut membrane_factored_moment_candidate_receivers = ptr::null_mut();
            let mut membrane_factored_moment_functional_projection = ptr::null_mut();
            let mut membrane_factored_moment_constitutive_aperture = ptr::null_mut();
            let mut membrane_factored_moment_functional_dualization = ptr::null_mut();
            let mut membrane_factored_moment_functional_pairs = ptr::null_mut();
            let mut membrane_factored_moment_functional_receiver_factors = ptr::null_mut();
            let mut membrane_factored_moment_functional_receiver_reduce = ptr::null_mut();
            let mut membrane_sparse_quadratic_pair_transport = ptr::null_mut();
            let mut membrane_sparse_quadratic_diagonal_chronology = ptr::null_mut();
            let mut membrane_sparse_quadratic_generator_pair_transport = ptr::null_mut();
            let mut membrane_sparse_quadratic_state_generator_pair_transport = ptr::null_mut();
            let mut membrane_sparse_quadratic_state_face_restriction_gather = ptr::null_mut();
            let mut membrane_sparse_quadratic_state_situated_front_chunks = ptr::null_mut();
            let mut membrane_sparse_quadratic_state_returned_face_index = ptr::null_mut();
            let mut membrane_sparse_quadratic_state_returned_faces_condition = ptr::null_mut();
            let mut membrane_sparse_quadratic_phase_front_lift = ptr::null_mut();
            let mut membrane_sparse_quadratic_returned_port_resolve = ptr::null_mut();
            let mut membrane_sparse_quadratic_returned_port_condition = ptr::null_mut();
            let mut membrane_sparse_quadratic_returned_faces_condition = ptr::null_mut();
            let mut membrane_sparse_quadratic_pair_receivers = ptr::null_mut();
            let mut membrane_sparse_quadratic_situated_chunks = ptr::null_mut();
            let mut membrane_sparse_quadratic_situated_reduce = ptr::null_mut();
            let mut membrane_sparse_quadratic_situated_signs = ptr::null_mut();
            let mut membrane_sparse_quadratic_native_family_chunks = ptr::null_mut();
            let mut membrane_sparse_quadratic_native_potential_chunks = ptr::null_mut();
            let mut membrane_sparse_quadratic_situated_front_chunks = ptr::null_mut();
            let mut membrane_sparse_quadratic_situated_front_scatter = ptr::null_mut();
            let mut membrane_sparse_quadratic_projective_interval_chunks = ptr::null_mut();
            let mut membrane_sparse_quadratic_unsigned_interval_reduce = ptr::null_mut();
            let mut membrane_sparse_quadratic_projective_interval_pairs = ptr::null_mut();
            let mut membrane_sparse_quadratic_projective_interval_select = ptr::null_mut();
            let mut membrane_sparse_quadratic_projective_interval_ensure = ptr::null_mut();
            let mut membrane_sparse_quadratic_signed_reduce = ptr::null_mut();
            let mut membrane_sparse_quadratic_native_receiver_scatter = ptr::null_mut();
            let mut membrane_sparse_quadratic_situated_norm_products = ptr::null_mut();
            let mut membrane_sparse_quadratic_situated_projective_pairs = ptr::null_mut();
            let mut membrane_sparse_quadratic_situated_projective_front_join = ptr::null_mut();
            let mut membrane_factor_current_transport = ptr::null_mut();
            let mut membrane_generated_port_restriction_collect = ptr::null_mut();
            let mut membrane_generated_port_current_condition = ptr::null_mut();
            let mut membrane_factor_current_identify = ptr::null_mut();
            let mut membrane_factor_current_compact = ptr::null_mut();
            let mut membrane_factorized_moment_contract = ptr::null_mut();
            let mut membrane_factorized_moment_reduce = ptr::null_mut();
            let mut membrane_boundary_chain_radiation = ptr::null_mut();
            let mut membrane_factored_receiver_boundary_supports = ptr::null_mut();
            let mut membrane_boundary_phase_components = ptr::null_mut();
            let mut membrane_boundary_phase_pairs = ptr::null_mut();
            let mut membrane_boundary_phase_select = ptr::null_mut();
            let mut membrane_situated_output_pairing = ptr::null_mut();
            let mut membrane_situated_output_pairing_pairs = ptr::null_mut();
            let mut membrane_situated_output_pairing_select = ptr::null_mut();
            let mut membrane_boundary_chain_balance = ptr::null_mut();
            for (slot, symbol, operation) in [
                (
                    &mut refine as *mut CuFunction,
                    c"refine_shell",
                    "cuModuleGetFunction(refine_shell)",
                ),
                (
                    &mut claim as *mut CuFunction,
                    c"claim_identities",
                    "cuModuleGetFunction(claim_identities)",
                ),
                (
                    &mut native_word as *mut CuFunction,
                    c"conduct_native_word",
                    "cuModuleGetFunction(conduct_native_word)",
                ),
                (
                    &mut complex_incidence as *mut CuFunction,
                    c"conduct_complex_incidence",
                    "cuModuleGetFunction(conduct_complex_incidence)",
                ),
                (
                    &mut addressed_complex_junction as *mut CuFunction,
                    c"conduct_addressed_complex_junction",
                    "cuModuleGetFunction(conduct_addressed_complex_junction)",
                ),
                (
                    &mut coupled_complex_parametron as *mut CuFunction,
                    c"conduct_coupled_complex_parametron",
                    "cuModuleGetFunction(conduct_coupled_complex_parametron)",
                ),
                (
                    &mut interval_potential_receiver as *mut CuFunction,
                    c"receive_interval_potential_incidence",
                    "cuModuleGetFunction(receive_interval_potential_incidence)",
                ),
                (
                    &mut native_trace as *mut CuFunction,
                    c"conduct_native_trace",
                    "cuModuleGetFunction(conduct_native_trace)",
                ),
                (
                    &mut native_ragged_trace as *mut CuFunction,
                    c"conduct_native_ragged_trace",
                    "cuModuleGetFunction(conduct_native_ragged_trace)",
                ),
                (
                    &mut returned_recurrence as *mut CuFunction,
                    c"return_and_recur_native",
                    "cuModuleGetFunction(return_and_recur_native)",
                ),
                (
                    &mut dynamic_morphology as *mut CuFunction,
                    c"cultivate_dynamic_morphology",
                    "cuModuleGetFunction(cultivate_dynamic_morphology)",
                ),
                (
                    &mut condensed_recurrence as *mut CuFunction,
                    c"conduct_condensed_recurrences",
                    "cuModuleGetFunction(conduct_condensed_recurrences)",
                ),
                (
                    &mut heterogeneous_fusion as *mut CuFunction,
                    c"conduct_heterogeneous_fusion",
                    "cuModuleGetFunction(conduct_heterogeneous_fusion)",
                ),
                (
                    &mut media_candidate_counts as *mut CuFunction,
                    c"derive_media_candidate_counts",
                    "cuModuleGetFunction(derive_media_candidate_counts)",
                ),
                (
                    &mut joint_media_transport as *mut CuFunction,
                    c"conduct_joint_media_transport",
                    "cuModuleGetFunction(conduct_joint_media_transport)",
                ),
                (
                    &mut production_aperture_fronts as *mut CuFunction,
                    c"conduct_production_aperture_fronts",
                    "cuModuleGetFunction(conduct_production_aperture_fronts)",
                ),
                (
                    &mut production_aperture_reduction as *mut CuFunction,
                    c"reduce_production_aperture_fronts",
                    "cuModuleGetFunction(reduce_production_aperture_fronts)",
                ),
                (
                    &mut quadratic_section_transport as *mut CuFunction,
                    c"conduct_quadratic_section_transport",
                    "cuModuleGetFunction(conduct_quadratic_section_transport)",
                ),
                (
                    &mut fixed_section_families as *mut CuFunction,
                    c"conduct_fixed_section_families",
                    "cuModuleGetFunction(conduct_fixed_section_families)",
                ),
                (
                    &mut native_fixed_section_families as *mut CuFunction,
                    c"conduct_native_fixed_section_families",
                    "cuModuleGetFunction(conduct_native_fixed_section_families)",
                ),
                (
                    &mut fixed_section_family_reduction as *mut CuFunction,
                    c"reduce_fixed_section_families",
                    "cuModuleGetFunction(reduce_fixed_section_families)",
                ),
                (
                    &mut inference_ecology as *mut CuFunction,
                    c"conduct_inference_ecology",
                    "cuModuleGetFunction(conduct_inference_ecology)",
                ),
                (
                    &mut material_operation_world_tube as *mut CuFunction,
                    c"conduct_material_operation_world_tube",
                    "cuModuleGetFunction(conduct_material_operation_world_tube)",
                ),
                (
                    &mut contact_pairs as *mut CuFunction,
                    c"classify_contact_pairs",
                    "cuModuleGetFunction(classify_contact_pairs)",
                ),
                (
                    &mut contact_compare as *mut CuFunction,
                    c"compare_contact_presentations",
                    "cuModuleGetFunction(compare_contact_presentations)",
                ),
                (
                    &mut optical_incidence as *mut CuFunction,
                    c"classify_optical_incidence",
                    "cuModuleGetFunction(classify_optical_incidence)",
                ),
                (
                    &mut participant_causal_front as *mut CuFunction,
                    c"select_participant_causal_front",
                    "cuModuleGetFunction(select_participant_causal_front)",
                ),
                (
                    &mut situated_current_difference as *mut CuFunction,
                    c"differentiate_situated_current_contexts",
                    "cuModuleGetFunction(differentiate_situated_current_contexts)",
                ),
                (
                    &mut situated_current_affine_cells as *mut CuFunction,
                    c"contract_situated_current_affine_cells",
                    "cuModuleGetFunction(contract_situated_current_affine_cells)",
                ),
                (
                    &mut situated_current_structural_front as *mut CuFunction,
                    c"select_situated_current_structural_front",
                    "cuModuleGetFunction(select_situated_current_structural_front)",
                ),
                (
                    &mut situated_current_causal_front as *mut CuFunction,
                    c"select_situated_current_causal_front",
                    "cuModuleGetFunction(select_situated_current_causal_front)",
                ),
                (
                    &mut affine_barycentric_transport as *mut CuFunction,
                    c"conduct_affine_barycentric_transport",
                    "cuModuleGetFunction(conduct_affine_barycentric_transport)",
                ),
                (
                    &mut membrane_local_contacts as *mut CuFunction,
                    c"conduct_membrane_local_contacts",
                    "cuModuleGetFunction(conduct_membrane_local_contacts)",
                ),
                (
                    &mut membrane_radiation as *mut CuFunction,
                    c"gather_membrane_radiation",
                    "cuModuleGetFunction(gather_membrane_radiation)",
                ),
                (
                    &mut membrane_boundary_injection as *mut CuFunction,
                    c"inject_membrane_boundary_current",
                    "cuModuleGetFunction(inject_membrane_boundary_current)",
                ),
                (
                    &mut membrane_boundary_chain_contacts as *mut CuFunction,
                    c"conduct_membrane_boundary_chain_contacts",
                    "cuModuleGetFunction(conduct_membrane_boundary_chain_contacts)",
                ),
                (
                    &mut membrane_quadratic_moment_form as *mut CuFunction,
                    c"form_membrane_quadratic_moments",
                    "cuModuleGetFunction(form_membrane_quadratic_moments)",
                ),
                (
                    &mut membrane_quadratic_moment_contract as *mut CuFunction,
                    c"contract_membrane_quadratic_moments",
                    "cuModuleGetFunction(contract_membrane_quadratic_moments)",
                ),
                (
                    &mut membrane_resident_boundary_restriction_gather as *mut CuFunction,
                    c"gather_membrane_resident_boundary_restrictions",
                    "cuModuleGetFunction(gather_membrane_resident_boundary_restrictions)",
                ),
                (
                    &mut membrane_observable_form_contract as *mut CuFunction,
                    c"contract_membrane_observable_integral_forms",
                    "cuModuleGetFunction(contract_membrane_observable_integral_forms)",
                ),
                (
                    &mut membrane_observable_form_transport as *mut CuFunction,
                    c"transport_membrane_observable_integral_form_factors",
                    "cuModuleGetFunction(transport_membrane_observable_integral_form_factors)",
                ),
                (
                    &mut membrane_factored_moment_incidence_transport as *mut CuFunction,
                    c"transport_membrane_factored_moment_incidence",
                    "cuModuleGetFunction(transport_membrane_factored_moment_incidence)",
                ),
                (
                    &mut membrane_factored_history_identify as *mut CuFunction,
                    c"identify_membrane_equal_factored_history_blocks",
                    "cuModuleGetFunction(identify_membrane_equal_factored_history_blocks)",
                ),
                (
                    &mut membrane_factored_history_compact as *mut CuFunction,
                    c"compact_membrane_equal_factored_history_blocks",
                    "cuModuleGetFunction(compact_membrane_equal_factored_history_blocks)",
                ),
                (
                    &mut membrane_factored_moment_modular_rank as *mut CuFunction,
                    c"derive_membrane_factored_moment_modular_rank",
                    "cuModuleGetFunction(derive_membrane_factored_moment_modular_rank)",
                ),
                (
                    &mut membrane_factored_moment_modular_rank_select as *mut CuFunction,
                    c"select_membrane_factored_moment_modular_rank",
                    "cuModuleGetFunction(select_membrane_factored_moment_modular_rank)",
                ),
                (
                    &mut membrane_factored_moment_coordinate_residues as *mut CuFunction,
                    c"derive_membrane_factored_moment_coordinate_residues",
                    "cuModuleGetFunction(derive_membrane_factored_moment_coordinate_residues)",
                ),
                (
                    &mut membrane_factored_moment_crt_prepare as *mut CuFunction,
                    c"prepare_membrane_factored_moment_crt_chart",
                    "cuModuleGetFunction(prepare_membrane_factored_moment_crt_chart)",
                ),
                (
                    &mut membrane_factored_moment_crt_accumulate as *mut CuFunction,
                    c"accumulate_membrane_factored_moment_crt_chart",
                    "cuModuleGetFunction(accumulate_membrane_factored_moment_crt_chart)",
                ),
                (
                    &mut membrane_factored_moment_crt_advance as *mut CuFunction,
                    c"advance_membrane_factored_moment_crt_chart",
                    "cuModuleGetFunction(advance_membrane_factored_moment_crt_chart)",
                ),
                (
                    &mut membrane_factored_moment_crt_close as *mut CuFunction,
                    c"close_membrane_factored_moment_crt_product",
                    "cuModuleGetFunction(close_membrane_factored_moment_crt_product)",
                ),
                (
                    &mut membrane_factored_moment_signed_crt as *mut CuFunction,
                    c"center_membrane_factored_moment_signed_crt",
                    "cuModuleGetFunction(center_membrane_factored_moment_signed_crt)",
                ),
                (
                    &mut membrane_factored_moment_square_source_projection as *mut CuFunction,
                    c"project_membrane_factored_moment_square_source_residues",
                    "cuModuleGetFunction(project_membrane_factored_moment_square_source_residues)",
                ),
                (
                    &mut membrane_factored_moment_square_verify as *mut CuFunction,
                    c"verify_membrane_factored_moment_reconstruction_squares",
                    "cuModuleGetFunction(verify_membrane_factored_moment_reconstruction_squares)",
                ),
                (
                    &mut membrane_factored_moment_target_gather as *mut CuFunction,
                    c"gather_membrane_factored_moment_target_image",
                    "cuModuleGetFunction(gather_membrane_factored_moment_target_image)",
                ),
                (
                    &mut membrane_factored_moment_candidate_receivers as *mut CuFunction,
                    c"contract_membrane_factored_moment_candidate_receivers",
                    "cuModuleGetFunction(contract_membrane_factored_moment_candidate_receivers)",
                ),
                (
                    &mut membrane_factored_moment_functional_projection as *mut CuFunction,
                    c"project_membrane_factored_moment_candidate_functionals",
                    "cuModuleGetFunction(project_membrane_factored_moment_candidate_functionals)",
                ),
                (
                    &mut membrane_factored_moment_constitutive_aperture as *mut CuFunction,
                    c"measure_membrane_factored_moment_candidate_constitutive_aperture",
                    "cuModuleGetFunction(measure_membrane_factored_moment_candidate_constitutive_aperture)",
                ),
                (
                    &mut membrane_factored_moment_functional_dualization as *mut CuFunction,
                    c"dualize_membrane_factored_moment_candidate_functionals",
                    "cuModuleGetFunction(dualize_membrane_factored_moment_candidate_functionals)",
                ),
                (
                    &mut membrane_factored_moment_functional_pairs as *mut CuFunction,
                    c"contract_membrane_factored_moment_candidate_functional_pairs",
                    "cuModuleGetFunction(contract_membrane_factored_moment_candidate_functional_pairs)",
                ),
                (
                    &mut membrane_factored_moment_functional_receiver_factors as *mut CuFunction,
                    c"scale_membrane_factored_moment_candidate_receiver_factors",
                    "cuModuleGetFunction(scale_membrane_factored_moment_candidate_receiver_factors)",
                ),
                (
                    &mut membrane_factored_moment_functional_receiver_reduce as *mut CuFunction,
                    c"reduce_membrane_factored_moment_candidate_functional_receivers",
                    "cuModuleGetFunction(reduce_membrane_factored_moment_candidate_functional_receivers)",
                ),
                (
                    &mut membrane_sparse_quadratic_pair_transport as *mut CuFunction,
                    c"transport_membrane_sparse_quadratic_pairs",
                    "cuModuleGetFunction(transport_membrane_sparse_quadratic_pairs)",
                ),
                (
                    &mut membrane_sparse_quadratic_diagonal_chronology as *mut CuFunction,
                    c"form_membrane_sparse_quadratic_diagonal_chronology",
                    "cuModuleGetFunction(form_membrane_sparse_quadratic_diagonal_chronology)",
                ),
                (
                    &mut membrane_sparse_quadratic_generator_pair_transport as *mut CuFunction,
                    c"transport_membrane_sparse_quadratic_generator_pairs",
                    "cuModuleGetFunction(transport_membrane_sparse_quadratic_generator_pairs)",
                ),
                (
                    &mut membrane_sparse_quadratic_state_generator_pair_transport
                        as *mut CuFunction,
                    c"transport_membrane_sparse_quadratic_state_generator_pairs",
                    "cuModuleGetFunction(transport_membrane_sparse_quadratic_state_generator_pairs)",
                ),
                (
                    &mut membrane_sparse_quadratic_state_face_restriction_gather as *mut CuFunction,
                    c"gather_membrane_sparse_quadratic_state_addressed_face_restrictions",
                    "cuModuleGetFunction(gather_membrane_sparse_quadratic_state_addressed_face_restrictions)",
                ),
                (
                    &mut membrane_sparse_quadratic_state_situated_front_chunks as *mut CuFunction,
                    c"form_membrane_sparse_quadratic_state_addressed_situated_front_chunks",
                    "cuModuleGetFunction(form_membrane_sparse_quadratic_state_addressed_situated_front_chunks)",
                ),
                (
                    &mut membrane_sparse_quadratic_state_returned_face_index as *mut CuFunction,
                    c"index_membrane_sparse_quadratic_returned_state_faces",
                    "cuModuleGetFunction(index_membrane_sparse_quadratic_returned_state_faces)",
                ),
                (
                    &mut membrane_sparse_quadratic_state_returned_faces_condition
                        as *mut CuFunction,
                    c"condition_membrane_sparse_quadratic_state_addressed_pairs_by_returned_faces",
                    "cuModuleGetFunction(condition_membrane_sparse_quadratic_state_addressed_pairs_by_returned_faces)",
                ),
                (
                    &mut membrane_sparse_quadratic_phase_front_lift as *mut CuFunction,
                    c"lift_membrane_phase_front_to_addressed_faces",
                    "cuModuleGetFunction(lift_membrane_phase_front_to_addressed_faces)",
                ),
                (
                    &mut membrane_sparse_quadratic_returned_port_resolve as *mut CuFunction,
                    c"resolve_membrane_sparse_quadratic_returned_port",
                    "cuModuleGetFunction(resolve_membrane_sparse_quadratic_returned_port)",
                ),
                (
                    &mut membrane_sparse_quadratic_returned_port_condition as *mut CuFunction,
                    c"condition_membrane_sparse_quadratic_pairs_by_returned_port",
                    "cuModuleGetFunction(condition_membrane_sparse_quadratic_pairs_by_returned_port)",
                ),
                (
                    &mut membrane_sparse_quadratic_returned_faces_condition as *mut CuFunction,
                    c"condition_membrane_sparse_quadratic_pairs_by_returned_faces",
                    "cuModuleGetFunction(condition_membrane_sparse_quadratic_pairs_by_returned_faces)",
                ),
                (
                    &mut membrane_sparse_quadratic_pair_receivers as *mut CuFunction,
                    c"contract_membrane_sparse_quadratic_pair_receivers",
                    "cuModuleGetFunction(contract_membrane_sparse_quadratic_pair_receivers)",
                ),
                (
                    &mut membrane_sparse_quadratic_situated_chunks as *mut CuFunction,
                    c"form_membrane_sparse_quadratic_situated_chunks",
                    "cuModuleGetFunction(form_membrane_sparse_quadratic_situated_chunks)",
                ),
                (
                    &mut membrane_sparse_quadratic_situated_reduce as *mut CuFunction,
                    c"reduce_membrane_sparse_quadratic_situated_chunks",
                    "cuModuleGetFunction(reduce_membrane_sparse_quadratic_situated_chunks)",
                ),
                (
                    &mut membrane_sparse_quadratic_situated_signs as *mut CuFunction,
                    c"mark_membrane_sparse_quadratic_situated_signs",
                    "cuModuleGetFunction(mark_membrane_sparse_quadratic_situated_signs)",
                ),
                (
                    &mut membrane_sparse_quadratic_native_family_chunks as *mut CuFunction,
                    c"form_membrane_sparse_quadratic_native_family_chunks",
                    "cuModuleGetFunction(form_membrane_sparse_quadratic_native_family_chunks)",
                ),
                (
                    &mut membrane_sparse_quadratic_native_potential_chunks as *mut CuFunction,
                    c"form_membrane_sparse_quadratic_native_potential_chunks",
                    "cuModuleGetFunction(form_membrane_sparse_quadratic_native_potential_chunks)",
                ),
                (
                    &mut membrane_sparse_quadratic_situated_front_chunks as *mut CuFunction,
                    c"form_membrane_sparse_quadratic_situated_front_chunks",
                    "cuModuleGetFunction(form_membrane_sparse_quadratic_situated_front_chunks)",
                ),
                (
                    &mut membrane_sparse_quadratic_situated_front_scatter as *mut CuFunction,
                    c"scatter_membrane_sparse_quadratic_situated_front",
                    "cuModuleGetFunction(scatter_membrane_sparse_quadratic_situated_front)",
                ),
                (
                    &mut membrane_sparse_quadratic_projective_interval_chunks as *mut CuFunction,
                    c"form_membrane_sparse_quadratic_projective_interval_chunks",
                    "cuModuleGetFunction(form_membrane_sparse_quadratic_projective_interval_chunks)",
                ),
                (
                    &mut membrane_sparse_quadratic_unsigned_interval_reduce as *mut CuFunction,
                    c"reduce_membrane_sparse_quadratic_unsigned_intervals",
                    "cuModuleGetFunction(reduce_membrane_sparse_quadratic_unsigned_intervals)",
                ),
                (
                    &mut membrane_sparse_quadratic_projective_interval_pairs as *mut CuFunction,
                    c"compare_membrane_sparse_quadratic_projective_interval_pairs",
                    "cuModuleGetFunction(compare_membrane_sparse_quadratic_projective_interval_pairs)",
                ),
                (
                    &mut membrane_sparse_quadratic_projective_interval_select as *mut CuFunction,
                    c"select_membrane_sparse_quadratic_projective_interval_front",
                    "cuModuleGetFunction(select_membrane_sparse_quadratic_projective_interval_front)",
                ),
                (
                    &mut membrane_sparse_quadratic_projective_interval_ensure as *mut CuFunction,
                    c"ensure_membrane_sparse_quadratic_projective_interval_front",
                    "cuModuleGetFunction(ensure_membrane_sparse_quadratic_projective_interval_front)",
                ),
                (
                    &mut membrane_sparse_quadratic_signed_reduce as *mut CuFunction,
                    c"reduce_membrane_sparse_quadratic_signed_sections",
                    "cuModuleGetFunction(reduce_membrane_sparse_quadratic_signed_sections)",
                ),
                (
                    &mut membrane_sparse_quadratic_native_receiver_scatter as *mut CuFunction,
                    c"scatter_membrane_sparse_quadratic_native_receivers",
                    "cuModuleGetFunction(scatter_membrane_sparse_quadratic_native_receivers)",
                ),
                (
                    &mut membrane_sparse_quadratic_situated_norm_products as *mut CuFunction,
                    c"form_membrane_sparse_quadratic_situated_norm_products",
                    "cuModuleGetFunction(form_membrane_sparse_quadratic_situated_norm_products)",
                ),
                (
                    &mut membrane_sparse_quadratic_situated_projective_pairs as *mut CuFunction,
                    c"compare_membrane_sparse_quadratic_situated_projective_pairs",
                    "cuModuleGetFunction(compare_membrane_sparse_quadratic_situated_projective_pairs)",
                ),
                (
                    &mut membrane_sparse_quadratic_situated_projective_front_join
                        as *mut CuFunction,
                    c"combine_membrane_sparse_quadratic_projective_pair_fronts",
                    "cuModuleGetFunction(combine_membrane_sparse_quadratic_projective_pair_fronts)",
                ),
                (
                    &mut membrane_factor_current_transport as *mut CuFunction,
                    c"transport_membrane_factor_current_sections",
                    "cuModuleGetFunction(transport_membrane_factor_current_sections)",
                ),
                (
                    &mut membrane_generated_port_restriction_collect as *mut CuFunction,
                    c"collect_membrane_selected_generated_port_restrictions",
                    "cuModuleGetFunction(collect_membrane_selected_generated_port_restrictions)",
                ),
                (
                    &mut membrane_generated_port_current_condition as *mut CuFunction,
                    c"condition_membrane_factor_current_sections_by_generated_ports",
                    "cuModuleGetFunction(condition_membrane_factor_current_sections_by_generated_ports)",
                ),
                (
                    &mut membrane_factor_current_identify as *mut CuFunction,
                    c"identify_membrane_equal_factor_current_sections",
                    "cuModuleGetFunction(identify_membrane_equal_factor_current_sections)",
                ),
                (
                    &mut membrane_factor_current_compact as *mut CuFunction,
                    c"compact_membrane_equal_factor_current_sections",
                    "cuModuleGetFunction(compact_membrane_equal_factor_current_sections)",
                ),
                (
                    &mut membrane_factorized_moment_contract as *mut CuFunction,
                    c"contract_membrane_factorized_quadratic_moments",
                    "cuModuleGetFunction(contract_membrane_factorized_quadratic_moments)",
                ),
                (
                    &mut membrane_factorized_moment_reduce as *mut CuFunction,
                    c"reduce_membrane_factorized_quadratic_moments",
                    "cuModuleGetFunction(reduce_membrane_factorized_quadratic_moments)",
                ),
                (
                    &mut membrane_factored_receiver_boundary_supports as *mut CuFunction,
                    c"prepare_membrane_factored_receiver_boundary_supports",
                    "cuModuleGetFunction(prepare_membrane_factored_receiver_boundary_supports)",
                ),
                (
                    &mut membrane_boundary_chain_radiation as *mut CuFunction,
                    c"gather_membrane_boundary_chain_radiation",
                    "cuModuleGetFunction(gather_membrane_boundary_chain_radiation)",
                ),
                (
                    &mut membrane_boundary_phase_components as *mut CuFunction,
                    c"form_membrane_boundary_phase_components",
                    "cuModuleGetFunction(form_membrane_boundary_phase_components)",
                ),
                (
                    &mut membrane_boundary_phase_pairs as *mut CuFunction,
                    c"compare_membrane_boundary_phase_pairs",
                    "cuModuleGetFunction(compare_membrane_boundary_phase_pairs)",
                ),
                (
                    &mut membrane_boundary_phase_select as *mut CuFunction,
                    c"select_membrane_boundary_phase_front",
                    "cuModuleGetFunction(select_membrane_boundary_phase_front)",
                ),
                (
                    &mut membrane_situated_output_pairing as *mut CuFunction,
                    c"form_membrane_situated_output_pairing",
                    "cuModuleGetFunction(form_membrane_situated_output_pairing)",
                ),
                (
                    &mut membrane_situated_output_pairing_pairs as *mut CuFunction,
                    c"compare_membrane_situated_output_pairing_pairs",
                    "cuModuleGetFunction(compare_membrane_situated_output_pairing_pairs)",
                ),
                (
                    &mut membrane_situated_output_pairing_select as *mut CuFunction,
                    c"select_membrane_situated_output_pairing_front",
                    "cuModuleGetFunction(select_membrane_situated_output_pairing_front)",
                ),
                (
                    &mut membrane_boundary_chain_balance as *mut CuFunction,
                    c"balance_membrane_boundary_chain",
                    "cuModuleGetFunction(balance_membrane_boundary_chain)",
                ),
            ] {
                if let Err(error) = driver(
                    cuModuleGetFunction(slot, module, symbol.as_ptr()),
                    operation,
                ) {
                    let _ = cuModuleUnload(module);
                    let _ = cuCtxDestroy_v2(context);
                    return Err(error);
                }
            }

            // The block must fit whichever the kernel and the device admit fewer of, down to a
            // whole warp: a partial warp issues with idle lanes.
            let mut kernel_block = device_block;
            for function in [
                refine,
                claim,
                native_word,
                complex_incidence,
                addressed_complex_junction,
                coupled_complex_parametron,
                interval_potential_receiver,
                native_trace,
                native_ragged_trace,
                returned_recurrence,
                dynamic_morphology,
                condensed_recurrence,
                heterogeneous_fusion,
                media_candidate_counts,
                joint_media_transport,
                production_aperture_fronts,
                production_aperture_reduction,
                quadratic_section_transport,
                fixed_section_families,
                native_fixed_section_families,
                fixed_section_family_reduction,
                inference_ecology,
                material_operation_world_tube,
                contact_pairs,
                contact_compare,
                optical_incidence,
                participant_causal_front,
                situated_current_difference,
                situated_current_affine_cells,
                situated_current_structural_front,
                situated_current_causal_front,
                affine_barycentric_transport,
                membrane_local_contacts,
                membrane_radiation,
                membrane_boundary_injection,
                membrane_boundary_chain_contacts,
                membrane_quadratic_moment_form,
                membrane_quadratic_moment_contract,
                membrane_resident_boundary_restriction_gather,
                membrane_observable_form_contract,
                membrane_observable_form_transport,
                membrane_factored_moment_incidence_transport,
                membrane_factored_history_identify,
                membrane_factored_history_compact,
                membrane_factored_moment_modular_rank,
                membrane_factored_moment_modular_rank_select,
                membrane_factored_moment_coordinate_residues,
                membrane_factored_moment_crt_prepare,
                membrane_factored_moment_crt_accumulate,
                membrane_factored_moment_crt_advance,
                membrane_factored_moment_crt_close,
                membrane_factored_moment_signed_crt,
                membrane_factored_moment_square_source_projection,
                membrane_factored_moment_square_verify,
                membrane_factored_moment_target_gather,
                membrane_factored_moment_candidate_receivers,
                membrane_factored_moment_functional_projection,
                membrane_factored_moment_constitutive_aperture,
                membrane_factored_moment_functional_dualization,
                membrane_factored_moment_functional_pairs,
                membrane_factored_moment_functional_receiver_factors,
                membrane_factored_moment_functional_receiver_reduce,
                membrane_sparse_quadratic_pair_transport,
                membrane_sparse_quadratic_diagonal_chronology,
                membrane_sparse_quadratic_generator_pair_transport,
                membrane_sparse_quadratic_state_generator_pair_transport,
                membrane_sparse_quadratic_state_face_restriction_gather,
                membrane_sparse_quadratic_state_situated_front_chunks,
                membrane_sparse_quadratic_state_returned_face_index,
                membrane_sparse_quadratic_state_returned_faces_condition,
                membrane_sparse_quadratic_phase_front_lift,
                membrane_sparse_quadratic_returned_port_resolve,
                membrane_sparse_quadratic_returned_port_condition,
                membrane_sparse_quadratic_returned_faces_condition,
                membrane_sparse_quadratic_pair_receivers,
                membrane_sparse_quadratic_situated_chunks,
                membrane_sparse_quadratic_situated_reduce,
                membrane_sparse_quadratic_situated_signs,
                membrane_sparse_quadratic_native_family_chunks,
                membrane_sparse_quadratic_native_potential_chunks,
                membrane_sparse_quadratic_situated_front_chunks,
                membrane_sparse_quadratic_situated_front_scatter,
                membrane_sparse_quadratic_projective_interval_chunks,
                membrane_sparse_quadratic_unsigned_interval_reduce,
                membrane_sparse_quadratic_projective_interval_pairs,
                membrane_sparse_quadratic_projective_interval_select,
                membrane_sparse_quadratic_projective_interval_ensure,
                membrane_sparse_quadratic_signed_reduce,
                membrane_sparse_quadratic_native_receiver_scatter,
                membrane_sparse_quadratic_situated_norm_products,
                membrane_sparse_quadratic_situated_projective_pairs,
                membrane_sparse_quadratic_situated_projective_front_join,
                membrane_factor_current_transport,
                membrane_generated_port_restriction_collect,
                membrane_generated_port_current_condition,
                membrane_factor_current_identify,
                membrane_factor_current_compact,
                membrane_factorized_moment_contract,
                membrane_factorized_moment_reduce,
                membrane_factored_receiver_boundary_supports,
                membrane_boundary_chain_radiation,
                membrane_boundary_phase_components,
                membrane_boundary_phase_pairs,
                membrane_boundary_phase_select,
                membrane_situated_output_pairing,
                membrane_situated_output_pairing_pairs,
                membrane_situated_output_pairing_select,
                membrane_boundary_chain_balance,
            ] {
                let mut value = 0i32;
                driver(
                    cuFuncGetAttribute(&mut value, FUNCTION_MAX_THREADS_PER_BLOCK, function),
                    "cuFuncGetAttribute(MAX_THREADS_PER_BLOCK)",
                )?;
                kernel_block = kernel_block.min(value.max(0) as u32);
            }
            let block_x = (kernel_block / warp).max(1) * warp;

            Ok(Self {
                context,
                module,
                refine,
                claim,
                native_word,
                complex_incidence,
                addressed_complex_junction,
                coupled_complex_parametron,
                interval_potential_receiver,
                native_trace,
                native_ragged_trace,
                returned_recurrence,
                dynamic_morphology,
                condensed_recurrence,
                heterogeneous_fusion,
                media_candidate_counts,
                joint_media_transport,
                production_aperture_fronts,
                production_aperture_reduction,
                quadratic_section_transport,
                fixed_section_families,
                native_fixed_section_families,
                fixed_section_family_reduction,
                inference_ecology,
                material_operation_world_tube,
                contact_pairs,
                contact_compare,
                optical_incidence,
                participant_causal_front,
                situated_current_difference,
                situated_current_affine_cells,
                situated_current_structural_front,
                situated_current_causal_front,
                affine_barycentric_transport,
                membrane_local_contacts,
                membrane_radiation,
                membrane_boundary_injection,
                membrane_boundary_chain_contacts,
                membrane_quadratic_moment_form,
                membrane_quadratic_moment_contract,
                membrane_resident_boundary_restriction_gather,
                membrane_observable_form_contract,
                membrane_observable_form_transport,
                membrane_factored_moment_incidence_transport,
                membrane_factored_history_identify,
                membrane_factored_history_compact,
                membrane_factored_moment_modular_rank,
                membrane_factored_moment_modular_rank_select,
                membrane_factored_moment_coordinate_residues,
                membrane_factored_moment_crt_prepare,
                membrane_factored_moment_crt_accumulate,
                membrane_factored_moment_crt_advance,
                membrane_factored_moment_crt_close,
                membrane_factored_moment_signed_crt,
                membrane_factored_moment_square_source_projection,
                membrane_factored_moment_square_verify,
                membrane_factored_moment_target_gather,
                membrane_factored_moment_candidate_receivers,
                membrane_factored_moment_functional_projection,
                membrane_factored_moment_constitutive_aperture,
                membrane_factored_moment_functional_dualization,
                membrane_factored_moment_functional_pairs,
                membrane_factored_moment_functional_receiver_factors,
                membrane_factored_moment_functional_receiver_reduce,
                membrane_sparse_quadratic_pair_transport,
                membrane_sparse_quadratic_diagonal_chronology,
                membrane_sparse_quadratic_generator_pair_transport,
                membrane_sparse_quadratic_state_generator_pair_transport,
                membrane_sparse_quadratic_state_face_restriction_gather,
                membrane_sparse_quadratic_state_situated_front_chunks,
                membrane_sparse_quadratic_state_returned_face_index,
                membrane_sparse_quadratic_state_returned_faces_condition,
                membrane_sparse_quadratic_phase_front_lift,
                membrane_sparse_quadratic_returned_port_resolve,
                membrane_sparse_quadratic_returned_port_condition,
                membrane_sparse_quadratic_returned_faces_condition,
                membrane_sparse_quadratic_pair_receivers,
                membrane_sparse_quadratic_situated_chunks,
                membrane_sparse_quadratic_situated_reduce,
                membrane_sparse_quadratic_situated_signs,
                membrane_sparse_quadratic_native_family_chunks,
                membrane_sparse_quadratic_native_potential_chunks,
                membrane_sparse_quadratic_situated_front_chunks,
                membrane_sparse_quadratic_situated_front_scatter,
                membrane_sparse_quadratic_projective_interval_chunks,
                membrane_sparse_quadratic_unsigned_interval_reduce,
                membrane_sparse_quadratic_projective_interval_pairs,
                membrane_sparse_quadratic_projective_interval_select,
                membrane_sparse_quadratic_projective_interval_ensure,
                membrane_sparse_quadratic_signed_reduce,
                membrane_sparse_quadratic_native_receiver_scatter,
                membrane_sparse_quadratic_situated_norm_products,
                membrane_sparse_quadratic_situated_projective_pairs,
                membrane_sparse_quadratic_situated_projective_front_join,
                membrane_factor_current_transport,
                membrane_generated_port_restriction_collect,
                membrane_generated_port_current_condition,
                membrane_factor_current_identify,
                membrane_factor_current_compact,
                membrane_factorized_moment_contract,
                membrane_factorized_moment_reduce,
                membrane_factored_receiver_boundary_supports,
                membrane_boundary_chain_radiation,
                membrane_boundary_phase_components,
                membrane_boundary_phase_pairs,
                membrane_boundary_phase_select,
                membrane_situated_output_pairing,
                membrane_situated_output_pairing_pairs,
                membrane_situated_output_pairing_select,
                membrane_boundary_chain_balance,
                device_name,
                block_x,
                max_grid_x,
                warp,
                launches: 0,
                owns_context: true,
            })
        }
    }

    pub fn device_name(&self) -> &str {
        &self.device_name
    }

    pub fn block_threads(&self) -> u32 {
        self.block_x
    }

    pub fn warp_size(&self) -> u32 {
        self.warp
    }

    pub fn launches(&self) -> u64 {
        self.launches
    }

    /// Lend the exact already-mounted CUDA context/module to a bounded resident leaf.  The fork
    /// owns no driver resources and may only be used while its originating executor remains
    /// alive inside a composite owner.
    pub(super) fn fork_same_context(&self) -> Self {
        Self {
            context: self.context,
            module: self.module,
            refine: self.refine,
            claim: self.claim,
            native_word: self.native_word,
            complex_incidence: self.complex_incidence,
            addressed_complex_junction: self.addressed_complex_junction,
            coupled_complex_parametron: self.coupled_complex_parametron,
            participant_causal_front: self.participant_causal_front,
            situated_current_difference: self.situated_current_difference,
            situated_current_affine_cells: self.situated_current_affine_cells,
            situated_current_structural_front: self.situated_current_structural_front,
            situated_current_causal_front: self.situated_current_causal_front,
            affine_barycentric_transport: self.affine_barycentric_transport,
            membrane_local_contacts: self.membrane_local_contacts,
            membrane_radiation: self.membrane_radiation,
            membrane_boundary_injection: self.membrane_boundary_injection,
            membrane_boundary_chain_contacts: self.membrane_boundary_chain_contacts,
            membrane_quadratic_moment_form: self.membrane_quadratic_moment_form,
            membrane_quadratic_moment_contract: self.membrane_quadratic_moment_contract,
            membrane_resident_boundary_restriction_gather: self
                .membrane_resident_boundary_restriction_gather,
            membrane_observable_form_contract: self.membrane_observable_form_contract,
            membrane_observable_form_transport: self.membrane_observable_form_transport,
            membrane_factored_moment_incidence_transport: self
                .membrane_factored_moment_incidence_transport,
            membrane_factored_history_identify: self.membrane_factored_history_identify,
            membrane_factored_history_compact: self.membrane_factored_history_compact,
            membrane_factored_moment_modular_rank: self.membrane_factored_moment_modular_rank,
            membrane_factored_moment_modular_rank_select: self
                .membrane_factored_moment_modular_rank_select,
            membrane_factored_moment_coordinate_residues: self
                .membrane_factored_moment_coordinate_residues,
            membrane_factored_moment_crt_prepare: self.membrane_factored_moment_crt_prepare,
            membrane_factored_moment_crt_accumulate: self.membrane_factored_moment_crt_accumulate,
            membrane_factored_moment_crt_advance: self.membrane_factored_moment_crt_advance,
            membrane_factored_moment_crt_close: self.membrane_factored_moment_crt_close,
            membrane_factored_moment_signed_crt: self.membrane_factored_moment_signed_crt,
            membrane_factored_moment_square_source_projection: self
                .membrane_factored_moment_square_source_projection,
            membrane_factored_moment_square_verify: self.membrane_factored_moment_square_verify,
            membrane_factored_moment_target_gather: self.membrane_factored_moment_target_gather,
            membrane_factored_moment_candidate_receivers: self
                .membrane_factored_moment_candidate_receivers,
            membrane_factored_moment_functional_projection: self
                .membrane_factored_moment_functional_projection,
            membrane_factored_moment_constitutive_aperture: self
                .membrane_factored_moment_constitutive_aperture,
            membrane_factored_moment_functional_dualization: self
                .membrane_factored_moment_functional_dualization,
            membrane_factored_moment_functional_pairs: self
                .membrane_factored_moment_functional_pairs,
            membrane_factored_moment_functional_receiver_factors: self
                .membrane_factored_moment_functional_receiver_factors,
            membrane_factored_moment_functional_receiver_reduce: self
                .membrane_factored_moment_functional_receiver_reduce,
            membrane_sparse_quadratic_pair_transport: self.membrane_sparse_quadratic_pair_transport,
            membrane_sparse_quadratic_diagonal_chronology: self
                .membrane_sparse_quadratic_diagonal_chronology,
            membrane_sparse_quadratic_generator_pair_transport: self
                .membrane_sparse_quadratic_generator_pair_transport,
            membrane_sparse_quadratic_state_generator_pair_transport: self
                .membrane_sparse_quadratic_state_generator_pair_transport,
            membrane_sparse_quadratic_state_face_restriction_gather: self
                .membrane_sparse_quadratic_state_face_restriction_gather,
            membrane_sparse_quadratic_state_situated_front_chunks: self
                .membrane_sparse_quadratic_state_situated_front_chunks,
            membrane_sparse_quadratic_state_returned_face_index: self
                .membrane_sparse_quadratic_state_returned_face_index,
            membrane_sparse_quadratic_state_returned_faces_condition: self
                .membrane_sparse_quadratic_state_returned_faces_condition,
            membrane_sparse_quadratic_phase_front_lift: self
                .membrane_sparse_quadratic_phase_front_lift,
            membrane_sparse_quadratic_returned_port_resolve: self
                .membrane_sparse_quadratic_returned_port_resolve,
            membrane_sparse_quadratic_returned_port_condition: self
                .membrane_sparse_quadratic_returned_port_condition,
            membrane_sparse_quadratic_returned_faces_condition: self
                .membrane_sparse_quadratic_returned_faces_condition,
            membrane_sparse_quadratic_pair_receivers: self.membrane_sparse_quadratic_pair_receivers,
            membrane_sparse_quadratic_situated_chunks: self
                .membrane_sparse_quadratic_situated_chunks,
            membrane_sparse_quadratic_situated_reduce: self
                .membrane_sparse_quadratic_situated_reduce,
            membrane_sparse_quadratic_situated_signs: self.membrane_sparse_quadratic_situated_signs,
            membrane_sparse_quadratic_native_family_chunks: self
                .membrane_sparse_quadratic_native_family_chunks,
            membrane_sparse_quadratic_native_potential_chunks: self
                .membrane_sparse_quadratic_native_potential_chunks,
            membrane_sparse_quadratic_situated_front_chunks: self
                .membrane_sparse_quadratic_situated_front_chunks,
            membrane_sparse_quadratic_situated_front_scatter: self
                .membrane_sparse_quadratic_situated_front_scatter,
            membrane_sparse_quadratic_projective_interval_chunks: self
                .membrane_sparse_quadratic_projective_interval_chunks,
            membrane_sparse_quadratic_unsigned_interval_reduce: self
                .membrane_sparse_quadratic_unsigned_interval_reduce,
            membrane_sparse_quadratic_projective_interval_pairs: self
                .membrane_sparse_quadratic_projective_interval_pairs,
            membrane_sparse_quadratic_projective_interval_select: self
                .membrane_sparse_quadratic_projective_interval_select,
            membrane_sparse_quadratic_projective_interval_ensure: self
                .membrane_sparse_quadratic_projective_interval_ensure,
            membrane_sparse_quadratic_signed_reduce: self.membrane_sparse_quadratic_signed_reduce,
            membrane_sparse_quadratic_native_receiver_scatter: self
                .membrane_sparse_quadratic_native_receiver_scatter,
            membrane_sparse_quadratic_situated_norm_products: self
                .membrane_sparse_quadratic_situated_norm_products,
            membrane_sparse_quadratic_situated_projective_pairs: self
                .membrane_sparse_quadratic_situated_projective_pairs,
            membrane_sparse_quadratic_situated_projective_front_join: self
                .membrane_sparse_quadratic_situated_projective_front_join,
            membrane_factor_current_transport: self.membrane_factor_current_transport,
            membrane_generated_port_restriction_collect: self
                .membrane_generated_port_restriction_collect,
            membrane_generated_port_current_condition: self
                .membrane_generated_port_current_condition,
            membrane_factor_current_identify: self.membrane_factor_current_identify,
            membrane_factor_current_compact: self.membrane_factor_current_compact,
            membrane_factorized_moment_contract: self.membrane_factorized_moment_contract,
            membrane_factorized_moment_reduce: self.membrane_factorized_moment_reduce,
            membrane_factored_receiver_boundary_supports: self
                .membrane_factored_receiver_boundary_supports,
            membrane_boundary_chain_radiation: self.membrane_boundary_chain_radiation,
            membrane_boundary_phase_components: self.membrane_boundary_phase_components,
            membrane_boundary_phase_pairs: self.membrane_boundary_phase_pairs,
            membrane_boundary_phase_select: self.membrane_boundary_phase_select,
            membrane_situated_output_pairing: self.membrane_situated_output_pairing,
            membrane_situated_output_pairing_pairs: self.membrane_situated_output_pairing_pairs,
            membrane_situated_output_pairing_select: self.membrane_situated_output_pairing_select,
            membrane_boundary_chain_balance: self.membrane_boundary_chain_balance,
            interval_potential_receiver: self.interval_potential_receiver,
            native_trace: self.native_trace,
            native_ragged_trace: self.native_ragged_trace,
            returned_recurrence: self.returned_recurrence,
            dynamic_morphology: self.dynamic_morphology,
            condensed_recurrence: self.condensed_recurrence,
            heterogeneous_fusion: self.heterogeneous_fusion,
            media_candidate_counts: self.media_candidate_counts,
            joint_media_transport: self.joint_media_transport,
            production_aperture_fronts: self.production_aperture_fronts,
            production_aperture_reduction: self.production_aperture_reduction,
            quadratic_section_transport: self.quadratic_section_transport,
            fixed_section_families: self.fixed_section_families,
            native_fixed_section_families: self.native_fixed_section_families,
            fixed_section_family_reduction: self.fixed_section_family_reduction,
            inference_ecology: self.inference_ecology,
            material_operation_world_tube: self.material_operation_world_tube,
            contact_pairs: self.contact_pairs,
            contact_compare: self.contact_compare,
            optical_incidence: self.optical_incidence,
            device_name: self.device_name.clone(),
            block_x: self.block_x,
            max_grid_x: self.max_grid_x,
            warp: self.warp,
            launches: 0,
            owns_context: false,
        }
    }

    pub(super) fn grid_for(&self, work: u64) -> Result<u32, CudaRefineError> {
        let blocks = work.div_ceil(u64::from(self.block_x.max(1)));
        if blocks > u64::from(self.max_grid_x) {
            return Err(CudaRefineError::ExtentOverflow { work });
        }
        Ok(blocks as u32)
    }
}

impl Drop for CudaRefineExecutor {
    fn drop(&mut self) {
        if !self.owns_context {
            return;
        }
        unsafe {
            let _ = super::cuda_driver::cuCtxSetCurrent(self.context);
            let _ = super::cuda_driver::cuModuleUnload(self.module);
            let _ = super::cuda_driver::cuCtxDestroy_v2(self.context);
        }
    }
}
