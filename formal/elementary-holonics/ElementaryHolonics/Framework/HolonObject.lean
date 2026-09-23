import ElementaryHolonics.Holon.Port
import ElementaryHolonics.Holon.Dirac
import ElementaryHolonics.Holon.Complex
import ElementaryHolonics.Holon.Element
import ElementaryHolonics.Holon.Generator
import ElementaryHolonics.Holon.Restriction
import ElementaryHolonics.Holon.Law
import ElementaryHolonics.Holon.Conformance
import ElementaryHolonics.Holon.Deposition
import ElementaryHolonics.Holon.Reaction
import ElementaryHolonics.Holon.Cayley

/-!
# The Holon object

[definition] The foundation of `docs/ELEMENTARY_OBJECTS.md` §"The Holon as one object": a Holon
is its law and ports — complex and connection (`Holon.Complex`), ports and power (`Holon.Port`),
Dirac interconnection (`Holon.Dirac`), element relations and balances (`Holon.Element`),
generators and clock jumps (`Holon.Generator`), restrictions (`Holon.Restriction`), the five laws
(`Holon.Law`), the existing owners as instances (`Holon.Conformance`) deposition under
learning (`Holon.Deposition`) the workless reaction (`Holon.Reaction`) and its implicit
Cayley step (`Holon.Cayley`). Namespace
`Soma.Holonics.HolonCore`. No axioms are added.
-/

section Audit
open Soma.Holonics.HolonCore
#print axioms bondForm_nondegenerate
#print axioms mem_range_iff_annihilators_vanish
#print axioms IsDirac.power_eq_zero
#print axioms skewGraph_isDirac
#print axioms tellegen
#print axioms kirchhoff_isDirac
#print axioms gyrator_witness
#print axioms identity_graph_not_dirac
#print axioms zero_not_dirac
#print axioms triangle_witness
#print axioms orthogonal_inf
#print axioms compose_isDirac
#print axioms link_isDirac
#print axioms pairedD_isDirac
#print axioms interconnect_isDirac
#print axioms interconnect_power
#print axioms orthogonal_kernelForm
#print axioms kernelForm_isDirac
#print axioms skewGraph_eq_kernelForm
#print axioms skewGraph_kernel_hypotheses
#print axioms kirchhoff_eq_kernelForm
#print axioms IsDirac.reindex
#print axioms triangle_kernelForm
#print axioms gyrator_chain_witness
#print axioms dA_squared
#print axioms connection_isDirac
#print axioms exact_closed_iff_flat
#print axioms pure_gauge_is_flat
#print axioms curved_witness
#print axioms PortHolon.power_balance
#print axioms PortHolon.passive
#print axioms hasDerivAt_storageEnergy
#print axioms PortHolon.energy_balance
#print axioms PortHolon.energy_balance_const
#print axioms midpoint_balance
#print axioms backwardEuler_balance
#print axioms backwardEuler_defect_witness
#print axioms ball_image
#print axioms jump_lossless
#print axioms jump_carries_winding
#print axioms jumps_are_carries
#print axioms clockPassage_jumps_lossless
#print axioms power_pushforward
#print axioms IsMorphism.comp
#print axioms scale_square_pow
#print axioms shift_has_no_coarse_generator
#print axioms diagonal_square
#print axioms kron_exact
#print axioms series_path_restriction
#print axioms storageEnergy_blocks
#print axioms dissipation_blocks
#print axioms PortHolon.mem_interconnect
#print axioms passiveCoholon_isDirac
#print axioms passive_reading
#print axioms active_receiver_law
#print axioms advance_law
#print axioms pullback_law
#print axioms medium_admits
#print axioms medium_rate_agrees
#print axioms two_media_witness
#print axioms diffusion_dissipates
#print axioms ssm_port_output
#print axioms lc_pump_work
#print axioms pairContact_resistive
#print axioms comp_is_port_identification
#print axioms exists_cycleMatrix
#print axioms kirchhoff_is_kernelForm
#print axioms walkRead_connection
#print axioms cell_curvature
#print axioms connectionIncidence_isDirac
#print axioms seam_curvature_witness
#print axioms PortHolon.energy_balance_fderiv
#print axioms quartic_storage_effort
#print axioms graphD_isDirac
#print axioms negEffort_isDirac
#print axioms mem_pushforwardD
#print axioms pushforwardD_isDirac
#print axioms gyrator_projection_witness
#print axioms maxwell_gauss
#print axioms triangle_face_complex
#print axioms maxwell_balance
#print axioms hat_casimir
#print axioms navierStokes_balance
#print axioms deposition_work
#print axioms commit_balance
#print axioms learned_rate_form
#print axioms learned_energy_balance
#print axioms energy_product_bound
#print axioms committed_energy_bound
#print axioms product_le_exp_sum
#print axioms normal_law_divergence_witness
#print axioms clipNeg_nonpos
#print axioms clipNeg_of_nonpos
#print axioms projectPassive_passive
#print axioms projectPassive_of_passive
#print axioms projected_committed_energy_bound
#print axioms clipNeg_commute
#print axioms congruenceClip_eq
#print axioms congruenceClip_nonpos
#print axioms congruence_diag
#print axioms congruenceClip_of_nonpos
#print axioms projectPassiveCongruence_passive
#print axioms projectPassiveCongruence_of_passive
#print axioms certified_committed_energy_bound
#print axioms congruence_vs_eigen_witness
#print axioms re_sum_antiConj
#print axioms re_herm_skew
#print axioms eq_zero_of_herm_zero
#print axioms bilinear_reaction_workless_iff_zero
#print axioms skewReaction_skew
#print axioms skewReaction_workless
#print axioms realify_skew
#print axioms reaction_balance
#print axioms skewPart_skew
#print axioms skewPart_of_skew
#print axioms skewPart_idem
#print axioms skewPart_orthogonal
#print axioms runaway_witness
#print axioms cayley_denominator_det
#print axioms cayley_isometry_rel
#print axioms cayley_isometry
#print axioms cayley_isometry_real
#print axioms midpoint_reaction_balance
#print axioms explicit_step_growth
#print axioms explicit_growth_witness
#print axioms rayleigh_le
#print axioms shift_passive_iff
#print axioms shifted_committed_energy_bound
#print axioms recentre_contains
#print axioms device_containment
#print axioms key_contraction
#print axioms resolvent_bound
#print axioms cayley_contraction
#print axioms cayley_bijective
#print axioms inner_devK
#print axioms drive_balance
#print axioms device_radius
#print axioms adjoint_radius
end Audit
