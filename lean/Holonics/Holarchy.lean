import Holonics.Holarchy.Join
import Holonics.Holarchy.View
import Holonics.Holarchy.Receipt
import Holonics.Holarchy.Reception
import Holonics.Holarchy.Hearing
import Holonics.Holarchy.Globe

/-!
# The Holarchy

[definition] `docs/ELEMENTARY_OBJECTS.md` §10–11 and §7, over the Holon owners of
`Holonics.Framework.HolonObject` and the aeon owners of `Holonics.Aeon`. The Holarchy modules
live in namespace `Holonics.HolarchyCore`; the receipt and reception modules, which are the
receiver's operations of #72, live in namespace `Holonics.Receiver` (they sit in this directory
because reception joins two Holons, a source and a receiver, the smallest Holarchy).

* `Holarchy.Join` — a `Constituent` is a port Holon with its complex, interior, port units and
  faces, navigators and pumps; `interconnect` reads both constituents and returns a `Holarchy`
  (the typed declaration of the two retained constituents and its proof of gluing) or a typed
  `GluingDefect`; the whole is again a constituent, with the navigators joined and the pumps on the
  joint clock, and its parametric orientation is the lift of the navigators' clock torus.
* `Holarchy.View` — `view receiver grain aeon section`: the receiver ticks where an aeon of the
  parametric complex crosses its section, cutting it into epochs; `count` under a certified
  partition; `refine` through a restriction of grains; the shared-face flux cancels exactly once
  at every grain.
* `Holarchy.Receipt` — receipts over regions, each reading with its clock exponent and frame;
  `Ratio.between` after the common transport, exact under composition, and group-valued frame
  transports in the gauge chart.
* `Holarchy.Reception` — `interact` solves the joint midpoint step for both next states or refuses a
  singular step, and returns the face, the receipt, the boundary bond, the certified power
  balance and the unresolved fibre; the moving-receiver rate along the law; `HolonLaw.receive` is
  the zero-storage specialization.
* `Holarchy.Hearing` — hearing, listening and nullity on the receiver: `Heard`, `Null` and
  `Listened` against a present face and a reached-action map; `HearingLaw` with its present face
  and admitted future family; the future-null differences are null now, what changes no retained
  state is future-null, the reached action is a lawful standing exactly when every unlistened
  difference is future-null (so heard-but-not-listened refutes it), `range F* = (ker F)^⊥`, and the
  zero-storage receiver hears without storing (namespace `Holonics.Receiver.Hearing`).
* `Holarchy.Globe` — a block of a Holarchy's grain is a constituent region whose boundary map is
  the view's interface; a globe exactly when coupled and not determined, with the linear criterion
  and a globe of an actual Holarchy. The relative completeness theorem stays owed in #62.

No axioms are added.
-/

section Audit
open Holonics.HolarchyCore Holonics.Receiver
#print axioms interfacePower_cancels_iff
#print axioms gainLink_isDirac
#print axioms joinHolon_one
#print axioms Holarchy.power_balance
#print axioms Holarchy.balance_is_sum
#print axioms interface_obstructed_iff
#print axioms interface_plural_iff
#print axioms CellEmbedding.flux_pullback
#print axioms CellEmbedding.restrict_exact
#print axioms CellEmbedding.m₂_ne_zero
#print axioms OnJointClock.closes
#print axioms OnJointClock.lock
#print axioms incommensurate_rates_never_close
#print axioms GluingDefect.not_glues
#print axioms JoinDeclaration.faceFlows_join_iff
#print axioms Holarchy.whole_flux
#print axioms Holarchy.sharedFace_silent
#print axioms Holarchy.sharedPort_face_join
#print axioms Holarchy.wholeConstituent_pumpRate
#print axioms interconnect_ok_iff
#print axioms interconnect_ok_retains
#print axioms interconnect_error_of_not_glues
#print axioms base_glues
#print axioms pumped_glues
#print axioms pumped_pumps_lock
#print axioms unitMismatch_witness
#print axioms uncancelledPower_witness
#print axioms nonCommutingCells_witness
#print axioms degenerateCells_witness
#print axioms uncoveredCells_witness
#print axioms unidentifiedSharedFace_witness
#print axioms strayOverlap_witness
#print axioms sharedFaceUncancelled_witness
#print axioms incompatibleClocks_witness
#print axioms plural_interface_witness
#print axioms obstructed_interface_witness
#print axioms unique_interface_witness
#print axioms certified_count_eq_faces
#print axioms certified_count_le_cells
#print axioms sum_blockFlux
#print axioms total_flux_grain_independent
#print axioms shared_face_cancels
#print axioms interior_face_silent
#print axioms blockFlux_stokes
#print axioms blockFlux_exact
#print axioms refine_flux
#print axioms view_ticks
#print axioms view_unresolved_singleton_iff
#print axioms holarchy_view_flux
#print axioms infinite_witness
#print axioms uncovered_witness
#print axioms overlapping_witness
#print axioms blind_witness
#print axioms refine_defect_witness
#print axioms count_stable_while_faces_move
#print axioms continents_and_islands
#print axioms count_stable_representative_moves
#print axioms padic_quotient_card
#print axioms padic_two_restrictions_differ
#print axioms between_reframe_projectivelyEq
#print axioms between_reclock
#print axioms between_reclock_count
#print axioms rate_against_count_is_clock_dependent
#print axioms between_comp
#print axioms between_comp_projectivelyEq
#print axioms between_comp_through_zero
#print axioms raw_comparison_is_frame_dependent
#print axioms between_log_comp
#print axioms between_log_winding
#print axioms logFibre_between_reframe
#print axioms between_refuses_log
#print axioms betweenGauge_reframe
#print axioms betweenGauge_comp
#print axioms gauge_frames_do_not_commute
#print axioms jointStep_iff
#print axioms solveStep_unique
#print axioms interact_ok_iff
#print axioms interact_solves
#print axioms boundaryBond_power
#print axioms readStep_stored_split
#print axioms readStep_passive
#print axioms zero_storage_receiver_is_passive_reading
#print axioms moving_receiver_rate
#print axioms moving_receiver_rate_of_law
#print axioms reception_changes_both
#print axioms singular_step_refused
#print axioms active_element_is_not_passive
#print axioms unresolved_fibre_is_plural
#print axioms Hearing.null_of_factors
#print axioms Hearing.HearingLaw.future_nil
#print axioms Hearing.HearingLaw.futureNull_le_ker_present
#print axioms Hearing.HearingLaw.futureNull_of_retain_eq
#print axioms Hearing.HearingLaw.act_is_standing_iff
#print axioms Hearing.HearingLaw.heard_not_listened_refutes_standing
#print axioms Hearing.mem_pulledBack_iff
#print axioms Hearing.zero_storage_receiver_hears_without_storing
#print axioms constituentMembrane_boundsInterior
#print axioms constituent_no_exact_flux
#print axioms blockMembrane_gauss
#print axioms constituentRegion_observe
#print axioms holarchyGlobe_iff_coupled_notDetermined
#print axioms ofAdditive_coupled_iff
#print axioms ofAdditive_notDetermined_iff
#print axioms constituent_agree_iff
#print axioms constituent_coupled_iff
#print axioms constituent_notDetermined_iff
#print axioms holarchyGlobe_iff_linear
#print axioms globeDecl_glues
#print axioms globeHolarchy_left_block_is_globe
#print axioms globeHolarchy_right_block_is_not_globe
#print axioms tube_is_not_a_constituent
#print axioms hollow_is_not_a_constituent
end Audit
