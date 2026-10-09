import Holonics.Geometry.FrameTransport
import Holonics.Geometry.Motion
import Holonics.Objects.SourceHolon

/-!
Independent consumer/import check for the exact accepted owners materialized on
public main 3c67beee7f656798f912c974f12c482ea12c5e42. This is validation input,
not a second geometry owner. The actual consuming relations remain in their owners.
Fresh acceptance requires source-matched objects and standard axiom closures for
every query below. No source-only bridge record is imported or kernel certified.
-/

#print axioms Holonics.Geometry.FrameTransport.tube_section_area_vector
#print axioms Holonics.Geometry.FrameTransport.tube_section_flux
#print axioms Holonics.Geometry.FrameTransport.tube_sweep_hasFDerivAt
#print axioms Holonics.Geometry.FrameTransport.tube_sweep_slope_volume
#print axioms Holonics.Geometry.FrameTransport.tube_sweep_actual_volume
#print axioms Holonics.Geometry.FrameTransport.egg_chart_hasFDerivAt
#print axioms Holonics.Geometry.FrameTransport.egg_relative_current_section_flux
#print axioms Holonics.Geometry.FrameTransport.egg_chart_eq_tube_sweep
#print axioms Holonics.Geometry.FrameTransport.egg_jacobian_eq
#print axioms Holonics.Geometry.FrameTransport.egg_jacobian_hasDerivAt
#print axioms Holonics.Geometry.Motion.energy_rate_moving_metric
#print axioms Holonics.Geometry.Motion.finite_work_form_rechart_defect
#print axioms Holonics.Geometry.Motion.finite_work_form_rechart
#print axioms Holonics.Foundation.CausalChord.futureReadForm_pairing
#print axioms Holonics.Foundation.CausalChord.futureReadForm_zero_iff
#print axioms Holonics.Objects.SourceHolon.matrixReader_futureAgreement_iff_zero_futureReadScore
