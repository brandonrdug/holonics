import Holonics.Geometry.FrameTransport
import Holonics.Geometry.Motion

/-! Import and audit the two freshly compiled actual owners. No copied
frame or finite-work proof is supplied by this consumer. Refs #62,#73. -/

#check Holonics.Geometry.Motion.finite_work_form_rechart
#print axioms Holonics.Geometry.Motion.finite_work_form_rechart
#check Holonics.Geometry.Motion.affine_quadratic_work
#print axioms Holonics.Geometry.Motion.affine_quadratic_work
#check Holonics.Geometry.FrameTransport.tube_section_area_vector
#print axioms Holonics.Geometry.FrameTransport.tube_section_area_vector
#check Holonics.Geometry.FrameTransport.tube_section_flux
#print axioms Holonics.Geometry.FrameTransport.tube_section_flux
#check Holonics.Geometry.FrameTransport.tube_section_hasFDerivAt
#print axioms Holonics.Geometry.FrameTransport.tube_section_hasFDerivAt
#check Holonics.Geometry.FrameTransport.tube_section_fderiv_first
#print axioms Holonics.Geometry.FrameTransport.tube_section_fderiv_first
#check Holonics.Geometry.FrameTransport.tube_section_fderiv_second
#print axioms Holonics.Geometry.FrameTransport.tube_section_fderiv_second
#check Holonics.Geometry.FrameTransport.tube_section_actual_area
#print axioms Holonics.Geometry.FrameTransport.tube_section_actual_area
#check Holonics.Geometry.FrameTransport.tube_section_actual_flux
#print axioms Holonics.Geometry.FrameTransport.tube_section_actual_flux
