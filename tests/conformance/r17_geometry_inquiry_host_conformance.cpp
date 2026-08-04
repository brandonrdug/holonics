#include "r17_cases.hpp"

#include <holonics/codec/geometry_theory_renderer.hpp>
#include <holonics/organ/geometry_inquiry_law.hpp>

int main() {
  const auto mount = holonics::tests::r17_case(holonics::tests::r17_host_terminal_rest());
  holonics::organ::geometry_inquiry_receipt inquiry{};
  for (std::uint16_t slot = 0; slot < mount.foundation.probe_count; ++slot) {
    inquiry.probes[slot] = holonics::organ::form_geometry_probe(mount.foundation, slot);
  }
  holonics::organ::close_geometry_inquiry(mount.foundation, mount.question, inquiry);
  const auto& plan = inquiry.theory;
  const holonics::codec::geometry_theory_surface surface{plan.passage,
      plan.auxiliary_statement, plan.affine_statement, plan.fractional_statement,
      plan.counterexample_statement, plan.difference_factor, plan.affine_common_square,
      plan.fractional_invariance, plan.coordinate_counterexample, plan.singular_boundary};
  holonics::codec::geometry_theory_face formal{};
  holonics::codec::geometry_theory_explanation explanation{};
  return inquiry.theory_formed && inquiry.returned_probe_count == 32 &&
      inquiry.projective_probe_count == 31 && inquiry.coordinate_counterexamples == 31 &&
      inquiry.singular_probe_count == 1 && inquiry.mode_field_absent &&
      inquiry.expected_answer_absent && holonics::codec::render_geometry_theory(surface, formal) &&
      holonics::codec::render_geometry_explanation(surface, explanation) ? 0 : 1;
}
