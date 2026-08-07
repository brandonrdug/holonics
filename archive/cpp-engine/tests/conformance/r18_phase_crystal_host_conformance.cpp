#include "r18_cases.hpp"

#include <holonics/codec/phase_crystal_renderer.hpp>
#include <holonics/organ/phase_crystal_law.hpp>

int main() {
  const auto mount = holonics::tests::r18_case(holonics::tests::r18_host_geometry_rest());
  holonics::organ::phase_crystal_receipt inquiry{};
  for (std::uint16_t slot = 0; slot < mount.foundation.case_count; ++slot) {
    inquiry.cases[slot] = holonics::organ::form_phase_crystal_case(mount.foundation, slot);
  }
  holonics::organ::close_phase_crystal_inquiry(mount.foundation, mount.question, inquiry);
  const auto& plan = inquiry.theory;
  const holonics::codec::phase_crystal_surface surface{plan.passage,
      plan.diagonal_statement, plan.coprime_statement, plan.population_statement,
      plan.series_statement, plan.diagonal_lcm, plan.coprime_full_tour,
      plan.cell_population_product, plan.seam_cancellation, plan.gauss_transport,
      plan.projection_distinguished};
  holonics::codec::phase_crystal_face formal{};
  holonics::codec::phase_crystal_explanation explanation{};
  return inquiry.theory_formed && inquiry.returned_cases == 16 &&
      inquiry.shared_factor_cases == 2 && inquiry.dilation_control_exact &&
      inquiry.turn_control_exact && inquiry.reversal_control_exact &&
      holonics::codec::render_phase_crystal_theory(surface, formal) &&
      holonics::codec::render_phase_crystal_explanation(surface, explanation) ? 0 : 1;
}
