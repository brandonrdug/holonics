#include "r19_cases.hpp"

#include <holonics/codec/characteristic_renderer.hpp>
#include <holonics/organ/characteristic_law.hpp>

int main() {
  const auto mount = holonics::tests::r19_case(holonics::tests::r19_host_phase_rest());
  holonics::organ::characteristic_receipt inquiry{};
  for (std::uint16_t slot = 0; slot < mount.foundation.case_count; ++slot) {
    inquiry.cases[slot] = holonics::organ::form_characteristic_case(
        mount.foundation, slot);
  }
  holonics::organ::close_characteristic_inquiry(mount.foundation, mount.question, inquiry);
  const auto& plan = inquiry.theory;
  const holonics::codec::characteristic_surface surface{plan.passage,
      plan.diagonal_factor, plan.weighted_cycle, plan.matrix_controls,
      plan.discriminants_typed, plan.gauss_indicial, plan.lineage_retained};
  holonics::codec::characteristic_face formal{};
  holonics::codec::characteristic_explanation explanation{};
  return inquiry.theory_formed && inquiry.returned_cases == 16 &&
      inquiry.repeated_mode_cases == 2 && inquiry.simple_mode_cases == 14 &&
      inquiry.scalar.exact && inquiry.matrices.exact && inquiry.indicial.exact &&
      holonics::codec::render_characteristic_theory(surface, formal) &&
      holonics::codec::render_characteristic_explanation(surface, explanation) ? 0 : 1;
}
