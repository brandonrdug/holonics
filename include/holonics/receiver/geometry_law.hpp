#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/receiver/connection_law.hpp>
#include <holonics/receiver/extended_carrier_law.hpp>
#include <holonics/receiver/hypergeometric_law.hpp>
#include <holonics/receiver/information_geometry_law.hpp>
#include <holonics/receiver/projective_swing_law.hpp>
#include <holonics/receiver/projection_law.hpp>
#include <holonics/receiver/sameness_law.hpp>

namespace holonics::receiver {

[[nodiscard]] HOLONICS_CALLABLE constexpr geometry_obstruction validate_geometry_program(
    const geometry_program& program) noexcept {
  if (program.identity.value() == 0 || !program.swing.field_carrier ||
      program.swing.path.value() == 0 ||
      !swing_detail::distinct_four(program.swing.points) ||
      program.sameness.digest_mask.value() == 0 ||
      program.projection.receiver_masks[0].value() == 0 ||
      program.projection.receiver_masks[1].value() == 0 ||
      program.projection.lineage.value() == 0 ||
      program.connection.path_support.value() == 0 ||
      program.connection.lineage.value() == 0 ||
      program.hypergeometric.family != solution_family::gauss ||
      program.hypergeometric.term_count == 0 ||
      program.hypergeometric.term_count > hypergeometric_term_capacity ||
      program.hypergeometric.initial_coefficient.second.value() == 0 ||
      program.carrier.line_carrier.value() == 0 ||
      program.carrier.sheet_carrier.value() == 0 ||
      program.carrier.higher_carrier.value() == 0 ||
      program.information.metric[0].second.value() == 0 ||
      program.information.metric[1].second.value() == 0 ||
      program.information.first_support.value() == 0 ||
      program.information.missing_relativistic_obligations.value() == 0) {
    return geometry_obstruction::invalid_program;
  }
  std::uint64_t first = 0;
  std::uint64_t second = 0;
  if (!geometry_multiply(program.swing.frame[0].value(),
          program.swing.frame[3].value(), first) ||
      !geometry_multiply(program.swing.frame[1].value(),
          program.swing.frame[2].value(), second) || first <= second) {
    return geometry_obstruction::invalid_program;
  }
  return geometry_obstruction::none;
}

}  // namespace holonics::receiver
