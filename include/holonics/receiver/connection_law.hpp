#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/receiver/geometry_exact.hpp>

namespace holonics::receiver {

[[nodiscard]] HOLONICS_CALLABLE constexpr connection_receipt carry_connection(
    const connection_program& program) noexcept {
  connection_receipt result{};
  result.start_endpoint = program.start_endpoint;
  result.end_endpoint = program.end_endpoint;
  result.initial_fiber = program.initial_fiber;
  result.lineage = program.lineage;
  std::uint64_t positive = 0;
  std::uint64_t negative = 0;
  for (std::size_t edge = 0; edge < connection_edge_capacity; ++edge) {
    std::uint64_t& side = program.edge_negative[edge] ? negative : positive;
    if (!geometry_add(side, program.edge_magnitudes[edge].value(), side)) { return {}; }
  }
  result.finite_holonomy = geometry_signed_difference(positive, negative);
  result.endpoint_equal = program.start_endpoint == program.end_endpoint;
  result.curvature_certified = result.endpoint_equal &&
      program.path_support == program.plaquette_boundary_support;
  if (result.curvature_certified) { result.local_curvature = result.finite_holonomy; }
  if (!result.finite_holonomy.negative) {
    std::uint64_t transported = 0;
    if (!geometry_add(program.initial_fiber.value(),
            result.finite_holonomy.magnitude.value(), transported)) {
      return {};
    }
    result.transported_fiber = exact::word{transported};
  } else if (program.initial_fiber.value() >= result.finite_holonomy.magnitude.value()) {
    result.transported_fiber = exact::word{
        program.initial_fiber.value() - result.finite_holonomy.magnitude.value()};
  }
  result.open_path_residual_is_holonomy =
      program.open_start == program.open_end && program.open_path_residual.value() != 0;
  result.global_triviality_open = true;
  return result;
}

}  // namespace holonics::receiver
