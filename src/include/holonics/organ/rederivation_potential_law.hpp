#pragma once

#include <holonics/exact/integer_division.hpp>
#include <holonics/organ/rederivation_receipt.hpp>

namespace holonics::organ::rederivation_potential_detail {

[[nodiscard]] HOLONICS_CALLABLE inline std::int32_t
absolute(std::int32_t value) noexcept {
  return value < 0 ? -value : value;
}

HOLONICS_CALLABLE inline void
derive(const lattice_problem_card &card,
       const polygon_rederivation_receipt &polygon,
       const rederivation_workspace &workspace,
       potential_rederivation_receipt &out) noexcept {
  const auto selected = card.potential_polygon;
  if (selected >= rederivation_polygon_count)
    return;
  rederivation_point interior[2]{};
  std::uint8_t interior_count = 0;
  for (std::uint8_t x = 0; x < rederivation_lattice_x_capacity; ++x)
    for (std::uint8_t y = 0; y < rederivation_lattice_y_capacity; ++y) {
      const auto &point = workspace.lattice[selected][1][x][y];
      if (point.in_box && point.included && !point.boundary &&
          interior_count < 2)
        interior[interior_count++] = {static_cast<std::int16_t>(x),
                                      static_cast<std::int16_t>(y)};
    }
  constexpr std::int32_t dx[4]{-1, 1, 0, 0};
  constexpr std::int32_t dy[4]{0, 0, -1, 1};
  for (std::uint8_t i = 0; i < interior_count; ++i)
    for (std::uint8_t direction = 0; direction < 4; ++direction) {
      const auto x = static_cast<std::int32_t>(interior[i].x) + dx[direction];
      const auto y = static_cast<std::int32_t>(interior[i].y) + dy[direction];
      if (x < 0 || y < 0 ||
          x >= static_cast<std::int32_t>(rederivation_lattice_x_capacity) ||
          y >= static_cast<std::int32_t>(rederivation_lattice_y_capacity))
        continue;
      const auto &neighbor = workspace.lattice[selected][1][x][y];
      if (!neighbor.in_box || !neighbor.included)
        continue;
      ++out.matrix[i * 2U + i];
      if (neighbor.boundary) {
        out.boundary[i] +=
            card.boundary_x_coefficient * x + card.boundary_y_coefficient * y;
        continue;
      }
      for (std::uint8_t j = 0; j < interior_count; ++j)
        if (interior[j].x == x && interior[j].y == y)
          --out.matrix[i * 2U + j];
    }
  const auto determinant =
      out.matrix[0] * out.matrix[3] - out.matrix[1] * out.matrix[2];
  const auto first_numerator =
      out.boundary[0] * out.matrix[3] - out.matrix[1] * out.boundary[1];
  const auto second_numerator =
      out.matrix[0] * out.boundary[1] - out.boundary[0] * out.matrix[2];
  exact::word_division_result first{}, second{};
  const bool division_admitted =
      determinant > 0 && first_numerator >= 0 && second_numerator >= 0;
  if (division_admitted) {
    first = exact::divide_unsigned(static_cast<std::uint64_t>(first_numerator),
                                   static_cast<std::uint64_t>(determinant));
    second =
        exact::divide_unsigned(static_cast<std::uint64_t>(second_numerator),
                               static_cast<std::uint64_t>(determinant));
  }
  const bool solvable = interior_count == 2 && division_admitted &&
                        first.remainder == 0 && second.remainder == 0 &&
                        first.quotient <= 2'147'483'647U &&
                        second.quotient <= 2'147'483'647U;
  if (solvable) {
    out.solution[0] = static_cast<std::int32_t>(first.quotient);
    out.solution[1] = static_cast<std::int32_t>(second.quotient);
  }
  out.characteristic[0] = 1;
  out.characteristic[1] = -(out.matrix[0] + out.matrix[3]);
  out.characteristic[2] = determinant;
  out.eigenvalues[0] = out.matrix[0] + out.matrix[1];
  out.eigenvalues[1] = out.matrix[0] - out.matrix[1];
  out.eigenvectors[0] = 1;
  out.eigenvectors[1] = 1;
  out.eigenvectors[2] = 1;
  out.eigenvectors[3] = -1;
  out.energy[0] = out.matrix[0];
  out.energy[1] = out.matrix[1] + out.matrix[2];
  out.energy[2] = out.matrix[3];
  out.geometry_return_mounted =
      polygon.identity == exact::word{197'301U + selected} &&
      polygon.lattice_count[1] == 12 && interior_count == 2;
  out.equations_exact =
      solvable &&
      out.matrix[0] * out.solution[0] + out.matrix[1] * out.solution[1] ==
          out.boundary[0] &&
      out.matrix[2] * out.solution[0] + out.matrix[3] * out.solution[1] ==
          out.boundary[1];
  out.eigen_exact = out.matrix[0] == out.matrix[3] &&
                    out.matrix[1] == out.matrix[2] &&
                    out.matrix[0] + out.matrix[1] == out.eigenvalues[0] &&
                    out.matrix[0] - out.matrix[1] == out.eigenvalues[1];
  out.symbolic_minimum =
      out.eigen_exact && out.eigenvalues[0] > 0 && out.eigenvalues[1] > 0 &&
      out.energy[0] == out.eigenvalues[0] + 1 && out.energy[1] == -2 &&
      out.energy[2] == out.eigenvalues[0] + 1;
  std::int32_t disconnected[4]{};
  for (std::uint8_t i = 0; i < interior_count; ++i)
    for (std::uint8_t j = 0; j < interior_count; ++j) {
      const auto separation = absolute(interior[i].x - interior[j].x) +
                              absolute(interior[i].y - interior[j].y);
      if (separation == 1) {
        ++disconnected[i * 2U + i];
        --disconnected[i * 2U + j];
      }
    }
  out.disconnected_determinant =
      disconnected[0] * disconnected[3] - disconnected[1] * disconnected[2];
  out.disconnected_obstructed = out.disconnected_determinant == 0;
  out.identity = exact::word{197'302};
  out.lineage =
      exact::word{polygon.lineage.value() + card.metadata.lineage.value()};
}

} // namespace holonics::organ::rederivation_potential_detail
