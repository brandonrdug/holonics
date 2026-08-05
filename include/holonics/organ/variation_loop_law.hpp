#pragma once

#include <holonics/organ/variation_operator_law.hpp>

namespace holonics::organ::variation_loop_detail {

HOLONICS_CALLABLE constexpr void multiply(const std::int64_t left[2][2],
    const std::int64_t right[2][2], std::int64_t result[2][2]) noexcept {
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      result[row][column] = 0;
      for (std::uint8_t inner = 0; inner < 2; ++inner) {
        result[row][column] += left[row][inner] * right[inner][column];
      }
    }
  }
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool identity(
    const std::int64_t matrix[2][2]) noexcept {
  return matrix[0][0] == 1 && matrix[0][1] == 0 &&
      matrix[1][0] == 0 && matrix[1][1] == 1;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool preserves(
    const std::int64_t matrix[2][2], const std::int64_t form[2][2]) noexcept {
  std::int64_t transpose_form[2][2]{}; std::int64_t returned[2][2]{};
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      for (std::uint8_t inner = 0; inner < 2; ++inner) {
        transpose_form[row][column] += matrix[inner][row] * form[inner][column];
      }
    }
  }
  multiply(transpose_form, matrix, returned);
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      if (returned[row][column] != form[row][column]) { return false; }
    }
  }
  return true;
}

HOLONICS_CALLABLE constexpr void transvection(std::int64_t output[2][2],
    const std::int64_t cycle[2], const std::int64_t form[2][2],
    std::int64_t weight) noexcept {
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      std::int64_t pairing = 0;
      for (std::uint8_t inner = 0; inner < 2; ++inner) {
        pairing += cycle[inner] * form[inner][column];
      }
      output[row][column] = (row == column ? 1 : 0) +
          weight * cycle[row] * pairing;
    }
  }
}

HOLONICS_CALLABLE constexpr void derive_loops(algebraic_variation_receipt& out) noexcept {
  if (!out.scalar.exact || out.collision_count != 2) {
    out.obstruction = variation_obstruction::loop_refused; return;
  }
  auto& loops = out.loops; loops.vanishing_cycles[0][0] = 1;
  loops.vanishing_cycles[1][1] = 1;
  loops.twist_weight = out.mounted.cover_degree;
  for (std::uint8_t loop = 0; loop < 2; ++loop) {
    transvection(loops.monodromy[loop], loops.vanishing_cycles[loop],
        out.invariant.selected, loops.twist_weight);
    loops.identities[loop] = exact::word{191'580U + loop};
    loops.lineages[loop] = out.collisions[loop].lineage;
  }
  std::int64_t finite[2][2]{};
  multiply(loops.monodromy[0], loops.monodromy[1], finite);
  const auto determinant = finite[0][0] * finite[1][1] - finite[0][1] * finite[1][0];
  if (determinant != 1) { out.obstruction = variation_obstruction::loop_refused; return; }
  loops.monodromy[2][0][0] = finite[1][1];
  loops.monodromy[2][0][1] = -finite[0][1];
  loops.monodromy[2][1][0] = -finite[1][0];
  loops.monodromy[2][1][1] = finite[0][0];
  loops.identities[2] = exact::word{191'582};
  loops.lineages[2] = exact::word{out.mounted.lineage.value() + 194U};
  multiply(finite, loops.monodromy[2], loops.loop_product);
  std::int64_t reverse[2][2]{};
  multiply(loops.monodromy[1], loops.monodromy[0], reverse);
  loops.standard_hypotheses = out.mounted.degree == 3 && out.mounted.cover_degree == 2;
  loops.pairing_preserved = preserves(loops.monodromy[0], out.invariant.selected) &&
      preserves(loops.monodromy[1], out.invariant.selected) &&
      preserves(loops.monodromy[2], out.invariant.selected);
  loops.ordered_product_identity = identity(loops.loop_product);
  loops.noncommuting = reverse[0][0] != finite[0][0] || reverse[0][1] != finite[0][1] ||
      reverse[1][0] != finite[1][0] || reverse[1][1] != finite[1][1];
  loops.unequal_collision_lineage = loops.lineages[0] != loops.lineages[1];
  loops.exact = loops.standard_hypotheses && loops.pairing_preserved &&
      loops.ordered_product_identity && loops.noncommuting && loops.unequal_collision_lineage;
  out.foils.commuting_loops_rejected = loops.noncommuting;
  out.foils.equal_spectrum_not_equal_collision = loops.unequal_collision_lineage &&
      loops.monodromy[0][0][0] + loops.monodromy[0][1][1] ==
      loops.monodromy[1][0][0] + loops.monodromy[1][1][1];
  if (!loops.exact) { out.obstruction = variation_obstruction::loop_refused; }
}

}  // namespace holonics::organ::variation_loop_detail
