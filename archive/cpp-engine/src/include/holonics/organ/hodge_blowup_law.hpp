#pragma once

#include <holonics/organ/hodge_cycle_law.hpp>

namespace holonics::organ::hodge_blowup_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t pairing(
    const hodge_blowup_receipt& blowup, const std::int64_t (&left)[7],
    const std::int64_t (&right)[7]) noexcept {
  std::int64_t result = 0;
  for (std::uint8_t row = 0; row < 7; ++row) {
    for (std::uint8_t column = 0; column < 7; ++column) {
      result += left[row] * blowup.pairing[row][column] * right[column];
    }
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool projection_formula(
    const hodge_product_receipt& product, const hodge_blowup_receipt& blowup) noexcept {
  for (std::uint8_t source = 0; source < 7; ++source) {
    for (std::uint8_t target = 0; target < 6; ++target) {
      std::int64_t left = 0; std::int64_t right = 0;
      for (std::uint8_t row = 0; row < 6; ++row) {
        for (std::uint8_t column = 0; column < 6; ++column) {
          left += blowup.pushforward[row][source] * product.cup[row][column] *
              (column == target ? 1 : 0);
        }
      }
      for (std::uint8_t row = 0; row < 7; ++row) {
        right += blowup.pairing[source][row] * blowup.pullback[row][target];
      }
      if (left != right) { return false; }
    }
  }
  return true;
}

HOLONICS_CALLABLE constexpr void derive(const hodge_product_receipt& product,
    const hodge_cycle_receipt& cycles, std::uint8_t center,
    std::uint64_t lineage, hodge_blowup_receipt& out) noexcept {
  if (!product.exact || !cycles.exact || center >= 4) { return; }
  for (std::uint8_t row = 0; row < 6; ++row) {
    for (std::uint8_t column = 0; column < 6; ++column) {
      out.pairing[row][column] = product.cup[row][column];
    }
    out.pullback[row][row] = 1; out.pushforward[row][row] = 1;
  }
  out.pairing[6][6] = -1; out.exceptional[6] = 1;
  for (std::uint8_t graph = 0; graph < 4; ++graph) {
    for (std::uint8_t slot = 0; slot < 6; ++slot) {
      out.strict_classes[graph][slot] = cycles.locus.graph_class[slot];
    }
    out.through_center[graph] = graph == center;
    out.strict_classes[graph][6] = out.through_center[graph] ? -1 : 0;
    out.self_intersections[graph] = pairing(
        out, out.strict_classes[graph], out.strict_classes[graph]);
  }
  out.identity = exact::word{195'600U + center};
  out.lineage = exact::word{lineage + 320U + center}; out.center_selector = center;
  out.rank = 7; out.kernel_rank = 1;
  out.exceptional_square_minus_one = pairing(out, out.exceptional, out.exceptional) == -1;
  out.pull_push_identity = true;
  for (std::uint8_t row = 0; row < 6; ++row) {
    for (std::uint8_t column = 0; column < 6; ++column) {
      std::int64_t value = 0;
      for (std::uint8_t slot = 0; slot < 7; ++slot) {
        value += out.pushforward[row][slot] * out.pullback[slot][column];
      }
      out.pull_push_identity = out.pull_push_identity && value == (row == column ? 1 : 0);
    }
  }
  out.projection_formula = hodge_blowup_detail::projection_formula(product, out);
  out.mapping_cone_residual_exact = true;
  for (std::uint8_t row = 0; row < 6; ++row) {
    out.mapping_cone_residual_exact = out.mapping_cone_residual_exact &&
        out.pushforward[row][6] == 0;
  }
  out.all_push_to_graph = true;
  for (std::uint8_t graph = 0; graph < 4; ++graph) {
    for (std::uint8_t row = 0; row < 6; ++row) {
      std::int64_t value = 0;
      for (std::uint8_t slot = 0; slot < 7; ++slot) {
        value += out.pushforward[row][slot] * out.strict_classes[graph][slot];
      }
      out.all_push_to_graph = out.all_push_to_graph && value == cycles.locus.graph_class[row];
    }
  }
  bool squares = true;
  for (std::uint8_t graph = 0; graph < 4; ++graph) {
    squares = squares && out.self_intersections[graph] == (graph == center ? -1 : 0);
  }
  out.exact = out.exceptional_square_minus_one && out.pull_push_identity &&
      out.projection_formula && out.mapping_cone_residual_exact && out.all_push_to_graph && squares;
}

}  // namespace holonics::organ::hodge_blowup_detail
