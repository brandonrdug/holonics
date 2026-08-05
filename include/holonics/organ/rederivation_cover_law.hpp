#pragma once

#include <holonics/organ/rederivation_receipt.hpp>

namespace holonics::organ::rederivation_cover_detail {

[[nodiscard]] HOLONICS_CALLABLE inline std::uint8_t
bit(std::uint8_t word, std::uint8_t row) noexcept {
  return static_cast<std::uint8_t>((word >> row) & 1U);
}

[[nodiscard]] HOLONICS_CALLABLE inline bool
find_collision(std::uint8_t width, std::uint8_t (&witness)[2]) noexcept {
  for (std::uint8_t left = 0; left < 8; ++left)
    for (std::uint8_t right = static_cast<std::uint8_t>(left + 1U); right < 8;
         ++right) {
      bool equal = true;
      for (std::uint8_t row = 0; row < width; ++row)
        equal = equal && bit(left, row) == bit(right, row);
      if (equal) {
        witness[0] = left;
        witness[1] = right;
        return true;
      }
    }
  return false;
}

HOLONICS_CALLABLE inline void derive(const cover_problem_card &card,
                                     rederivation_workspace &workspace,
                                     cover_rederivation_receipt &out) noexcept {
  for (std::uint8_t row = 0; row < card.maximum_width; ++row)
    for (std::uint8_t word = 0; word < card.words; ++word)
      if (bit(word, row) != 0)
        out.rows[row] = static_cast<std::uint8_t>(
            out.rows[row] | static_cast<std::uint8_t>(1U << word));
  out.width = 3;
  std::uint8_t subset_slot = 0;
  for (std::uint8_t a = 0; a < 5; ++a)
    for (std::uint8_t b = a + 1; b < 6; ++b)
      for (std::uint8_t c = b + 1; c < 7; ++c)
        for (std::uint8_t d = c + 1; d < 8; ++d) {
          saturation_receipt receipt{};
          receipt.columns[0] = a;
          receipt.columns[1] = b;
          receipt.columns[2] = c;
          receipt.columns[3] = d;
          receipt.saturated = false;
          for (std::uint8_t row = 0; row < 3 && !receipt.saturated; ++row) {
            const auto first = bit(a, row);
            const bool mixed = bit(b, row) != first || bit(c, row) != first ||
                               bit(d, row) != first;
            if (mixed) {
              receipt.witness_row = row;
              receipt.saturated = true;
            }
          }
          receipt.lineage = exact::word{card.metadata.lineage.value() +
                                        70'000U + subset_slot};
          workspace.subsets[subset_slot++] = receipt;
        }
  for (std::uint8_t y = 0; y < 8; ++y) {
    out.g[y] = y;
    out.exceptional[y] = static_cast<std::uint8_t>(7U - y);
    out.f[y] = bit(out.exceptional[y], 0);
  }
  bool pairs = true;
  for (std::uint8_t x = 0; x < 8; ++x)
    for (std::uint8_t y = 0; y < 8; ++y) {
      cover_pair_receipt receipt{};
      receipt.x = x;
      receipt.y = y;
      if (x == out.exceptional[y]) {
        receipt.witness = 0;
        receipt.left = bit(x, 0) == out.f[y];
      } else {
        for (std::uint8_t row = 0; row < 3; ++row)
          if (bit(x, row) == bit(y, row)) {
            receipt.witness = row;
            receipt.right = true;
            break;
          }
      }
      receipt.lineage =
          exact::word{card.metadata.lineage.value() + 71'000U + x * 8U + y};
      pairs = pairs && (receipt.left || receipt.right);
      workspace.pairs[x * 8U + y] = receipt;
    }
  out.subset_receipts = subset_slot;
  out.pair_receipts = 64;
  out.width_one_obstructed = find_collision(1, out.width_one_collision);
  out.width_two_obstructed = find_collision(2, out.width_two_collision);
  out.saturation_exact = subset_slot == 70;
  out.cover_exact = pairs;
  out.identity = exact::word{197'303};
  out.lineage = exact::word{card.metadata.lineage.value() + 72'000U};
}

} // namespace holonics::organ::rederivation_cover_detail
