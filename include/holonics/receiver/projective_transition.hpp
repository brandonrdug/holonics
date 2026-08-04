#pragma once

#include <cstdint>

#include <holonics/exact/projective.hpp>
#include <holonics/exact/signed_magnitude.hpp>

namespace holonics::receiver {

struct projective_transition_value final {
  exact::projective_pair<exact::unsigned_128> sequence{};
  exact::projective_pair<exact::unsigned_128> projected{};
  exact::signed_magnitude<2> determinant{};
  exact::operation_receipt receipt{};
  bool invertible{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr projective_transition_value transition_face(
    std::uint64_t local_coordinate,
    std::uint64_t source_extent,
    std::uint8_t face) noexcept {
  projective_transition_value result{};
  result.sequence.first = exact::unsigned_128::from_word(local_coordinate + 1U);
  result.sequence.second = exact::unsigned_128::from_word(source_extent + 1U);
  const auto upper = exact::unsigned_128::from_word(static_cast<std::uint64_t>(face) + 1U);
  const auto lower = exact::unsigned_128::from_word(257U);
  const auto upper_product = exact::multiply(upper, result.sequence.first);
  const auto lower_product = exact::multiply(lower, result.sequence.first);
  const auto projected_first = exact::add(upper_product.value, result.sequence.second);
  const auto projected_second = exact::add(lower_product.value, result.sequence.second);
  result.receipt = projected_first.receipt;
  if (!upper_product.accepted() || !lower_product.accepted() ||
      !projected_first.accepted() || !projected_second.accepted()) {
    result.receipt.state = exact::status::capacity_refused;
    return result;
  }
  result.projected = {projected_first.value, projected_second.value};
  const auto determinant_magnitude = exact::subtract(lower, upper);
  result.determinant = exact::signed_magnitude<2>{true, determinant_magnitude.value};
  result.invertible = determinant_magnitude.accepted() && !determinant_magnitude.value.is_zero();
  return result;
}

}  // namespace holonics::receiver
