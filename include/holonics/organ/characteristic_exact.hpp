#pragma once

#include <holonics/exact/signed_magnitude.hpp>
#include <holonics/organ/phase_crystal_exact.hpp>
#include <holonics/organ/characteristic_receipt.hpp>

namespace holonics::organ::characteristic_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_foundation(
    const characteristic_foundation& value) noexcept {
  return value.ecology.value() != 0 && value.cyclic_transport.value() != 0 &&
      value.shape_transport.value() != 0 && value.matrix_transport.value() != 0 &&
      value.discriminant.value() != 0 && value.indicial.value() != 0 &&
      value.provenance.value() != 0 && value.case_seed.value() != 0 &&
      value.case_count == characteristic_case_capacity;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t fold_word(
    const std::uint16_t* values, std::size_t count) noexcept {
  std::uint64_t fold = 14'695'981'039'346'656'037ULL;
  for (std::size_t slot = 0; slot < count; ++slot) {
    fold ^= values[slot];
    fold *= 1'099'511'628'211ULL;
  }
  return fold;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool matrix_bounded(matrix_two value) noexcept {
  return phase_crystal_detail::magnitude(value.a) <= 1'000U &&
      phase_crystal_detail::magnitude(value.b) <= 1'000U &&
      phase_crystal_detail::magnitude(value.c) <= 1'000U &&
      phase_crystal_detail::magnitude(value.d) <= 1'000U;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t fold_matrix_word(
    const matrix_two* values, std::size_t count) noexcept {
  std::uint64_t fold = 14'695'981'039'346'656'037ULL;
  for (std::size_t slot = 0; slot < count; ++slot) {
    const std::int64_t fields[4]{values[slot].a, values[slot].b,
        values[slot].c, values[slot].d};
    for (const auto field : fields) {
      fold ^= static_cast<std::uint64_t>(field);
      fold *= 1'099'511'628'211ULL;
    }
  }
  return fold;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool multiply(
    matrix_two left, matrix_two right, matrix_two& output) noexcept {
  if (!matrix_bounded(left) || !matrix_bounded(right)) { return false; }
  output = {left.a * right.a + left.b * right.c,
      left.a * right.b + left.b * right.d,
      left.c * right.a + left.d * right.c,
      left.c * right.b + left.d * right.d};
  return matrix_bounded(output);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t trace(matrix_two value) noexcept {
  return value.a + value.d;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t determinant(matrix_two value) noexcept {
  return value.a * value.d - value.b * value.c;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t fixed_dimension(
    matrix_two value) noexcept {
  const matrix_two shifted{value.a - 1, value.b, value.c, value.d - 1};
  if (shifted.a == 0 && shifted.b == 0 && shifted.c == 0 && shifted.d == 0) { return 2; }
  return determinant(shifted) == 0 ? 1 : 0;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_matrix(
    matrix_two left, matrix_two right) noexcept {
  return left.a == right.a && left.b == right.b && left.c == right.c && left.d == right.d;
}

}  // namespace holonics::organ::characteristic_detail
