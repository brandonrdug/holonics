#pragma once

#include <holonics/organ/characteristic_exact.hpp>
#include <holonics/organ/regular_singular_receipt.hpp>

namespace holonics::organ::regular_singular_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_foundation(
    const regular_singular_foundation& value) noexcept {
  return value.ecology.value() != 0 && value.differential_transport.value() != 0 &&
      value.frobenius_transport.value() != 0 && value.resonance_transport.value() != 0 &&
      value.chamber_transport.value() != 0 && value.monodromy_transport.value() != 0 &&
      value.provenance.value() != 0 && value.term_seed.value() != 0 &&
      value.term_count == regular_singular_term_capacity &&
      value.mounted_operator.second[0] == 0 &&
      value.mounted_operator.second[1] == 1 &&
      value.mounted_operator.second[2] == -1 &&
      value.mounted_operator.first[0] == 2 &&
      value.mounted_operator.first[1] == -3 &&
      value.mounted_operator.zeroth == -1;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr fuchsian_system derive_system(
    const gauss_operator& source) noexcept {
  fuchsian_system result{};
  const auto q0 = source.second[1];
  const auto q1 = source.second[2];
  if (q0 != 1 || q1 != -1) { return result; }
  result.zero = {0, 1, 0, 1 - source.first[0]};
  result.one = {0, 0, source.zeroth,
      source.first[0] + source.first[1]};
  result.infinity = {-result.zero.a - result.one.a,
      -result.zero.b - result.one.b,
      -result.zero.c - result.one.c,
      -result.zero.d - result.one.d};
  result.derived = characteristic_detail::same_matrix(result.zero, {0, 1, 0, -1}) &&
      characteristic_detail::same_matrix(result.one, {0, 0, -1, -1}) &&
      characteristic_detail::same_matrix(result.infinity, {0, -1, 1, 2});
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr period_entry add(
    period_entry left, period_entry right) noexcept {
  return {left.constant + right.constant, left.omega + right.omega};
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool multiply(period_entry left,
    period_entry right, period_entry& output) noexcept {
  if (left.omega * right.omega != 0) { return false; }
  output = {left.constant * right.constant,
      left.constant * right.omega + left.omega * right.constant};
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool multiply(period_matrix_two left,
    period_matrix_two right, period_matrix_two& output) noexcept {
  period_entry aa{};
  period_entry bc{};
  period_entry ab{};
  period_entry bd{};
  period_entry ca{};
  period_entry dc{};
  period_entry cb{};
  period_entry dd{};
  if (!multiply(left.a, right.a, aa) || !multiply(left.b, right.c, bc) ||
      !multiply(left.a, right.b, ab) || !multiply(left.b, right.d, bd) ||
      !multiply(left.c, right.a, ca) || !multiply(left.d, right.c, dc) ||
      !multiply(left.c, right.b, cb) || !multiply(left.d, right.d, dd)) { return false; }
  output = {add(aa, bc), add(ab, bd), add(ca, dc), add(cb, dd)};
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool same(
    period_entry left, period_entry right) noexcept {
  return left.constant == right.constant && left.omega == right.omega;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool same(
    period_matrix_two left, period_matrix_two right) noexcept {
  return same(left.a, right.a) && same(left.b, right.b) &&
      same(left.c, right.c) && same(left.d, right.d);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr period_matrix_two lift(matrix_two value) noexcept {
  return {{value.a, 0}, {value.b, 0}, {value.c, 0}, {value.d, 0}};
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t fold_values(
    const std::int64_t* values, std::size_t count) noexcept {
  std::uint64_t fold = 14'695'981'039'346'656'037ULL;
  for (std::size_t slot = 0; slot < count; ++slot) {
    fold ^= static_cast<std::uint64_t>(values[slot]);
    fold *= 1'099'511'628'211ULL;
  }
  return fold;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t dot(
    const std::int64_t left[2], const std::int64_t right[2]) noexcept {
  return left[0] * right[0] + left[1] * right[1];
}

HOLONICS_CALLABLE constexpr void matvec(matrix_two matrix,
    const std::int64_t vector[2], std::int64_t output[2]) noexcept {
  output[0] = matrix.a * vector[0] + matrix.b * vector[1];
  output[1] = matrix.c * vector[0] + matrix.d * vector[1];
}

}  // namespace holonics::organ::regular_singular_detail
