#pragma once

#include <holonics/organ/toric_fan_law.hpp>

namespace holonics::organ::toric_intersection_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool adjacent(
    std::uint8_t left, std::uint8_t right, std::uint8_t count) noexcept {
  return left != right && (toric_exact::next(left, count) == right ||
      toric_exact::next(right, count) == left);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr toric_rational fan_self(
    const toric_fan_card& fan, std::uint8_t ray) noexcept {
  const auto previous = fan.rays[toric_exact::previous(ray, fan.ray_count)];
  const auto next = fan.rays[toric_exact::next(ray, fan.ray_count)];
  const auto current = fan.rays[ray];
  if (current.x != 0) {
    return toric_exact::make(-(previous.x + next.x), current.x);
  }
  return toric_exact::make(-(previous.y + next.y), current.y);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr toric_rational chow_self(
    const toric_fan_card& fan, std::uint8_t ray) noexcept {
  const auto previous = fan.rays[toric_exact::previous(ray, fan.ray_count)];
  const auto next = fan.rays[toric_exact::next(ray, fan.ray_count)];
  const auto current = fan.rays[ray];
  const toric_integer_pair character = current.x != 0 ?
      toric_integer_pair{1, 0} : toric_integer_pair{0, 1};
  const auto coefficient = toric_exact::dot(character, current);
  const auto neighboring = toric_exact::dot(character, previous) +
      toric_exact::dot(character, next);
  return toric_exact::make(-neighboring, coefficient);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr toric_rational pair(
    const toric_intersection_receipt& intersection,
    const toric_rational* left, const toric_rational* right,
    std::uint8_t rank) noexcept;

HOLONICS_CALLABLE constexpr void form_intersection(const toric_fan_receipt& fan,
    const toric_quotient_receipt& quotient, toric_intersection_receipt& out) noexcept {
  out.identity = exact::word{190'430U + fan.source.ray_count};
  out.lineage = quotient.lineage + 1U;
  if (!quotient.exact) { return; }
  out.fan_chow_agree = true;
  for (std::uint8_t left = 0; left < fan.source.ray_count; ++left) {
    for (std::uint8_t right = 0; right < fan.source.ray_count; ++right) {
      const auto fan_value = left == right ? fan_self(fan.source, left) :
          toric_exact::make(adjacent(left, right, fan.source.ray_count) ? 1 : 0);
      const auto chow_value = left == right ? chow_self(fan.source, left) :
          toric_exact::make(adjacent(left, right, fan.source.ray_count) ? 1 : 0);
      out.fan_divisor_form[left][right] = fan_value;
      out.chow_divisor_form[left][right] = chow_value;
      out.fan_chow_agree = out.fan_chow_agree && toric_exact::equal(fan_value, chow_value);
    }
  }
  for (std::uint8_t left = 0; left < quotient.rank; ++left) {
    for (std::uint8_t right = 0; right < quotient.rank; ++right) {
      out.congruence_basis[left][right] = toric_exact::make(0);
      out.congruence_form[left][right] = toric_exact::make(0);
      out.quotient_form[left][right] =
          out.chow_divisor_form[left + 2U][right + 2U];
    }
  }
  if (quotient.rank == 1) {
    out.determinant = out.quotient_form[0][0];
    const auto diagonal = out.quotient_form[0][0].numerator;
    out.positive = diagonal > 0 ? 1 : 0;
    out.negative = diagonal < 0 ? 1 : 0;
    out.radical = diagonal == 0 ? 1 : 0;
    out.inertia_exact = true;
    out.congruence_basis[0][0] = toric_exact::make(1);
    out.congruence_form[0][0] = out.quotient_form[0][0];
    out.basis_determinant = toric_exact::make(1);
  } else if (quotient.rank == 2) {
    const auto a = out.quotient_form[0][0];
    const auto b = out.quotient_form[0][1];
    const auto d = out.quotient_form[1][1];
    const auto determinant = toric_exact::subtract(
        toric_exact::multiply(a, d), toric_exact::multiply(b, b));
    out.determinant = determinant;
    if (determinant.numerator < 0) { out.positive = 1; out.negative = 1; }
    else if (determinant.numerator > 0 &&
        (a.numerator > 0 || (a.numerator == 0 && d.numerator > 0))) {
      out.positive = 2;
    } else if (determinant.numerator > 0) { out.negative = 2; }
    else { out.radical = 1; out.positive = a.numerator > 0 ? 1 : 0;
      out.negative = a.numerator < 0 ? 1 : 0; }
    out.inertia_exact = true;
    if (a.numerator != 0) {
      out.congruence_basis[0][0] = toric_exact::make(1);
      out.congruence_basis[0][1] = {-b.numerator, b.denominator};
      out.congruence_basis[1][1] = a;
    } else if (d.numerator != 0) {
      out.congruence_basis[1][0] = toric_exact::make(1);
      out.congruence_basis[0][1] = d;
      out.congruence_basis[1][1] = {-b.numerator, b.denominator};
    } else {
      out.congruence_basis[0][0] = toric_exact::make(1);
      out.congruence_basis[1][0] = toric_exact::make(1);
      out.congruence_basis[0][1] = toric_exact::make(1);
      out.congruence_basis[1][1] = toric_exact::make(-1);
    }
    toric_rational directions[2][2]{{toric_exact::make(0), toric_exact::make(0)},
        {toric_exact::make(0), toric_exact::make(0)}};
    for (std::uint8_t direction = 0; direction < 2; ++direction) {
      for (std::uint8_t coordinate = 0; coordinate < 2; ++coordinate) {
        directions[direction][coordinate] = out.congruence_basis[coordinate][direction];
      }
    }
    for (std::uint8_t left = 0; left < 2; ++left) {
      for (std::uint8_t right = 0; right < 2; ++right) {
        out.congruence_form[left][right] = pair(out,
            directions[left], directions[right], 2);
      }
    }
    out.basis_determinant = toric_exact::subtract(
        toric_exact::multiply(out.congruence_basis[0][0],
            out.congruence_basis[1][1]),
        toric_exact::multiply(out.congruence_basis[0][1],
            out.congruence_basis[1][0]));
  }
  out.rank = static_cast<std::uint8_t>(out.positive + out.negative);
  out.exact = out.fan_chow_agree && out.inertia_exact;
}

HOLONICS_CALLABLE constexpr void form_comparison(const toric_fan_receipt& fan,
    const toric_quotient_receipt& quotient,
    toric_comparison_receipt& out) noexcept {
  out.identity = exact::word{190'470U + fan.source.ray_count};
  out.lineage = quotient.lineage + 2U;
  out.standard_hypotheses = fan.smooth && fan.complete && quotient.exact;
  if (!out.standard_hypotheses) { return; }
  out.betti[0] = 1; out.betti[2] = quotient.rank; out.betti[4] = 1;
  out.hodge[0][0] = 1; out.hodge[1][1] = quotient.rank; out.hodge[2][2] = 1;
  out.ranks_returned = true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr toric_rational pair(
    const toric_intersection_receipt& intersection,
    const toric_rational* left, const toric_rational* right,
    std::uint8_t rank) noexcept {
  auto result = toric_exact::make(0);
  for (std::uint8_t row = 0; row < rank; ++row) {
    for (std::uint8_t column = 0; column < rank; ++column) {
      result = toric_exact::add(result, toric_exact::multiply(
          toric_exact::multiply(left[row], intersection.quotient_form[row][column]),
          right[column]));
    }
  }
  return result;
}

}  // namespace holonics::organ::toric_intersection_detail
