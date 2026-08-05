#pragma once

#include <holonics/organ/toric_intersection_law.hpp>

namespace holonics::organ::toric_realization_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr exact::small_rational response_at(
    const toric_quotient_receipt& quotient,
    const toric_intersection_receipt& intersection,
    const exact::small_rational* coordinates, std::uint8_t ray) noexcept {
  return toric_intersection_detail::pair(intersection, coordinates,
      quotient.divisor_classes[ray], quotient.rank);
}

HOLONICS_CALLABLE constexpr void enumerate_representatives(
    const toric_cycle_card& card, const toric_fan_receipt& fan,
    const toric_quotient_receipt& quotient, toric_realization_receipt& out) noexcept {
  for (std::int64_t first = card.representative_min;
      first <= card.representative_max; ++first) {
    for (std::int64_t second = card.representative_min;
        second <= card.representative_max; ++second) {
      toric_representative candidate{};
      bool in_aperture = true;
      for (std::uint8_t ray = 0; ray < fan.source.ray_count; ++ray) {
        auto value = ray >= 2 && ray - 2U < quotient.rank ?
            out.class_coordinates[ray - 2U] : toric_exact::make(0);
        value = toric_exact::add(value, toric_exact::make(
            first * quotient.principal_relations[0][ray] +
            second * quotient.principal_relations[1][ray]));
        candidate.coefficients[ray] = value;
        in_aperture = in_aperture && value.denominator != 0 &&
            value.numerator >= card.representative_min * value.denominator &&
            value.numerator <= card.representative_max * value.denominator;
        if (value.numerator != 0) {
          candidate.support_mask = static_cast<std::uint8_t>(
              candidate.support_mask | static_cast<std::uint8_t>(1U << ray));
        }
      }
      if (in_aperture && out.representative_count < toric_representative_capacity) {
        candidate.identity = exact::word{190'480U + out.representative_count};
        candidate.lineage = out.lineage + out.representative_count + 1U;
        out.representatives[out.representative_count++] = candidate;
      }
    }
  }
}

HOLONICS_CALLABLE constexpr void realize(const toric_cycle_card& card,
    const toric_fan_receipt& fan, const toric_quotient_receipt& quotient,
    const toric_intersection_receipt& intersection, const toric_target& target,
    std::uint8_t target_index, toric_realization_receipt& out) noexcept {
  out.identity = exact::word{190'440U + target_index};
  out.lineage = intersection.lineage + 1U + target_index;
  out.target = target;
  if (!intersection.exact || quotient.rank == 0 || quotient.rank > 2) { return; }
  for (std::uint8_t coordinate = 0; coordinate < quotient.rank; ++coordinate) {
    out.class_coordinates[coordinate] = toric_exact::make(0);
  }
  out.kernel_rank = quotient.relation_rank;
  for (std::uint8_t relation = 0; relation < quotient.relation_rank; ++relation) {
    for (std::uint8_t ray = 0; ray < fan.source.ray_count; ++ray) {
      out.principal_kernel[relation][ray] = quotient.principal_relations[relation][ray];
    }
  }
  if (quotient.rank == 1) {
    out.class_coordinates[0] = toric_exact::divide(target.response[2],
        intersection.quotient_form[0][0]);
  } else {
    const auto a = intersection.quotient_form[0][0];
    const auto b = intersection.quotient_form[0][1];
    const auto c = intersection.quotient_form[1][0];
    const auto d = intersection.quotient_form[1][1];
    const auto determinant = toric_exact::subtract(
        toric_exact::multiply(a, d), toric_exact::multiply(b, c));
    if (determinant.numerator == 0) { return; }
    const auto y0 = target.response[2];
    const auto y1 = target.response[3];
    out.class_coordinates[0] = toric_exact::divide(toric_exact::subtract(
        toric_exact::multiply(d, y0), toric_exact::multiply(b, y1)), determinant);
    out.class_coordinates[1] = toric_exact::divide(toric_exact::subtract(
        toric_exact::multiply(a, y1), toric_exact::multiply(c, y0)), determinant);
  }
  out.full_response_checked = true;
  bool integral = true;
  for (std::uint8_t coordinate = 0; coordinate < quotient.rank; ++coordinate) {
    out.full_response_checked = out.full_response_checked &&
        toric_exact::valid(out.class_coordinates[coordinate]);
    integral = integral && out.class_coordinates[coordinate].denominator == 1;
  }
  for (std::uint8_t ray = 0; ray < fan.source.ray_count; ++ray) {
    out.full_response_checked = out.full_response_checked && toric_exact::equal(
        response_at(quotient, intersection, out.class_coordinates, ray), target.response[ray]);
  }
  if (!out.full_response_checked) {
    out.state = toric_realization_state::incompatible;
    out.exact = true;
    return;
  }
  out.state = integral ? toric_realization_state::integral :
      toric_realization_state::rational_only;
  enumerate_representatives(card, fan, quotient, out);
  out.exact = out.representative_count != 0;
}

HOLONICS_CALLABLE constexpr void form_polarization(const toric_fan_receipt& fan,
    const toric_quotient_receipt& quotient,
    const toric_intersection_receipt& intersection,
    toric_polarization_receipt& out) noexcept {
  out.identity = exact::word{190'450U + fan.source.ray_count};
  out.lineage = intersection.lineage + 8U;
  if (!intersection.exact) { return; }
  for (std::uint8_t coordinate = 0; coordinate < quotient.rank; ++coordinate) {
    out.anticanonical[coordinate] = toric_exact::make(0);
    out.primitive[coordinate] = toric_exact::make(0);
    out.primitive_negative[coordinate] = toric_exact::make(0);
  }
  for (std::uint8_t ray = 0; ray < fan.source.ray_count; ++ray) {
    for (std::uint8_t coordinate = 0; coordinate < quotient.rank; ++coordinate) {
      out.anticanonical[coordinate] = toric_exact::add(out.anticanonical[coordinate],
          quotient.divisor_classes[ray][coordinate]);
    }
  }
  std::int64_t divisor = 0;
  for (std::uint8_t coordinate = 0; coordinate < quotient.rank; ++coordinate) {
    divisor = toric_exact::gcd(divisor, out.anticanonical[coordinate].numerator);
  }
  for (std::uint8_t coordinate = 0; coordinate < quotient.rank; ++coordinate) {
    out.primitive[coordinate] = toric_exact::make(
        toric_exact::quotient(out.anticanonical[coordinate].numerator, divisor),
        out.anticanonical[coordinate].denominator);
  }
  out.response_positive = true;
  for (std::uint8_t ray = 0; ray < fan.source.ray_count; ++ray) {
    out.response[ray] = response_at(quotient, intersection, out.primitive, ray);
    out.response_positive = out.response_positive && out.response[ray].numerator > 0;
  }
  if (quotient.rank == 2) {
    exact::small_rational covector[2]{toric_exact::make(0), toric_exact::make(0)};
    for (std::uint8_t row = 0; row < 2; ++row) {
      for (std::uint8_t column = 0; column < 2; ++column) {
        covector[row] = toric_exact::add(covector[row], toric_exact::multiply(
            intersection.quotient_form[row][column], out.primitive[column]));
      }
    }
    out.primitive_negative[0] = covector[1];
    out.primitive_negative[1] = {-covector[0].numerator, covector[0].denominator};
    const auto common = toric_exact::gcd(out.primitive_negative[0].numerator,
        out.primitive_negative[1].numerator);
    for (std::uint8_t coordinate = 0; coordinate < 2; ++coordinate) {
      out.primitive_negative[coordinate] = toric_exact::make(
          toric_exact::quotient(out.primitive_negative[coordinate].numerator, common),
          out.primitive_negative[coordinate].denominator);
    }
    out.primitive_square = toric_intersection_detail::pair(intersection,
        out.primitive_negative, out.primitive_negative, 2);
    out.negative_control = out.primitive_square.numerator < 0;
    out.has_orthogonal_direction = true;
  } else { out.negative_control = true; out.has_orthogonal_direction = false; }
  out.exact = out.response_positive && out.negative_control;
}

}  // namespace holonics::organ::toric_realization_detail
