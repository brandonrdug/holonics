#pragma once

#include <holonics/organ/toric_realization_law.hpp>

namespace holonics::organ::toric_blowup_detail {

HOLONICS_CALLABLE constexpr void form_blowup(const toric_cycle_card& card,
    const toric_fan_receipt& source_fan, const toric_quotient_receipt& source_quotient,
    const toric_intersection_receipt& source_intersection,
    toric_blowup_receipt& out) noexcept {
  if (!source_intersection.exact || source_fan.source.ray_count + 1U > toric_ray_capacity ||
      card.selected_cone >= source_fan.source.ray_count) { return; }
  out.identity = exact::word{190'460};
  out.lineage = source_intersection.lineage + 16U;
  const auto selected = card.selected_cone;
  const auto next = toric_exact::next(selected, source_fan.source.ray_count);
  out.derived_ray = {source_fan.source.rays[selected].x + source_fan.source.rays[next].x,
      source_fan.source.rays[selected].y + source_fan.source.rays[next].y};
  toric_fan_card subdivided{};
  subdivided.ray_count = static_cast<std::uint8_t>(source_fan.source.ray_count + 1U);
  std::uint8_t destination = 0;
  for (std::uint8_t ray = 0; ray < source_fan.source.ray_count; ++ray) {
    subdivided.rays[destination++] = source_fan.source.rays[ray];
    if (ray == selected) { subdivided.rays[destination++] = out.derived_ray; }
  }
  toric_fan_detail::form_fan(subdivided, out.lineage + 1U, out.fan);
  toric_fan_detail::form_quotient(out.fan, out.quotient);
  toric_intersection_detail::form_intersection(out.fan, out.quotient, out.intersection);
  toric_intersection_detail::form_comparison(out.fan, out.quotient, out.comparison);
  toric_realization_detail::form_polarization(
      out.fan, out.quotient, out.intersection, out.polarization);
  out.old_ray_count = source_fan.source.ray_count;
  for (std::uint8_t coordinate = 0; coordinate < out.quotient.rank; ++coordinate) {
    out.exceptional[coordinate] = toric_exact::make(0);
    out.pullback[coordinate] = toric_exact::make(0);
    out.pushforward[coordinate] = toric_exact::make(0);
    out.exceptional[coordinate] = out.quotient.divisor_classes[selected + 1U][coordinate];
  }
  out.exceptional_square = toric_intersection_detail::pair(out.intersection,
      out.exceptional, out.exceptional, out.quotient.rank);
  for (std::uint8_t old_ray = 0; old_ray < source_fan.source.ray_count; ++old_ray) {
    const auto new_ray = old_ray <= selected ? old_ray :
        static_cast<std::uint8_t>(old_ray + 1U);
    auto& transform = out.transforms[old_ray];
    transform.identity = exact::word{190'465U + old_ray};
    transform.lineage = out.lineage + old_ray + 1U;
    transform.old_ray = old_ray; transform.new_ray = new_ray;
    for (std::uint8_t coordinate = 0; coordinate < out.quotient.rank; ++coordinate) {
      transform.strict[coordinate] =
          out.quotient.divisor_classes[new_ray][coordinate];
      transform.total[coordinate] = transform.strict[coordinate];
      if (old_ray == selected || old_ray == next) {
        transform.total[coordinate] = toric_exact::add(
            transform.total[coordinate], out.exceptional[coordinate]);
      }
    }
    transform.exact = true;
  }
  for (std::uint8_t old_basis = 0; old_basis < source_quotient.rank; ++old_basis) {
    for (std::uint8_t coordinate = 0; coordinate < out.quotient.rank; ++coordinate) {
      out.pullback_matrix[coordinate][old_basis] =
          out.transforms[old_basis + 2U].total[coordinate];
      out.pullback[coordinate] = out.pullback_matrix[coordinate][old_basis];
    }
  }
  for (std::uint8_t new_basis = 0; new_basis < out.quotient.rank; ++new_basis) {
    const auto new_ray = static_cast<std::uint8_t>(new_basis + 2U);
    const bool is_exceptional = new_ray == selected + 1U;
    const auto old_ray = new_ray <= selected ? new_ray :
        static_cast<std::uint8_t>(new_ray - 1U);
    for (std::uint8_t old_basis = 0; old_basis < source_quotient.rank; ++old_basis) {
      out.pushforward_matrix[old_basis][new_basis] = is_exceptional ?
          toric_exact::make(0) : source_quotient.divisor_classes[old_ray][old_basis];
      out.pushforward[new_basis] = out.pushforward_matrix[old_basis][new_basis];
    }
  }
  out.pullback_kernel_rank = 0; out.pullback_image_rank = source_quotient.rank;
  out.pushforward_kernel_rank = static_cast<std::uint8_t>(
      out.quotient.rank - source_quotient.rank);
  out.pushforward_image_rank = source_quotient.rank;
  out.projection_formula = source_quotient.rank == 1 && out.quotient.rank == 2;
  for (std::uint8_t basis = 0; basis < out.quotient.rank; ++basis) {
    const auto left = toric_intersection_detail::pair(out.intersection, out.pullback,
        out.quotient.divisor_classes[basis + 2U], out.quotient.rank);
    const auto right = toric_exact::multiply(source_intersection.quotient_form[0][0],
        out.pushforward_matrix[0][basis]);
    out.projection_formula = out.projection_formula && toric_exact::equal(left, right);
  }
  const auto exceptional_push = toric_exact::add(
      toric_exact::multiply(out.exceptional[0], out.pushforward_matrix[0][0]),
      toric_exact::multiply(out.exceptional[1], out.pushforward_matrix[0][1]));
  out.projection_formula = out.projection_formula && exceptional_push.numerator == 0;
  out.exact = out.fan.smooth && out.fan.complete && out.quotient.exact &&
      out.intersection.exact && out.exceptional_square.numerator == -1 &&
      out.exceptional_square.denominator == 1 && out.projection_formula &&
      out.polarization.exact && out.comparison.ranks_returned;
}

}  // namespace holonics::organ::toric_blowup_detail
