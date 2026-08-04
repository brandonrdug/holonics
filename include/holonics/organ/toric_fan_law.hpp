#pragma once

#include <holonics/organ/toric_cycle_receipt.hpp>
#include <holonics/organ/toric_exact_law.hpp>

namespace holonics::organ::toric_fan_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool primitive(
    toric_integer_pair ray) noexcept {
  return (ray.x != 0 || ray.y != 0) && toric_exact::gcd(ray.x, ray.y) == 1;
}

HOLONICS_CALLABLE constexpr void form_fan(const toric_fan_card& source,
    std::uint64_t lineage, toric_fan_receipt& out) noexcept {
  out.identity = exact::word{190'410U + source.ray_count};
  out.source = source;
  out.lineage = lineage;
  out.cone_count = source.ray_count;
  out.primitive = source.ray_count >= 3 && source.ray_count <= toric_ray_capacity;
  out.smooth = out.primitive;
  for (std::uint8_t ray = 0; ray < source.ray_count; ++ray) {
    out.primitive = out.primitive && primitive(source.rays[ray]);
    const auto next = toric_exact::next(ray, source.ray_count);
    out.cone_determinants[ray] =
        toric_exact::determinant(source.rays[ray], source.rays[next]);
    out.smooth = out.smooth && out.cone_determinants[ray] == 1;
    out.character_map[0][ray] = source.rays[ray].x;
    out.character_map[1][ray] = source.rays[ray].y;
  }
  out.complete = out.smooth;
  std::int64_t divisor_one = 0;
  std::int64_t divisor_two = 0;
  for (std::uint8_t ray = 0; ray < source.ray_count; ++ray) {
    divisor_one = toric_exact::gcd(divisor_one, source.rays[ray].x);
    divisor_one = toric_exact::gcd(divisor_one, source.rays[ray].y);
    for (std::uint8_t other = static_cast<std::uint8_t>(ray + 1U);
        other < source.ray_count; ++other) {
      divisor_two = toric_exact::gcd(divisor_two,
          toric_exact::determinant(source.rays[ray], source.rays[other]));
    }
  }
  out.smith_invariants[0] = divisor_one;
  out.smith_invariants[1] = toric_exact::quotient(divisor_two, divisor_one);
  out.character_exact = out.primitive && out.smith_invariants[0] != 0 &&
      out.smith_invariants[1] != 0;
}

HOLONICS_CALLABLE constexpr void form_quotient(const toric_fan_receipt& fan,
    toric_quotient_receipt& out) noexcept {
  out.identity = exact::word{190'420U + fan.source.ray_count};
  out.lineage = fan.lineage + 1U;
  if (!fan.smooth || !fan.complete || fan.source.ray_count < 3) { return; }
  out.rank = static_cast<std::uint8_t>(fan.source.ray_count - 2U);
  out.relation_rank = 2;
  for (std::uint8_t ray = 0; ray < fan.source.ray_count; ++ray) {
    for (std::uint8_t coordinate = 0; coordinate < out.rank; ++coordinate) {
      out.divisor_classes[ray][coordinate] = toric_exact::make(0);
    }
    out.principal_relations[0][ray] = fan.character_map[0][ray];
    out.principal_relations[1][ray] = fan.character_map[1][ray];
  }
  const auto first = fan.source.rays[0];
  const auto second = fan.source.rays[1];
  const auto det = toric_exact::determinant(first, second);
  if (det != 1) { return; }
  for (std::uint8_t basis = 0; basis < out.rank; ++basis) {
    const auto ray = fan.source.rays[static_cast<std::uint8_t>(basis + 2U)];
    out.divisor_classes[0][basis] = toric_exact::make(
        -(second.y * ray.x - second.x * ray.y), det);
    out.divisor_classes[1][basis] = toric_exact::make(
        -(-first.y * ray.x + first.x * ray.y), det);
    out.divisor_classes[basis + 2U][basis] = toric_exact::make(1);
    out.basis_lifts[basis][basis + 2U] = 1;
  }
  out.smith_exact = fan.character_exact;
  out.torsion_free = fan.smith_invariants[0] == 1 && fan.smith_invariants[1] == 1;
  out.torsion_count = out.torsion_free ? 0 : 1;
  out.exact = out.smith_exact && out.torsion_free;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_foundation(
    const toric_cycle_foundation& foundation) noexcept {
  const auto& card = foundation.card;
  if (!card.parsed || card.schema != exact::word{230'023} ||
      card.fan_count != 2 || card.selected_fan >= card.fan_count ||
      card.selected_cone >= card.fans[card.selected_fan].ray_count ||
      card.target_count != 3 || card.representative_min != -4 ||
      card.representative_max != 4) { return false; }
  const exact::word owners[8]{foundation.ecology, foundation.fan,
      foundation.character, foundation.quotient, foundation.intersection,
      foundation.realization, foundation.transport, foundation.provenance};
  for (const auto owner : owners) { if (owner.value() == 0) { return false; } }
  return true;
}

}  // namespace holonics::organ::toric_fan_detail
