#pragma once

#include <holonics/organ/causal_linear_cm_law.hpp>
#include <holonics/organ/toric_cycle_law.hpp>

namespace holonics::organ::causal_linear_detail {

HOLONICS_CALLABLE constexpr void map_fan(const toric_fan_receipt& fan,
    causal_toric_map_section& out, std::uint64_t identity) noexcept {
  out.identity = exact::word{identity}; out.lineage = exact::word{fan.lineage + 20U};
  set_matrix(out.character, fan.source.ray_count, 2, identity + 1U,
      out.lineage.value() + 1U);
  for (std::uint8_t ray = 0; ray < fan.source.ray_count; ++ray) {
    for (std::uint8_t coordinate = 0; coordinate < 2; ++coordinate) {
      out.character.values[ray][coordinate] = fan.character_map[coordinate][ray];
    }
  }
  analyze(out.character, out.analysis, identity + 2U);
  out.smith_exact = smith_rank_two(out.character, out.analysis, out.smith);
  out.free_cokernel_rank = static_cast<std::uint8_t>(
      out.character.rows - out.analysis.rank);
  out.exact = fan.character_exact && out.analysis.exact && out.analysis.rank == 2 &&
      out.analysis.nullity == 0 && out.smith_exact && out.smith[0] == 1 && out.smith[1] == 1;
}

HOLONICS_CALLABLE constexpr void derive_toric(const toric_cycle_card& card,
    causal_toric_section& out) noexcept {
  out.identity = exact::word{192'450};
  out.lineage = exact::word{card.lineage.value() + 50U};
  const toric_cycle_foundation foundation{exact::word{139'720}, exact::word{139'721},
      exact::word{139'722}, exact::word{139'723}, exact::word{139'724},
      exact::word{139'725}, exact::word{139'726}, exact::word{139'727}, card};
  if (!toric_fan_detail::valid_foundation(foundation)) { return; }
  toric_fan_receipt fans[2]{}; toric_quotient_receipt quotients[2]{};
  toric_intersection_receipt intersections[2]{};
  for (std::uint8_t slot = 0; slot < 2; ++slot) {
    toric_fan_detail::form_fan(card.fans[slot], card.lineage.value() + slot, fans[slot]);
    toric_fan_detail::form_quotient(fans[slot], quotients[slot]);
    toric_intersection_detail::form_intersection(fans[slot], quotients[slot],
        intersections[slot]);
    map_fan(fans[slot], out.source[slot], 192'451U + 4U * slot);
  }
  toric_blowup_receipt blowup{};
  const auto selected = card.selected_fan;
  toric_blowup_detail::form_blowup(card, fans[selected], quotients[selected],
      intersections[selected], blowup);
  map_fan(blowup.fan, out.blowup, 192'460);
  out.exceptional_square = blowup.exceptional_square.numerator;
  out.source_positive = intersections[selected].positive;
  out.source_negative = intersections[selected].negative;
  out.blowup_positive = blowup.intersection.positive;
  out.blowup_negative = blowup.intersection.negative;
  out.topology_changed = blowup.exact &&
      out.blowup.free_cokernel_rank ==
          static_cast<std::uint8_t>(out.source[selected].free_cokernel_rank + 1U) &&
      out.exceptional_square == -1 && out.blowup_negative > out.source_negative;
  out.exact = out.source[0].exact && out.source[1].exact && out.blowup.exact &&
      intersections[0].exact && intersections[1].exact && out.topology_changed;
}

}  // namespace holonics::organ::causal_linear_detail
