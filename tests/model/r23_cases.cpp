#include "r23_cases.hpp"

#include "r22_cases.hpp"

namespace holonics::tests {
namespace {

[[nodiscard]] organ::toric_cycle_foundation foundation(
    const organ::toric_cycle_card& card) noexcept {
  return {exact::word{137'500}, exact::word{137'501}, exact::word{137'502},
      exact::word{137'503}, exact::word{137'504}, exact::word{137'505},
      exact::word{137'506}, exact::word{137'507}, card};
}

[[nodiscard]] organ::toric_cycle_question question() noexcept {
  return {exact::word{147'500}, exact::word{147'501}, exact::word{147'502}};
}

}  // namespace

apparatus::toric_cycle_mount r23_case(
    const event::cm_incidence_rest_record& inherited,
    const organ::toric_cycle_card& card) noexcept {
  return {foundation(card), question(), inherited};
}

organ::toric_cycle_card r23_host_card() noexcept {
  organ::toric_cycle_card card{};
  card.schema = exact::word{230'023}; card.occurrence = exact::word{230'003};
  card.lineage = exact::word{250'003}; card.byte_fold = 260'003;
  card.path_fold = 270'003; card.byte_count = 137;
  card.fan_count = 2; card.selected_fan = 0; card.selected_cone = 0;
  card.representative_min = -4; card.representative_max = 4;
  card.fans[0].ray_count = 3;
  card.fans[0].rays[0] = {1, 0}; card.fans[0].rays[1] = {0, 1};
  card.fans[0].rays[2] = {-1, -1};
  card.fans[1].ray_count = 4;
  card.fans[1].rays[0] = {1, 0}; card.fans[1].rays[1] = {0, 1};
  card.fans[1].rays[2] = {-1, 0}; card.fans[1].rays[3] = {0, -1};
  card.target_count = 3;
  const std::int64_t numerators[3][4]{{3,2,3,2}, {0,1,0,1}, {1,0,0,0}};
  const std::int64_t denominators[3][4]{{1,1,1,1}, {1,2,1,2}, {1,1,1,1}};
  for (std::uint8_t target = 0; target < 3; ++target) {
    for (std::uint8_t ray = 0; ray < 4; ++ray) {
      card.targets[target].response[ray] =
          {numerators[target][ray], denominators[target][ray]};
    }
  }
  card.parsed = true;
  return card;
}

event::cm_incidence_rest_record r23_host_cm_rest() noexcept {
  const auto prior = r22_host_blind_rest();
  event::cm_incidence_rest_record record{};
  record.body = prior.body;
  record.body.head = 14'001'018; record.body.next_head = 14'001'019;
  record.body.continuation = 15'001'018; record.body.next_continuation = 15'001'019;
  record.body.lineage = 16'001'018;
  record.body.regions[0] = {327, 176'500};
  record.body.integrity = body::rest_integrity(record.body);
  record.first = prior.first; record.second = prior.second;
  record.geometry = prior.geometry; record.phase_crystal = prior.phase_crystal;
  record.characteristic = prior.characteristic;
  record.regular_singular = prior.regular_singular;
  record.code_reconstruction = prior.code_reconstruction;
  record.moment_reconstruction = prior.moment_reconstruction;
  record.cm_incidence = {exact::word{189'300}, exact::word{176'500},
      exact::word{160'900}, exact::word{190'900}, exact::word{16}, true};
  record.mathematical_morphology = 104; record.codec_morphology = 58;
  record.geometry_morphology = prior.geometry_morphology;
  record.phase_morphology = prior.phase_morphology;
  record.characteristic_morphology = prior.characteristic_morphology;
  record.regular_singular_morphology = prior.regular_singular_morphology;
  record.blind_reconstruction_morphology = prior.blind_reconstruction_morphology;
  record.cm_incidence_morphology = 17;
  record.integrity = event::cm_incidence_rest_integrity(record);
  return record;
}

}  // namespace holonics::tests
