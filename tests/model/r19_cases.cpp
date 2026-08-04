#include "r19_cases.hpp"

namespace holonics::tests {
namespace {

[[nodiscard]] organ::characteristic_foundation foundation() noexcept {
  return {exact::word{134'400}, exact::word{134'401}, exact::word{134'402},
      exact::word{134'403}, exact::word{134'404}, exact::word{134'405},
      exact::word{134'406}, exact::word{186'400}, 16};
}

[[nodiscard]] organ::characteristic_question question() noexcept {
  return {exact::word{144'400}, exact::word{144'401}, exact::word{144'402}};
}

}  // namespace

apparatus::characteristic_mount r19_case(
    const event::phase_crystal_rest_record& inherited) noexcept {
  return {foundation(), question(), inherited};
}

event::phase_crystal_rest_record r19_host_phase_rest() noexcept {
  event::phase_crystal_rest_record record{};
  record.body.head = 14'001'008;
  record.body.next_head = 14'001'009;
  record.body.continuation = 15'001'008;
  record.body.next_continuation = 15'001'009;
  record.body.lineage = 16'001'008;
  record.body.regions[0] = {192, 174'300};
  record.body.regions[1] = {129, 0};
  record.body.regions[2] = {130, 0};
  record.body.regions[3] = {131, 0};
  record.body.integrity = body::rest_integrity(record.body);
  record.first = {exact::word{181'200}, exact::word{171'200}, exact::word{151'200},
      exact::word{161'200}, exact::word{160'200}, exact::word{141'010}, exact::word{5}, 3, true};
  record.second = {exact::word{182'200}, exact::word{172'200}, exact::word{152'200},
      exact::word{162'200}, exact::word{160'300}, exact::word{181'200}, exact::word{5}, 2, true};
  record.geometry = {exact::word{184'300}, exact::word{173'300}, exact::word{160'400},
      exact::word{193'310}, exact::word{9}, true};
  record.phase_crystal = {exact::word{185'300}, exact::word{174'300},
      exact::word{160'500}, exact::word{194'300}, exact::word{11}, true};
  record.mathematical_morphology = 62;
  record.codec_morphology = 42;
  record.geometry_morphology = 10;
  record.phase_morphology = 14;
  record.integrity = event::phase_crystal_rest_integrity(record);
  return record;
}

}  // namespace holonics::tests
