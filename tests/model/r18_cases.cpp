#include "r18_cases.hpp"

namespace holonics::tests {
namespace {

[[nodiscard]] organ::phase_crystal_foundation foundation() noexcept {
  return {exact::word{134'300}, exact::word{134'301}, exact::word{134'302},
      exact::word{134'303}, exact::word{134'304}, exact::word{134'305},
      exact::word{185'400}, 16};
}

[[nodiscard]] organ::phase_crystal_question question() noexcept {
  return {exact::word{144'300}, exact::word{144'301}, exact::word{144'302}};
}

}  // namespace

apparatus::phase_crystal_mount r18_case(
    const event::geometry_inquiry_rest_record& inherited) noexcept {
  return {foundation(), question(), inherited};
}

event::geometry_inquiry_rest_record r18_host_geometry_rest() noexcept {
  event::geometry_inquiry_rest_record record{};
  record.body.head = 14'001'006;
  record.body.next_head = 14'001'007;
  record.body.continuation = 15'001'006;
  record.body.next_continuation = 15'001'007;
  record.body.lineage = 16'001'006;
  record.body.regions[0] = {169, 173'300};
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
  record.mathematical_admitted_tally = 55;
  record.codec_admitted_tally = 39;
  record.geometry_admitted_tally = 10;
  record.integrity = event::geometry_inquiry_rest_integrity(record);
  return record;
}

}  // namespace holonics::tests
