#include "r17_cases.hpp"

namespace holonics::tests {
namespace {

[[nodiscard]] organ::geometry_inquiry_foundation foundation() noexcept {
  return {exact::word{133'300}, exact::word{133'301}, exact::word{133'302},
      exact::word{133'303}, exact::word{133'304}, exact::word{133'305},
      exact::word{183'400}, 32};
}

[[nodiscard]] organ::geometry_inquiry_question question() noexcept {
  return {exact::word{143'300}, exact::word{143'301}, exact::word{143'302}};
}

}  // namespace

apparatus::geometry_inquiry_mount r17_case(
    const event::terminal_theorem_rest_record& inherited) noexcept {
  return {foundation(), question(), inherited};
}

event::terminal_theorem_rest_record r17_host_terminal_rest() noexcept {
  event::terminal_theorem_rest_record record{};
  record.body.head = 14'001'004;
  record.body.next_head = 14'001'005;
  record.body.continuation = 15'001'004;
  record.body.next_continuation = 15'001'005;
  record.body.lineage = 16'001'004;
  record.body.regions[0] = {152, 172'200};
  record.body.regions[1] = {129, 0};
  record.body.regions[2] = {130, 0};
  record.body.regions[3] = {131, 0};
  record.body.integrity = body::rest_integrity(record.body);
  record.first = {exact::word{181'200}, exact::word{171'200}, exact::word{151'200},
      exact::word{161'200}, exact::word{160'200}, exact::word{141'010}, exact::word{5}, 3, true};
  record.second = {exact::word{182'200}, exact::word{172'200}, exact::word{152'200},
      exact::word{162'200}, exact::word{160'300}, exact::word{181'200}, exact::word{5}, 2, true};
  record.mathematical_morphology = 49;
  record.codec_morphology = 36;
  record.integrity = event::terminal_theorem_rest_integrity(record);
  return record;
}

}  // namespace holonics::tests
