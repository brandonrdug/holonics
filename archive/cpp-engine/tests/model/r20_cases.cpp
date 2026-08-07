#include "r20_cases.hpp"

namespace holonics::tests {
namespace {
[[nodiscard]] organ::regular_singular_foundation foundation() noexcept {
  return {exact::word{135'400}, exact::word{135'401}, exact::word{135'402},
      exact::word{135'403}, exact::word{135'404}, exact::word{135'405},
      exact::word{135'406}, exact::word{187'400},
      {{0, 1, -1}, {2, -3}, -1}, 12};
}

[[nodiscard]] organ::regular_singular_question question() noexcept {
  return {exact::word{145'400}, exact::word{145'401}, exact::word{145'402}};
}

}  // namespace

apparatus::regular_singular_mount r20_case(
    const event::characteristic_rest_record& inherited) noexcept {
  return {foundation(), question(), inherited};
}

event::characteristic_rest_record r20_host_characteristic_rest() noexcept {
  event::characteristic_rest_record record{};
  record.body.head = 14'001'010;
  record.body.next_head = 14'001'011;
  record.body.continuation = 15'001'010;
  record.body.next_continuation = 15'001'011;
  record.body.lineage = 16'001'010;
  record.body.regions[0] = {174'400};
  record.body.regions[1] = {0};
  record.body.regions[2] = {0};
  record.body.regions[3] = {0};
  record.body.integrity = body::rest_integrity(record.body);
  record.first = {exact::word{181'200}, exact::word{171'200}, exact::word{151'200},
      exact::word{161'200}, exact::word{160'200}, exact::word{141'010}, 3, true};
  record.second = {exact::word{182'200}, exact::word{172'200}, exact::word{152'200},
      exact::word{162'200}, exact::word{160'300}, exact::word{181'200}, 2, true};
  record.geometry = {exact::word{184'300}, exact::word{173'300}, exact::word{160'400},
      exact::word{193'310}, true};
  record.phase_crystal = {exact::word{185'300}, exact::word{174'300},
      exact::word{160'500}, exact::word{194'300}, true};
  record.characteristic = {exact::word{186'300}, exact::word{174'400},
      exact::word{160'600}, exact::word{194'400}, true};
  record.integrity = event::characteristic_rest_integrity(record);
  return record;
}

}  // namespace holonics::tests
