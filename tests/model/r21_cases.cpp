#include "r21_cases.hpp"

namespace holonics::tests {
namespace {

[[nodiscard]] organ::blind_reconstruction_foundation foundation(
    const organ::binary_code_problem_card& code,
    const organ::moment_problem_card& moments) noexcept {
  return {exact::word{136'500}, exact::word{136'501}, exact::word{136'502},
      exact::word{136'503}, exact::word{136'504}, exact::word{136'505},
      exact::word{136'506}, code, moments};
}

[[nodiscard]] organ::blind_reconstruction_question question() noexcept {
  return {exact::word{146'500}, exact::word{146'501}, exact::word{146'502}};
}

}  // namespace

apparatus::blind_reconstruction_mount r21_case(
    const event::regular_singular_rest_record& inherited,
    const organ::binary_code_problem_card& code,
    const organ::moment_problem_card& moments) noexcept {
  return {foundation(code, moments), question(), inherited};
}

organ::binary_code_problem_card r21_host_code_card() noexcept {
  organ::binary_code_problem_card card{};
  card.schema = exact::word{210'021};
  card.occurrence = exact::word{210'001};
  card.lineage = exact::word{220'001};
  card.byte_fold = 230'001;
  card.path_fold = 240'001;
  card.byte_count = 31;
  card.dimension = 7;
  card.row_count = 3;
  card.parity_rows[0] = 85;
  card.parity_rows[1] = 102;
  card.parity_rows[2] = 120;
  card.parsed = true;
  return card;
}

organ::moment_problem_card r21_host_moment_card() noexcept {
  organ::moment_problem_card card{};
  card.schema = exact::word{210'022};
  card.lineage = exact::word{220'002};
  card.byte_fold = 230'002;
  card.path_fold = 240'002;
  card.byte_count = 224;
  card.case_count = 5;
  card.parsed = true;
  card.cases[0] = {exact::word{210'101}, {3, 7, 21, 73, 273, 1057}, -8, 8, 3, 6};
  card.cases[1] = {exact::word{210'102}, {3, 2, 14, 20, 98, 212}, -8, 8, 3, 6};
  card.cases[2] = {exact::word{210'103},
      {4, 14, 78, 476, 3042, 19964, 133338, 901796}, -8, 8, 4, 8};
  card.cases[3] = {exact::word{210'104}, {3, 6, 18, 66, 258, 1026}, -8, 8, 3, 6};
  card.cases[4] = {exact::word{210'105}, {3, 7, 21, 73}, -8, 8, 3, 4};
  return card;
}

event::regular_singular_rest_record r21_host_regular_singular_rest() noexcept {
  event::regular_singular_rest_record record{};
  record.body.head = 14'001'012;
  record.body.next_head = 14'001'013;
  record.body.continuation = 15'001'012;
  record.body.next_continuation = 15'001'013;
  record.body.lineage = 16'001'012;
  record.body.regions[0] = {244, 175'400};
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
  record.characteristic = {exact::word{186'300}, exact::word{174'400},
      exact::word{160'600}, exact::word{194'400}, exact::word{12}, true};
  record.regular_singular = {exact::word{187'300}, exact::word{175'400},
      exact::word{160'700}, exact::word{195'400}, exact::word{13}, true};
  record.mathematical_admitted_tally = 79;
  record.codec_admitted_tally = 48;
  record.geometry_admitted_tally = 10;
  record.phase_admitted_tally = 14;
  record.characteristic_admitted_tally = 16;
  record.regular_singular_admitted_tally = 20;
  record.integrity = event::regular_singular_rest_integrity(record);
  return record;
}

}  // namespace holonics::tests
