#include "r22_cases.hpp"

namespace holonics::tests {
namespace {

[[nodiscard]] organ::cm_incidence_foundation foundation(
    const organ::cm_problem_card& card) noexcept {
  return {exact::word{136'600}, exact::word{136'601}, exact::word{136'602},
      exact::word{136'603}, exact::word{136'604}, exact::word{136'605},
      exact::word{136'606}, card};
}

[[nodiscard]] organ::cm_incidence_question question() noexcept {
  return {exact::word{146'600}, exact::word{146'601}, exact::word{146'602}};
}

}  // namespace

apparatus::cm_incidence_mount r22_case(
    const event::blind_reconstruction_rest_record& inherited,
    const organ::cm_problem_card& card) noexcept {
  return {foundation(card), question(), inherited};
}

organ::cm_problem_card r22_host_card() noexcept {
  organ::cm_problem_card card{};
  card.schema = exact::word{210'023};
  card.occurrence = exact::word{210'003};
  card.lineage = exact::word{220'003};
  card.byte_fold = 230'003;
  card.path_fold = 240'003;
  card.byte_count = 35;
  card.factor_min = -8;
  card.factor_max = 8;
  card.cyclotomic_order = 5;
  card.degree = 4;
  card.periodic_modulus = 2;
  card.window_min = 0;
  card.window_max = 1;
  card.translation_count = 5;
  card.parsed = true;
  return card;
}

event::blind_reconstruction_rest_record r22_host_blind_rest() noexcept {
  event::blind_reconstruction_rest_record record{};
  record.body.head = 14'001'016;
  record.body.next_head = 14'001'017;
  record.body.continuation = 15'001'016;
  record.body.next_continuation = 15'001'017;
  record.body.lineage = 16'001'016;
  record.body.regions[0] = {296, 176'400};
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
  record.code_reconstruction = {exact::word{188'300}, exact::word{176'300},
      exact::word{160'802}, exact::word{196'300}, exact::word{12}, true};
  record.moment_reconstruction = {exact::word{188'301}, exact::word{176'400},
      exact::word{160'812}, exact::word{196'400}, exact::word{14}, true};
  record.mathematical_morphology = 94;
  record.codec_morphology = 54;
  record.geometry_morphology = 10;
  record.phase_morphology = 14;
  record.characteristic_morphology = 16;
  record.regular_singular_morphology = 20;
  record.blind_reconstruction_morphology = 24;
  record.integrity = event::blind_reconstruction_rest_integrity(record);
  return record;
}

}  // namespace holonics::tests
