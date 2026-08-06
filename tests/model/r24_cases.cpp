#include "r24_cases.hpp"

#include "r23_cases.hpp"

namespace holonics::tests {
namespace {

[[nodiscard]] organ::algebraic_variation_foundation foundation(
    const organ::algebraic_variation_card& card) noexcept {
  return {exact::word{138'600}, exact::word{138'601}, exact::word{138'602},
      exact::word{138'603}, exact::word{138'604}, exact::word{138'605},
      exact::word{138'606}, exact::word{138'607}, card};
}

[[nodiscard]] organ::algebraic_variation_question question() noexcept {
  return {exact::word{148'600}, exact::word{148'601}, exact::word{148'602}};
}

}  // namespace

apparatus::algebraic_variation_mount r24_case(
    const event::toric_cycle_rest_record& inherited,
    const organ::algebraic_variation_card& card) noexcept {
  return {foundation(card), question(), inherited};
}

organ::algebraic_variation_card r24_host_card() noexcept {
  organ::algebraic_variation_card card{};
  card.schema = exact::word{240'024}; card.occurrence = exact::word{191'300};
  card.lineage = exact::word{250'304}; card.byte_fold = 260'304;
  card.path_fold = 270'304; card.byte_count = 101;
  card.coefficients[0] = {0,0}; card.coefficients[1] = {0,1};
  card.coefficients[2] = {-1,-1}; card.coefficients[3] = {1,0};
  const exact::small_rational samples[7]{{-3,1},{-2,1},{-1,1},{1,2},{2,1},{3,1},{4,1}};
  for (std::uint8_t slot = 0; slot < 7; ++slot) { card.samples[slot] = samples[slot]; }
  card.root_min = -2; card.root_max = 2; card.form_min = -2; card.form_max = 2;
  card.degree = 3; card.cover_degree = 2; card.sample_count = 7;
  card.discovery_count = 5; card.series_depth = 6; card.parsed = true; return card;
}

event::toric_cycle_rest_record r24_host_toric_rest() noexcept {
  const auto prior = r23_host_cm_rest(); event::toric_cycle_rest_record record{};
  record.body = prior.body; record.body.head = 14'001'020; record.body.next_head = 14'001'021;
  record.body.continuation = 15'001'020; record.body.next_continuation = 15'001'021;
  record.body.lineage = 16'001'020; record.body.regions[0] = {366, 190'300};
  record.body.integrity = body::rest_integrity(record.body);
  record.first = prior.first; record.second = prior.second; record.geometry = prior.geometry;
  record.phase_crystal = prior.phase_crystal; record.characteristic = prior.characteristic;
  record.regular_singular = prior.regular_singular;
  record.code_reconstruction = prior.code_reconstruction;
  record.moment_reconstruction = prior.moment_reconstruction;
  record.cm_incidence = prior.cm_incidence;
  record.toric_cycle = {exact::word{190'300}, exact::word{177'500},
      exact::word{161'000}, exact::word{191'050}, exact::word{20}, true};
  record.mathematical_admitted_tally = 116; record.codec_admitted_tally = 63;
  record.geometry_admitted_tally = prior.geometry_admitted_tally;
  record.phase_admitted_tally = prior.phase_admitted_tally;
  record.characteristic_admitted_tally = prior.characteristic_admitted_tally;
  record.regular_singular_admitted_tally = prior.regular_singular_admitted_tally;
  record.blind_reconstruction_admitted_tally = prior.blind_reconstruction_admitted_tally;
  record.cm_incidence_admitted_tally = 17; record.toric_cycle_admitted_tally = 19;
  record.integrity = event::toric_cycle_rest_integrity(record); return record;
}

}  // namespace holonics::tests
