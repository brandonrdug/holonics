#pragma once

#include <type_traits>

#include <holonics/event/algebraic_variation_rest.hpp>
#include <holonics/organ/causal_linear_schema.hpp>

namespace holonics::event {

struct causal_linear_rest_record final {
  body::rest_record body{};
  organ::acquired_theorem_fiber first{};
  organ::acquired_theorem_fiber second{};
  organ::acquired_geometry_theory geometry{};
  organ::acquired_phase_crystal phase_crystal{};
  organ::acquired_characteristic characteristic{};
  organ::acquired_regular_singular regular_singular{};
  organ::acquired_blind_reconstruction code_reconstruction{};
  organ::acquired_blind_reconstruction moment_reconstruction{};
  organ::acquired_cm_incidence cm_incidence{};
  organ::acquired_toric_cycle toric_cycle{};
  organ::acquired_algebraic_variation algebraic_variation{};
  organ::acquired_causal_linear causal_linear{};
  std::uint64_t mathematical_admitted_tally{};
  std::uint64_t codec_admitted_tally{};
  std::uint64_t geometry_admitted_tally{};
  std::uint64_t phase_admitted_tally{};
  std::uint64_t characteristic_admitted_tally{};
  std::uint64_t regular_singular_admitted_tally{};
  std::uint64_t blind_reconstruction_admitted_tally{};
  std::uint64_t cm_incidence_admitted_tally{};
  std::uint64_t toric_cycle_admitted_tally{};
  std::uint64_t algebraic_variation_admitted_tally{};
  std::uint64_t causal_linear_admitted_tally{};
  std::uint64_t integrity{};
};

struct causal_linear_rest_receipt final {
  body::rest_receipt body{};
  exact::word theory{};
  exact::word integrity{};
  bool prior_returns_preserved{};
  bool source_detached{};
  bool returned{};
};

struct causal_linear_remount_receipt final {
  body::rest_receipt body{};
  exact::word theory{};
  bool same_body{};
  bool theory_preserved{};
  bool source_replayed{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t causal_linear_rest_integrity(
    const causal_linear_rest_record& record) noexcept {
  algebraic_variation_rest_record inherited{};
  inherited.body = record.body; inherited.first = record.first; inherited.second = record.second;
  inherited.geometry = record.geometry; inherited.phase_crystal = record.phase_crystal;
  inherited.characteristic = record.characteristic;
  inherited.regular_singular = record.regular_singular;
  inherited.code_reconstruction = record.code_reconstruction;
  inherited.moment_reconstruction = record.moment_reconstruction;
  inherited.cm_incidence = record.cm_incidence; inherited.toric_cycle = record.toric_cycle;
  inherited.algebraic_variation = record.algebraic_variation;
  inherited.mathematical_admitted_tally = record.mathematical_admitted_tally;
  inherited.codec_admitted_tally = record.codec_admitted_tally;
  inherited.geometry_admitted_tally = record.geometry_admitted_tally;
  inherited.phase_admitted_tally = record.phase_admitted_tally;
  inherited.characteristic_admitted_tally = record.characteristic_admitted_tally;
  inherited.regular_singular_admitted_tally = record.regular_singular_admitted_tally;
  inherited.blind_reconstruction_admitted_tally = record.blind_reconstruction_admitted_tally;
  inherited.cm_incidence_admitted_tally = record.cm_incidence_admitted_tally;
  inherited.toric_cycle_admitted_tally = record.toric_cycle_admitted_tally;
  inherited.algebraic_variation_admitted_tally = record.algebraic_variation_admitted_tally;
  std::uint64_t fold = algebraic_variation_rest_integrity(inherited);
  const std::uint64_t values[7]{record.causal_linear.identity.value(),
      record.causal_linear.passage.value(), record.causal_linear.kernel_return.value(),
      record.causal_linear.lineage.value(), record.causal_linear.admitted_tally_delta.value(),
      record.causal_linear.accepted ? 1U : 0U, record.causal_linear_admitted_tally};
  for (const auto value : values) { terminal_rest_detail::fold_value(fold, value); }
  return fold;
}

static_assert(std::is_trivially_copyable_v<causal_linear_rest_record>);

}  // namespace holonics::event
