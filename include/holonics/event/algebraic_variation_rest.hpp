#pragma once

#include <type_traits>

#include <holonics/event/toric_cycle_rest.hpp>
#include <holonics/organ/algebraic_variation_schema.hpp>

namespace holonics::event {

struct algebraic_variation_rest_record final {
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
  std::uint64_t mathematical_morphology{};
  std::uint64_t codec_morphology{};
  std::uint64_t geometry_morphology{};
  std::uint64_t phase_morphology{};
  std::uint64_t characteristic_morphology{};
  std::uint64_t regular_singular_morphology{};
  std::uint64_t blind_reconstruction_morphology{};
  std::uint64_t cm_incidence_morphology{};
  std::uint64_t toric_cycle_morphology{};
  std::uint64_t algebraic_variation_morphology{};
  std::uint64_t integrity{};
};

struct algebraic_variation_rest_receipt final {
  body::rest_receipt body{};
  exact::word theory{};
  exact::word integrity{};
  bool prior_returns_preserved{};
  bool source_detached{};
  bool returned{};
};

struct algebraic_variation_remount_receipt final {
  body::rest_receipt body{};
  exact::word theory{};
  bool same_body{};
  bool theory_preserved{};
  bool source_replayed{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t algebraic_variation_rest_integrity(
    const algebraic_variation_rest_record& record) noexcept {
  toric_cycle_rest_record inherited{};
  inherited.body = record.body; inherited.first = record.first; inherited.second = record.second;
  inherited.geometry = record.geometry; inherited.phase_crystal = record.phase_crystal;
  inherited.characteristic = record.characteristic;
  inherited.regular_singular = record.regular_singular;
  inherited.code_reconstruction = record.code_reconstruction;
  inherited.moment_reconstruction = record.moment_reconstruction;
  inherited.cm_incidence = record.cm_incidence; inherited.toric_cycle = record.toric_cycle;
  inherited.mathematical_morphology = record.mathematical_morphology;
  inherited.codec_morphology = record.codec_morphology;
  inherited.geometry_morphology = record.geometry_morphology;
  inherited.phase_morphology = record.phase_morphology;
  inherited.characteristic_morphology = record.characteristic_morphology;
  inherited.regular_singular_morphology = record.regular_singular_morphology;
  inherited.blind_reconstruction_morphology = record.blind_reconstruction_morphology;
  inherited.cm_incidence_morphology = record.cm_incidence_morphology;
  inherited.toric_cycle_morphology = record.toric_cycle_morphology;
  std::uint64_t fold = toric_cycle_rest_integrity(inherited);
  const std::uint64_t values[7]{record.algebraic_variation.identity.value(),
      record.algebraic_variation.passage.value(), record.algebraic_variation.kernel_return.value(),
      record.algebraic_variation.lineage.value(),
      record.algebraic_variation.morphology_delta.value(),
      record.algebraic_variation.accepted ? 1U : 0U,
      record.algebraic_variation_morphology};
  for (const auto value : values) { terminal_rest_detail::fold_value(fold, value); }
  return fold;
}

static_assert(std::is_trivially_copyable_v<algebraic_variation_rest_record>);

}  // namespace holonics::event
