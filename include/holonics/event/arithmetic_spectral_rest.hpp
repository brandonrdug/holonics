#pragma once

#include <type_traits>

#include <holonics/event/hodge_realization_rest.hpp>
#include <holonics/organ/arithmetic_spectral_receipt.hpp>

namespace holonics::event {
struct arithmetic_spectral_rest_record final {
  body::rest_record body{};
  organ::acquired_theorem_fiber first{}; organ::acquired_theorem_fiber second{};
  organ::acquired_geometry_theory geometry{}; organ::acquired_phase_crystal phase_crystal{};
  organ::acquired_characteristic characteristic{}; organ::acquired_regular_singular regular_singular{};
  organ::acquired_blind_reconstruction code_reconstruction{};
  organ::acquired_blind_reconstruction moment_reconstruction{};
  organ::acquired_cm_incidence cm_incidence{}; organ::acquired_toric_cycle toric_cycle{};
  organ::acquired_algebraic_variation algebraic_variation{};
  organ::acquired_causal_linear causal_linear{};
  organ::acquired_intrinsic_hypergeometry intrinsic_hypergeometry{};
  organ::acquired_expression_geometry expression_geometry{};
  organ::acquired_hodge_realization hodge_realization{};
  organ::acquired_arithmetic_spectral arithmetic_spectral{}; std::uint64_t integrity{};
};

struct arithmetic_spectral_rest_receipt final {
  body::rest_receipt body{}; exact::word theory{}; exact::word integrity{};
  bool prior_returns_preserved{}; bool source_detached{}; bool returned{};
};

struct arithmetic_spectral_remount_receipt final {
  body::rest_receipt body{}; exact::word theory{};
  bool same_body{}; bool theory_preserved{}; bool source_replayed{};
};

[[nodiscard]] HOLONICS_CALLABLE inline std::uint64_t arithmetic_spectral_rest_integrity(
    const arithmetic_spectral_rest_record& record) noexcept {
  hodge_realization_rest_record inherited{}; inherited.body = record.body;
  inherited.first = record.first; inherited.second = record.second; inherited.geometry = record.geometry;
  inherited.phase_crystal = record.phase_crystal; inherited.characteristic = record.characteristic;
  inherited.regular_singular = record.regular_singular;
  inherited.code_reconstruction = record.code_reconstruction;
  inherited.moment_reconstruction = record.moment_reconstruction;
  inherited.cm_incidence = record.cm_incidence; inherited.toric_cycle = record.toric_cycle;
  inherited.algebraic_variation = record.algebraic_variation; inherited.causal_linear = record.causal_linear;
  inherited.intrinsic_hypergeometry = record.intrinsic_hypergeometry;
  inherited.expression_geometry = record.expression_geometry;
  inherited.hodge_realization = record.hodge_realization;
  std::uint64_t fold = hodge_realization_rest_integrity(inherited);
  const std::uint64_t values[5]{record.arithmetic_spectral.identity.value(),
      record.arithmetic_spectral.passage.value(), record.arithmetic_spectral.returned_event.value(),
      record.arithmetic_spectral.lineage.value(),
      record.arithmetic_spectral.accepted ? 1U : 0U};
  for (const auto value : values) { terminal_rest_detail::fold_value(fold, value); }
  return fold;
}

static_assert(std::is_trivially_copyable_v<arithmetic_spectral_rest_record>);

}  // namespace holonics::event
