#pragma once

#include <type_traits>

#include <holonics/event/intrinsic_hypergeometry_rest.hpp>
#include <holonics/organ/expression_geometry_schema.hpp>

namespace holonics::event {
struct expression_geometry_rest_record final {
  body::rest_record body{};
  organ::acquired_theorem_fiber first{}; organ::acquired_theorem_fiber second{};
  organ::acquired_geometry_theory geometry{}; organ::acquired_phase_crystal phase_crystal{};
  organ::acquired_characteristic characteristic{};
  organ::acquired_regular_singular regular_singular{};
  organ::acquired_blind_reconstruction code_reconstruction{};
  organ::acquired_blind_reconstruction moment_reconstruction{};
  organ::acquired_cm_incidence cm_incidence{}; organ::acquired_toric_cycle toric_cycle{};
  organ::acquired_algebraic_variation algebraic_variation{};
  organ::acquired_causal_linear causal_linear{};
  organ::acquired_intrinsic_hypergeometry intrinsic_hypergeometry{};
  organ::acquired_expression_geometry expression_geometry{}; std::uint64_t integrity{};
};

struct expression_geometry_rest_receipt final {
  body::rest_receipt body{}; exact::word theory{}; exact::word integrity{};
  bool prior_returns_preserved{}; bool source_detached{}; bool returned{};
};

struct expression_geometry_remount_receipt final {
  body::rest_receipt body{}; exact::word theory{};
  bool same_body{}; bool theory_preserved{}; bool source_replayed{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t expression_geometry_rest_integrity(
    const expression_geometry_rest_record& record) noexcept {
  intrinsic_hypergeometry_rest_record inherited{}; inherited.body = record.body;
  inherited.first = record.first; inherited.second = record.second; inherited.geometry = record.geometry;
  inherited.phase_crystal = record.phase_crystal; inherited.characteristic = record.characteristic;
  inherited.regular_singular = record.regular_singular;
  inherited.code_reconstruction = record.code_reconstruction;
  inherited.moment_reconstruction = record.moment_reconstruction;
  inherited.cm_incidence = record.cm_incidence; inherited.toric_cycle = record.toric_cycle;
  inherited.algebraic_variation = record.algebraic_variation; inherited.causal_linear = record.causal_linear;
  inherited.intrinsic_hypergeometry = record.intrinsic_hypergeometry;
  std::uint64_t fold = intrinsic_hypergeometry_rest_integrity(inherited);
  const std::uint64_t values[5]{record.expression_geometry.identity.value(),
      record.expression_geometry.passage.value(), record.expression_geometry.kernel_return.value(),
      record.expression_geometry.lineage.value(),
      record.expression_geometry.accepted ? 1U : 0U};
  for (const auto value : values) { terminal_rest_detail::fold_value(fold, value); }
  return fold;
}

static_assert(std::is_trivially_copyable_v<expression_geometry_rest_record>);

}  // namespace holonics::event
