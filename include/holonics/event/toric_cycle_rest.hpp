#pragma once

#include <type_traits>

#include <holonics/event/cm_incidence_rest.hpp>
#include <holonics/organ/toric_cycle_schema.hpp>

namespace holonics::event {
struct toric_cycle_rest_record final {
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
  std::uint64_t integrity{};
};

struct toric_cycle_rest_receipt final {
  body::rest_receipt body{};
  exact::word theory{};
  exact::word integrity{};
  bool prior_returns_preserved{};
  bool source_detached{};
  bool returned{};
};

struct toric_cycle_remount_receipt final {
  body::rest_receipt body{};
  exact::word theory{};
  bool same_body{};
  bool theory_preserved{};
  bool source_replayed{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t toric_cycle_rest_integrity(
    const toric_cycle_rest_record& record) noexcept {
  cm_incidence_rest_record inherited{};
  inherited.body = record.body;
  inherited.first = record.first;
  inherited.second = record.second;
  inherited.geometry = record.geometry;
  inherited.phase_crystal = record.phase_crystal;
  inherited.characteristic = record.characteristic;
  inherited.regular_singular = record.regular_singular;
  inherited.code_reconstruction = record.code_reconstruction;
  inherited.moment_reconstruction = record.moment_reconstruction;
  inherited.cm_incidence = record.cm_incidence;
  std::uint64_t fold = cm_incidence_rest_integrity(inherited);
  const std::uint64_t values[5]{record.toric_cycle.identity.value(),
      record.toric_cycle.passage.value(), record.toric_cycle.kernel_return.value(),
      record.toric_cycle.lineage.value(),
      record.toric_cycle.accepted ? 1U : 0U};
  for (const auto value : values) { terminal_rest_detail::fold_value(fold, value); }
  return fold;
}

static_assert(std::is_trivially_copyable_v<toric_cycle_rest_record>);

}  // namespace holonics::event
