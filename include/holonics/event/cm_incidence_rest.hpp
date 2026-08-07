#pragma once

#include <type_traits>

#include <holonics/event/blind_reconstruction_rest.hpp>
#include <holonics/organ/cm_incidence_schema.hpp>

namespace holonics::event {
struct cm_incidence_rest_record final {
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
  std::uint64_t integrity{};
};

struct cm_incidence_rest_receipt final {
  body::rest_receipt body{};
  exact::word theory{};
  exact::word integrity{};
  bool prior_returns_preserved{};
  bool source_detached{};
  bool returned{};
};

struct cm_incidence_remount_receipt final {
  body::rest_receipt body{};
  exact::word theory{};
  bool same_body{};
  bool theory_preserved{};
  bool source_replayed{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t cm_incidence_rest_integrity(
    const cm_incidence_rest_record& record) noexcept {
  std::uint64_t fold = record.body.integrity;
  terminal_rest_detail::fold_fiber(fold, record.first);
  terminal_rest_detail::fold_fiber(fold, record.second);
  const std::uint64_t fibers[35]{record.geometry.identity.value(),
      record.geometry.passage.value(), record.geometry.kernel_return.value(),
      record.geometry.lineage.value(),
      record.geometry.accepted ? 1U : 0U, record.phase_crystal.identity.value(),
      record.phase_crystal.passage.value(), record.phase_crystal.kernel_return.value(),
      record.phase_crystal.lineage.value(),
      record.phase_crystal.accepted ? 1U : 0U, record.characteristic.identity.value(),
      record.characteristic.passage.value(), record.characteristic.kernel_return.value(),
      record.characteristic.lineage.value(),
      record.characteristic.accepted ? 1U : 0U, record.regular_singular.identity.value(),
      record.regular_singular.passage.value(), record.regular_singular.kernel_return.value(),
      record.regular_singular.lineage.value(),
      record.regular_singular.accepted ? 1U : 0U, record.code_reconstruction.identity.value(),
      record.code_reconstruction.passage.value(), record.code_reconstruction.kernel_return.value(),
      record.code_reconstruction.lineage.value(),
      record.code_reconstruction.accepted ? 1U : 0U, record.moment_reconstruction.identity.value(),
      record.moment_reconstruction.passage.value(), record.moment_reconstruction.kernel_return.value(),
      record.moment_reconstruction.lineage.value(),
      record.moment_reconstruction.accepted ? 1U : 0U, record.cm_incidence.identity.value(),
      record.cm_incidence.passage.value(), record.cm_incidence.kernel_return.value(),
      record.cm_incidence.lineage.value(),
      record.cm_incidence.accepted ? 1U : 0U};
  for (const auto value : fibers) { terminal_rest_detail::fold_value(fold, value); }
  return fold;
}

static_assert(std::is_trivially_copyable_v<cm_incidence_rest_record>);

}  // namespace holonics::event
