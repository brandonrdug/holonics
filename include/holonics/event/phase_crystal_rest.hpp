#pragma once

#include <type_traits>

#include <holonics/event/geometry_inquiry_rest.hpp>
#include <holonics/organ/phase_crystal_schema.hpp>

namespace holonics::event {

struct phase_crystal_rest_record final {
  body::rest_record body{};
  organ::acquired_theorem_fiber first{};
  organ::acquired_theorem_fiber second{};
  organ::acquired_geometry_theory geometry{};
  organ::acquired_phase_crystal phase_crystal{};
  std::uint64_t mathematical_admitted_tally{};
  std::uint64_t codec_admitted_tally{};
  std::uint64_t geometry_admitted_tally{};
  std::uint64_t phase_admitted_tally{};
  std::uint64_t integrity{};
};

struct phase_crystal_rest_receipt final {
  body::rest_receipt body{};
  exact::word atlas{};
  exact::word integrity{};
  bool prior_returns_preserved{};
  bool source_detached{};
  bool returned{};
};

struct phase_crystal_remount_receipt final {
  body::rest_receipt body{};
  exact::word atlas{};
  bool same_body{};
  bool atlas_preserved{};
  bool source_replayed{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t phase_crystal_rest_integrity(
    const phase_crystal_rest_record& record) noexcept {
  std::uint64_t fold = record.body.integrity;
  terminal_rest_detail::fold_fiber(fold, record.first);
  terminal_rest_detail::fold_fiber(fold, record.second);
  const std::uint64_t geometry[6]{record.geometry.identity.value(),
      record.geometry.passage.value(), record.geometry.kernel_return.value(),
      record.geometry.lineage.value(), record.geometry.admitted_tally_delta.value(),
      record.geometry.accepted ? 1U : 0U};
  const std::uint64_t phase[6]{record.phase_crystal.identity.value(),
      record.phase_crystal.passage.value(), record.phase_crystal.kernel_return.value(),
      record.phase_crystal.lineage.value(), record.phase_crystal.admitted_tally_delta.value(),
      record.phase_crystal.accepted ? 1U : 0U};
  for (const auto value : geometry) { terminal_rest_detail::fold_value(fold, value); }
  for (const auto value : phase) { terminal_rest_detail::fold_value(fold, value); }
  terminal_rest_detail::fold_value(fold, record.mathematical_admitted_tally);
  terminal_rest_detail::fold_value(fold, record.codec_admitted_tally);
  terminal_rest_detail::fold_value(fold, record.geometry_admitted_tally);
  terminal_rest_detail::fold_value(fold, record.phase_admitted_tally);
  return fold;
}

static_assert(std::is_trivially_copyable_v<phase_crystal_rest_record>);

}  // namespace holonics::event
