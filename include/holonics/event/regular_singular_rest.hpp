#pragma once

#include <type_traits>

#include <holonics/event/characteristic_rest.hpp>
#include <holonics/organ/regular_singular_schema.hpp>

namespace holonics::event {

struct regular_singular_rest_record final {
  body::rest_record body{};
  organ::acquired_theorem_fiber first{};
  organ::acquired_theorem_fiber second{};
  organ::acquired_geometry_theory geometry{};
  organ::acquired_phase_crystal phase_crystal{};
  organ::acquired_characteristic characteristic{};
  organ::acquired_regular_singular regular_singular{};
  std::uint64_t mathematical_morphology{};
  std::uint64_t codec_morphology{};
  std::uint64_t geometry_morphology{};
  std::uint64_t phase_morphology{};
  std::uint64_t characteristic_morphology{};
  std::uint64_t regular_singular_morphology{};
  std::uint64_t integrity{};
};

struct regular_singular_rest_receipt final {
  body::rest_receipt body{};
  exact::word theory{};
  exact::word integrity{};
  bool prior_returns_preserved{};
  bool source_detached{};
  bool returned{};
};

struct regular_singular_remount_receipt final {
  body::rest_receipt body{};
  exact::word theory{};
  bool same_body{};
  bool theory_preserved{};
  bool source_replayed{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t regular_singular_rest_integrity(
    const regular_singular_rest_record& record) noexcept {
  std::uint64_t fold = record.body.integrity;
  terminal_rest_detail::fold_fiber(fold, record.first);
  terminal_rest_detail::fold_fiber(fold, record.second);
  const std::uint64_t geometry[6]{record.geometry.identity.value(),
      record.geometry.passage.value(), record.geometry.kernel_return.value(),
      record.geometry.lineage.value(), record.geometry.morphology_delta.value(),
      record.geometry.accepted ? 1U : 0U};
  const std::uint64_t phase[6]{record.phase_crystal.identity.value(),
      record.phase_crystal.passage.value(), record.phase_crystal.kernel_return.value(),
      record.phase_crystal.lineage.value(), record.phase_crystal.morphology_delta.value(),
      record.phase_crystal.accepted ? 1U : 0U};
  const std::uint64_t characteristic[6]{record.characteristic.identity.value(),
      record.characteristic.passage.value(), record.characteristic.kernel_return.value(),
      record.characteristic.lineage.value(), record.characteristic.morphology_delta.value(),
      record.characteristic.accepted ? 1U : 0U};
  const std::uint64_t regular[6]{record.regular_singular.identity.value(),
      record.regular_singular.passage.value(), record.regular_singular.kernel_return.value(),
      record.regular_singular.lineage.value(), record.regular_singular.morphology_delta.value(),
      record.regular_singular.accepted ? 1U : 0U};
  for (const auto value : geometry) { terminal_rest_detail::fold_value(fold, value); }
  for (const auto value : phase) { terminal_rest_detail::fold_value(fold, value); }
  for (const auto value : characteristic) { terminal_rest_detail::fold_value(fold, value); }
  for (const auto value : regular) { terminal_rest_detail::fold_value(fold, value); }
  terminal_rest_detail::fold_value(fold, record.mathematical_morphology);
  terminal_rest_detail::fold_value(fold, record.codec_morphology);
  terminal_rest_detail::fold_value(fold, record.geometry_morphology);
  terminal_rest_detail::fold_value(fold, record.phase_morphology);
  terminal_rest_detail::fold_value(fold, record.characteristic_morphology);
  terminal_rest_detail::fold_value(fold, record.regular_singular_morphology);
  return fold;
}

static_assert(std::is_trivially_copyable_v<regular_singular_rest_record>);

}  // namespace holonics::event
