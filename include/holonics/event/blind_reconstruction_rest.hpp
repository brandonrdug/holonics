#pragma once

#include <type_traits>

#include <holonics/event/regular_singular_rest.hpp>
#include <holonics/organ/blind_reconstruction_schema.hpp>

namespace holonics::event {

struct blind_reconstruction_rest_record final {
  body::rest_record body{};
  organ::acquired_theorem_fiber first{};
  organ::acquired_theorem_fiber second{};
  organ::acquired_geometry_theory geometry{};
  organ::acquired_phase_crystal phase_crystal{};
  organ::acquired_characteristic characteristic{};
  organ::acquired_regular_singular regular_singular{};
  organ::acquired_blind_reconstruction code_reconstruction{};
  organ::acquired_blind_reconstruction moment_reconstruction{};
  std::uint64_t mathematical_morphology{};
  std::uint64_t codec_morphology{};
  std::uint64_t geometry_morphology{};
  std::uint64_t phase_morphology{};
  std::uint64_t characteristic_morphology{};
  std::uint64_t regular_singular_morphology{};
  std::uint64_t blind_reconstruction_morphology{};
  std::uint64_t integrity{};
};

struct blind_reconstruction_rest_receipt final {
  body::rest_receipt body{};
  exact::word code_theory{};
  exact::word moment_theory{};
  exact::word integrity{};
  bool prior_returns_preserved{};
  bool source_detached{};
  bool returned{};
};

struct blind_reconstruction_remount_receipt final {
  body::rest_receipt body{};
  exact::word code_theory{};
  exact::word moment_theory{};
  bool same_body{};
  bool theories_preserved{};
  bool source_replayed{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t blind_reconstruction_rest_integrity(
    const blind_reconstruction_rest_record& record) noexcept {
  std::uint64_t fold = record.body.integrity;
  terminal_rest_detail::fold_fiber(fold, record.first);
  terminal_rest_detail::fold_fiber(fold, record.second);
  const std::uint64_t fibers[36]{record.geometry.identity.value(),
      record.geometry.passage.value(), record.geometry.kernel_return.value(),
      record.geometry.lineage.value(), record.geometry.morphology_delta.value(),
      record.geometry.accepted ? 1U : 0U, record.phase_crystal.identity.value(),
      record.phase_crystal.passage.value(), record.phase_crystal.kernel_return.value(),
      record.phase_crystal.lineage.value(), record.phase_crystal.morphology_delta.value(),
      record.phase_crystal.accepted ? 1U : 0U, record.characteristic.identity.value(),
      record.characteristic.passage.value(), record.characteristic.kernel_return.value(),
      record.characteristic.lineage.value(), record.characteristic.morphology_delta.value(),
      record.characteristic.accepted ? 1U : 0U, record.regular_singular.identity.value(),
      record.regular_singular.passage.value(), record.regular_singular.kernel_return.value(),
      record.regular_singular.lineage.value(), record.regular_singular.morphology_delta.value(),
      record.regular_singular.accepted ? 1U : 0U, record.code_reconstruction.identity.value(),
      record.code_reconstruction.passage.value(), record.code_reconstruction.kernel_return.value(),
      record.code_reconstruction.lineage.value(), record.code_reconstruction.morphology_delta.value(),
      record.code_reconstruction.accepted ? 1U : 0U, record.moment_reconstruction.identity.value(),
      record.moment_reconstruction.passage.value(), record.moment_reconstruction.kernel_return.value(),
      record.moment_reconstruction.lineage.value(), record.moment_reconstruction.morphology_delta.value(),
      record.moment_reconstruction.accepted ? 1U : 0U};
  for (const auto value : fibers) { terminal_rest_detail::fold_value(fold, value); }
  const std::uint64_t morphology[7]{record.mathematical_morphology,
      record.codec_morphology, record.geometry_morphology, record.phase_morphology,
      record.characteristic_morphology, record.regular_singular_morphology,
      record.blind_reconstruction_morphology};
  for (const auto value : morphology) { terminal_rest_detail::fold_value(fold, value); }
  return fold;
}

static_assert(std::is_trivially_copyable_v<blind_reconstruction_rest_record>);

}  // namespace holonics::event
