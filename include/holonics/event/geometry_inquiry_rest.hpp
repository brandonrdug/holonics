#pragma once

#include <cstddef>
#include <cstdint>
#include <type_traits>

#include <holonics/event/terminal_theorem_rest.hpp>
#include <holonics/organ/geometry_inquiry_schema.hpp>

namespace holonics::event {
struct geometry_inquiry_rest_record final {
  body::rest_record body{};
  organ::acquired_theorem_fiber first{};
  organ::acquired_theorem_fiber second{};
  organ::acquired_geometry_theory geometry{};
  std::uint64_t integrity{};
};

struct geometry_inquiry_rest_receipt final {
  body::rest_receipt body{};
  exact::word theory{};
  exact::word integrity{};
  bool prior_theorems_preserved{};
  bool source_detached{};
  bool returned{};
};

struct geometry_inquiry_remount_receipt final {
  body::rest_receipt body{};
  exact::word theory{};
  bool same_body{};
  bool theory_preserved{};
  bool source_replayed{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t geometry_inquiry_rest_integrity(
    const geometry_inquiry_rest_record& record) noexcept {
  std::uint64_t fold = record.body.integrity;
  terminal_rest_detail::fold_fiber(fold, record.first);
  terminal_rest_detail::fold_fiber(fold, record.second);
  const std::uint64_t geometry[5]{record.geometry.identity.value(),
      record.geometry.passage.value(), record.geometry.kernel_return.value(),
      record.geometry.lineage.value(),
      record.geometry.accepted ? 1U : 0U};
  for (const auto value : geometry) { terminal_rest_detail::fold_value(fold, value); }
  return fold;
}

static_assert(std::is_trivially_copyable_v<geometry_inquiry_rest_record>);

}  // namespace holonics::event
