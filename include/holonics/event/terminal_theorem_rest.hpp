#pragma once

#include <cstddef>
#include <cstdint>
#include <type_traits>

#include <holonics/body/rest_record.hpp>
#include <holonics/organ/theorem_production_schema.hpp>

namespace holonics::event {

struct terminal_theorem_rest_record final {
  body::rest_record body{};
  organ::acquired_theorem_fiber first{};
  organ::acquired_theorem_fiber second{};
  std::uint64_t mathematical_morphology{};
  std::uint64_t codec_morphology{};
  std::uint64_t integrity{};
};

struct terminal_theorem_rest_receipt final {
  body::rest_receipt body{};
  exact::word first_fiber{};
  exact::word second_fiber{};
  exact::word integrity{};
  std::uint32_t retained_source_bytes{};
  bool source_detached{};
  bool returned{};
};

struct terminal_theorem_remount_receipt final {
  body::rest_receipt body{};
  exact::word first_fiber{};
  exact::word second_fiber{};
  bool same_body{};
  bool both_returns_preserved{};
  bool source_replayed{};
};

namespace terminal_rest_detail {

HOLONICS_CALLABLE constexpr void fold_value(std::uint64_t& fold, std::uint64_t value) noexcept {
  constexpr std::uint64_t prime = 1'099'511'628'211ULL;
  for (std::size_t octet = 0; octet < 8; ++octet) {
    fold ^= value & 255U;
    fold *= prime;
    value >>= 8U;
  }
}

HOLONICS_CALLABLE constexpr void fold_fiber(
    std::uint64_t& fold, const organ::acquired_theorem_fiber& fiber) noexcept {
  const std::uint64_t values[9]{fiber.identity.value(), fiber.passage.value(),
      fiber.statement.value(), fiber.proof.value(), fiber.kernel_return.value(),
      fiber.selected_rule.value(), fiber.morphology_delta.value(), fiber.dependency_count,
      fiber.accepted ? 1U : 0U};
  for (const auto value : values) { fold_value(fold, value); }
}

}  // namespace terminal_rest_detail

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t terminal_theorem_rest_integrity(
    const terminal_theorem_rest_record& record) noexcept {
  std::uint64_t fold = record.body.integrity;
  terminal_rest_detail::fold_fiber(fold, record.first);
  terminal_rest_detail::fold_fiber(fold, record.second);
  terminal_rest_detail::fold_value(fold, record.mathematical_morphology);
  terminal_rest_detail::fold_value(fold, record.codec_morphology);
  return fold;
}

static_assert(std::is_trivially_copyable_v<terminal_theorem_rest_record>);

}  // namespace holonics::event
