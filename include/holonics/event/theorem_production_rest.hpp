#pragma once

#include <cstddef>
#include <cstdint>
#include <type_traits>

#include <holonics/body/rest_record.hpp>
#include <holonics/organ/theorem_production_schema.hpp>

namespace holonics::event {

struct theorem_production_rest_record final {
  body::rest_record body{};
  organ::acquired_theorem_fiber acquired{};
  std::uint64_t mathematical_morphology{};
  std::uint64_t codec_morphology{};
  std::uint64_t integrity{};
};

struct theorem_production_rest_receipt final {
  body::rest_receipt body{};
  exact::word acquired_fiber{};
  exact::word integrity{};
  std::uint32_t retained_source_bytes{};
  bool source_detached{};
  bool returned{};
};

struct theorem_production_remount_receipt final {
  body::rest_receipt body{};
  exact::word acquired_fiber{};
  bool same_body{};
  bool acquired_return_preserved{};
  bool source_replayed{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t theorem_production_rest_integrity(
    const theorem_production_rest_record& record) noexcept {
  std::uint64_t fold = record.body.integrity;
  constexpr std::uint64_t prime = 1'099'511'628'211ULL;
  const std::uint64_t values[11]{record.acquired.identity.value(),
      record.acquired.passage.value(), record.acquired.statement.value(),
      record.acquired.proof.value(), record.acquired.kernel_return.value(),
      record.acquired.selected_rule.value(), record.acquired.morphology_delta.value(),
      record.acquired.dependency_count, record.acquired.accepted ? 1U : 0U,
      record.mathematical_morphology, record.codec_morphology};
  for (const auto value : values) {
    std::uint64_t remainder = value;
    for (std::size_t octet = 0; octet < 8; ++octet) {
      fold ^= remainder & 255U;
      fold *= prime;
      remainder >>= 8U;
    }
  }
  return fold;
}

static_assert(std::is_trivially_copyable_v<theorem_production_rest_record>);

}  // namespace holonics::event
