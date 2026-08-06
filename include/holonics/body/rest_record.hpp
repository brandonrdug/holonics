#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::body {

inline constexpr std::size_t live_region_capacity = 4;

/// One region of the continuing body's rest.
///
/// `admitted_tally` is **provenance: a count of admitted deeds.** It was named
/// `morphology` until 2026-08-06, which made the standing of every mathematical
/// deed misdescribe itself — the excision of 2026-08-05 renamed the receipts and
/// left the standing untouched, so the convicted word survived in the one place
/// it mattered most.
///
/// **A morphology is the contemporary causal organization by which a body
/// receives, transforms, retains, and emits differences.** It is never a number.
/// A field of this type may be carried, folded into an integrity word, and
/// reported as provenance; it may never be read as evidence that anything was
/// learned.
struct rest_region final {
  std::uint64_t admitted_tally{};
  std::uint64_t current{};
};

struct rest_record final {
  std::uint64_t head{};
  std::uint64_t next_head{};
  std::uint64_t continuation{};
  std::uint64_t next_continuation{};
  std::uint64_t lineage{};
  rest_region regions[live_region_capacity]{};
  std::uint64_t integrity{};
};

struct rest_receipt final {
  bool returned{};
  bool integrity_exact{};
  std::uint16_t source_replay_count{};
  exact::word head{};
  exact::word continuation{};
  exact::word integrity{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t rest_integrity(
    const rest_record& record) noexcept {
  std::uint64_t fold = 14'695'981'039'346'656'037ULL;
  constexpr std::uint64_t prime = 1'099'511'628'211ULL;
  const std::uint64_t prefix[5]{record.head, record.next_head, record.continuation,
      record.next_continuation, record.lineage};
  for (std::size_t field = 0; field < 5; ++field) {
    std::uint64_t value = prefix[field];
    for (std::size_t octet = 0; octet < 8; ++octet) {
      fold ^= value & 255U;
      fold *= prime;
      value >>= 8U;
    }
  }
  for (std::size_t region = 0; region < live_region_capacity; ++region) {
    std::uint64_t values[2]{record.regions[region].admitted_tally, record.regions[region].current};
    for (std::size_t field = 0; field < 2; ++field) {
      for (std::size_t octet = 0; octet < 8; ++octet) {
        fold ^= values[field] & 255U;
        fold *= prime;
        values[field] >>= 8U;
      }
    }
  }
  return fold;
}

}  // namespace holonics::body
