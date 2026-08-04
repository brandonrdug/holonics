#pragma once

#include <cstdint>

#include <holonics/structure/receipt.hpp>

namespace holonics::receiver {

enum class navigation_status : std::uint8_t {
  exact,
  empty_preimage,
  requested_occurrence_outside_preimage,
  malformed_chart
};

struct preimage_receipt final {
  using holonics_receipt = structure::receipt_marker;
  navigation_status state{navigation_status::exact};
  std::uint8_t face{};
  std::uint16_t projection_words_touched{};
  std::uint16_t occurrences_touched{};
  std::uint64_t occurrence_fold{};
  std::uint64_t selected_occurrence{};
};

struct local_support_receipt final {
  using holonics_receipt = structure::receipt_marker;
  std::uint16_t occurrence_count{};
  std::uint16_t relation_count{};
  std::uint16_t source_occurrence_count{};
  std::uint16_t source_relation_count{};
  std::uint64_t occurrence_identities[5]{};
  std::uint8_t payloads[5]{};
};

struct transition_receipt final {
  using holonics_receipt = structure::receipt_marker;
  bool invertible{};
  bool determinant_negative{};
  std::uint64_t determinant_magnitude{};
  std::uint64_t sequence_first{};
  std::uint64_t sequence_second{};
  std::uint64_t projected_first{};
  std::uint64_t projected_second{};
};

struct overlap_receipt final {
  using holonics_receipt = structure::receipt_marker;
  std::uint64_t occurrence{};
  std::uint64_t projection_chart{};
  std::uint64_t sequence_chart{};
  bool same_source_occurrence{};
};

struct navigation_receipt final {
  preimage_receipt preimage{};
  local_support_receipt support{};
  transition_receipt transition{};
  overlap_receipt overlap{};
  preimage_receipt obstruction{};
  std::uint16_t source_bytes_visible_to_query{};
};

}  // namespace holonics::receiver
