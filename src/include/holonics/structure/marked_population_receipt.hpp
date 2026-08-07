#pragma once

#include <cstdint>

#include <holonics/exact/word.hpp>
#include <holonics/structure/receipt.hpp>

namespace holonics::structure {

enum class marked_population_status : std::uint8_t { exact, capacity_refused, malformed };

struct marked_population_receipt final {
  using holonics_receipt = receipt_marker;
  marked_population_status state{marked_population_status::exact};
  std::uint16_t source_count{};
  std::uint16_t occurrence_count{};
  std::uint16_t relation_count{};
  exact::word occurrence_fold{};
  exact::word relation_fold{};
};

}  // namespace holonics::structure
