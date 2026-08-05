#pragma once

#include <cstdint>

#include <holonics/organ/arithmetic_spectral_schema.hpp>

namespace holonics::organ {

struct field_candidate_receipt final {
  std::uint16_t prime{};
  std::uint8_t degree{};
  std::uint32_t code{};
  std::uint16_t coefficient[arithmetic_degree_count + 1]{};
  std::uint32_t divisor_code{};
  bool irreducible{};
  exact::word lineage{};
};

struct field_tower_receipt final {
  extension_field_spec fields[arithmetic_degree_count]{};
  field_candidate_receipt candidates[arithmetic_field_candidate_capacity]{};
  std::uint8_t candidate_count{};
  std::uint16_t imaginary_unit{};
  bool exact{};
  exact::word lineage{};
};

struct fixed_locus_contribution final {
  std::uint8_t curve{};
  std::uint8_t degree{};
  std::uint32_t x_encoding{};
  std::uint32_t rhs_encoding{};
  std::int8_t character{};
  std::uint8_t point_count{};
  exact::word lineage{};
};

}  // namespace holonics::organ
