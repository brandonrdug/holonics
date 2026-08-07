#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::structure {

// Widened 2026-08-07. Sixteen cells could not hold the machine's own
// transport population, and an organ used past its declared aperture is a
// defect even when it appears to return.
inline constexpr std::size_t resident_cell_capacity = 64;
inline constexpr std::size_t resident_incidence_capacity = 256;
inline constexpr std::size_t resident_path_capacity = 16;
inline constexpr std::size_t encoded_cell_capacity = 20;
inline constexpr std::size_t encoded_incidence_capacity = 64;
inline constexpr std::uint16_t no_local_slot = 65'535;

enum class structure_status : std::uint8_t {
  exact,
  capacity_refused,
  identity_refused,
  invalid_incidence,
  invalid_traversal_seed,
  path_capacity_refused,
  departure_blocked,
  invalid_departure
};

struct encoded_cell final {
  std::uint8_t dimension{};
  std::uint64_t multiplicity{1};
};

struct encoded_incidence final {
  std::uint16_t higher_slot{};
  std::uint16_t lower_slot{};
  std::int8_t orientation{};
  std::uint64_t multiplicity{1};
};

struct structure_case final {
  std::uint64_t case_identity{};
  std::uint64_t owner_seed{1};
  encoded_cell cells[encoded_cell_capacity]{};
  encoded_incidence incidences[encoded_incidence_capacity]{};
  std::uint16_t cell_count{};
  std::uint16_t incidence_count{};
  std::uint16_t traversal_seed{no_local_slot};
  std::uint16_t departure_slot{no_local_slot};
  std::uint16_t append_isolated_count{};
};

struct admission_receipt final {
  structure_status state{structure_status::capacity_refused};
  std::uint16_t requested_cells{};
  std::uint16_t requested_incidences{};
  std::uint16_t admitted_cells{};
  std::uint16_t admitted_incidences{};
  std::uint16_t cell_capacity{static_cast<std::uint16_t>(resident_cell_capacity)};
  std::uint16_t incidence_capacity{
      static_cast<std::uint16_t>(resident_incidence_capacity)};
};

struct support_certificate final {
  structure_status state{structure_status::exact};
  std::uint16_t reachable_cells{};
  std::uint16_t touched_cells{};
  std::uint16_t touched_incidences{};
  std::uint16_t persistent_path_nodes{};
  std::uint16_t terminal_path_depth{};
  exact::word support_hash{};
  exact::word terminal_path_hash{};
};

struct structural_delta_receipt final {
  structure_status append_state{structure_status::exact};
  structure_status departure_state{structure_status::exact};
  std::uint16_t added_cells{};
  std::uint16_t removed_cells{};
  std::uint16_t removed_incidences{};
  exact::word added_first_identity{};
  exact::word removed_identity{};
};

struct structure_output final {
  std::uint64_t case_identity{};
  admission_receipt admission{};
  support_certificate traversal{};
  structural_delta_receipt delta{};
  std::uint16_t boundary_checks{};
  std::uint16_t boundary_failures{};
  std::uint16_t boundary_terms_touched{};
  std::uint16_t active_cells_before{};
  std::uint16_t active_cells_after{};
  exact::word predecessor_hash{};
  exact::word successor_hash{};
  exact::word occurrence_mint_before{};
  exact::word occurrence_mint_after{};
  std::uint64_t visited_identities[resident_path_capacity]{};
};

}  // namespace holonics::structure
