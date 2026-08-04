#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/structure/arena.hpp>
#include <holonics/structure/bounded_view.hpp>
#include <holonics/structure/identity_mint.hpp>
#include <holonics/structure/resident_types.hpp>

namespace holonics::structure {

class resident_complex final {
 public:
  resident_complex() = delete;
  HOLONICS_CALLABLE explicit resident_complex(std::uint64_t owner_seed) noexcept
      : occurrence_mint_(owner_seed),
        event_mint_(owner_seed),
        port_mint_(owner_seed),
        region_mint_(owner_seed),
        lineage_mint_(owner_seed),
        region_(region_mint_.mint()) {}

  resident_complex(const resident_complex&) = delete;
  resident_complex& operator=(const resident_complex&) = delete;
  resident_complex(resident_complex&&) = delete;
  resident_complex& operator=(resident_complex&&) = delete;

  [[nodiscard]] HOLONICS_CALLABLE structure_status admit(
      const structure_case& input,
      structure_output& output) noexcept {
    output.case_identity = input.case_identity;
    output.admission.requested_cells = input.cell_count;
    output.admission.requested_incidences = input.incidence_count;
    output.occurrence_mint_before = occurrence_mint_.next_serial();
    const bounded_view cells{input.cells, input.cell_count, encoded_cell_capacity};
    const bounded_view incidences{
        input.incidences, input.incidence_count, encoded_incidence_capacity};
    if (!cells.complete() || !incidences.complete() ||
        !cells_.can_reserve(input.cell_count) ||
        !incidences_.can_reserve(input.incidence_count)) {
      return refuse_admission(output, structure_status::capacity_refused);
    }
    if (!valid_incidence(input)) {
      return refuse_admission(output, structure_status::invalid_incidence);
    }
    const std::size_t lineage_count =
        static_cast<std::size_t>(input.cell_count) + input.incidence_count;
    if (!occurrence_mint_.can_mint(input.cell_count) ||
        !event_mint_.can_mint(input.incidence_count) ||
        !port_mint_.can_mint(input.incidence_count) ||
        !lineage_mint_.can_mint(lineage_count)) {
      return refuse_admission(output, structure_status::identity_refused);
    }

    const auto cell_reservation = cells_.reserve(input.cell_count);
    const auto incidence_reservation = incidences_.reserve(input.incidence_count);
    for (std::size_t slot = 0; slot < input.cell_count; ++slot) {
      cells_.emplace(
          cell_reservation.offset + slot,
          occurrence_mint_.mint(),
          lineage_mint_.mint(),
          region_,
          input.cells[slot].dimension,
          exact::word{input.cells[slot].multiplicity});
    }
    for (std::size_t slot = 0; slot < input.incidence_count; ++slot) {
      const auto encoded = input.incidences[slot];
      incidences_.emplace(
          incidence_reservation.offset + slot,
          encoded.higher_slot,
          encoded.lower_slot,
          event_mint_.mint(),
          port_mint_.mint(),
          lineage_mint_.mint(),
          encoded.orientation,
          exact::word{encoded.multiplicity});
      resident_cell* higher = cells_.at(encoded.higher_slot);
      resident_cell* lower = cells_.at(encoded.lower_slot);
      if (higher->outgoing_count() == 0) {
        higher->set_outgoing(static_cast<std::uint16_t>(slot), 1);
      } else {
        higher->set_outgoing(higher->outgoing_begin(), higher->outgoing_count() + 1);
      }
      higher->attach_incidence();
      lower->attach_incidence();
    }
    output.admission.state = structure_status::exact;
    output.admission.admitted_cells = input.cell_count;
    output.admission.admitted_incidences = input.incidence_count;
    output.active_cells_before = static_cast<std::uint16_t>(active_cell_count());
    output.predecessor_hash = standing_hash();
    output.occurrence_mint_after = occurrence_mint_.next_serial();
    return structure_status::exact;
  }

  HOLONICS_CALLABLE void append_isolated(
      std::uint16_t count,
      structural_delta_receipt& delta) noexcept {
    if (count == 0) {
      return;
    }
    if (!cells_.can_reserve(count) || !occurrence_mint_.can_mint(count) ||
        !lineage_mint_.can_mint(count)) {
      delta.append_state = structure_status::capacity_refused;
      return;
    }
    const auto reservation = cells_.reserve(count);
    for (std::size_t offset = 0; offset < count; ++offset) {
      const auto occurrence = occurrence_mint_.mint();
      if (offset == 0) {
        delta.added_first_identity = occurrence.serial();
      }
      cells_.emplace(
          reservation.offset + offset,
          occurrence,
          lineage_mint_.mint(),
          region_,
          std::uint8_t{0},
          exact::word{1});
    }
    delta.added_cells = count;
  }

  HOLONICS_CALLABLE void depart(
      std::uint16_t slot,
      structural_delta_receipt& delta) noexcept {
    if (slot == no_local_slot) {
      return;
    }
    resident_cell* cell = cells_.at(slot);
    if (cell == nullptr || !cell->active()) {
      delta.departure_state = structure_status::invalid_departure;
      return;
    }
    if (cell->incident_count() != 0) {
      delta.departure_state = structure_status::departure_blocked;
      return;
    }
    delta.removed_identity = cell->occurrence().serial();
    delta.removed_cells = 1;
    cell->depart();
  }

  [[nodiscard]] HOLONICS_CALLABLE resident_cell* cell(std::size_t slot) noexcept {
    return cells_.at(slot);
  }
  [[nodiscard]] HOLONICS_CALLABLE const resident_cell* cell(std::size_t slot) const noexcept {
    return cells_.at(slot);
  }
  [[nodiscard]] HOLONICS_CALLABLE const resident_incidence* incidence(
      std::size_t slot) const noexcept {
    return incidences_.at(slot);
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::size_t cell_count() const noexcept {
    return cells_.used();
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::size_t incidence_count() const noexcept {
    return incidences_.used();
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::size_t path_count() const noexcept {
    return paths_.used();
  }
  [[nodiscard]] HOLONICS_CALLABLE arena<persistent_path_node, resident_path_capacity>& paths()
      noexcept {
    return paths_;
  }
  [[nodiscard]] HOLONICS_CALLABLE std::size_t active_cell_count() const noexcept;
  [[nodiscard]] HOLONICS_CALLABLE exact::word standing_hash() const noexcept;
  [[nodiscard]] HOLONICS_CALLABLE exact::word occurrence_mint_cursor() const noexcept {
    return occurrence_mint_.next_serial();
  }

 private:
  [[nodiscard]] HOLONICS_CALLABLE bool valid_incidence(const structure_case& input) const noexcept;
  [[nodiscard]] HOLONICS_CALLABLE structure_status refuse_admission(
      structure_output& output,
      structure_status state) noexcept;

  identity_mint<occurrence_identity_owner> occurrence_mint_;
  identity_mint<event_identity_owner> event_mint_;
  identity_mint<port_identity_owner> port_mint_;
  identity_mint<region_identity_owner> region_mint_;
  identity_mint<lineage_identity_owner> lineage_mint_;
  identity<region_identity_owner> region_;
  arena<resident_cell, resident_cell_capacity> cells_{};
  arena<resident_incidence, resident_incidence_capacity> incidences_{};
  arena<persistent_path_node, resident_path_capacity> paths_{};
};

}  // namespace holonics::structure
