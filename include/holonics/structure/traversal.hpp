#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/structure/resident_complex_law.hpp>

namespace holonics::structure {

HOLONICS_CALLABLE inline void traverse_boundary_support(
    resident_complex& complex,
    std::uint16_t seed,
    structure_output& output) noexcept {
  if (seed == no_local_slot) {
    return;
  }
  const resident_cell* seed_cell = complex.cell(seed);
  if (seed_cell == nullptr || !seed_cell->active()) {
    output.traversal.state = structure_status::invalid_traversal_seed;
    return;
  }

  bool visited[resident_cell_capacity]{};
  std::uint16_t queue[resident_cell_capacity]{};
  std::size_t head = 0;
  std::size_t tail = 1;
  queue[0] = seed;
  visited[seed] = true;
  auto reservation = complex.paths().reserve(1);
  if (!reservation.accepted()) {
    output.traversal.state = structure_status::path_capacity_refused;
    return;
  }
  complex.paths().emplace(
      reservation.offset, seed_cell->occurrence(), std::uint16_t{65'535});

  std::uint64_t support_hash = 14'695'981'039'346'656'037ULL;
  while (head < tail) {
    const std::uint16_t slot = queue[head];
    const resident_cell* current = complex.cell(slot);
    output.visited_identities[head] = current->occurrence().serial().value();
    detail::mix_hash(support_hash, output.visited_identities[head]);
    ++output.traversal.touched_cells;
    for (std::size_t offset = 0; offset < current->outgoing_count(); ++offset) {
      const resident_incidence* relation = complex.incidence(
          static_cast<std::size_t>(current->outgoing_begin()) + offset);
      if (!relation->active()) {
        continue;
      }
      ++output.traversal.touched_incidences;
      const std::uint16_t lower_slot = relation->lower_slot();
      const resident_cell* lower = complex.cell(lower_slot);
      if (visited[lower_slot] || !lower->active()) {
        continue;
      }
      reservation = complex.paths().reserve(1);
      if (!reservation.accepted() || tail >= resident_cell_capacity) {
        output.traversal.state = structure_status::path_capacity_refused;
        return;
      }
      visited[lower_slot] = true;
      queue[tail] = lower_slot;
      complex.paths().emplace(
          reservation.offset, lower->occurrence(), static_cast<std::uint16_t>(head));
      ++tail;
    }
    ++head;
  }
  output.traversal.reachable_cells = static_cast<std::uint16_t>(tail);
  output.traversal.persistent_path_nodes = static_cast<std::uint16_t>(complex.path_count());
  output.traversal.support_hash = exact::word{support_hash};
  std::uint16_t cursor = static_cast<std::uint16_t>(tail - 1);
  std::uint64_t path_hash = 14'695'981'039'346'656'037ULL;
  while (cursor != no_local_slot) {
    const persistent_path_node* node = complex.paths().at(cursor);
    detail::mix_hash(path_hash, node->occurrence().serial().value());
    ++output.traversal.terminal_path_depth;
    cursor = node->parent();
  }
  output.traversal.terminal_path_hash = exact::word{path_hash};
}

}  // namespace holonics::structure
