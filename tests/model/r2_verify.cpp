#include "r2_verify.hpp"

#include <cstddef>
#include <cstdint>

namespace holonics::tests {
namespace {

void mix(std::uint64_t& hash, std::uint64_t value) noexcept {
  constexpr std::uint64_t prime = 1'099'511'628'211ULL;
  for (std::size_t octet = 0; octet < 8; ++octet) {
    hash ^= value & 255U;
    hash *= prime;
    value >>= 8U;
  }
}

[[nodiscard]] std::uint16_t outgoing_count(
    const structure::structure_case& input,
    std::size_t cell) noexcept {
  std::uint16_t count = 0;
  for (std::size_t slot = 0; slot < input.incidence_count; ++slot) {
    if (input.incidences[slot].higher_slot == cell) {
      ++count;
    }
  }
  return count;
}

[[nodiscard]] std::uint64_t standing_hash(
    const structure::structure_case& input,
    std::size_t appended,
    std::uint16_t departed) noexcept {
  std::uint64_t hash = 14'695'981'039'346'656'037ULL;
  const std::size_t removed = departed == structure::no_local_slot ? 0 : 1;
  mix(hash, static_cast<std::uint64_t>(input.cell_count + appended - removed));
  for (std::size_t slot = 0; slot < input.cell_count + appended; ++slot) {
    if (slot == departed) {
      continue;
    }
    mix(hash, input.owner_seed + slot);
    mix(hash, slot < input.cell_count ? input.cells[slot].dimension : 0);
    mix(hash, slot < input.cell_count ? outgoing_count(input, slot) : 0);
  }
  for (std::size_t slot = 0; slot < input.incidence_count; ++slot) {
    const auto relation = input.incidences[slot];
    mix(hash, relation.higher_slot);
    mix(hash, relation.lower_slot);
    mix(hash, static_cast<std::uint8_t>(relation.orientation));
    mix(hash, relation.multiplicity);
  }
  return hash;
}

struct boundary_expectation final {
  std::uint16_t checks{};
  std::uint16_t failures{};
  std::uint16_t terms{};
};

[[nodiscard]] boundary_expectation boundary_oracle(
    const structure::structure_case& input) noexcept {
  boundary_expectation expected{};
  for (std::size_t top = 0; top < input.cell_count; ++top) {
    if (input.cells[top].dimension < 2) {
      continue;
    }
    ++expected.checks;
    std::int64_t coefficients[structure::encoded_cell_capacity]{};
    for (std::size_t first = 0; first < input.incidence_count; ++first) {
      if (input.incidences[first].higher_slot != top) {
        continue;
      }
      const std::uint16_t middle = input.incidences[first].lower_slot;
      for (std::size_t second = 0; second < input.incidence_count; ++second) {
        if (input.incidences[second].higher_slot != middle) {
          continue;
        }
        ++expected.terms;
        const std::int64_t first_value = input.incidences[first].orientation *
            static_cast<std::int64_t>(input.incidences[first].multiplicity);
        const std::int64_t second_value = input.incidences[second].orientation *
            static_cast<std::int64_t>(input.incidences[second].multiplicity);
        coefficients[input.incidences[second].lower_slot] += first_value * second_value;
      }
    }
    for (std::size_t slot = 0; slot < input.cell_count; ++slot) {
      if (coefficients[slot] != 0) {
        ++expected.failures;
        break;
      }
    }
  }
  return expected;
}

struct traversal_expectation final {
  std::uint16_t cells{};
  std::uint16_t incidences{};
  std::uint16_t path_depth{};
  std::uint64_t hash{};
  std::uint64_t path_hash{};
  std::uint64_t identities[structure::resident_path_capacity]{};
};

[[nodiscard]] traversal_expectation traversal_oracle(
    const structure::structure_case& input) noexcept {
  traversal_expectation expected{};
  if (input.traversal_seed == structure::no_local_slot) {
    return expected;
  }
  bool visited[structure::encoded_cell_capacity]{};
  std::uint16_t queue[structure::encoded_cell_capacity]{};
  std::uint16_t parent[structure::encoded_cell_capacity]{};
  std::size_t head = 0;
  std::size_t tail = 1;
  queue[0] = input.traversal_seed;
  parent[0] = structure::no_local_slot;
  visited[input.traversal_seed] = true;
  expected.hash = 14'695'981'039'346'656'037ULL;
  while (head < tail) {
    const std::uint16_t cell = queue[head];
    expected.identities[head] = input.owner_seed + cell;
    mix(expected.hash, expected.identities[head]);
    for (std::size_t slot = 0; slot < input.incidence_count; ++slot) {
      if (input.incidences[slot].higher_slot != cell) {
        continue;
      }
      ++expected.incidences;
      const std::uint16_t lower = input.incidences[slot].lower_slot;
      if (!visited[lower]) {
        visited[lower] = true;
        queue[tail] = lower;
        parent[tail] = static_cast<std::uint16_t>(head);
        ++tail;
      }
    }
    ++head;
  }
  expected.cells = static_cast<std::uint16_t>(tail);
  std::uint16_t cursor = static_cast<std::uint16_t>(tail - 1);
  expected.path_hash = 14'695'981'039'346'656'037ULL;
  while (cursor != structure::no_local_slot) {
    mix(expected.path_hash, input.owner_seed + queue[cursor]);
    ++expected.path_depth;
    cursor = parent[cursor];
  }
  return expected;
}

}  // namespace

std::size_t r2_verification_failures(
    const r2_input_batch& inputs,
    const r2_output_batch& outputs) noexcept {
  std::size_t failures = 0;
  for (std::size_t case_slot = 0; case_slot < inputs.size(); ++case_slot) {
    const auto& input = inputs[case_slot];
    const auto& output = outputs[case_slot];
    const bool admitted = input.cell_count <= structure::resident_cell_capacity &&
        input.incidence_count <= structure::resident_incidence_capacity;
    const auto admission_state = admitted
        ? structure::structure_status::exact
        : structure::structure_status::capacity_refused;
    if (output.case_identity != input.case_identity ||
        output.admission.state != admission_state ||
        output.occurrence_mint_before.value() != input.owner_seed) {
      ++failures;
      continue;
    }
    if (!admitted) {
      if (output.predecessor_hash != output.successor_hash ||
          output.occurrence_mint_after.value() != input.owner_seed) {
        ++failures;
      }
      continue;
    }
    const auto boundary = boundary_oracle(input);
    const auto traversal = traversal_oracle(input);
    const bool append_accepted = input.cell_count + input.append_isolated_count <=
        structure::resident_cell_capacity;
    const std::size_t appended = append_accepted ? input.append_isolated_count : 0;
    std::uint16_t departed = structure::no_local_slot;
    structure::structure_status departure_state = structure::structure_status::exact;
    if (input.departure_slot != structure::no_local_slot) {
      if (outgoing_count(input, input.departure_slot) != 0) {
        departure_state = structure::structure_status::departure_blocked;
      } else {
        bool incoming = false;
        for (std::size_t slot = 0; slot < input.incidence_count; ++slot) {
          incoming = incoming || input.incidences[slot].lower_slot == input.departure_slot;
        }
        if (incoming) {
          departure_state = structure::structure_status::departure_blocked;
        } else {
          departed = input.departure_slot;
        }
      }
    }
    const std::size_t removed = departed == structure::no_local_slot ? 0 : 1;
    const std::uint64_t expected_mint = input.owner_seed + input.cell_count + appended;
    if (output.boundary_checks != boundary.checks ||
        output.boundary_failures != boundary.failures ||
        output.boundary_terms_touched != boundary.terms ||
        output.traversal.reachable_cells != traversal.cells ||
        output.traversal.touched_cells != traversal.cells ||
        output.traversal.touched_incidences != traversal.incidences ||
        output.traversal.persistent_path_nodes != traversal.cells ||
        output.traversal.support_hash.value() != traversal.hash ||
        output.traversal.terminal_path_depth != traversal.path_depth ||
        output.traversal.terminal_path_hash.value() != traversal.path_hash ||
        output.delta.append_state != (append_accepted
            ? structure::structure_status::exact
            : structure::structure_status::capacity_refused) ||
        output.delta.departure_state != departure_state ||
        output.delta.added_cells != appended || output.delta.removed_cells != removed ||
        output.active_cells_before != input.cell_count ||
        output.active_cells_after != input.cell_count + appended - removed ||
        output.occurrence_mint_after.value() != expected_mint ||
        output.predecessor_hash.value() != standing_hash(input, 0, structure::no_local_slot) ||
        output.successor_hash.value() != standing_hash(input, appended, departed)) {
      ++failures;
      continue;
    }
    for (std::size_t slot = 0; slot < structure::resident_path_capacity; ++slot) {
      if (output.visited_identities[slot] != traversal.identities[slot]) {
        ++failures;
        break;
      }
    }
  }
  return failures;
}

}  // namespace holonics::tests
