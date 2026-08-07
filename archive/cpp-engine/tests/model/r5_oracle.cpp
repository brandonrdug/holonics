#include "r5_oracle.hpp"

#include <cstddef>
#include <cstdint>

namespace holonics::tests {
namespace {

struct oracle_state final {
  current::sparse_current active[current::sparse_current_capacity]{};
  current::sparse_current staged[current::sparse_current_capacity]{};
  current::morphology_cell morphology[current::program_site_capacity]{};
  current::current_delta deltas[current::current_delta_capacity]{};
  std::uint64_t head{};
  std::uint64_t next_occurrence{};
  std::uint64_t next_event{};
  std::uint64_t touched{};
  std::uint16_t active_count{};
  std::uint16_t delta_count{};
};

bool transform(std::uint64_t value,
    std::uint64_t scale,
    std::uint64_t offset,
    std::uint16_t multiplicity,
    std::uint64_t& result) noexcept {
  if (scale != 0 && value > ~std::uint64_t{0} / scale) { return false; }
  const std::uint64_t scaled = value * scale;
  if (scaled > ~std::uint64_t{0} - offset) { return false; }
  const std::uint64_t shifted = scaled + offset;
  if (multiplicity != 0 && shifted > ~std::uint64_t{0} / multiplicity) { return false; }
  result = shifted * multiplicity;
  return true;
}

std::uint64_t current_fold(
    const current::sparse_current* values,
    std::size_t count) noexcept {
  std::uint64_t fold = 14'695'981'039'346'656'037ULL;
  constexpr std::uint64_t prime = 1'099'511'628'211ULL;
  for (std::size_t slot = 0; slot < count; ++slot) {
    const std::uint64_t fields[5]{values[slot].occurrence.value(),
        values[slot].lineage.value(), values[slot].local_state.value(),
        values[slot].caused_support.value(), values[slot].site};
    for (std::size_t field = 0; field < 5; ++field) {
      fold ^= fields[field];
      fold *= prime;
    }
  }
  return fold;
}

void certify(const current::causal_program& program,
    const oracle_state& state,
    current::current_observation& output) noexcept {
  output.compositional_quiescence = true;
  for (std::size_t component = 0; component < program.component_count; ++component) {
    auto& receipt = output.components[component];
    receipt = {};
    for (std::size_t slot = 0; slot < state.active_count; ++slot) {
      if (state.active[slot].component == component) { ++receipt.local_current; }
    }
    receipt.certified = receipt.local_current == 0;
    output.compositional_quiescence &= receipt.certified;
  }
}

void observe(const current::causal_program& program,
    const oracle_state& state,
    current::current_observation& output) noexcept {
  output.program_identity = program.identity;
  output.predecessor = program.predecessor;
  output.successor = exact::word{state.head};
  output.receiver_support = program.receiver_support;
  output.touched_support = exact::word{state.touched};
  output.final_current_count = state.active_count;
  output.delta_count = state.delta_count;
  output.source_detached = true;
  for (std::size_t slot = 0; slot < state.active_count; ++slot) {
    output.final_currents[slot] = state.active[slot];
  }
  for (std::size_t slot = 0; slot < program.site_count; ++slot) {
    output.morphology[slot] = state.morphology[slot];
  }
  for (std::size_t slot = 0; slot < state.delta_count; ++slot) {
    output.deltas[slot] = state.deltas[slot];
  }
  certify(program, state, output);
}

void advance_case(const current::causal_program& program,
    current::current_observation& output) noexcept {
  oracle_state state{};
  state.head = program.predecessor.value();
  state.next_occurrence = program.next_occurrence.value();
  state.next_event = program.next_event.value();
  state.active_count = program.initial_current_count;
  for (std::size_t slot = 0; slot < program.site_count; ++slot) {
    state.morphology[slot] = program.morphology[slot];
  }
  for (std::size_t slot = 0; slot < state.active_count; ++slot) {
    state.active[slot] = program.initial_currents[slot];
  }
  output.state = current::current_status::mounted;
  for (std::uint16_t frontier = 0; frontier < program.receiver_front_aperture; ++frontier) {
    if (state.active_count == 0) {
      output.state = current::current_status::exact_rest;
      break;
    }
    auto& front = output.fronts[frontier];
    front.predecessor = exact::word{state.head};
    front.event_first = exact::word{state.next_event};
    front.input_count = state.active_count;
    state.next_event += state.active_count;
    std::uint16_t offsets[current::sparse_current_capacity]{};
    std::uint16_t counts[current::sparse_current_capacity]{};
    std::uint16_t produced = 0;
    for (std::size_t slot = 0; slot < state.active_count; ++slot) {
      const auto& site = program.sites[state.active[slot].site];
      counts[slot] = site.arc_count != 0 ? site.arc_count :
          static_cast<std::uint16_t>(site.outbound_port.value() != 0 ? 1U : 0U);
      offsets[slot] = produced;
      produced = static_cast<std::uint16_t>(produced + counts[slot]);
    }
    const std::uint64_t occurrence_first = state.next_occurrence;
    state.next_occurrence += produced;
    front.output_count = produced;
    front.pending_before = state.active_count;
    bool reserved[current::program_site_capacity]{};
    current::current_obstruction failure = current::current_obstruction::none;
    std::uint64_t read_support = 0;
    std::uint64_t change_support = 0;
    std::uint16_t open_count = 0;
    for (std::size_t slot = 0; slot < state.active_count; ++slot) {
      const auto value = state.active[slot];
      const auto& site = program.sites[value.site];
      read_support |= value.caused_support.value();
      std::uint64_t member_change_support = site.support.value();
      std::uint64_t transformed = 0;
      const bool exact = transform(value.local_state.value(),
          state.morphology[value.site].scale.value(),
          state.morphology[value.site].offset.value(), 1, transformed);
      if (!exact) { failure = current::current_obstruction::arithmetic_overflow; }
      for (std::size_t offset = 0; exact && offset < counts[slot]; ++offset) {
        const std::size_t target_slot = offsets[slot] + offset;
        auto successor = value;
        successor.occurrence = exact::word{occurrence_first + target_slot};
        successor.phase = static_cast<std::uint16_t>(value.phase + 1U);
        successor.open = site.arc_count == 0;
        std::uint64_t output_value = transformed;
        if (site.arc_count != 0) {
          const auto& arc = program.arcs[site.first_arc + offset];
          if (reserved[arc.target]) { failure = current::current_obstruction::reservation_conflict; }
          reserved[arc.target] = true;
          if (!transform(transformed, arc.multiplicity, 0, 1, output_value)) {
            failure = current::current_obstruction::arithmetic_overflow;
          }
          successor.site = arc.target;
          successor.component = program.sites[arc.target].component;
          successor.caused_support = exact::word{value.caused_support.value() |
              program.sites[arc.target].support.value()};
          successor.lineage = exact::word{
              value.lineage.value() + arc.lineage.value() + front.event_first.value() + slot};
          successor.multiplicity = arc.multiplicity;
          member_change_support |= program.sites[arc.target].support.value();
        } else {
          successor.lineage = exact::word{
              value.lineage.value() + front.event_first.value() + slot};
          ++open_count;
        }
        successor.local_state = exact::word{output_value};
        state.staged[target_slot] = successor;
      }
      change_support |= member_change_support;
      auto& delta = state.deltas[state.delta_count + slot];
      delta = {exact::word{state.head}, exact::word{front.event_first.value() + slot},
          exact::word{front.event_first.value() + slot}, value.caused_support,
          exact::word{member_change_support}, static_cast<std::int64_t>(counts[slot]) - 1,
          exact::word{transformed}, exact::word{transformed},
          exact::word{value.multiplicity}, exact::word{static_cast<std::uint64_t>(failure)},
          exact::word{counts[slot]},
          exact::word{value.lineage.value() + front.event_first.value() + slot},
          value.site, counts[slot]};
    }
    state.touched |= read_support;
    front.read_support = exact::word{read_support};
    front.change_support = exact::word{change_support};
    front.pending_after = 0;
    ++output.front_count;
    state.delta_count = static_cast<std::uint16_t>(state.delta_count + state.active_count);
    if (failure != current::current_obstruction::none) {
      front.successor = front.predecessor;
      output.state = current::current_status::obstructed;
      output.obstruction = failure;
      break;
    }
    for (std::size_t slot = 0; slot < state.active_count; ++slot) {
      auto& morphology = state.morphology[state.active[slot].site];
      morphology.passages = exact::word{morphology.passages.value() + 1U};
    }
    ++state.head;
    front.successor = exact::word{state.head};
    front.current_fold = exact::word{current_fold(state.staged, produced)};
    front.reservations = produced;
    state.active_count = produced;
    for (std::size_t slot = 0; slot < produced; ++slot) { state.active[slot] = state.staged[slot]; }
    if (open_count != 0) { output.state = current::current_status::open_frontier; break; }
    if (produced == 0) { output.state = current::current_status::exact_rest; break; }
    if (frontier + 1U == program.receiver_front_aperture) {
      output.state = current::current_status::open_frontier;
      output.obstruction = current::current_obstruction::receiver_aperture;
    }
  }
  observe(program, state, output);
}

}  // namespace

current::current_batch_observation r5_oracle(
    const current::current_mount_batch& mount) noexcept {
  current::current_batch_observation output{};
  output.count = mount.count;
  for (std::size_t slot = 0; slot < mount.count; ++slot) {
    advance_case(mount.programs[slot], output.cases[slot]);
  }
  return output;
}

}  // namespace holonics::tests
