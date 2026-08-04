#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/receiver/condensation_law.hpp>

namespace holonics::receiver {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool make_group_sums(
    const exact::word* source_values,
    std::size_t source_count,
    const std::uint16_t* groups,
    std::size_t group_count,
    exact::word* sums) noexcept {
  for (std::size_t group = 0; group < group_count; ++group) { sums[group] = {}; }
  for (std::size_t source = 0; source < source_count; ++source) {
    std::uint64_t next = 0;
    if (groups[source] >= group_count ||
        !geometry_add(sums[groups[source]].value(), source_values[source].value(), next)) {
      return false;
    }
    sums[groups[source]] = exact::word{next};
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool direct_response(
    const exact::word* source_values,
    std::size_t source_count,
    const future_receiver_family& family,
    const condensation_input& input,
    exact::word& response) noexcept {
  std::uint64_t result = 0;
  for (std::size_t source = 0; source < source_count; ++source) {
    std::uint64_t value = source_values[source].value();
    std::uint64_t contribution = 0;
    if (source == input.source_cell && !geometry_add(value, input.delta.value(), value)) {
      return false;
    }
    if (!geometry_multiply(value, family.query_weights[input.query][source].value(),
            contribution) || !geometry_add(result, contribution, result)) {
      return false;
    }
  }
  response = exact::word{result};
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool boundary_response(
    const exact::word* group_sums,
    const std::uint16_t* groups,
    std::size_t source_count,
    std::size_t group_count,
    const future_receiver_family& family,
    const condensation_input& input,
    exact::word& response) noexcept {
  std::uint64_t result = 0;
  for (std::size_t group = 0; group < group_count; ++group) {
    std::uint64_t sum = group_sums[group].value();
    std::uint64_t contribution = 0;
    if (group == groups[input.source_cell] && !geometry_add(sum, input.delta.value(), sum)) {
      return false;
    }
    std::size_t representative = source_count;
    for (std::size_t source = 0; source < source_count; ++source) {
      if (groups[source] == group) { representative = source; break; }
    }
    if (representative == source_count ||
        !geometry_multiply(sum, family.query_weights[input.query][representative].value(),
            contribution) || !geometry_add(result, contribution, result)) {
      return false;
    }
  }
  response = exact::word{result};
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr condensed_snapshot make_condensed_snapshot(
    const condensation_program& program,
    const exact::word* source_values,
    exact::word head,
    exact::word morphology,
    exact::word current,
    exact::word lineage,
    exact::word logical_resource,
    condensation_obstruction obstruction) noexcept {
  condensed_snapshot result{};
  result.head = head;
  result.incidence = program.incidence;
  result.morphology = morphology;
  result.current = current;
  result.lineage = lineage;
  result.logical_resource = logical_resource;
  result.alternatives = program.alternatives;
  result.obstruction = obstruction;
  result.source_count = program.source_count;
  for (std::size_t slot = 0; slot < program.source_count; ++slot) {
    result.source_identities[slot] = program.source_identities[slot];
    result.source_values[slot] = source_values[slot];
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool apply_snapshot_delta(
    condensed_snapshot& snapshot,
    const condensation_input& input,
    exact::word successor_head,
    exact::word response) noexcept {
  std::uint64_t source = 0;
  std::uint64_t morphology = 0;
  std::uint64_t lineage = 0;
  std::uint64_t resource = 0;
  if (!geometry_add(snapshot.source_values[input.source_cell].value(), input.delta.value(), source) ||
      !geometry_add(snapshot.morphology.value(), input.delta.value(), morphology) ||
      !geometry_add(snapshot.lineage.value(), input.lineage.value(), lineage) ||
      !geometry_add(snapshot.logical_resource.value(), 1U, resource)) {
    return false;
  }
  snapshot.head = successor_head;
  snapshot.source_values[input.source_cell] = exact::word{source};
  snapshot.morphology = exact::word{morphology};
  snapshot.current = response;
  snapshot.lineage = exact::word{lineage};
  snapshot.logical_resource = exact::word{resource};
  return true;
}

}  // namespace holonics::receiver
