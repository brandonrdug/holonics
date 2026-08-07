#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/receiver/geometry_exact.hpp>

namespace holonics::receiver {

[[nodiscard]] HOLONICS_CALLABLE constexpr projection_receipt project_shadow(
    const projection_program& program) noexcept {
  projection_receipt result{};
  result.source_incidence_before = program.source_incidence;
  result.source_incidence_after = program.source_incidence;
  result.lineage = program.lineage;
  for (std::size_t receiver = 0; receiver < 2; ++receiver) {
    std::uint64_t face = 0;
    std::uint64_t support = 0;
    std::uint16_t count = 0;
    for (std::size_t source = 0; source < projection_source_capacity; ++source) {
      if ((program.receiver_masks[receiver].value() & (std::uint64_t{1} << source)) == 0) {
        continue;
      }
      std::uint64_t contribution = 0;
      if (!geometry_multiply(program.geometry[source].value(),
              program.propagation[source].value(), contribution) ||
          !geometry_add(face, contribution, face)) {
        return {};
      }
      support |= std::uint64_t{1} << source;
      result.preimage_occurrences[receiver][count] = program.source_occurrences[source];
      ++count;
    }
    result.faces[receiver] = exact::word{face};
    result.preimage_supports[receiver] = exact::word{support};
    result.preimage_counts[receiver] = count;
  }
  result.unresolved_preimage =
      result.preimage_counts[0] > 1 || result.preimage_counts[1] > 1;
  result.counterexample_receivers_differ = result.faces[0] != result.faces[1];
  return result;
}

}  // namespace holonics::receiver
