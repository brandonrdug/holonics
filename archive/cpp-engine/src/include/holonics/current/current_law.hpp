#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/current/current_receipt.hpp>

namespace holonics::current {

struct transform_receipt final {
  exact::word value{};
  current_obstruction obstruction{current_obstruction::none};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr bool multiply_exact(
    std::uint64_t left,
    std::uint64_t right,
    std::uint64_t& product) noexcept {
  product = 0;
  std::uint64_t addend = left;
  std::uint64_t factor = right;
  while (factor != 0) {
    if ((factor & 1U) != 0) {
      if (addend > ~std::uint64_t{0} - product) { return false; }
      product += addend;
    }
    factor >>= 1U;
    if (factor != 0) {
      if (addend > ~std::uint64_t{0} - addend) { return false; }
      addend += addend;
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr transform_receipt apply_morphology(
    exact::word input,
    const morphology_cell& morphology,
    std::uint16_t multiplicity) noexcept {
  transform_receipt result{};
  const std::uint64_t scale = morphology.scale.value();
  const std::uint64_t value = input.value();
  std::uint64_t scaled = 0;
  if (!multiply_exact(value, scale, scaled)) {
    result.obstruction = current_obstruction::arithmetic_overflow;
    return result;
  }
  if (scaled > ~std::uint64_t{0} - morphology.offset.value()) {
    result.obstruction = current_obstruction::arithmetic_overflow;
    return result;
  }
  const std::uint64_t shifted = scaled + morphology.offset.value();
  std::uint64_t multiplied = 0;
  if (!multiply_exact(shifted, multiplicity, multiplied)) {
    result.obstruction = current_obstruction::arithmetic_overflow;
    return result;
  }
  result.value = exact::word{multiplied};
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr current_obstruction validate_program(
    const causal_program& program) noexcept {
  if (program.identity.value() == 0 || program.predecessor.value() == 0 ||
      program.input_port.value() == 0 || program.output_port.value() == 0 ||
      program.lineage.value() == 0 || program.receiver_support.value() == 0 ||
      program.next_occurrence.value() == 0 || program.next_event.value() == 0 ||
      program.predecessor.value() > ~std::uint64_t{0} - program_front_capacity ||
      program.next_occurrence.value() > ~std::uint64_t{0} - current_delta_capacity ||
      program.next_event.value() > ~std::uint64_t{0} - current_delta_capacity ||
      program.site_count == 0 || program.site_count > program_site_capacity ||
      program.arc_count > program_arc_capacity ||
      program.initial_current_count == 0 ||
      program.initial_current_count > sparse_current_capacity ||
      program.resource_obligation > current_delta_capacity ||
      program.component_count == 0 ||
      program.component_count > program_component_capacity ||
      program.receiver_front_aperture == 0 ||
      program.receiver_front_aperture > program_front_capacity) {
    return current_obstruction::invalid_program;
  }
  for (std::size_t site = 0; site < program.site_count; ++site) {
    const current_site& encoded = program.sites[site];
    if (encoded.identity.value() == 0 || encoded.support.value() == 0 ||
        (encoded.support.value() & program.receiver_support.value()) != encoded.support.value() ||
        encoded.component >= program.component_count ||
        encoded.first_arc > program.arc_count ||
        encoded.arc_count > program.arc_count - encoded.first_arc) {
      return current_obstruction::invalid_program;
    }
    for (std::size_t edge = encoded.first_arc;
         edge < static_cast<std::size_t>(encoded.first_arc) + encoded.arc_count;
         ++edge) {
      if (program.arcs[edge].target >= program.site_count ||
          program.arcs[edge].port.value() == 0 ||
          program.arcs[edge].lineage.value() == 0 ||
          program.arcs[edge].multiplicity == 0) {
        return current_obstruction::invalid_program;
      }
    }
  }
  std::uint64_t initial_support = 0;
  for (std::size_t slot = 0; slot < program.initial_current_count; ++slot) {
    const sparse_current& value = program.initial_currents[slot];
    if (value.occurrence.value() == 0 || value.lineage.value() == 0 ||
        value.site >= program.site_count ||
        value.component != program.sites[value.site].component ||
        value.caused_support != program.sites[value.site].support || value.open) {
      return current_obstruction::invalid_program;
    }
    if ((initial_support & value.caused_support.value()) != 0) {
      return current_obstruction::reservation_conflict;
    }
    initial_support |= value.caused_support.value();
  }
  return current_obstruction::none;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr exact::word fold_currents(
    const sparse_current* values,
    std::size_t count) noexcept {
  std::uint64_t fold = 14'695'981'039'346'656'037ULL;
  constexpr std::uint64_t prime = 1'099'511'628'211ULL;
  for (std::size_t slot = 0; slot < count; ++slot) {
    const std::uint64_t fields[5]{values[slot].occurrence.value(),
        values[slot].lineage.value(), values[slot].local_state.value(),
        values[slot].caused_support.value(), values[slot].site};
    for (std::uint64_t field : fields) {
      fold ^= field;
      fold *= prime;
    }
  }
  return exact::word{fold};
}

}  // namespace holonics::current
