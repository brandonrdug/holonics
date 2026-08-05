#pragma once

#include <holonics/organ/hodge_correspondence_law.hpp>

namespace holonics::organ::hodge_cycle_detail {

HOLONICS_CALLABLE constexpr void derive_locus(const hodge_product_receipt& product,
    std::uint64_t lineage, hodge_locus_receipt& out) noexcept {
  constexpr std::int64_t identity[2][2]{{1,0},{0,1}};
  constexpr std::int64_t negation[2][2]{{-1,0},{0,-1}};
  hodge_correspondence_detail::graph_class(identity, out.graph_class);
  hodge_correspondence_detail::graph_class(negation, out.negation_class);
  for (std::uint8_t slot = 0; slot < 6; ++slot) {
    out.primitive_class[slot] = out.graph_class[slot] - product.polarization[slot];
  }
  for (std::uint8_t slot = 0; slot < 6; ++slot) {
    out.quotient_obstruction[0] += product.connection_t_base[5][slot] * out.graph_class[slot];
    out.quotient_obstruction[1] += product.connection_u_base[5][slot] * out.graph_class[slot];
  }
  out.tangent_jet[0] = 1; out.tangent_jet[1] = 1;
  out.normal_jet[0] = 0; out.normal_jet[1] = 1;
  out.tangent_obstruction = out.quotient_obstruction[0] + out.quotient_obstruction[1];
  out.normal_obstruction = out.quotient_obstruction[1];
  out.graph_square = hodge_product_detail::pairing(product, out.graph_class, out.graph_class);
  out.negation_square = hodge_product_detail::pairing(
      product, out.negation_class, out.negation_class);
  out.mutual_intersection = hodge_product_detail::pairing(
      product, out.graph_class, out.negation_class);
  out.primitive_square = hodge_product_detail::pairing(
      product, out.primitive_class, out.primitive_class);
  out.identity = exact::word{195'520}; out.lineage = exact::word{lineage + 160U};
  out.multiplicity = out.normal_obstruction != 0 ? 1 : 0; out.graph_derived = true;
  out.diagonal_tangent_exact = out.tangent_obstruction == 0;
  out.normal_refused = out.normal_obstruction != 0;
  out.exact = out.quotient_obstruction[0] == -1 && out.quotient_obstruction[1] == 1 &&
      out.diagonal_tangent_exact && out.normal_refused && out.multiplicity == 1 &&
      out.graph_square == 0 && out.negation_square == 0 &&
      out.mutual_intersection == 4 && out.primitive_square == -2;
}

HOLONICS_CALLABLE constexpr void generator(hodge_cycle_generator& out,
    std::uint64_t identity, std::uint64_t lineage, const std::int64_t (&value)[6],
    std::uint16_t support, bool effective) noexcept {
  out.identity = exact::word{identity}; out.lineage = exact::word{lineage};
  for (std::uint8_t slot = 0; slot < 6; ++slot) { out.cycle_class[slot] = value[slot]; }
  out.support_mask = support; out.effective = effective;
}

HOLONICS_CALLABLE constexpr void derive_generators(hodge_cycle_receipt& out) noexcept {
  constexpr std::int64_t first[6]{1,0,0,0,0,0};
  constexpr std::int64_t second[6]{0,1,0,0,0,0};
  generator(out.generators[0],195'540,195'640,first,1U,true);
  generator(out.generators[1],195'541,195'641,second,2U,true);
  for (std::uint8_t slot = 0; slot < 4; ++slot) {
    generator(out.generators[slot + 2U],195'542U + slot,195'642U + slot,
        out.translations[slot].graph_class, static_cast<std::uint16_t>(1U << (slot + 2U)), true);
  }
  generator(out.generators[6],195'546,195'646,out.locus.negation_class,64U,true);
  out.generator_count = 7;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool target_equal(
    const hodge_class_question& target, const std::int64_t (&value)[6]) noexcept {
  for (std::uint8_t slot = 0; slot < 6; ++slot) {
    if (target.numerator[slot] != value[slot]) { return false; }
  }
  return true;
}

HOLONICS_CALLABLE constexpr void retain(hodge_realizer_fiber& fiber,
    const std::int8_t (&coefficients)[7], const hodge_cycle_generator (&generators)[7]) noexcept {
  if (fiber.realizer_count == hodge_realizer_capacity) { fiber.complete = false; return; }
  auto& out = fiber.realizers[fiber.realizer_count]; out.denominator = fiber.target.denominator;
  std::uint8_t nonzero = 0; std::uint8_t graph = 0; bool reduced_integral = true;
  for (std::uint8_t slot = 0; slot < 7; ++slot) {
    out.coefficients[slot] = coefficients[slot];
    if (coefficients[slot] != 0) { ++nonzero; out.support_mask = static_cast<std::uint16_t>(
        out.support_mask | generators[slot].support_mask); if (slot >= 2 && slot <= 5) { ++graph; } }
    if (fiber.target.denominator == 2 && (coefficients[slot] & 1) != 0) {
      reduced_integral = false;
    }
  }
  out.effective_single_graph = nonzero == 1 && graph == 1;
  out.integral = fiber.target.denominator == 1 || reduced_integral;
  out.identity = exact::word{195'700U + fiber.identity.value() * 32U + fiber.realizer_count};
  out.lineage = exact::word{fiber.lineage.value() + fiber.realizer_count + 1U};
  out.exact = true; ++fiber.realizer_count;
  if (out.effective_single_graph) { ++fiber.effective_count; }
  fiber.integral_member = fiber.integral_member || out.integral;
}

HOLONICS_CALLABLE constexpr void derive_fiber(const hodge_realization_card& card,
    const hodge_cycle_generator (&generators)[7], std::uint8_t target,
    hodge_realizer_fiber& fiber) noexcept {
  fiber.target = card.questions[target]; fiber.identity = exact::word{195'560U + target};
  fiber.lineage = exact::word{card.lineage.value() + 192U + target}; fiber.complete = true;
  std::int8_t coefficients[7]{-1,-1,-1,-1,-1,-1,-1};
  for (std::uint16_t tuple = 0; tuple < 2187; ++tuple) {
    std::int64_t value[6]{};
    for (std::uint8_t generator_slot = 0; generator_slot < 7; ++generator_slot) {
      for (std::uint8_t slot = 0; slot < 6; ++slot) {
        value[slot] += coefficients[generator_slot] *
            generators[generator_slot].cycle_class[slot];
      }
    }
    if (target_equal(fiber.target, value)) { retain(fiber, coefficients, generators); }
    for (std::uint8_t offset = 0; offset < 7; ++offset) {
      const auto slot = static_cast<std::uint8_t>(6U - offset);
      if (coefficients[slot] < 1) { ++coefficients[slot]; break; }
      coefficients[slot] = -1;
    }
    ++fiber.enumerated;
  }
  fiber.outside_image = fiber.realizer_count == 0;
  const bool expected = target < 2 ? fiber.realizer_count == 16 : fiber.outside_image;
  fiber.exact = fiber.complete && expected && (target != 0 ||
      (fiber.effective_count == 4 && fiber.integral_member)) &&
      (target != 1 || !fiber.integral_member);
}

}  // namespace holonics::organ::hodge_cycle_detail
