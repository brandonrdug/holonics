#pragma once

#include <cstdint>

#include <holonics/exact/integer_arithmetic.hpp>
#include <holonics/organ/conditioning_receipt.hpp>

namespace holonics::organ {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_morphology(
    const navigation_morphology& value) noexcept {
  return value.identity.value() != 0 && value.provenance.value() != 0 &&
      value.response_weight.value() != 0 && value.transport_weight.value() != 0 &&
      value.obstruction_threshold.value() != 0 && value.incidence_gate.value() <= 1U;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool exact_add(
    std::uint64_t left, std::uint64_t right, std::uint64_t& result) noexcept {
  const auto value = exact::add(exact::unsigned_integer<1>::from_word(left),
      exact::unsigned_integer<1>::from_word(right));
  if (!value.accepted()) { return false; }
  result = value.value.limb(0);
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool exact_multiply(
    std::uint64_t left, std::uint64_t right, std::uint64_t& result) noexcept {
  const auto value = exact::multiply(exact::unsigned_integer<1>::from_word(left),
      exact::unsigned_integer<1>::from_word(right));
  if (!value.accepted()) { return false; }
  result = value.value.limb(0);
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr conditioning_obstruction respond(
    const navigation_morphology& morphology,
    std::uint64_t support,
    std::uint64_t path_length,
    std::uint64_t unknown_count,
    navigation_consequence& result) noexcept {
  if (!valid_morphology(morphology)) { return conditioning_obstruction::invalid_morphology; }
  std::uint64_t response_part = 0;
  std::uint64_t transport_part = 0;
  std::uint64_t joined = 0;
  std::uint64_t response = 0;
  if (!exact_multiply(morphology.response_weight.value(), support, response_part) ||
      !exact_multiply(morphology.transport_weight.value(), path_length, transport_part) ||
      !exact_add(response_part, transport_part, joined) ||
      !exact_add(joined, morphology.codec_bias.value(), response)) {
    return conditioning_obstruction::arithmetic_refused;
  }
  result.response = exact::word{response};
  result.incidence = morphology.incidence_gate;
  result.transport = exact::word{transport_part};
  result.codec = morphology.codec_bias;
  result.obstruction = exact::word{
      unknown_count > morphology.obstruction_threshold.value() ? unknown_count : 0};
  return conditioning_obstruction::none;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool returned_delta(
    const navigation_morphology& before,
    const training_return& returned,
    morphology_delta& delta,
    navigation_morphology& after) noexcept {
  if (returned.occurrence.value() == 0 || returned.return_port.value() == 0 ||
      returned.lineage.value() == 0 || returned.response_weight.value() < before.response_weight.value() ||
      returned.transport_weight.value() < before.transport_weight.value() ||
      returned.incidence_gate.value() < before.incidence_gate.value() ||
      returned.codec_bias.value() < before.codec_bias.value() ||
      returned.obstruction_threshold.value() < before.obstruction_threshold.value()) {
    return false;
  }
  delta.response_weight = exact::word{returned.response_weight.value() - before.response_weight.value()};
  delta.transport_weight = exact::word{returned.transport_weight.value() - before.transport_weight.value()};
  delta.incidence_gate = exact::word{returned.incidence_gate.value() - before.incidence_gate.value()};
  delta.codec_bias = exact::word{returned.codec_bias.value() - before.codec_bias.value()};
  delta.obstruction_threshold = exact::word{
      returned.obstruction_threshold.value() - before.obstruction_threshold.value()};
  after = before;
  after.response_weight = returned.response_weight;
  after.transport_weight = returned.transport_weight;
  after.incidence_gate = returned.incidence_gate;
  after.codec_bias = returned.codec_bias;
  after.obstruction_threshold = returned.obstruction_threshold;
  return valid_morphology(after);
}

}  // namespace holonics::organ
