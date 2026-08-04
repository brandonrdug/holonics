#pragma once

#include <cstdint>

#include <holonics/codec/reflection_receipt.hpp>
#include <holonics/exact/integer_division.hpp>

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_program(
    const codec_program& program) noexcept {
  const bool form_valid = program.face.form == codec_form::additive_symbol ||
      program.face.form == codec_form::split_pulse;
  return program.identity.value() != 0 && program.version.value() != 0 &&
      program.face.identity.value() != 0 && program.face.exterior_port.value() != 0 &&
      program.face.body_port.value() != 0 && program.scale.value() != 0 &&
      program.inherited_lineage.value() != 0 && form_valid &&
      (program.face.form != codec_form::additive_symbol || program.scale.value() == 1U);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_environment(
    const codec_environment& environment) noexcept {
  return environment.identity.value() != 0 && environment.inherited_provenance.value() != 0 &&
      environment.core_occurrence.value() != 0 && environment.source_material_testimony.value() != 0 &&
      environment.storage_lineage.value() != 0 && valid_program(environment.operative) &&
      valid_program(environment.unrelated) &&
      environment.operative.identity != environment.unrelated.identity &&
      environment.operative.face.identity != environment.unrelated.face.identity &&
      environment.operative.face.form != environment.unrelated.face.form &&
      environment.operative.face.body_port == environment.unrelated.face.body_port;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool add_word(
    std::uint64_t left, std::uint64_t right, std::uint64_t& result) noexcept {
  const auto sum = exact::add(exact::unsigned_integer<1>::from_word(left),
      exact::unsigned_integer<1>::from_word(right));
  if (!sum.accepted()) { return false; }
  result = sum.value.limb(0);
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool multiply_word(
    std::uint64_t left, std::uint64_t right, std::uint64_t& result) noexcept {
  const auto product = exact::multiply(exact::unsigned_integer<1>::from_word(left),
      exact::unsigned_integer<1>::from_word(right));
  if (!product.accepted()) { return false; }
  result = product.value.limb(0);
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr codec_obstruction parse_surface(
    const codec_program& program,
    surface_packet surface,
    exact::word& core) noexcept {
  if (!valid_program(program) ||
      (program.face.form == codec_form::additive_symbol && surface.second.value() != 0) ||
      (program.face.form == codec_form::split_pulse &&
          surface.second.value() >= program.scale.value())) {
    return codec_obstruction::invalid_surface;
  }
  std::uint64_t scaled = 0;
  std::uint64_t joined = 0;
  std::uint64_t result = 0;
  if (!multiply_word(surface.first.value(), program.scale.value(), scaled) ||
      !add_word(scaled, surface.second.value(), joined) ||
      !add_word(joined, program.bias.value(), result)) {
    return codec_obstruction::arithmetic_refused;
  }
  core = exact::word{result};
  return codec_obstruction::none;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr codec_obstruction render_surface(
    const codec_program& program,
    exact::word core,
    surface_packet& surface) noexcept {
  if (!valid_program(program) || core.value() < program.bias.value()) {
    return codec_obstruction::invalid_surface;
  }
  const auto value = exact::unsigned_integer<1>::from_word(core.value() - program.bias.value());
  const auto scale = exact::unsigned_integer<1>::from_word(program.scale.value());
  const auto divided = exact::divide(value, scale);
  if (!divided.accepted()) { return codec_obstruction::arithmetic_refused; }
  surface.first = exact::word{divided.quotient.limb(0)};
  surface.second = exact::word{divided.remainder.limb(0)};
  return codec_obstruction::none;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr codec_obstruction transduce_surface(
    const codec_program& source,
    const codec_program& destination,
    surface_packet input,
    exact::word& core,
    surface_packet& output) noexcept {
  const auto parsed = parse_surface(source, input, core);
  return parsed == codec_obstruction::none ? render_surface(destination, core, output) : parsed;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal_program(
    const codec_program& left, const codec_program& right) noexcept {
  return left.identity == right.identity && left.version == right.version &&
      left.face.identity == right.face.identity && left.face.form == right.face.form &&
      left.face.exterior_port == right.face.exterior_port &&
      left.face.body_port == right.face.body_port && left.scale == right.scale &&
      left.bias == right.bias && left.inherited_lineage == right.inherited_lineage;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr codec_crossing parse_crossing(
    const codec_environment& environment,
    const codec_program& program,
    surface_packet input,
    exact::word predecessor,
    exact::word occurrence,
    exact::word lineage) noexcept {
  codec_crossing result{};
  result.kind = crossing_kind::parse;
  result.occurrence = occurrence;
  result.lineage = lineage;
  result.predecessor = predecessor;
  result.program = program.identity;
  result.version = program.version;
  result.source_face = program.face.identity;
  result.target_face = program.face.body_port;
  result.input = input;
  result.core_occurrence = environment.core_occurrence;
  result.obstruction = parse_surface(program, input, result.core_value);
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr codec_crossing render_crossing(
    const codec_environment& environment,
    const codec_program& program,
    exact::word core,
    exact::word predecessor,
    exact::word occurrence,
    exact::word lineage) noexcept {
  codec_crossing result{};
  result.kind = crossing_kind::render;
  result.occurrence = occurrence;
  result.lineage = lineage;
  result.predecessor = predecessor;
  result.program = program.identity;
  result.version = program.version;
  result.source_face = program.face.body_port;
  result.target_face = program.face.identity;
  result.core_occurrence = environment.core_occurrence;
  result.core_value = core;
  result.obstruction = render_surface(program, core, result.output);
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr codec_crossing transduce_crossing(
    const codec_environment& environment,
    const codec_program& source,
    const codec_program& destination,
    surface_packet input,
    exact::word predecessor,
    exact::word occurrence,
    exact::word lineage) noexcept {
  codec_crossing result{};
  result.kind = crossing_kind::transduce;
  result.occurrence = occurrence;
  result.lineage = lineage;
  result.predecessor = predecessor;
  result.program = source.identity;
  result.version = source.version;
  result.source_face = source.face.identity;
  result.target_face = destination.face.identity;
  result.input = input;
  result.core_occurrence = environment.core_occurrence;
  result.obstruction = transduce_surface(source, destination, input,
      result.core_value, result.output);
  return result;
}

}  // namespace holonics::codec
