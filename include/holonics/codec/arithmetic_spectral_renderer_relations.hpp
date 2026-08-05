#pragma once

#include <holonics/codec/arithmetic_spectral_renderer_atoms.hpp>

namespace holonics::codec::arithmetic_render_detail {

[[nodiscard]] HOLONICS_CALLABLE inline bool smoothness_atoms(
    arithmetic_formal_face& out, const arithmetic_spectral_surface& source) noexcept {
  bool first = true;
  for (const auto& curve : source.curves) {
    const auto discriminant = -64 * curve.coefficient * curve.coefficient * curve.coefficient;
    if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
        !integer(out, discriminant) || !append_blind(out.bytes, out.byte_count, " : ℤ) = -64 * ") ||
        !integer(out, curve.coefficient) || !append_blind(out.bytes, out.byte_count, "^3)")) {
      return false;
    }
    if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
        !integer(out, discriminant) || !append_blind(out.bytes, out.byte_count, " : ℤ) % ") ||
        !integer(out, curve.prime) || !append_blind(out.bytes, out.byte_count, " ≠ 0)")) {
      return false;
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE inline bool recurrence_atoms(
    arithmetic_formal_face& out, const arithmetic_spectral_surface& source) noexcept {
  bool first = true;
  for (const auto& curve : source.curves) {
    if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
        !integer(out, curve.traces[0]) || !append_blind(out.bytes, out.byte_count, " : ℤ) = 2)")) {
      return false;
    }
    if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
        !integer(out, curve.traces[1]) || !append_blind(out.bytes, out.byte_count, " : ℤ) = 2 * ") ||
        !integer(out, curve.a) || !append_blind(out.bytes, out.byte_count, ")")) { return false; }
    for (std::uint8_t degree = 2; degree <= arithmetic_surface_degree_count; ++degree) {
      if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
          !integer(out, curve.traces[degree]) || !append_blind(out.bytes, out.byte_count, " : ℤ) = 2 * ") ||
          !integer(out, curve.a) || !append_blind(out.bytes, out.byte_count, " * ") ||
          !integer(out, curve.traces[degree - 1U]) || !append_blind(out.bytes, out.byte_count, " - ") ||
          !integer(out, curve.prime) || !append_blind(out.bytes, out.byte_count, " * ") ||
          !integer(out, curve.traces[degree - 2U]) || !append_blind(out.bytes, out.byte_count, ")")) {
        return false;
      }
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE inline bool duality_atoms(
    arithmetic_formal_face& out, const arithmetic_spectral_surface& source) noexcept {
  bool first = true;
  for (const auto& curve : source.curves) {
    const auto trace = 2 * curve.a;
    if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "(∀ T : ℤ, ") ||
        !integer(out, curve.prime) || !append_blind(out.bytes, out.byte_count, "*T^2 - ") ||
        !integer(out, trace) || !append_blind(out.bytes, out.byte_count, "*T + 1 = 1 - ") ||
        !integer(out, trace) || !append_blind(out.bytes, out.byte_count, "*T + ") ||
        !integer(out, curve.prime) || !append_blind(out.bytes, out.byte_count, "*T^2)")) {
      return false;
    }
    if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "(∀ T : ℤ, (") ||
        !integer(out, curve.prime) || !append_blind(out.bytes, out.byte_count,
          "*T-1)*(T-1) = (1-T)*(1-") || !integer(out, curve.prime) ||
        !append_blind(out.bytes, out.byte_count, "*T))")) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t choose2(std::int64_t n) noexcept {
  return static_cast<std::int64_t>(exact::divide_unsigned(
      static_cast<std::uint64_t>(n * (n - 1)), 2U).quotient);
}

[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t choose3(std::int64_t n) noexcept {
  return static_cast<std::int64_t>(exact::divide_unsigned(
      static_cast<std::uint64_t>(n * (n - 1) * (n - 2)), 6U).quotient);
}

[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t choose4(std::int64_t n) noexcept {
  return static_cast<std::int64_t>(exact::divide_unsigned(
      static_cast<std::uint64_t>(n * (n - 1) * (n - 2) * (n - 3)), 24U).quotient);
}

[[nodiscard]] HOLONICS_CALLABLE inline bool euler_atoms(
    arithmetic_formal_face& out, const arithmetic_spectral_surface& source) noexcept {
  bool first = true;
  for (const auto& curve : source.curves) {
    std::int64_t z[5]{1,0,0,0,0}; const auto trace = 2 * curve.a;
    z[1] = curve.prime + 1 - trace;
    z[2] = (curve.prime + 1) * z[1];
    for (std::uint8_t degree = 3; degree <= 4; ++degree) {
      z[degree] = (curve.prime + 1) * z[degree - 1U] - curve.prime * z[degree - 2U];
    }
    const auto b1 = curve.places[0]; const auto b2 = curve.places[1];
    const auto b3 = curve.places[2]; const auto b4 = curve.places[3];
    const std::int64_t euler[5]{1,b1,choose2(b1 + 1) + b2,
        choose3(b1 + 2) + b1 * b2 + b3,
        choose4(b1 + 3) + choose2(b1 + 1) * b2 + choose2(b2 + 1) + b1 * b3 + b4};
    for (std::uint8_t degree = 1; degree <= 4; ++degree) {
      if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
          !integer(out, z[degree]) || !append_blind(out.bytes, out.byte_count, " : ℤ) = ") ||
          !integer(out, euler[degree]) || !append_blind(out.bytes, out.byte_count, ")")) {
        return false;
      }
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE inline bool primary_atoms(
    arithmetic_formal_face& out, const arithmetic_spectral_surface& source) noexcept {
  bool first = true;
  for (const auto& curve : source.curves) {
    if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count,
        "(primaryEigenvectorRelation ") || !integer(out, curve.a) ||
        !append_blind(out.bytes, out.byte_count, " ") || !integer(out, curve.b) ||
        !append_blind(out.bytes, out.byte_count, ")")) { return false; }
    if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count,
        "(((0 : ℤ), (2 : ℤ)) = ((0 : ℤ), (2 : ℤ)))")) { return false; }
    if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count,
        "((0^2 + 2^2 : ℤ) = 4)")) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE inline bool twist_control_atoms(arithmetic_formal_face& out,
    bool& first, const arithmetic_curve_surface& left,
    const arithmetic_curve_surface& right) noexcept {
  if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
      !integer(out, left.a) || !append_blind(out.bytes, out.byte_count, " : ℤ) = -") ||
      !integer(out, right.a) || !append_blind(out.bytes, out.byte_count, ")") ||
      !conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
      !integer(out, left.b) || !append_blind(out.bytes, out.byte_count, " : ℤ) = -") ||
      !integer(out, right.b) || !append_blind(out.bytes, out.byte_count, ")")) { return false; }
  for (std::uint8_t degree = 1; degree <= 3; degree += 2) {
    if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
        !integer(out, left.counts[degree]) || !append_blind(out.bytes, out.byte_count, " : ℤ) = ") ||
        !integer(out, right.counts[degree]) || !append_blind(out.bytes, out.byte_count, ")")) {
      return false;
    }
  }
  std::int64_t prime_power = left.prime;
  for (std::uint8_t degree = 0; degree <= 2; degree += 2) {
    if (degree == 2) { prime_power = left.prime * left.prime * left.prime; }
    if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
        !integer(out, left.counts[degree] + right.counts[degree]) ||
        !append_blind(out.bytes, out.byte_count, " : ℤ) = 2 * (1 + ") ||
        !integer(out, prime_power) || !append_blind(out.bytes, out.byte_count, "))")) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE inline bool control_atoms(
    arithmetic_formal_face& out, const arithmetic_spectral_surface& source) noexcept {
  bool first = true; const auto& c = source.curves;
  if (!twist_control_atoms(out, first, c[0], c[1]) ||
      !twist_control_atoms(out, first, c[2], c[3]) ||
      !twist_control_atoms(out, first, c[4], c[6])) { return false; }
  if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
      !integer(out, c[2].coefficient) || !append_blind(out.bytes, out.byte_count, " : ℤ) ≠ ") ||
      !integer(out, c[5].coefficient) || !append_blind(out.bytes, out.byte_count, ")")) { return false; }
  for (std::uint8_t degree = 0; degree < arithmetic_surface_degree_count; ++degree) {
    if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
        !integer(out, c[2].counts[degree]) || !append_blind(out.bytes, out.byte_count, " : ℤ) = ") ||
        !integer(out, c[5].counts[degree]) || !append_blind(out.bytes, out.byte_count, ")")) {
      return false;
    }
  }
  if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
      !integer(out, c[2].a) || !append_blind(out.bytes, out.byte_count, " : ℤ) = ") ||
      !integer(out, c[5].a) || !append_blind(out.bytes, out.byte_count, ")") ||
      !conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
      !integer(out, c[2].b) || !append_blind(out.bytes, out.byte_count, " : ℤ) = ") ||
      !integer(out, c[5].b) || !append_blind(out.bytes, out.byte_count, ")") ||
      !conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((3 : ZMod 13) = (") ||
      !integer(out, source.rechart_scale) || !append_blind(out.bytes, out.byte_count, " : ZMod 13)^4)") ||
      !conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
      !integer(out, c[2].a) || !append_blind(out.bytes, out.byte_count, " : ℤ) ≠ ") ||
      !integer(out, c[4].a) || !append_blind(out.bytes, out.byte_count, ")") ||
      !conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
      !integer(out, c[2].b) || !append_blind(out.bytes, out.byte_count, " : ℤ) ≠ ") ||
      !integer(out, c[4].b) || !append_blind(out.bytes, out.byte_count, ")")) { return false; }
  return true;
}

}  // namespace holonics::codec::arithmetic_render_detail
