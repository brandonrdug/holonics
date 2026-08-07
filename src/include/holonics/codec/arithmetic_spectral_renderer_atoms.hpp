#pragma once

#include <holonics/codec/arithmetic_spectral_face.hpp>
#include <holonics/exact/integer_division.hpp>

namespace holonics::codec::arithmetic_render_detail {

template<class Face>
[[nodiscard]] HOLONICS_CALLABLE inline bool integer(Face& out, std::int64_t value) noexcept {
  if (value >= 0) { return append_blind_integer(out.bytes, out.byte_count, value); }
  return append_blind(out.bytes, out.byte_count, "(") &&
      append_blind_integer(out.bytes, out.byte_count, value) &&
      append_blind(out.bytes, out.byte_count, ")");
}

[[nodiscard]] HOLONICS_CALLABLE inline bool conjunction(
    arithmetic_formal_face& out, bool& first) noexcept {
  if (first) { first = false; return true; }
  return append_blind(out.bytes, out.byte_count, " ∧\n  ");
}

[[nodiscard]] HOLONICS_CALLABLE inline bool carrier_atoms(
    arithmetic_formal_face& out, const arithmetic_spectral_surface& source) noexcept {
  bool first = true;
  for (const auto& curve : source.curves) {
    const auto a = curve.a; const auto b = curve.b; const auto p = curve.prime;
    if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
        !integer(out, a) || !append_blind(out.bytes, out.byte_count, "*") || !integer(out, a) ||
        !append_blind(out.bytes, out.byte_count, " + ") || !integer(out, b) ||
        !append_blind(out.bytes, out.byte_count, "*") || !integer(out, b) ||
        !append_blind(out.bytes, out.byte_count, " : ℤ) = ") || !integer(out, p) ||
        !append_blind(out.bytes, out.byte_count, ")")) { return false; }
    if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "(∀ X : ℤ, (X-") ||
        !integer(out, a) || !append_blind(out.bytes, out.byte_count, ")*(X-") ||
        !integer(out, a) || !append_blind(out.bytes, out.byte_count, ") + ") ||
        !integer(out, b) || !append_blind(out.bytes, out.byte_count, "*") || !integer(out, b) ||
        !append_blind(out.bytes, out.byte_count, " = X^2 - 2*") || !integer(out, a) ||
        !append_blind(out.bytes, out.byte_count, "*X + ") || !integer(out, p) ||
        !append_blind(out.bytes, out.byte_count, ")")) { return false; }
    const std::int64_t positive[4]{a*a+b*b, -a*b+b*a, -b*a+a*b, b*b+a*a};
    const std::int64_t symplectic[4]{0, a*a+b*b, -(a*a+b*b), 0};
    for (std::uint8_t slot = 0; slot < 4; ++slot) {
      if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
          !integer(out, positive[slot]) || !append_blind(out.bytes, out.byte_count, " : ℤ) = ") ||
          !integer(out, slot == 0 || slot == 3 ? p : 0) ||
          !append_blind(out.bytes, out.byte_count, ")") || !conjunction(out, first) ||
          !append_blind(out.bytes, out.byte_count, "((") || !integer(out, symplectic[slot]) ||
          !append_blind(out.bytes, out.byte_count, " : ℤ) = ") ||
          !integer(out, slot == 1 ? p : (slot == 2 ? -p : 0)) ||
          !append_blind(out.bytes, out.byte_count, ")")) { return false; }
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE inline bool trace_atoms(
    arithmetic_formal_face& out, const arithmetic_spectral_surface& source) noexcept {
  bool first = true;
  for (const auto& curve : source.curves) {
    for (std::uint8_t degree = 1; degree <= arithmetic_surface_degree_count; ++degree) {
      std::int64_t prime_power = 1;
      for (std::uint8_t slot = 0; slot < degree; ++slot) { prime_power *= curve.prime; }
      if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
          !integer(out, curve.counts[degree - 1U]) ||
          !append_blind(out.bytes, out.byte_count, " : ℤ) = 1 + ") || !integer(out, prime_power) ||
          !append_blind(out.bytes, out.byte_count, " - ") || !integer(out, curve.traces[degree]) ||
          !append_blind(out.bytes, out.byte_count, ")")) { return false; }
      std::int64_t place_sum = 0;
      for (std::uint8_t divisor = 1; divisor <= degree; ++divisor) {
        if (exact::divide_unsigned(degree, divisor).remainder == 0) {
          place_sum += divisor * curve.places[divisor - 1U];
        }
      }
      if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count, "((") ||
          !integer(out, place_sum) || !append_blind(out.bytes, out.byte_count, " : ℤ) = ") ||
          !integer(out, curve.counts[degree - 1U]) ||
          !append_blind(out.bytes, out.byte_count, ")")) { return false; }
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE inline bool explicit_atoms(
    arithmetic_formal_face& out, const arithmetic_spectral_surface& source) noexcept {
  bool first = true;
  for (const auto& curve : source.curves) {
    if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count,
        "(∀ c1 c2 c3 c4 : ℤ, ")) { return false; }
    for (std::uint8_t degree = 1; degree <= arithmetic_surface_degree_count; ++degree) {
      if (degree != 1 && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
      std::int64_t prime_power = 1; std::int64_t place_sum = 0;
      for (std::uint8_t slot = 0; slot < degree; ++slot) { prime_power *= curve.prime; }
      for (std::uint8_t divisor = 1; divisor <= degree; ++divisor) {
        if (exact::divide_unsigned(degree, divisor).remainder == 0) {
          place_sum += divisor * curve.places[divisor - 1U];
        }
      }
      if (!append_blind(out.bytes, out.byte_count, "c") || !integer(out, degree) ||
          !append_blind(out.bytes, out.byte_count, "*(") || !integer(out, place_sum) ||
          !append_blind(out.bytes, out.byte_count, " - 1 - ") || !integer(out, prime_power) ||
          !append_blind(out.bytes, out.byte_count, " + ") || !integer(out, curve.traces[degree]) ||
          !append_blind(out.bytes, out.byte_count, ")")) { return false; }
    }
    if (!append_blind(out.bytes, out.byte_count, " = 0)")) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE inline bool positivity_atoms(
    arithmetic_formal_face& out, const arithmetic_spectral_surface& source) noexcept {
  bool first = true;
  for (const auto& curve : source.curves) {
    if (!conjunction(out, first) || !append_blind(out.bytes, out.byte_count,
        "(∀ c0 c1 c2 c3 c4 : ℤ, 0 ≤ (")) { return false; }
    for (std::uint8_t slot = 0; slot <= arithmetic_surface_degree_count; ++slot) {
      if (slot != 0 && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
      if (!append_blind(out.bytes, out.byte_count, "c") || !integer(out, slot) ||
          !append_blind(out.bytes, out.byte_count, "*") ||
          !integer(out, curve.homogeneous[slot][0])) { return false; }
    }
    if (!append_blind(out.bytes, out.byte_count, ")^2 + (")) { return false; }
    for (std::uint8_t slot = 0; slot <= arithmetic_surface_degree_count; ++slot) {
      if (slot != 0 && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
      if (!append_blind(out.bytes, out.byte_count, "c") || !integer(out, slot) ||
          !append_blind(out.bytes, out.byte_count, "*") ||
          !integer(out, curve.homogeneous[slot][1])) { return false; }
    }
    if (!append_blind(out.bytes, out.byte_count, ")^2)")) { return false; }
  }
  return true;
}

}  // namespace holonics::codec::arithmetic_render_detail
