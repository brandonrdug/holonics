#pragma once

#include <holonics/codec/blind_reconstruction_face.hpp>

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_blind_code_explanation(
    const blind_reconstruction_surface& surface, blind_explanation& out) noexcept {
  if (surface.passage.value() == 0 || !surface.incidence || !surface.source_separated) {
    return false;
  }
  out.identity = exact::word{126'510};
  out.passage = surface.passage;
  return append_blind(out.bytes, out.byte_count,
      "The binary card supplied only seven coordinate sites and three parity contacts. The card ") &&
      append_blind(out.bytes, out.byte_count,
      "enumerated its own code population, then each nonzero pair distance repartitioned the ") &&
      append_blind(out.bytes, out.byte_count,
      "whole cube by two receiver distances. Bit flips formed the cell contacts. Their quotient ") &&
      append_blind(out.bytes, out.byte_count,
      "is not an unweighted grid: cell mass transports it by WQ=Q^T W. Complete contact then ") &&
      append_blind(out.bytes, out.byte_count,
      "factors the distance-three and distance-four strata into commuting radial directions, ") &&
      append_blind(out.bytes, out.byte_count,
      "whose integer Krawtchouk vectors carry the exact characteristic modes. The two strata ") &&
      append_blind(out.bytes, out.byte_count,
      "share a factor only after swapping axes; their pair occurrences remain distinct. A ") &&
      append_blind(out.bytes, out.byte_count,
      "one-shell collapse is exact only at the antipodal one-axis stratum. Unit weighting and ") &&
      append_blind(out.bytes, out.byte_count,
      "lineage reversal retain plausible topology or spectrum but fail actual oriented contact.\n");
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_blind_moment_explanation(
    const blind_reconstruction_surface& surface, blind_explanation& out) noexcept {
  if (surface.passage.value() == 0 || !surface.characteristic ||
      !surface.obstruction || !surface.source_separated) { return false; }
  out.identity = exact::word{126'511};
  out.passage = surface.passage;
  return append_blind(out.bytes, out.byte_count,
      "The moment card supplied no roots. Consecutive power sums formed H0 and its transported ") &&
      append_blind(out.bytes, out.byte_count,
      "neighbor H1. Fraction-free elimination of xH0-H1 returns the characteristic polynomial ") &&
      append_blind(out.bytes, out.byte_count,
      "of multiplication by the hidden coordinate in the moment basis; independent Newton ") &&
      append_blind(out.bytes, out.byte_count,
      "transport returns the same monic law. Inside the declared integer aperture its roots ") &&
      append_blind(out.bytes, out.byte_count,
      "remove that law exactly. With unit source masses, H0 factors as a Vandermonde matrix ") &&
      append_blind(out.bytes, out.byte_count,
      "times its transpose, so det(H0) is exactly the polynomial discriminant. It is therefore ") &&
      append_blind(out.bytes, out.byte_count,
      "the invertible transport aperture for distinct roots, not a generic label. The collision ") &&
      append_blind(out.bytes, out.byte_count,
      "case returns determinant and discriminant zero; the short stream returns missing access. ") &&
      append_blind(out.bytes, out.byte_count,
      "Neither is repaired by guessing. Toeplitz, reversed-order, and collapsed-degree candidates ") &&
      append_blind(out.bytes, out.byte_count,
      "remain with the exact receiver each one fails.\n");
}

}  // namespace holonics::codec
