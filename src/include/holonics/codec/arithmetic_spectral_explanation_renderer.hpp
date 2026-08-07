#pragma once

#include <holonics/codec/arithmetic_spectral_face.hpp>

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE inline bool render_arithmetic_spectral_explanation(
    const arithmetic_spectral_surface& source, arithmetic_explanation& out) noexcept {
  if (source.passage.value() == 0 || !source.fields_exact || !source.correspondences_exact ||
      !source.forms_exact || !source.traces_exact || !source.controls_exact ||
      !source.archimedean_inapplicable) { return false; }
  out.identity = exact::word{129'001}; out.passage = source.passage;
  return append_blind(out.bytes, out.byte_count,
      "Seven exact elliptic source passages were carried through finite fields of degrees one "
      "through four. The machine first derived each quotient field and enumerated the geometric "
      "fixed loci. Independently, it compared coordinate Frobenius with every bounded Gaussian "
      "endomorphism on every point over the quadratic field. Only after the unique geometric "
      "match returned did it form the rank-two operator. Its alternating form scales by p and "
      "its positive Rosati chart returns F-transpose-F equal to p times identity; the Gaussian "
      "eigenvalues therefore have exact norm p without a decimal modulus. Fixed-point counts, "
      "power traces, closed-place populations, the local zeta numerator, and its reciprocal "
      "duality all agree while retaining separate lineage. Twist pairs reverse odd spectral "
      "hands but preserve the shell and even counts; an equal-factor pair retains its source "
      "rechart. Every bounded explicit-formula current balances closed places against the two "
      "normalization poles and H1 trace, and every homogeneous phase current is a symbolic "
      "Gaussian norm square. This function-field world has no archimedean place. The return is "
      "a geometric calibration of spectral placement, not a classical RH operator, a finite "
      "zero fit, or a proof of all-test Weil positivity.");
}

}  // namespace holonics::codec
