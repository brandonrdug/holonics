#pragma once

#include <holonics/codec/characteristic_hypergeometry_face.hpp>
#include <holonics/codec/rederivation_renderer_atoms.hpp>

namespace holonics::codec::characteristic_render_detail {

template <class Writer>
HOLONICS_CALLABLE inline bool
coefficient_list(Writer &out, const std::int64_t *values) noexcept {
  if (!out.text("["))
    return false;
  for (std::uint8_t i = 0; i < characteristic_surface_feature_count; ++i) {
    if (i != 0 && !out.text(","))
      return false;
    if (!out.integer(values[i]))
      return false;
  }
  return out.text("]");
}
template <class Writer>
HOLONICS_CALLABLE inline bool polynomial(Writer &out,
                                         const std::int64_t *values) noexcept {
  constexpr const char *terms[characteristic_surface_feature_count]{
      "1",     "x",     "y",     "z",     "x*x",   "x*y",   "x*z",
      "y*y",   "y*z",   "z*z",   "x*x*x", "x*x*y", "x*x*z", "x*y*y",
      "x*y*z", "x*z*z", "y*y*y", "y*y*z", "y*z*z", "z*z*z", "k"};
  for (std::uint8_t i = 0; i < characteristic_surface_feature_count; ++i) {
    if (i != 0 && !out.text(" + "))
      return false;
    if (!out.integer(values[i]) || !out.text(" * ") || !out.text(terms[i]))
      return false;
  }
  return true;
}
template <class Writer>
HOLONICS_CALLABLE inline bool
matrix_value(Writer &out, const elementary_matrix2_surface &matrix) noexcept {
  return out.text("{a:=") && out.integer(matrix.value[0]) && out.text(",b:=") &&
         out.integer(matrix.value[1]) && out.text(",c:=") &&
         out.integer(matrix.value[2]) && out.text(",d:=") &&
         out.integer(matrix.value[3]) && out.text("}");
}
template <class Writer>
HOLONICS_CALLABLE inline bool
pair_definitions(Writer &out, const char *prefix,
                 const characteristic_pair_surface &pair) noexcept {
  constexpr const char *suffixes[4]{"A", "B", "AB", "C"};
  const elementary_matrix2_surface *matrices[4]{&pair.first, &pair.second,
                                                &pair.product, &pair.closed};
  for (std::uint8_t i = 0; i < 4; ++i)
    if (!out.text("def ") || !out.text(prefix) || !out.text(suffixes[i]) ||
        !out.text(" : Matrix2 := ") || !matrix_value(out, *matrices[i]) ||
        !out.text("\n"))
      return false;
  return out.text("\n");
}
template <class Writer>
HOLONICS_CALLABLE inline bool countermodel_prefix(Writer &out,
                                                  const char *prefix) noexcept {
  return out.text(prefix) && out.text("AB = matrixMultiply ") &&
         out.text(prefix) && out.text("A ") && out.text(prefix) &&
         out.text("B ∧\n  ") && out.text(prefix) &&
         out.text("C = matrixMultiply (matrixMultiply (matrixMultiply ") &&
         out.text(prefix) && out.text("A ") && out.text(prefix) &&
         out.text("B) (matrixInverse ") && out.text(prefix) &&
         out.text("A)) (matrixInverse ") && out.text(prefix) &&
         out.text("B) ∧\n  ");
}
template <class Writer>
HOLONICS_CALLABLE inline bool
numeric_countermodel(Writer &out, const char *name, const char *left,
                     const char *right, const characteristic_pair_surface &a,
                     const characteristic_pair_surface &b,
                     std::uint8_t kind) noexcept {
  if (!pair_definitions(out, left, a) || !pair_definitions(out, right, b) ||
      !out.text("theorem ") || !out.text(name) || !out.text(" :\n  ") ||
      !countermodel_prefix(out, left) || !countermodel_prefix(out, right))
    return false;
  if (kind == 0) {
    if (!out.text("matrixTrace ") || !out.text(left) ||
        !out.text("A = matrixTrace ") || !out.text(right) ||
        !out.text("A ∧ matrixTrace ") || !out.text(left) ||
        !out.text("B = matrixTrace ") || !out.text(right) ||
        !out.text("B ∧ matrixTrace ") || !out.text(left) ||
        !out.text("AB ≠ matrixTrace ") || !out.text(right) ||
        !out.text("AB ∧ matrixTrace ") || !out.text(left) ||
        !out.text("C ≠ matrixTrace ") || !out.text(right) || !out.text("C"))
      return false;
  } else if (kind == 1) {
    if (!out.text("matrixTrace ") || !out.text(left) ||
        !out.text("A = matrixTrace ") || !out.text(right) ||
        !out.text("A ∧ matrixTrace ") || !out.text(left) ||
        !out.text("B = matrixTrace ") || !out.text(right) ||
        !out.text("B ∧ matrixTrace ") || !out.text(left) ||
        !out.text("AB = matrixTrace ") || !out.text(right) ||
        !out.text("AB ∧ matrixTrace ") || !out.text(left) ||
        !out.text("C = matrixTrace ") || !out.text(right) ||
        !out.text("C ∧ (") || !out.integer(a.source) || !out.text(" : ℕ) ≠ ") ||
        !out.integer(b.source))
      return false;
  } else if (kind == 2) {
    if (!out.text("matrixTrace ") || !out.text(left) ||
        !out.text("C = matrixTrace ") || !out.text(right) ||
        !out.text("C ∧ ") || !out.text(left) || !out.text("C ≠ ") ||
        !out.text(right) || !out.text("C"))
      return false;
  } else if (kind == 3) {
    if (!out.text("matrixTrace ") || !out.text(left) ||
        !out.text("A = matrixTrace ") || !out.text(right) ||
        !out.text("A ∧ matrixTrace ") || !out.text(left) ||
        !out.text("B = matrixTrace ") || !out.text(right) ||
        !out.text("B ∧ matrixTrace ") || !out.text(left) ||
        !out.text("AB = matrixTrace ") || !out.text(right) ||
        !out.text("AB ∧ matrixTrace ") || !out.text(left) ||
        !out.text("C = matrixTrace ") || !out.text(right) ||
        !out.text("C ∧ (") || !out.text(left) || !out.text("A ≠ ") ||
        !out.text(right) || !out.text("A ∨ ") || !out.text(left) ||
        !out.text("B ≠ ") || !out.text(right) || !out.text("B)"))
      return false;
  } else {
    if (!out.text("matrixTrace ") || !out.text(left) ||
        !out.text("A = 2 ∧ matrixTrace ") || !out.text(left) ||
        !out.text("B = 2 ∧ matrixTrace ") || !out.text(left) ||
        !out.text("C ≠ 2"))
      return false;
  }
  return out.text(" := by\n  norm_num [") && out.text(left) &&
         out.text("A, ") && out.text(left) && out.text("B, ") &&
         out.text(left) && out.text("AB, ") && out.text(left) &&
         out.text("C, ") && out.text(right) && out.text("A, ") &&
         out.text(right) && out.text("B, ") && out.text(right) &&
         out.text("AB, ") && out.text(right) &&
         out.text("C, matrixTrace, matrixMultiply, matrixInverse]\n\n");
}

} // namespace holonics::codec::characteristic_render_detail

namespace holonics::codec {

HOLONICS_CALLABLE inline bool render_characteristic_hypergeometry(
    const characteristic_hypergeometry_surface &surface,
    characteristic_formal_face &face) noexcept {
  using rederivation_render_detail::writer;
  using namespace characteristic_render_detail;
  writer out{face};
  face.identity = exact::word{200'410};
  face.passage = surface.passage;
  if (!surface.exact ||
      !out.text("import Mathlib.Tactic.LinearCombination\nimport "
                "Mathlib.Tactic.NormNum\n\nnamespace Soma.Holonics.R33\n\n"
                "structure Matrix2 where\n  a : ℤ\n  b : ℤ\n  c : ℤ\n  d : ℤ\n "
                " deriving DecidableEq, Repr\n\n"
                "def matrixMultiply (u v : Matrix2) : Matrix2 :=\n  "
                "{a:=u.a*v.a+u.b*v.c,b:=u.a*v.b+u.b*v.d,c:=u.c*v.a+u.d*v.c,d:="
                "u.c*v.b+u.d*v.d}\n"
                "def matrixInverse (u : Matrix2) : Matrix2 := "
                "{a:=u.d,b:=-u.b,c:=-u.c,d:=u.a}\n"
                "def matrixTrace (u : Matrix2) : ℤ := u.a+u.d\n\n"
                "def traceLawCoefficients : List ℤ := ") ||
      !coefficient_list(out, surface.coefficients) ||
      !out.text("\n\ndef tracePolynomial (x y z k : ℤ) : ℤ :=\n  ") ||
      !polynomial(out, surface.coefficients) ||
      !out.text("\n\ntheorem returnedTraceLawCoefficients : "
                "traceLawCoefficients = ") ||
      !coefficient_list(out, surface.coefficients) ||
      !out.text(
          " := by rfl\n\n"
          "theorem discoveredCharacteristicTransport (a b c d e f g h : ℤ)\n"
          "    (hA : a*d-b*c=1) (hB : e*h-f*g=1) :\n"
          "    let A : Matrix2 := {a:=a,b:=b,c:=c,d:=d}\n"
          "    let B : Matrix2 := {a:=e,b:=f,c:=g,d:=h}\n"
          "    tracePolynomial (matrixTrace A) (matrixTrace B) (matrixTrace "
          "(matrixMultiply A B))\n"
          "      (matrixTrace (matrixMultiply (matrixMultiply (matrixMultiply "
          "A B) (matrixInverse A)) (matrixInverse B))) = 0 := by\n"
          "  dsimp [tracePolynomial, matrixTrace, matrixMultiply, "
          "matrixInverse]\n"
          "  linear_combination ((e+h)*(e+h)-2) * hA + "
          "((a+d)*(a+d)-2*(a*d-b*c)) * hB\n\n"))
    return false;
  constexpr const char *names[characteristic_surface_witness_count]{
      "individualFacesDoNotDetermineClosed",
      "equalCharacteristicDoesNotIdentifySource",
      "orderReversalRetainsCharacteristic",
      "simultaneousRechartRetainsCharacteristic",
      "parabolicFacesCanCloseHyperbolically"};
  constexpr const char *prefixes[characteristic_surface_witness_count][2]{
      {"w0l", "w0r"},
      {"w1l", "w1r"},
      {"w2l", "w2r"},
      {"w3l", "w3r"},
      {"w4l", "w4r"}};
  for (std::uint8_t i = 0; i < characteristic_surface_witness_count; ++i)
    if (!numeric_countermodel(out, names[i], prefixes[i][0], prefixes[i][1],
                              surface.witnesses[i][0], surface.witnesses[i][1],
                              i))
      return false;
  return out.text("theorem generated_characteristic_hypergeometry : "
                  "traceLawCoefficients = ") &&
         coefficient_list(out, surface.coefficients) &&
         out.text(" := by exact returnedTraceLawCoefficients\n\n"
                  "end Soma.Holonics.R33\n\n#check "
                  "Soma.Holonics.R33.discoveredCharacteristicTransport\n"
                  "#check "
                  "Soma.Holonics.R33.generated_characteristic_hypergeometry\n");
}

} // namespace holonics::codec
