#pragma once

#include <holonics/codec/trace_fiber_countermodel_renderer.hpp>

namespace holonics::codec {

HOLONICS_CALLABLE inline bool render_trace_fiber(
    const trace_fiber_discovery_surface &surface,
    trace_fiber_formal_face &face) noexcept {
  using rederivation_render_detail::writer;
  using namespace trace_fiber_render_detail;
  writer out{face};
  face.identity = exact::word{201'410};
  face.passage = surface.passage;
  if (!surface.exact ||
      !out.text("import Mathlib.Tactic.LinearCombination\nimport "
                "Mathlib.Tactic.NormNum\nimport Mathlib.Tactic.Ring\n\n"
                "namespace Soma.Holonics.R34\n\nstructure Matrix2 where\n"
                "  a : ℤ\n  b : ℤ\n  c : ℤ\n  d : ℤ\n"
                "  deriving DecidableEq, Repr\n\ndef matrixMultiply (u v : "
                "Matrix2) : Matrix2 :=\n  {a:=u.a*v.a+u.b*v.c,b:=u.a*v.b+"
                "u.b*v.d,c:=u.c*v.a+u.d*v.c,d:=u.c*v.b+u.d*v.d}\n"
                "def matrixTrace (u : Matrix2) : ℤ := u.a+u.d\n\n"
                "def sumLawCoefficients : List ℤ := ") ||
      !coefficient_list(out, surface.coefficients[0]) ||
      !out.text("\ndef productLawCoefficients : List ℤ := ") ||
      !coefficient_list(out, surface.coefficients[1]) ||
      !out.text("\n\ndef traceSumPolynomial (a b c d e f s : ℤ) : ℤ :=\n  ") ||
      !polynomial(out, surface.coefficients[0], "s") ||
      !out.text("\n\ndef traceProductPolynomial (a b c d e f r : ℤ) : ℤ :=\n  ") ||
      !polynomial(out, surface.coefficients[1], "r") ||
      !out.text(
          "\n\ntheorem discoveredTraceFiber (a b c d e f g h i j k l : ℤ)\n"
          "    (hA : a*d-b*c=1) (hB : e*h-f*g=1) (hC : i*l-j*k=1) :\n"
          "    let A : Matrix2 := {a:=a,b:=b,c:=c,d:=d}\n"
          "    let B : Matrix2 := {a:=e,b:=f,c:=g,d:=h}\n"
          "    let C : Matrix2 := {a:=i,b:=j,c:=k,d:=l}\n"
          "    let p := matrixTrace (matrixMultiply (matrixMultiply A B) C)\n"
          "    let q := matrixTrace (matrixMultiply (matrixMultiply A C) B)\n"
          "    traceSumPolynomial (matrixTrace A) (matrixTrace B) (matrixTrace C)\n"
          "      (matrixTrace (matrixMultiply A B)) (matrixTrace (matrixMultiply A C))\n"
          "      (matrixTrace (matrixMultiply B C)) (p+q) = 0 ∧\n"
          "    traceProductPolynomial (matrixTrace A) (matrixTrace B) (matrixTrace C)\n"
          "      (matrixTrace (matrixMultiply A B)) (matrixTrace (matrixMultiply A C))\n"
          "      (matrixTrace (matrixMultiply B C)) (p*q) = 0 ∧\n"
          "    p*p-(p+q)*p+p*q=0 ∧ q*q-(p+q)*q+p*q=0 ∧\n"
          "    (p+q)*(p+q)-4*(p*q)=(p-q)*(p-q) := by\n"
          "  dsimp [traceSumPolynomial, traceProductPolynomial, matrixTrace, matrixMultiply]\n"
          "  constructor\n  · ring\n  constructor\n  · linear_combination ") ||
      !out.integer(surface.coefficients[1][84]) ||
      !out.text(
          " * (-e^2*i*l + e^2 + e*f*i*k - e*f*k*l + e*g*i*j - e*g*j*l - "
          "e*h*i^2 + 2*e*h*i*l - e*h*l^2 + f^2*k^2 - f*h*i*k + f*h*k*l + "
          "g^2*j^2 - g*h*i*j + g*h*j*l - h^2*i*l + h^2 + i^2 + l^2 - 2) * hA + ") ||
      !out.integer(surface.coefficients[1][84]) ||
      !out.text(
          " * (-a^2*i*l + a^2 + a*b*i*k - a*b*k*l + a*c*i*j - a*c*j*l + "
          "b^2*k^2 - b*c*i^2 + 2*b*c*i*l - b*c*l^2 - b*d*i*k + b*d*k*l + "
          "c^2*j^2 - c*d*i*j + c*d*j*l - d^2*i*l + d^2 + 2*i*l - 2) * hB + ") ||
      !out.integer(surface.coefficients[1][84]) ||
      !out.text(
          " * (-a^2*f*g + a*b*e*g - a*b*g*h + a*c*e*f - a*c*f*h + b^2*g^2 - "
          "b*c*e^2 + 2*b*c*f*g - b*c*h^2 + 2*b*c - b*d*e*g + b*d*g*h + "
          "c^2*f^2 - c*d*e*f + c*d*f*h - d^2*f*g + 2*f*g) * hC\n"
          "  constructor\n  · ring\n  constructor <;> ring\n\n"))
    return false;
  constexpr const char *names[5]{"orientationExchangesSheets",
                                  "lowerFiberDoesNotIdentifySource",
                                  "simultaneousRechartRetainsFiber",
                                  "branchWitness", "twoSheetWitness"};
  constexpr const char *prefix[5][2]{{"w0l", "w0r"}, {"w1l", "w1r"},
                                      {"w2l", "w2r"}, {"w3l", "w3r"},
                                      {"w4l", "w4r"}};
  for (std::uint8_t i = 0; i < 5; ++i)
    if (!trace_fiber_countermodel_detail::countermodel(
            out, names[i], prefix[i][0], prefix[i][1],
            surface.witnesses[i][0], surface.witnesses[i][1], i))
      return false;
  return out.text("theorem generated_trace_fiber_lifting :\n  "
                  "sumLawCoefficients = ") &&
         coefficient_list(out, surface.coefficients[0]) &&
         out.text(" ∧ productLawCoefficients = ") &&
         coefficient_list(out, surface.coefficients[1]) &&
         out.text(" := by constructor <;> rfl\n\nend Soma.Holonics.R34\n\n"
                  "#check Soma.Holonics.R34.discoveredTraceFiber\n"
                  "#check Soma.Holonics.R34.generated_trace_fiber_lifting\n");
}

} // namespace holonics::codec
