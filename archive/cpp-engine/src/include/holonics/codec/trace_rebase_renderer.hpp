#pragma once

#include <holonics/codec/trace_rebase_renderer_atoms.hpp>
#include <holonics/codec/trace_rebase_witness_renderer.hpp>

namespace holonics::codec {

HOLONICS_CALLABLE inline bool render_trace_rebase(
    const trace_rebase_discovery_surface &surface,
    trace_rebase_formal_face &face) noexcept {
  using rederivation_render_detail::writer;
  using namespace trace_rebase_render_detail;
  writer out{face};
  face.identity = exact::word{202'410};
  face.passage = surface.passage;
  if (!surface.exact ||
      !out.text("import R34_TRACE_FIBER_LIFTING\n"
                "import Mathlib.Tactic.Linarith\n\nnamespace Soma.Holonics.R35\n\n"
                "open Soma.Holonics.R34\n\nset_option linter.unusedVariables false\n"
                "set_option linter.unusedTactic false\n"
                "set_option linter.unreachableTactic false\n\n"
                "@[ext] structure TraceChart where\n"
                "  a : ℤ\n  b : ℤ\n  c : ℤ\n  d : ℤ\n  e : ℤ\n  f : ℤ\n  t : ℤ\n"
                "  deriving DecidableEq, Repr\n\ndef matrixInverse (u : Matrix2) : Matrix2 :=\n"
                "  {a:=u.d,b:=-u.b,c:=-u.c,d:=u.a}\n\ndef chartOf (A B C : Matrix2) : TraceChart :=\n"
                "  {a:=matrixTrace A,b:=matrixTrace B,c:=matrixTrace C,"
                "d:=matrixTrace (matrixMultiply A B),e:=matrixTrace (matrixMultiply A C),"
                "f:=matrixTrace (matrixMultiply B C),"
                "t:=matrixTrace (matrixMultiply (matrixMultiply A B) C)}\n\n") ||
      !map_definitions(out, surface))
    return false;
  for (std::uint8_t move = 0; move < 5; ++move) {
    if (!out.text("\ndef applyRebase") || !out.natural(move) ||
        !out.text(" (x : TraceChart) : TraceChart := ") ||
        !application(out, move, "x") || !out.text("\n"))
      return false;
  }
  if (!out.text(
          "\ndef moved0 (A B C : Matrix2) : TraceChart := chartOf B A C\n"
          "def moved1 (A B C : Matrix2) : TraceChart := chartOf A C B\n"
          "def moved2 (A B C : Matrix2) : TraceChart := chartOf (matrixInverse A) B C\n"
          "def moved3 (A B C : Matrix2) : TraceChart := chartOf (matrixMultiply A B) B C\n"
          "def moved4 (A B C : Matrix2) : TraceChart := "
          "chartOf (matrixMultiply A (matrixInverse B)) B C\n\n"))
    return false;
  for (std::uint8_t move = 0; move < 5; ++move) {
    if (!out.text("theorem discoveredRebase") || !out.natural(move) ||
        !out.text(
            " (A B C : Matrix2)\n    (hA : A.a*A.d-A.b*A.c=1) "
            "(hB : B.a*B.d-B.b*B.c=1) (hC : C.a*C.d-C.b*C.c=1) :\n"
            "    applyRebase") ||
        !out.natural(move) || !out.text(" (chartOf A B C) = moved") ||
        !out.natural(move) ||
        !out.text(
            " A B C := by\n  rcases A with ⟨a0,a1,a2,a3⟩\n"
            "  rcases B with ⟨b0,b1,b2,b3⟩\n  rcases C with ⟨c0,c1,c2,c3⟩\n"
            "  have returned := discoveredTraceFiber a0 a1 a2 a3 b0 b1 b2 b3 "
            "c0 c1 c2 c3 (by simpa using hA) (by simpa using hB) (by simpa using hC)\n"
            "  have hsum := returned.1\n"
            "  dsimp [traceSumPolynomial] at hsum\n"
            "  have hBtraceA := congrArg (fun z : ℤ => (a0+a3)*z) hB\n"
            "  have hBtraceAC := congrArg (fun z : ℤ => "
            "(a0*c0+a3*c3+a1*c2+a2*c1)*z) hB\n"
            "  ext <;> dsimp [applyRebase0, applyRebase1, applyRebase2, applyRebase3, "
            "applyRebase4, chartOf, moved0, moved1, moved2, moved3, moved4, "
            "matrixInverse, matrixMultiply, matrixTrace, "
            "r35m0c0, r35m0c1, r35m0c2, r35m0c3, r35m0c4, r35m0c5, r35m0c6, "
            "r35m1c0, r35m1c1, r35m1c2, r35m1c3, r35m1c4, r35m1c5, r35m1c6, "
            "r35m2c0, r35m2c1, r35m2c2, r35m2c3, r35m2c4, r35m2c5, r35m2c6, "
            "r35m3c0, r35m3c1, r35m3c2, r35m3c3, r35m3c4, r35m3c5, r35m3c6, "
            "r35m4c0, r35m4c1, r35m4c2, r35m4c3, r35m4c4, r35m4c5, r35m4c6]\n"
            "  all_goals ring_nf at hA hB hC hsum hBtraceA hBtraceAC ⊢\n"
            "  all_goals nlinarith [hA, hB, hC, hsum, hBtraceA, hBtraceAC]\n\n"))
      return false;
  }
  if (!out.text(
      "def deckFiber (s t : ℤ) : ℤ := s-t\n\n"
      "theorem deckBranchVerticalDerivative (s t u : ℤ) (h : 2*t=s) :\n"
      "    deckFiber s t=t ∧ deckFiber s (t+u)-deckFiber s t=-u := by\n"
      "  constructor <;> dsimp [deckFiber] <;> nlinarith\n\n"
      "theorem returnedDeckEigenvalue : (-1 : ℤ) = ") ||
      !out.integer(surface.deck_eigenvalue) ||
      !out.text(" := by norm_num\n\n"
      "theorem generated_trace_character_rebases (A B C : Matrix2)\n"
      "    (hA : A.a*A.d-A.b*A.c=1) (hB : B.a*B.d-B.b*B.c=1) "
      "(hC : C.a*C.d-C.b*C.c=1) :\n"
      "    applyRebase0 (chartOf A B C)=moved0 A B C ∧\n"
      "    applyRebase1 (chartOf A B C)=moved1 A B C ∧\n"
      "    applyRebase2 (chartOf A B C)=moved2 A B C ∧\n"
      "    applyRebase3 (chartOf A B C)=moved3 A B C ∧\n"
      "    applyRebase4 (chartOf A B C)=moved4 A B C := by\n"
      "  exact ⟨discoveredRebase0 A B C hA hB hC, discoveredRebase1 A B C hA hB hC, "
      "discoveredRebase2 A B C hA hB hC, discoveredRebase3 A B C hA hB hC, "
      "discoveredRebase4 A B C hA hB hC⟩\n\nend Soma.Holonics.R35\n\n"
      "#check Soma.Holonics.R35.generated_trace_character_rebases\n"))
    return false;
  return true;
}

} // namespace holonics::codec
