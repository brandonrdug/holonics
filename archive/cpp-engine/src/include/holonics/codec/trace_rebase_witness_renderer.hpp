#pragma once

#include <holonics/codec/trace_rebase_renderer_atoms.hpp>

namespace holonics::codec::trace_rebase_render_detail {

template <class Writer>
HOLONICS_CALLABLE inline bool render_rebase_consequences(
    Writer &out, const trace_rebase_witness_surface &surface) noexcept {
  if (!out.text(
          "\nnamespace Soma.Holonics.R35\n\nopen Soma.Holonics.R34\n\n"
          "def traceFiberF (x : TraceChart) : ℤ :=\n"
          "  x.t*x.t - traceSumPolynomial x.a x.b x.c x.d x.e x.f 0*x.t "
          "- traceProductPolynomial x.a x.b x.c x.d x.e x.f 0\n\n"
          "theorem returnedHypersurfaceInvariance (x : TraceChart) :\n"
          "    traceFiberF (applyRebase0 x)=traceFiberF x ∧\n"
          "    traceFiberF (applyRebase1 x)=traceFiberF x ∧\n"
          "    traceFiberF (applyRebase2 x)=traceFiberF x ∧\n"
          "    traceFiberF (applyRebase3 x)=traceFiberF x ∧\n"
          "    traceFiberF (applyRebase4 x)=traceFiberF x := by\n"
          "  rcases x with ⟨a,b,c,d,e,f,t⟩\n"
          "  dsimp [traceFiberF, applyRebase0, applyRebase1, applyRebase2, "
          "applyRebase3, applyRebase4, traceSumPolynomial, "
          "traceProductPolynomial, r35m0c0, r35m0c1, r35m0c2, r35m0c3, "
          "r35m0c4, r35m0c5, r35m0c6, r35m1c0, r35m1c1, r35m1c2, "
          "r35m1c3, r35m1c4, r35m1c5, r35m1c6, r35m2c0, r35m2c1, "
          "r35m2c2, r35m2c3, r35m2c4, r35m2c5, r35m2c6, r35m3c0, "
          "r35m3c1, r35m3c2, r35m3c3, r35m3c4, r35m3c5, r35m3c6, "
          "r35m4c0, r35m4c1, r35m4c2, r35m4c3, r35m4c4, r35m4c5, "
          "r35m4c6]\n"
          "  constructor\n  · ring\n  constructor\n  · ring\n  constructor\n"
          "  · ring\n  constructor <;> ring\n\n"
          "theorem returnedInverseRelations (x : TraceChart) :\n"
          "    applyRebase0 (applyRebase0 x)=x ∧\n"
          "    applyRebase1 (applyRebase1 x)=x ∧\n"
          "    applyRebase2 (applyRebase2 x)=x ∧\n"
          "    applyRebase4 (applyRebase3 x)=x ∧\n"
          "    applyRebase3 (applyRebase4 x)=x := by\n"
          "  rcases x with ⟨a,b,c,d,e,f,t⟩\n"
          "  constructor\n  · ext <;> simp [applyRebase0, r35m0c0, r35m0c1, "
          "r35m0c2, r35m0c3, r35m0c4, r35m0c5, r35m0c6] <;> ring\n"
          "  constructor\n  · ext <;> simp [applyRebase1, r35m1c0, r35m1c1, "
          "r35m1c2, r35m1c3, r35m1c4, r35m1c5, r35m1c6] <;> ring\n"
          "  constructor\n  · ext <;> simp [applyRebase2, r35m2c0, r35m2c1, "
          "r35m2c2, r35m2c3, r35m2c4, r35m2c5, r35m2c6] <;> ring\n"
          "  constructor\n"
          "  · ext <;> simp [applyRebase3, applyRebase4, r35m3c0, r35m3c1, "
          "r35m3c2, r35m3c3, r35m3c4, r35m3c5, r35m3c6, r35m4c0, "
          "r35m4c1, r35m4c2, r35m4c3, r35m4c4, r35m4c5, r35m4c6] <;> ring\n"
          "  · ext <;> simp [applyRebase3, applyRebase4, r35m3c0, r35m3c1, "
          "r35m3c2, r35m3c3, r35m3c4, r35m3c5, r35m3c6, r35m4c0, "
          "r35m4c1, r35m4c2, r35m4c3, r35m4c4, r35m4c5, r35m4c6] <;> ring\n\n"))
    return false;

  if (!matrix_definition(out, "fixedA", surface.fixed_matrices[0]) ||
      !matrix_definition(out, "fixedB", surface.fixed_matrices[1]) ||
      !matrix_definition(out, "fixedC", surface.fixed_matrices[2]) ||
      !chart_definition(out, "fixedChart", surface.fixed_chart) ||
      !out.text(
          "theorem actualFixedWitness :\n"
          "    fixedA.a*fixedA.d-fixedA.b*fixedA.c=1 ∧\n"
          "    fixedB.a*fixedB.d-fixedB.b*fixedB.c=1 ∧\n"
          "    fixedC.a*fixedC.d-fixedC.b*fixedC.c=1 ∧\n"
          "    chartOf fixedA fixedB fixedC=fixedChart ∧\n"
          "    applyRebase0 fixedChart=fixedChart ∧ applyRebase1 fixedChart=fixedChart ∧\n"
          "    applyRebase2 fixedChart=fixedChart ∧ applyRebase3 fixedChart=fixedChart ∧\n"
          "    applyRebase4 fixedChart=fixedChart := by\n"
          "  norm_num [fixedA, fixedB, fixedC, fixedChart, chartOf, matrixTrace, "
          "matrixMultiply, applyRebase0, applyRebase1, applyRebase2, applyRebase3, "
          "applyRebase4, r35m0c0, r35m0c1, r35m0c2, r35m0c3, r35m0c4, r35m0c5, "
          "r35m0c6, r35m1c0, r35m1c1, r35m1c2, r35m1c3, r35m1c4, r35m1c5, "
          "r35m1c6, r35m2c0, r35m2c1, r35m2c2, r35m2c3, r35m2c4, r35m2c5, "
          "r35m2c6, r35m3c0, r35m3c1, r35m3c2, r35m3c3, r35m3c4, r35m3c5, "
          "r35m3c6, r35m4c0, r35m4c1, r35m4c2, r35m4c3, r35m4c4, r35m4c5, "
          "r35m4c6]\n\n"))
    return false;

  if (!matrix_definition(out, "exchangeA", surface.exchange_matrices[0]) ||
      !matrix_definition(out, "exchangeB", surface.exchange_matrices[1]) ||
      !matrix_definition(out, "exchangeC", surface.exchange_matrices[2]) ||
      !matrix_definition(out, "exchangeTargetA",
                         surface.exchange_target_matrices[0]) ||
      !matrix_definition(out, "exchangeTargetB",
                         surface.exchange_target_matrices[1]) ||
      !matrix_definition(out, "exchangeTargetC",
                         surface.exchange_target_matrices[2]) ||
      !chart_definition(out, "exchangeChart", surface.exchange_chart) ||
      !chart_definition(out, "exchangeTarget", surface.exchange_target) ||
      !out.text(
          "theorem actualExchangeWitness :\n"
          "    chartOf exchangeA exchangeB exchangeC=exchangeChart ∧\n"
          "    chartOf exchangeTargetA exchangeTargetB exchangeTargetC=exchangeTarget ∧\n"
          "    applyRebase0 exchangeChart=exchangeTarget ∧ exchangeChart≠exchangeTarget := by\n"
          "  norm_num [exchangeA, exchangeB, exchangeC, exchangeTargetA, "
          "exchangeTargetB, exchangeTargetC, exchangeChart, exchangeTarget, chartOf, "
          "matrixTrace, matrixMultiply, applyRebase0, r35m0c0, r35m0c1, r35m0c2, "
          "r35m0c3, r35m0c4, r35m0c5, r35m0c6]\n\n"))
    return false;

  if (!matrix_definition(out, "branchA", surface.branch_matrices[0]) ||
      !matrix_definition(out, "branchB", surface.branch_matrices[1]) ||
      !matrix_definition(out, "branchC", surface.branch_matrices[2]) ||
      !chart_definition(out, "branchChart", surface.branch_chart) ||
      !out.text(
          "theorem actualBranchWitness :\n"
          "    chartOf branchA branchB branchC=branchChart ∧\n"
          "    traceSumPolynomial branchChart.a branchChart.b branchChart.c "
          "branchChart.d branchChart.e branchChart.f (2*branchChart.t)=0 := by\n"
          "  norm_num [branchA, branchB, branchC, branchChart, chartOf, matrixTrace, "
          "matrixMultiply, traceSumPolynomial]\n\n"))
    return false;

  if (!chart_definition(out, "noncommutator", surface.noncommutator) ||
      !out.text(
          "def chartSub (x y : TraceChart) : TraceChart :=\n"
          "  {a:=x.a-y.a,b:=x.b-y.b,c:=x.c-y.c,d:=x.d-y.d,e:=x.e-y.e,"
          "f:=x.f-y.f,t:=x.t-y.t}\n\n"
          "theorem actualNoncommutingWitness :\n"
          "    chartSub (applyRebase1 (applyRebase0 exchangeChart)) "
          "(applyRebase0 (applyRebase1 exchangeChart))=noncommutator ∧\n"
          "    applyRebase1 (applyRebase0 exchangeChart)≠"
          "applyRebase0 (applyRebase1 exchangeChart) := by\n"
          "  norm_num [chartSub, exchangeChart, noncommutator, applyRebase0, "
          "applyRebase1, r35m0c0, r35m0c1, r35m0c2, r35m0c3, r35m0c4, "
          "r35m0c5, r35m0c6, r35m1c0, r35m1c1, r35m1c2, r35m1c3, "
          "r35m1c4, r35m1c5, r35m1c6]\n\n"))
    return false;

  if (!chart_definition(out, "chainSourceGradient",
                        surface.chain_source_gradient) ||
      !chart_definition(out, "chainTargetGradient",
                        surface.chain_target_gradient) ||
      !chart_definition(out, "chainTangent", surface.chain_tangent) ||
      !chart_definition(out, "chainImage", surface.chain_image) ||
      !out.text(
          "def dotChart (x y : TraceChart) : ℤ := "
          "x.a*y.a+x.b*y.b+x.c*y.c+x.d*y.d+x.e*y.e+x.f*y.f+x.t*y.t\n"
          "def returnedJacobian (v : TraceChart) : TraceChart := ") ||
      !jacobian_application(out, surface.chain_jacobian, "v") ||
      !out.text(
          "\n\ntheorem tangentTransport (sourceGradient targetGradient tangent image : "
          "TraceChart) (hSource : dotChart sourceGradient tangent=0) "
          "(hChain : dotChart targetGradient image=dotChart sourceGradient tangent) :\n"
          "    dotChart targetGradient image=0 := by rw [hChain, hSource]\n\n"
          "theorem actualReturnedChainRule :\n"
          "    dotChart chainSourceGradient chainTangent=0 ∧\n"
          "    returnedJacobian chainTangent=chainImage ∧\n"
          "    dotChart chainTargetGradient chainImage=0 := by\n"
          "  norm_num [dotChart, chainSourceGradient, chainTargetGradient, "
          "chainTangent, chainImage, returnedJacobian]\n\n"))
    return false;

  if (!chart_definition(out, "returnedDeckVector", surface.deck_vector) ||
      !chart_definition(out, "returnedDeckImage", surface.deck_image) ||
      !out.text("def scaleChart (z : ℤ) (x : TraceChart) : TraceChart := "
                "{a:=z*x.a,b:=z*x.b,c:=z*x.c,d:=z*x.d,e:=z*x.e,"
                "f:=z*x.f,t:=z*x.t}\n"
                "theorem actualDeckEigenWitness : returnedDeckImage=scaleChart ") ||
      !out.integer(surface.deck_eigenvalue) ||
      !out.text(" returnedDeckVector := by norm_num [returnedDeckImage, "
                "returnedDeckVector, scaleChart]\n\n"
                "end Soma.Holonics.R35\n\n"
                "#check Soma.Holonics.R35.returnedHypersurfaceInvariance\n"
                "#check Soma.Holonics.R35.actualReturnedChainRule\n"))
    return false;
  return true;
}

HOLONICS_CALLABLE inline bool render_trace_rebase_witnesses(
    const trace_rebase_witness_surface &surface,
    trace_rebase_formal_face &face) noexcept {
  rederivation_render_detail::writer out{face};
  return render_rebase_consequences(out, surface);
}

} // namespace holonics::codec::trace_rebase_render_detail
