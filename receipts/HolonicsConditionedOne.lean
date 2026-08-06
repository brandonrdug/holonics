import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix

namespace Holonics.Conditioned

/-- Returned by the conditioned body from the mounted declaration
    `Matrix.trace_mul_comm`, which it reached through its own material. -/
theorem holonicTraceSwap (A B : Matrix (Fin 3) (Fin 3) Int) :
    trace (A * B) = trace (B * A) :=
  Matrix.trace_mul_comm A B

end Holonics.Conditioned
