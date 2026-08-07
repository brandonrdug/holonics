import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix

namespace Holonics.Conditioned

theorem holonicTraceSwap (A B : Matrix (Fin 3) (Fin 3) Int) :
    trace (A * B) = trace (B * A) :=
  Matrix.trace_mul_comm A B

/-- Returned only because the first theorem's acceptance became material
    the body could reach. Its proof term is the reached name applied, and
    that name was copied out of the standing rather than authored here. -/
theorem holonicTraceCycle (A B C : Matrix (Fin 3) (Fin 3) Int) :
    trace (A * B * C) = trace (C * (A * B)) :=
  holonicTraceSwap (A * B) C

end Holonics.Conditioned
