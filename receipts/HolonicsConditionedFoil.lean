import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix

namespace Holonics.Conditioned

theorem holonicTraceCycleFoil (A B C : Matrix (Fin 3) (Fin 3) Int) :
    trace (A * B * C) = trace (C * (A * B)) :=
  holonicTraceSwap (A * B) C

end Holonics.Conditioned
