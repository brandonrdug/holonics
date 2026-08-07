import R34_TRACE_FIBER_LIFTING

namespace Soma.Holonics.R34

def heldA : Matrix2 := {a:=2,b:=1,c:=1,d:=1}
def heldB : Matrix2 := {a:=1,b:=2,c:=0,d:=1}
def heldC : Matrix2 := {a:=1,b:=0,c:=2,d:=1}
def heldAB : Matrix2 := {a:=2,b:=5,c:=1,d:=3}
def heldAC : Matrix2 := {a:=4,b:=1,c:=3,d:=1}
def heldBC : Matrix2 := {a:=5,b:=2,c:=2,d:=1}
def heldABC : Matrix2 := {a:=12,b:=5,c:=7,d:=3}
def heldACB : Matrix2 := {a:=4,b:=9,c:=3,d:=7}

def heldLower : List ℤ := [3,2,2,5,5,6]
def heldAnchor : ℤ := 15
def heldCompanion : ℤ := 11
def heldSourceCompanion : ℤ := 11
def heldQuadratic : List ℤ := [1,(-26),165]

theorem heldoutTraceFiberTransport :
  heldAB = matrixMultiply heldA heldB ∧ heldAC = matrixMultiply heldA heldC ∧
  heldBC = matrixMultiply heldB heldC ∧ heldABC = matrixMultiply heldAB heldC ∧
  heldACB = matrixMultiply heldAC heldB ∧ heldCompanion = heldSourceCompanion ∧
  traceSumPolynomial 3 2 2 5 5 6 (heldAnchor+heldCompanion) = 0 ∧ traceProductPolynomial 3 2 2 5 5 6 (heldAnchor*heldCompanion) = 0 := by
  have returned := discoveredTraceFiber 2 1 1 1 1 2 0 1 1 0 2 1 (by norm_num) (by norm_num) (by norm_num)
  constructor
  · norm_num [heldA, heldB, heldAB, matrixMultiply]
  constructor
  · norm_num [heldA, heldC, heldAC, matrixMultiply]
  constructor
  · norm_num [heldB, heldC, heldBC, matrixMultiply]
  constructor
  · norm_num [heldAB, heldC, heldABC, matrixMultiply]
  constructor
  · norm_num [heldAC, heldB, heldACB, matrixMultiply]
  constructor
  · norm_num [heldCompanion, heldSourceCompanion]
  constructor
  · simpa [heldAnchor, heldCompanion, matrixMultiply, matrixTrace] using returned.1
  · simpa [heldAnchor, heldCompanion, matrixMultiply, matrixTrace] using returned.2.1

theorem generated_heldout_trace_fiber : heldCompanion = heldSourceCompanion := by
  exact heldoutTraceFiberTransport.2.2.2.2.2.1

end Soma.Holonics.R34

#check Soma.Holonics.R34.generated_heldout_trace_fiber
