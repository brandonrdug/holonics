import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

open Matrix BigOperators
namespace Soma.Holonics.R21.Code

def pairMass : Fin 20 → ℤ := ![1,4,6,4,1,3,12,18,12,3,3,12,18,12,3,1,4,6,4,1]

def pairQ : Matrix (Fin 20) (Fin 20) ℤ :=
  ![![0,4,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  ![1,0,3,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,2,0,2,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,3,0,1,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,4,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0],
  ![1,0,0,0,0,0,4,0,0,0,2,0,0,0,0,0,0,0,0,0],
  ![0,1,0,0,0,1,0,3,0,0,0,2,0,0,0,0,0,0,0,0],
  ![0,0,1,0,0,0,2,0,2,0,0,0,2,0,0,0,0,0,0,0],
  ![0,0,0,1,0,0,0,3,0,1,0,0,0,2,0,0,0,0,0,0],
  ![0,0,0,0,1,0,0,0,4,0,0,0,0,0,2,0,0,0,0,0],
  ![0,0,0,0,0,2,0,0,0,0,0,4,0,0,0,1,0,0,0,0],
  ![0,0,0,0,0,0,2,0,0,0,1,0,3,0,0,0,1,0,0,0],
  ![0,0,0,0,0,0,0,2,0,0,0,2,0,2,0,0,0,1,0,0],
  ![0,0,0,0,0,0,0,0,2,0,0,0,3,0,1,0,0,0,1,0],
  ![0,0,0,0,0,0,0,0,0,2,0,0,0,4,0,0,0,0,0,1],
  ![0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,4,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,1,0,3,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,2,0,2,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,3,0,1],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,4,0]]

def pairVector : Fin 20 → ℤ := ![18,0,-6,0,18,6,0,-2,0,6,-6,0,2,0,-6,-18,0,6,0,-18]
def pairEigenvalue : ℤ := 1

theorem generated_pair_detailed_balance :
    ∀ i j, pairMass i * pairQ i j = pairMass j * pairQ j i := by
  native_decide

theorem generated_tensor_jacobi_eigenvector :
    pairQ *ᵥ pairVector = pairEigenvalue • pairVector := by
  native_decide

def codeWeight : Fin 8 → ℤ := ![1,0,0,7,7,0,0,1]
def codeDual : Fin 8 → ℤ := ![1,0,0,0,7,0,0,0]
def krawtchouk : Matrix (Fin 8) (Fin 8) ℤ :=
  ![![1,1,1,1,1,1,1,1],
  ![7,5,3,1,-1,-3,-5,-7],
  ![21,9,1,-3,-3,1,9,21],
  ![35,5,-5,-3,3,5,-5,-35],
  ![35,-5,-5,3,3,-5,-5,35],
  ![21,-9,1,3,-3,-1,9,-21],
  ![7,-5,3,-1,-1,3,-5,7],
  ![1,-1,1,-1,1,-1,1,-1]]

theorem generated_code_moment_transport :
    ∀ j, codeDual j * 16 = ∑ i, codeWeight i * krawtchouk j i := by
  native_decide

def characteristicMultiplicity : Fin 8 → ℤ := ![1,2,3,4,4,3,2,1]

theorem generated_pair_characteristic_degree :
    ∑ i, characteristicMultiplicity i = 20 := by
  native_decide

end Soma.Holonics.R21.Code

#check Soma.Holonics.R21.Code.generated_tensor_jacobi_eigenvector
