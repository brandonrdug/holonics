import HolonicsResearch.Geometry.CyclicGrover.GroverCycle

namespace Holonics.Epime.GroverCycle
open Matrix Polynomial
open scoped Fin.NatCast

theorem neighbors_distinct (n : ℕ) (hn : 1 ≤ n) (x : Vertex n) :
    finRotate (n+2) x ≠ (finRotate (n+2)).symm x := by
  haveI : NeZero (n+2) := ⟨by omega⟩
  intro h
  have ha := congrArg (fun y : Vertex n => y+1) h
  have hh : x+(1+1 : Vertex n)=x := by
    simpa [finRotate_apply, finRotate_symm_apply, add_assoc] using ha
  have hc : x+(1+1 : Vertex n)=x+0 := by rw [add_zero]; exact hh
  have hz : (1+1 : Vertex n)=0 := add_left_cancel hc
  have hz' : (2 : Vertex n)=0 := by simpa only [one_add_one_eq_two] using hz
  have hv := congrArg Fin.val hz'
  change 2 % (n+2) = 0 at hv
  rw [Nat.mod_eq_of_lt (by omega : 2 < n+2)] at hv
  omega

def neighbors (n : ℕ) (x : Vertex n) : Finset (Vertex n) :=
  {finRotate (n+2) x, (finRotate (n+2)).symm x}

theorem degree_two (n : ℕ) (hn : 1 ≤ n) (x : Vertex n) :
    (neighbors n x).card = 2 := by
  exact Finset.card_pair (neighbors_distinct n hn x)

/-- The foreign rational chart's literal Grover coin uses the derived neighbor
count. This certificate joins it to the integral operator; no 1/3 enters. -/
def rationalGrover (n : ℕ) : Matrix (Dart n) (Dart n) ℚ :=
  fun e d => if e.1=target n d then
    2 / ((neighbors n (target n d)).card : ℚ) - (if e=reverse n d then 1 else 0) else 0

theorem integral_matches_rational (n : ℕ) (hn : 1 ≤ n) :
    (Int.castRingHom ℚ).mapMatrix (grover n : Matrix (Dart n) (Dart n) ℤ) = rationalGrover n := by
  funext e d
  by_cases hi : e.1=target n d <;> by_cases hr : e=reverse n d <;>
    simp [grover, rationalGrover, hi, hr, degree_two n hn]

variable {R S : Type*} [CommRing R] [CommRing S]

theorem grover_map (n : ℕ) (f : R →+* S) :
    f.mapMatrix (grover n : Matrix (Dart n) (Dart n) R) =
      (grover n : Matrix (Dart n) (Dart n) S) := by
  funext e d
  by_cases hi : e.1=target n d <;> by_cases hr : e=reverse n d <;>
    simp [grover, hi, hr]

theorem grover_charpoly (n : ℕ) :
    (grover n : Matrix (Dart n) (Dart n) R).charpoly = ((X : R[X])^(n+2)-1)^2 := by
  change (Matrix.scalar (Dart n) (X : R[X]) -
    (C : R →+* R[X]).mapMatrix (grover n)).det = _
  rw [grover_map]
  exact grover_determinant n (X : R[X])

end Holonics.Epime.GroverCycle

#print axioms Holonics.Epime.GroverCycle.grover_charpoly
#print axioms Holonics.Epime.GroverCycle.integral_matches_rational
