import ElementaryHolonics.Foundation.Presentation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Unit 001 — The geometry inside a characteristic receiver

The declarations below remain symbolic in the entries of a two-by-two integer matrix. Integer
coefficients are sufficient for the polynomial identities; the Typst companion separately names
the hypotheses required to invert two or to discuss real quadric strata.
-/

namespace HolonicsNotebook.U001

structure Matrix2 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving DecidableEq, Repr

@[ext]
theorem Matrix2.ext {M N : Matrix2}
    (ha : M.a = N.a) (hb : M.b = N.b)
    (hc : M.c = N.c) (hd : M.d = N.d) : M = N := by
  cases M
  cases N
  simp_all

def zero : Matrix2 := ⟨0, 0, 0, 0⟩
def identity : Matrix2 := ⟨1, 0, 0, 1⟩

def add (M N : Matrix2) : Matrix2 :=
  ⟨M.a + N.a, M.b + N.b, M.c + N.c, M.d + N.d⟩

def scale (q : ℤ) (M : Matrix2) : Matrix2 :=
  ⟨q * M.a, q * M.b, q * M.c, q * M.d⟩

def mul (M N : Matrix2) : Matrix2 :=
  ⟨M.a * N.a + M.b * N.c,
   M.a * N.b + M.b * N.d,
   M.c * N.a + M.d * N.c,
   M.c * N.b + M.d * N.d⟩

def trace (M : Matrix2) : ℤ := M.a + M.d
def determinant (M : Matrix2) : ℤ := M.a * M.d - M.b * M.c
def discriminant (M : Matrix2) : ℤ := trace M ^ 2 - 4 * determinant M

def characteristicAt (M : Matrix2) (t : ℤ) : ℤ :=
  t ^ 2 - trace M * t + determinant M

def xCoord (M : Matrix2) : ℤ := M.a - M.d
def yCoord (M : Matrix2) : ℤ := M.b + M.c
def zCoord (M : Matrix2) : ℤ := M.b - M.c

theorem discriminant_entry_coupling (M : Matrix2) :
    discriminant M = (M.a - M.d) ^ 2 + 4 * M.b * M.c := by
  cases M
  simp [discriminant, trace, determinant]
  ring

theorem discriminant_quadric_coordinates (M : Matrix2) :
    discriminant M = xCoord M ^ 2 + yCoord M ^ 2 - zCoord M ^ 2 := by
  rw [discriminant_entry_coupling]
  simp [xCoord, yCoord, zCoord]
  ring

def adjugate (M : Matrix2) : Matrix2 :=
  ⟨M.d, -M.b, -M.c, M.a⟩

theorem determinant_mul (M N : Matrix2) :
    determinant (mul M N) = determinant M * determinant N := by
  cases M
  cases N
  simp [determinant, mul]
  ring

theorem mul_adjugate (M : Matrix2) :
    mul M (adjugate M) = scale (determinant M) identity := by
  cases M
  apply Matrix2.ext <;> simp [mul, adjugate, scale, determinant, identity] <;> ring

theorem cayleyHamilton (M : Matrix2) :
    add (add (mul M M) (scale (-trace M) M))
      (scale (determinant M) identity) = zero := by
  cases M
  apply Matrix2.ext <;>
    simp [add, mul, scale, trace, determinant, identity, zero] <;>
    ring

def commutatorTangent (X M : Matrix2) : Matrix2 :=
  add (mul X M) (scale (-1) (mul M X))

def determinantDifferential (M H : Matrix2) : ℤ :=
  M.d * H.a + M.a * H.d - M.c * H.b - M.b * H.c

theorem trace_commutatorTangent (X M : Matrix2) :
    trace (commutatorTangent X M) = 0 := by
  cases X
  cases M
  simp [trace, commutatorTangent, add, scale, mul]
  ring

theorem determinantDifferential_commutatorTangent (X M : Matrix2) :
    determinantDifferential M (commutatorTangent X M) = 0 := by
  cases X
  cases M
  simp [determinantDifferential, commutatorTangent, add, scale, mul]
  ring

theorem trace_rechart_with_adjugate (P M : Matrix2) :
    trace (mul (mul P M) (adjugate P)) = determinant P * trace M := by
  cases P
  cases M
  simp [trace, mul, adjugate, determinant]
  ring

theorem trace_rechart_of_determinant_one (P M : Matrix2)
    (hP : determinant P = 1) :
    trace (mul (mul P M) (adjugate P)) = trace M := by
  rw [trace_rechart_with_adjugate, hP, one_mul]

def scalarFiber (r : ℤ) : Matrix2 := ⟨r, 0, 0, r⟩
def repeatedRootFiber (r n : ℤ) : Matrix2 := ⟨r, n, 0, r⟩

theorem repeatedRoot_characteristicFiber (r n t : ℤ) :
    characteristicAt (repeatedRootFiber r n) t = characteristicAt (scalarFiber r) t := by
  simp [characteristicAt, repeatedRootFiber, scalarFiber, trace, determinant]

theorem repeatedRoot_nonScalar {r n : ℤ} (hn : n ≠ 0) :
    repeatedRootFiber r n ≠ scalarFiber r := by
  intro h
  have hb := congrArg Matrix2.b h
  simp [repeatedRootFiber, scalarFiber] at hb
  exact hn hb

theorem repeatedRoot_receiverFiber {r n : ℤ} (hn : n ≠ 0) :
    Soma.Holonics.FaceEq
        (fun M : Matrix2 ↦ (trace M, determinant M))
        (repeatedRootFiber r n) (scalarFiber r) ∧
      repeatedRootFiber r n ≠ scalarFiber r := by
  constructor
  · simp [Soma.Holonics.FaceEq, repeatedRootFiber, scalarFiber, trace, determinant]
  · exact repeatedRoot_nonScalar hn

theorem linearReceiver_cayleyHamilton
    (L : Matrix2 → ℤ)
    (hadd : ∀ A B, L (add A B) = L A + L B)
    (hscale : ∀ q A, L (scale q A) = q * L A)
    (hzero : L zero = 0)
    (M : Matrix2) :
    L (mul M M) + (-trace M) * L M + determinant M * L identity = 0 := by
  have h := congrArg L (cayleyHamilton M)
  rw [hadd, hadd, hscale, hscale, hzero] at h
  exact h

/- FORMAL PLAYGROUND: replace the reference with a direct `ring` proof, then change one coordinate. -/
example (M : Matrix2) :
    discriminant M = xCoord M ^ 2 + yCoord M ^ 2 - zCoord M ^ 2 := by
  exact discriminant_quadric_coordinates M

/- FORMAL PLAYGROUND: unfold the tangent and observe which terms cancel in each receiver. -/
example (X M : Matrix2) :
    trace (commutatorTangent X M) = 0 ∧
      determinantDifferential M (commutatorTangent X M) = 0 := by
  exact ⟨trace_commutatorTangent X M, determinantDifferential_commutatorTangent X M⟩

/- FORMAL PLAYGROUND: replace `trace` with another additive homogeneous receiver. -/
example (M : Matrix2) :
    trace (mul M M) + (-trace M) * trace M + determinant M * trace identity = 0 := by
  apply linearReceiver_cayleyHamilton trace
  · intro A B
    simp [trace, add]
    ring
  · intro q A
    simp [trace, scale]
    ring
  · rfl

#check discriminant_quadric_coordinates
#check determinantDifferential_commutatorTangent
#check repeatedRoot_receiverFiber
#check linearReceiver_cayleyHamilton

end HolonicsNotebook.U001
