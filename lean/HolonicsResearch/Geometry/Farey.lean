import HolonicsResearch.Mathematics.Towers
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The word is a matrix product, and the group is the modular one

The convergent determinant identity was proved in `Towers` by integer induction.  Here it is proved
again, and the second proof says where it comes from:

```text
!![h_{n+1}, h_n ; k_{n+1}, k_n]  =  ∏_{i≤n+1} !![a_i, 1 ; 1, 0]
det (∏ step)  =  ∏ det step  =  (−1)^{n+1}
```

**The continued-fraction recurrence is a matrix product in `GL₂(ℤ)`, and the alternating sign is the
multiplicativity of the determinant along the word.**  So the "arithmetic pathway between landmarks"
is literally a word in a group, and where it lands is the product.

That group is the modular one.  `L = !![1,0;1,1]` and `R = !![1,1;0,1]` are unimodular and generate
the Stern–Brocot tree; the step matrix `!![t,1;1,0]` is `R^t` composed with the exchange
`!![0,1;1,0]`, whose determinant is `−1` — **the exchange is the swing**, and it is what makes the
word alternate.  And two fractions are Farey neighbours exactly when `hk' − h'k = ±1`, i.e. exactly
when their matrix is unimodular.  Their Ford circles (radius `1/(2k²)` standing at `h/k`) stand apart by
`dx² − 4r₁r₂ = ((hK − Hk)² − 1)/(kK)²` (`ford_separation`), so two Ford circles touch exactly at a
unit determinant (`ford_tangent_iff_unimodular`): the Farey lock and the tangent packing are one
condition.

`GL₂(ℤ)` acts on the upper half plane by Möbius transformations, which **preserve the cross ratio**.
So the chain closes: the sign word's modulus, the convergents, the Farey tree, the modular group, and
the cross-ratio swing are one object seen at five grains.

The Gauss map `G(x) = 1/x − ⌊1/x⌋` is the shift on these words, and its transfer operator has kernel
`Σ_{n≥1}(n+x)^{−2β}`, which at the endpoint is `ζ(2β)` — the same `ζ(2s)` that carries the squarefree
correction.  **That identification is stated and not proved here**; the Knauf spin chain whose
partition function is `ζ(β−1)/ζ(β)` is not built.

Every `theorem` here is discharged and none depends on `sorryAx`.
-/

namespace Holonics.Geometry.Farey

open Matrix Holonics.Mathematics.Towers

variable (a : ℕ → ℤ)

/-- One partial quotient as a matrix. -/
def cfMatrix (t : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![t, 1; 1, 0]

theorem theStepMatrixHasDeterminantMinusOne (t : ℤ) : (cfMatrix t).det = -1 := by
  simp [cfMatrix, Matrix.det_fin_two]

/-- The product of the first `n+1` step matrices. -/
def cfProd : ℕ → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => cfMatrix (a 0)
  | (n + 1) => cfProd n * cfMatrix (a (n + 1))

/-- **The product carries the convergents.**  Its columns are two consecutive convergents, so the
continued-fraction recurrence *is* a matrix product in `GL₂(ℤ)`. -/
theorem theProductCarriesTheConvergents (n : ℕ) :
    cfProd a (n + 1) = !![hh a (n + 1), hh a n; kk a (n + 1), kk a n] := by
  induction n with
  | zero =>
    show cfProd a 0 * cfMatrix (a 1) = _
    simp only [cfProd, cfMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hh, kk] <;> ring
  | succ n ih =>
    show cfProd a (n + 1) * cfMatrix (a (n + 2)) = _
    rw [ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, cfMatrix,
        show hh a (n + 2) = a (n + 2) * hh a (n + 1) + hh a n from rfl,
        show kk a (n + 2) = a (n + 2) * kk a (n + 1) + kk a n from rfl] <;> ring

/-- **So the determinant identity is a product of determinants.**

`det (∏ step) = (−1)^{n+1}`, and the same determinant read off the convergents is
`h_{n+1}k_n − h_n k_{n+1}`.  The identity proved by induction in `Towers` is the multiplicativity of
the determinant along the word. -/
theorem theDeterminantIsTheProductAlongTheWord (n : ℕ) :
    (cfProd a n).det = (-1) ^ (n + 1) := by
  induction n with
  | zero => simpa [cfProd] using theStepMatrixHasDeterminantMinusOne (a 0)
  | succ n ih =>
    show (cfProd a n * cfMatrix (a (n + 1))).det = _
    rw [Matrix.det_mul, ih, theStepMatrixHasDeterminantMinusOne]
    ring

/-! ## The modular generators, and the word that is a continued fraction -/

/-- `L` and `R`, the Stern–Brocot generators. -/
def sbL : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, 1]
def sbR : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]

/-- **Both are in `SL₂(ℤ)`.** -/
theorem theGeneratorsAreUnimodular : sbL.det = 1 ∧ sbR.det = 1 := by
  constructor <;> simp [sbL, sbR, Matrix.det_fin_two]

/-- The natural power of the right Stern–Brocot generator. -/
def sbRPower : ℕ → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => 1
  | n + 1 => sbRPower n * sbR

/-- The exchange matrix used by a continued-fraction step. -/
def sbExchange : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

theorem sbRPower_eq (n : ℕ) : sbRPower n = !![1, (n : ℤ); 0, 1] := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sbRPower]
  | succ n ih =>
      rw [sbRPower, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sbR, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **A nonnegative step is a natural power followed by the exchange.**

The exponent is deliberately `ℕ`: no unsupported integer matrix-power notation is introduced. -/
theorem theNaturalStepIsAPowerTimesTheExchange (n : ℕ) :
    cfMatrix (n : ℤ) = sbRPower n * sbExchange := by
  rw [sbRPower_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cfMatrix, sbExchange, Matrix.mul_apply, Fin.sum_univ_two]

/-- The exchange has determinant `−1`. -/
theorem theStepExchangeHasDeterminantMinusOne : sbExchange.det = -1 := by
  simp [sbExchange, Matrix.det_fin_two]

/-- **Neighbouring Farey fractions and consecutive convergents satisfy one identity.**
`ad − bc = ±1` is `det ∈ {1,−1}`, which is exactly membership in `GL₂(ℤ)` — the modular group, whose
action on the upper half plane is by Möbius transformations, which preserve the cross ratio. -/
theorem theMediantConditionIsUnimodularity (h k h' k' : ℤ) :
    h * k' - h' * k = 1 ↔ (!![h, h'; k, k']).det = 1 := by
  simp [Matrix.det_fin_two]

/-! ## Ford circles: the separation is the determinant, and tangency is unimodularity -/

/-- [definition] The Ford radius over the denominator `k`, `1/(2k²)`; the circle stands on the
real axis at `h/k` with its centre at that height. -/
def fordRadius (k : ℤ) : ℚ := 1 / (2 * (k : ℚ) ^ 2)

/-- [proved-derived; formal-checked] **`ford_separation`.** For Ford circles at `h/k` and `H/K`,
`(h/k − H/K)² − 4 r₁ r₂ = ((hK − Hk)² − 1)/(kK)²`. -/
theorem ford_separation (h k H K : ℤ) (hk : k ≠ 0) (hK : K ≠ 0) :
    ((h : ℚ) / k - (H : ℚ) / K) ^ 2 - 4 * fordRadius k * fordRadius K =
      ((((h * K - H * k) ^ 2 : ℤ) : ℚ) - 1) / ((k : ℚ) * K) ^ 2 := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have hK' : (K : ℚ) ≠ 0 := by exact_mod_cast hK
  unfold fordRadius
  push_cast
  field_simp
  ring

/-- [proved-derived; formal-checked] **Ford circles are tangent exactly at a unit determinant.**
The circles of centres `(h/k, r₁)`, `(H/K, r₂)` and radii `r₁`, `r₂` touch
(`dx² + (r₁ − r₂)² = (r₁ + r₂)²`) exactly when `|hK − Hk| = 1`; that is, exactly when the pair is
unimodular in one of its two orders (`theMediantConditionIsUnimodularity`). -/
theorem ford_tangent_iff_unimodular (h k H K : ℤ) (hk : k ≠ 0) (hK : K ≠ 0) :
    (((h : ℚ) / k - (H : ℚ) / K) ^ 2 + (fordRadius k - fordRadius K) ^ 2 =
        (fordRadius k + fordRadius K) ^ 2 ↔ |h * K - H * k| = 1) ∧
      (|h * K - H * k| = 1 ↔ (!![h, H; k, K]).det = 1 ∨ (!![H, h; K, k]).det = 1) := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have hK' : (K : ℚ) ≠ 0 := by exact_mod_cast hK
  have hkK : ((k : ℚ) * K) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero hk' hK')
  have hsep := ford_separation h k H K hk hK
  have habs : |h * K - H * k| = 1 ↔ (h * K - H * k) ^ 2 = 1 := by
    rw [← sq_abs, pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [habs]
    constructor
    · intro htan
      have hzero : ((h : ℚ) / k - (H : ℚ) / K) ^ 2 - 4 * fordRadius k * fordRadius K = 0 := by
        linear_combination htan
      rw [hsep, div_eq_zero_iff, or_iff_left hkK, sub_eq_zero] at hzero
      exact_mod_cast hzero
    · intro hdet
      have hzero : ((h : ℚ) / k - (H : ℚ) / K) ^ 2 - 4 * fordRadius k * fordRadius K = 0 := by
        rw [hsep, hdet]
        norm_num
      linear_combination hzero
  · rw [← theMediantConditionIsUnimodularity, ← theMediantConditionIsUnimodularity, abs_eq
      zero_le_one]
    constructor
    · rintro (h1 | h1)
      · exact Or.inl h1
      · exact Or.inr (by linarith)
    · rintro (h1 | h1)
      · exact Or.inl h1
      · exact Or.inr (by linarith)


end Holonics.Geometry.Farey
