import Holonics.HNN.FiniteDecrease

/-!
# HNN.PairedDeposit: the pair-port reversal law and the equivariant deposit

[definition; agent-inferred, October 9] The helical code's step 3 (#386; the helical record §5, "Not
built: an equivariant deposition"). A paired carrier's source port `E` carries the pairing when
`B E = E Σ`: `B` is the lift of the source ring's reflector (`B² = 1`, and `B P = Q B` with `Q` the
reversed transport, `Q = P⁻¹` on a ring at modulus one), and `Σ` permutes the letters by the
fixed-point-free involution `σ` (`hnn::paired::{PairedCarrier, Sigma}`).

A located pair `y → x` at distance `δ` deposits its slip `Δ = Pᵟ E₀ y − (E − E₀) x`
(`hnn::executed::pair_slip`). Its dyad image is the pair read against the clock on the antiparallel
partner strand: `Qᵟ E₀ (Σ y) − (E − E₀) (Σ x)`, the **pair-port reversal law**.

1. **The lift reverses the transport** (`lift_pow`): `B P = Q B` gives `B Pᵏ = Qᵏ B`.
2. **The reversal identity** (`reversal_identity`): with an equivariant prior and port, the lift of a
   pair's slip is the slip of its dyad image read through the reversed transport. The reversed slip
   is read by its own law; this identity is the check that relates the two.
3. **The deposit stays equivariant** (`mul_commuting_stays`, `deposit_stays_equivariant`): when the
   deposit's aggregate covector `G` is equivariant (`B G = G Σ`, which holds when each pair enters
   with its reversed partner) and the chart `X` commutes with `Σ`, the step `E + η G X` keeps
   `B E = E Σ`.
4. **The symmetrized chart commutes** (`symmetrized_commutes`): with `Σ² = 1`, `X + Σ X Σ` commutes
   with `Σ`, so `½(X + Σ X Σ)` is a chart the deposit can use. (That it keeps the chart's certified
   bound `‖1 − X H‖ ≤ δ` whenever `Σ H = H Σ`, for a norm invariant under permutation similarity, is
   proved-derived in the design and owed here.)

[proved-derived] Written, not yet kernel-checked; the sole queue's owner check decides. No `sorry`,
no `axiom`, no `native_decide`.

| Lean | Rust (owed, loop 2 of step 3) |
|---|---|
| `lift_pow` | `hnn::paired::PairedCarrier::lift` against the ring's transport |
| `reversal_identity` | the reversed located pair beside `hnn::executed::pair_slip` |
| `mul_commuting_stays`, `deposit_stays_equivariant` | the paired deposit through `Constitution::stepped_source` |
| `symmetrized_commutes` | the symmetrized chart in `NormalLaw::prepare` |
-/

namespace Holonics.HNN.PairedDeposit

variable {R : Type*} [CommRing R] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m]

/-- [proved-derived] **The lift reverses the transport**: `B P = Q B` gives `B Pᵏ = Qᵏ B`. -/
theorem lift_pow {B P Q : Matrix n n R} (h : B * P = Q * B) : ∀ k : ℕ, B * P ^ k = Q ^ k * B
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ P k, ← Matrix.mul_assoc B (P ^ k) P, lift_pow h k, Matrix.mul_assoc (Q ^ k) B P,
      h, ← Matrix.mul_assoc (Q ^ k) Q B, ← pow_succ Q k]

/-- [proved-derived] **The pair-port reversal law.** With an equivariant prior and port
(`B E₀ = E₀ Σ`, `B E = E Σ`) and the lift reversing the transport (`B P = Q B`), the lift of a
pair's slip `Pᵟ E₀ y − (E − E₀) x` is the slip of its dyad image read through the reversed
transport, `Qᵟ E₀ (Σ y) − (E − E₀) (Σ x)`. -/
theorem reversal_identity {B P Q : Matrix n n R} {S : Matrix m m R} {E E₀ : Matrix n m R}
    (hP : B * P = Q * B) (h₀ : B * E₀ = E₀ * S) (hE : B * E = E * S) (δ : ℕ) (y x : m → R) :
    B.mulVec ((P ^ δ * E₀).mulVec y - (E - E₀).mulVec x) =
      (Q ^ δ * E₀).mulVec (S.mulVec y) - (E - E₀).mulVec (S.mulVec x) := by
  have hA : B * (P ^ δ * E₀) = Q ^ δ * E₀ * S := by
    rw [← Matrix.mul_assoc B (P ^ δ) E₀, lift_pow hP δ, Matrix.mul_assoc (Q ^ δ) B E₀, h₀,
      ← Matrix.mul_assoc (Q ^ δ) E₀ S]
  have hM : B * (E - E₀) = (E - E₀) * S := by
    rw [Matrix.mul_sub, hE, h₀, Matrix.sub_mul]
  have h₁ : B.mulVec ((P ^ δ * E₀).mulVec y) = (Q ^ δ * E₀).mulVec (S.mulVec y) := by
    simp only [Matrix.mulVec_mulVec, hA]
  have h₂ : B.mulVec ((E - E₀).mulVec x) = (E - E₀).mulVec (S.mulVec x) := by
    simp only [Matrix.mulVec_mulVec, hM]
  rw [Matrix.mulVec_sub, h₁, h₂]

/-- [proved-derived] **An equivariant covector stays equivariant through a commuting chart**:
`B G = G Σ` and `X Σ = Σ X` give `B (G X) = (G X) Σ`. -/
theorem mul_commuting_stays {B : Matrix n n R} {S X : Matrix m m R} {G : Matrix n m R}
    (hG : B * G = G * S) (hX : X * S = S * X) : B * (G * X) = G * X * S := by
  rw [← Matrix.mul_assoc B G X, hG, Matrix.mul_assoc G S X, ← hX, ← Matrix.mul_assoc G X S]

/-- [proved-derived] **The deposit stays equivariant**: with `B E = E Σ`, an equivariant aggregate
covector `B G = G Σ` and a chart commuting with `Σ`, the step `E + η G X` keeps the pairing. -/
theorem deposit_stays_equivariant {B : Matrix n n R} {S X : Matrix m m R} {E G : Matrix n m R}
    (η : R) (hE : B * E = E * S) (hG : B * G = G * S) (hX : X * S = S * X) :
    B * (E + η • (G * X)) = (E + η • (G * X)) * S := by
  rw [Matrix.mul_add, Matrix.mul_smul, mul_commuting_stays hG hX, hE, Matrix.add_mul,
    Matrix.smul_mul]

/-- [proved-derived] **The symmetrized chart commutes with the pairing**: with `Σ² = 1`,
`(X + Σ X Σ) Σ = Σ (X + Σ X Σ)`. -/
theorem symmetrized_commutes {S X : Matrix m m R} (hS : S * S = 1) :
    (X + S * X * S) * S = S * (X + S * X * S) := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc (S * X) S S, hS, Matrix.mul_one,
    ← Matrix.mul_assoc S (S * X) S, ← Matrix.mul_assoc S S X, hS, Matrix.one_mul, add_comm]

end Holonics.HNN.PairedDeposit
