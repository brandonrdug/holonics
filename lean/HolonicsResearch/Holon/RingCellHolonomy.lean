import Holonics.Holon.Complex

/-!
# The ring cell's holonomy decides which turns a transported cycle carries

[definition] The **ring cell** of `d` vertices `ℤ/d`, each edge `x → x + 1`, with connection-valued
incidence (`Holon/Complex.connectionIncidence`, edge transports `g_x ∈ 𝕜ˣ`). Its covariant step
`P` reads the next vertex's value transported back along edge `x`, `(Pφ)(x) = g_x φ(x + 1)`
(`ringStep`), so the ring's incidence is `d_A = P − 1` (`connectionIncidence_eq_step_sub_one`).
The ring's **holonomy** is the transport around the cell, `hol = Π_x g_x` (`ringHolonomy`,
`ringHolonomy_eq_prod`, read from any base, `walkTransport_ringWalk_period`). It is the curvature
face of `d_A² = hol − 1` on this cell (`ring_cell_curvature`, an instance of
`Holon/Complex.cell_curvature`), and no gauge moves it (`ringHolonomy_regauge`, the ring's case of
`Transport/CellHolonomy.abelian_holonomy_is_gauge_free`): changing a ring's holonomy is a material
change. Every holonomy is realized by one seam (`seam_ringHolonomy`); the seam `−1` is the Möbius
ring, the orientation-reversing cycle of `Objects/Orientation.two_face_mobius_band`.

[proved-derived; formal-checked] What is proved (#359's cycle-order condition, in the corrected
form of #62).
1. **One turn of the ring is its holonomy**: `P^d = hol` (`ringStep_pow_period`).
2. **A transported cycle closes on the holonomy's power** (`pow_step_cycle`, in any monoid): with
   `g = gcd(δ, d)` and `N = d/g`, `P^d = h` gives `(P^δ)^N = h^(δ/g)`.
3. **The carried turns** (`ring_carries_iff`): the step `P^δ` carries the turn `μ` (some nonzero
   vertex field `φ` with `P^δ φ = μ φ`, `Carries`) exactly when `μ^N = hol^(δ/g)`. The field needs
   no root of `hol`: the carried field is the cycle's own sum `Σ_(i<N) μ^(N−1−i) P^(δi) δ₀`, which
   the step turns by `μ` because `(P^δ − μ)·Σ = (P^δ)^N − μ^N = hol^(δ/g) − μ^N`
   (`Commute.mul_geom_sum₂`), and which reads `μ^(N−1)` at vertex `0` since `d ∤ δ i` for
   `0 < i < N` (`not_dvd_step_mul`). The forward half holds for any operator with `Q^N = c`
   (`carries_pow_eq`).
4. **The flat ring** (`flat_ring_carries_iff`): at `hol = 1` a turn `ζ` is carried exactly when its
   order divides `N`, the cycle-order condition `k ∣ d/gcd(δ, d)`.
5. **The remainder is the holonomy** (`carries_iff_remainder`): when `δ ∣ d`, `ζ` is carried exactly
   when `hol = ζ^(N mod ord ζ)`.

[counterexample; formal-checked] **The order-2 ring** (`sixty_*`): `d = 60 = 2²·3·5`, `δ = 2`,
`g = 2`, `N = 30`, `ζ = i`. Every ring of holonomy `−1` carries `i` under `P²`
(`sixty_mobius_carries_i`), realized by the seam (`sixty_seam_carries_i`), while no flat ring
does (`sixty_flat_refuses_i`): `i^30 = −1`, so the flat cycle-order condition `4 ∣ 30` fails and
the half-turn holonomy supplies the remainder `i^(30 mod 4) = i² = −1`.
-/

noncomputable section

namespace Holonics.HolonCore.RingCell

open Holonics.HolonCore
open Matrix

/-! ## 1. The monoid law -/

/-- [proved-derived; formal-checked] **A transported cycle closes on the holonomy's power.** If one
turn of the ring is its holonomy, `P^d = h`, then the step `P^δ` repeated `N = d/gcd(δ, d)` times
closes on `h^(δ/gcd(δ, d))`: `δ N = d (δ/g)`. -/
theorem pow_step_cycle {M : Type*} [Monoid M] {P h : M} {d : ℕ} (hP : P ^ d = h) (δ : ℕ) :
    (P ^ δ) ^ (d / Nat.gcd δ d) = h ^ (δ / Nat.gcd δ d) := by
  rw [← pow_mul, ← hP, ← pow_mul, ← Nat.mul_div_assoc δ (Nat.gcd_dvd_right δ d),
    ← Nat.mul_div_assoc d (Nat.gcd_dvd_left δ d), mul_comm δ d]

/-- [proved-derived; formal-checked] Inside one cycle no partial step returns to its start:
`d ∤ δ i` for `0 < i < d/gcd(δ, d)`, because `d/g` and `δ/g` are coprime. -/
theorem not_dvd_step_mul {d δ i : ℕ} (hd : 0 < d) (hi0 : 0 < i) (hi : i < d / Nat.gcd δ d) :
    ¬ d ∣ δ * i := by
  intro hdvd
  have hq : 0 < Nat.gcd δ d := Nat.gcd_pos_of_pos_right δ hd
  have h1 : Nat.gcd δ d * (d / Nat.gcd δ d) ∣ Nat.gcd δ d * (δ / Nat.gcd δ d * i) := by
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right δ d), ← mul_assoc,
      Nat.mul_div_cancel' (Nat.gcd_dvd_left δ d)]
    exact hdvd
  have h2 : d / Nat.gcd δ d ∣ δ / Nat.gcd δ d * i := Nat.dvd_of_mul_dvd_mul_left hq h1
  have h3 : d / Nat.gcd δ d ∣ i :=
    (Nat.coprime_div_gcd_div_gcd hq).symm.dvd_of_dvd_mul_left h2
  exact absurd (Nat.le_of_dvd hi0 h3) (not_le.mpr hi)

/-! ## 2. The ring cell, its step and its holonomy -/

variable {𝕜 : Type*} [Field 𝕜] {d : ℕ}

/-- [definition] The ring walk from `x` along `n` consecutive edges `x, x + 1, …, x + n − 1`
(edge `e` runs from vertex `e` to vertex `e + 1`). -/
def ringWalk (x : ZMod d) : ℕ → List (ZMod d)
  | 0 => []
  | n + 1 => x :: ringWalk (x + 1) n

/-- [proved-derived; formal-checked] The ring walk is a walk of the ring's incidence. -/
theorem ringWalk_isWalk (x : ZMod d) (n : ℕ) :
    IsWalk (fun e : ZMod d => e) (fun e => e + 1) x (x + n) (ringWalk x n) := by
  induction n generalizing x with
  | zero => simp [ringWalk, IsWalk]
  | succ n ih =>
    refine ⟨rfl, ?_⟩
    have h : x + ((n + 1 : ℕ) : ZMod d) = x + 1 + n := by push_cast; ring
    rw [h]
    exact ih (x + 1)

/-- [definition] **The ring's covariant step** `P`: `(Pφ)(x) = g_x φ(x + 1)`, the next vertex's
value transported back along edge `x`. -/
def ringStep (g : ZMod d → 𝕜ˣ) : Module.End 𝕜 (ZMod d → 𝕜) where
  toFun φ x := (g x : 𝕜) * φ (x + 1)
  map_add' φ ψ := by funext x; simp only [Pi.add_apply, mul_add]
  map_smul' c φ := by
    funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem ringStep_apply (g : ZMod d → 𝕜ˣ) (φ : ZMod d → 𝕜) (x : ZMod d) :
    ringStep g φ x = (g x : 𝕜) * φ (x + 1) := rfl

/-- [proved-derived; formal-checked] **The ring's incidence is its step minus one**:
`d_A φ = Pφ − φ`, edge by edge (`connectionIncidence_mulVec`). -/
theorem connectionIncidence_eq_step_sub_one [NeZero d] (g : ZMod d → 𝕜ˣ) (φ : ZMod d → 𝕜) :
    connectionIncidence (fun e : ZMod d => e) (fun e => e + 1) g *ᵥ φ = ringStep g φ - φ := by
  funext e
  rw [connectionIncidence_mulVec]
  simp

/-- [definition] **The ring's holonomy**: the transport around the cell from vertex `0`. -/
def ringHolonomy (g : ZMod d → 𝕜ˣ) : 𝕜 := walkTransport g (ringWalk 0 d)

/-- [proved-derived; formal-checked] The transport along `n` ring edges is the product of their
transports. -/
theorem walkTransport_ringWalk (g : ZMod d → 𝕜ˣ) (x : ZMod d) (n : ℕ) :
    walkTransport g (ringWalk x n) = ∏ k ∈ Finset.range n, (g (x + k) : 𝕜) := by
  induction n generalizing x with
  | zero => simp [ringWalk, walkTransport]
  | succ n ih =>
    rw [ringWalk, walkTransport, ih, Finset.prod_range_succ', Nat.cast_zero, add_zero, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [show x + 1 + (k : ZMod d) = x + ((k + 1 : ℕ) : ZMod d) by push_cast; ring]

/-- [proved-derived; formal-checked] `d` consecutive edges from any vertex visit every edge once. -/
theorem prod_range_shift [NeZero d] {M : Type*} [CommMonoid M] (f : ZMod d → M) (x : ZMod d) :
    ∏ k ∈ Finset.range d, f (x + k) = ∏ y, f y := by
  rw [Finset.prod_range]
  refine Fintype.prod_bijective (fun i : Fin d => x + ((i : ℕ) : ZMod d)) ?_ _ _ (fun _ => rfl)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun i j hij => ?_, by simp [ZMod.card]⟩
  have h : ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) := add_left_cancel hij
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at h
  exact Fin.ext h

/-- [proved-derived; formal-checked] **The holonomy is the product of every edge's transport**,
`hol = Π_x g_x` (the triangle's `CellHolonomy.triangleHolonomy` is the case `d = 3`). -/
theorem ringHolonomy_eq_prod [NeZero d] (g : ZMod d → 𝕜ˣ) : ringHolonomy g = ∏ y, (g y : 𝕜) := by
  rw [ringHolonomy, walkTransport_ringWalk, prod_range_shift (fun y => (g y : 𝕜)) 0]

/-- [proved-derived; formal-checked] One turn from any base reads the same holonomy. -/
theorem walkTransport_ringWalk_period [NeZero d] (g : ZMod d → 𝕜ˣ) (x : ZMod d) :
    walkTransport g (ringWalk x d) = ringHolonomy g := by
  rw [walkTransport_ringWalk, prod_range_shift (fun y => (g y : 𝕜)) x, ringHolonomy_eq_prod]

/-- [proved-derived; formal-checked] **`d_A² = hol − 1` on the ring cell**: the covariant face
reading of an exact effort around the ring is `(hol − 1) φ(0)` (`Holon/Complex.cell_curvature`). -/
theorem ring_cell_curvature [NeZero d] (g : ZMod d → 𝕜ˣ) (φ : ZMod d → 𝕜) :
    walkRead g (connectionIncidence (fun e : ZMod d => e) (fun e => e + 1) g *ᵥ φ)
        (ringWalk 0 d) = (ringHolonomy g - 1) * φ 0 := by
  have hw := ringWalk_isWalk (0 : ZMod d) d
  rw [ZMod.natCast_self, add_zero] at hw
  exact cell_curvature _ _ g φ _ 0 hw

/-- [proved-derived; formal-checked] **No gauge moves the ring's holonomy**: regauging every edge
`g_x ↦ k_x⁻¹ g_x k_(x+1)` (`CellHolonomy.regauge`) leaves `hol` fixed. -/
theorem ringHolonomy_regauge [NeZero d] (g k : ZMod d → 𝕜ˣ) :
    ringHolonomy (fun x => (k x)⁻¹ * g x * k (x + 1)) = ringHolonomy g := by
  have key : ∏ x, ((k x)⁻¹ * g x * k (x + 1)) = ∏ x, g x := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
      Fintype.prod_equiv (Equiv.addRight (1 : ZMod d)) (fun x => k (x + 1)) k (fun _ => rfl),
      mul_right_comm, inv_mul_cancel, one_mul]
  rw [ringHolonomy_eq_prod, ringHolonomy_eq_prod, ← Units.coe_prod, ← Units.coe_prod, key]

/-- [definition] **The seam**: every edge transports by `1` except edge `0`, which carries `c`. -/
def seam [NeZero d] (c : 𝕜ˣ) : ZMod d → 𝕜ˣ := Function.update 1 0 c

/-- [proved-derived; formal-checked] Every holonomy is realized by one seam. -/
theorem seam_ringHolonomy [NeZero d] (c : 𝕜ˣ) : ringHolonomy (seam (d := d) c) = c := by
  rw [ringHolonomy_eq_prod, ← Units.coe_prod, seam,
    Finset.prod_update_of_mem (Finset.mem_univ 0)]
  simp

/-! ## 3. One turn is the holonomy, and the carried turns -/

/-- [proved-derived; formal-checked] `n` steps read the value `n` vertices on, transported back
along the walk: `(P^n φ)(x) = T_(x,n) φ(x + n)`. -/
theorem ringStep_pow_apply (g : ZMod d → 𝕜ˣ) (n : ℕ) (φ : ZMod d → 𝕜) (x : ZMod d) :
    (ringStep g ^ n) φ x = walkTransport g (ringWalk x n) * φ (x + n) := by
  induction n generalizing x with
  | zero => simp [ringWalk, walkTransport]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ringStep_apply, ih, ringWalk, walkTransport, mul_assoc]
    rw [show x + 1 + (n : ZMod d) = x + ((n + 1 : ℕ) : ZMod d) by push_cast; ring]

/-- [proved-derived; formal-checked] **One turn of the ring is its holonomy**: `P^d = hol`. -/
theorem ringStep_pow_period [NeZero d] (g : ZMod d → 𝕜ˣ) :
    ringStep g ^ d = algebraMap 𝕜 (Module.End 𝕜 (ZMod d → 𝕜)) (ringHolonomy g) := by
  refine LinearMap.ext fun φ => funext fun x => ?_
  rw [ringStep_pow_apply, walkTransport_ringWalk_period, ZMod.natCast_self, add_zero,
    Module.algebraMap_end_apply, Pi.smul_apply, smul_eq_mul]

/-- [definition] An operator `Q` on the vertex fields **carries the turn** `μ` when some nonzero
field is turned by it: `Q φ = μ φ`. -/
def Carries {V : Type*} [AddCommGroup V] [Module 𝕜 V] (Q : Module.End 𝕜 V) (μ : 𝕜) : Prop :=
  ∃ φ : V, φ ≠ 0 ∧ Q φ = μ • φ

/-- [proved-derived; formal-checked] **A carried turn closes with its operator's cycle**: if
`Q^N = c` then every turn `Q` carries satisfies `μ^N = c`. -/
theorem carries_pow_eq {V : Type*} [AddCommGroup V] [Module 𝕜 V] {Q : Module.End 𝕜 V} {μ c : 𝕜}
    {N : ℕ} (hQ : Q ^ N = algebraMap 𝕜 (Module.End 𝕜 V) c) (h : Carries Q μ) : μ ^ N = c := by
  obtain ⟨φ, hφ, hμ⟩ := h
  have hpow : ∀ n : ℕ, (Q ^ n) φ = μ ^ n • φ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hμ, smul_smul, ← pow_succ]
  have h := hpow N
  rw [hQ, Module.algebraMap_end_apply] at h
  exact smul_left_injective 𝕜 hφ h.symm

/-- [proved-derived; formal-checked] One term of the cycle's sum, read at vertex `0`. -/
theorem cycle_term_apply (g : ZMod d → 𝕜ˣ) (δ i k : ℕ) (μ : 𝕜) :
    ((ringStep g ^ δ) ^ i * algebraMap 𝕜 (Module.End 𝕜 (ZMod d → 𝕜)) μ ^ k)
        (Pi.single 0 1) 0 =
      μ ^ k * (walkTransport g (ringWalk 0 (δ * i)) *
        (Pi.single (0 : ZMod d) (1 : 𝕜) : ZMod d → 𝕜) ((δ * i : ℕ) : ZMod d)) := by
  rw [Module.End.mul_apply, ← map_pow, Module.algebraMap_end_apply, map_smul, ← pow_mul,
    Pi.smul_apply, ringStep_pow_apply, zero_add, smul_eq_mul]

/-- [proved-derived; formal-checked] **The cycle's sum is carried.** If `μ^N = hol^(δ/g)`, the
field `Σ_(i<N) μ^(N−1−i) P^(δi) δ₀` is nonzero and `P^δ` turns it by `μ`. -/
theorem ring_carries_of_pow_eq [NeZero d] (g : ZMod d → 𝕜ˣ) (δ : ℕ) {μ : 𝕜}
    (hμ : μ ^ (d / Nat.gcd δ d) = ringHolonomy g ^ (δ / Nat.gcd δ d)) :
    Carries (ringStep g ^ δ) μ := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hN : 0 < d / Nat.gcd δ d :=
    Nat.div_pos (Nat.gcd_le_right δ hd) (Nat.gcd_pos_of_pos_right δ hd)
  have hcomm : Commute (ringStep g ^ δ) (algebraMap 𝕜 (Module.End 𝕜 (ZMod d → 𝕜)) μ) :=
    (Algebra.commutes μ _).symm
  have hQN : (ringStep g ^ δ) ^ (d / Nat.gcd δ d) =
      (algebraMap 𝕜 (Module.End 𝕜 (ZMod d → 𝕜)) μ) ^ (d / Nat.gcd δ d) := by
    rw [pow_step_cycle (ringStep_pow_period g) δ, ← map_pow, ← map_pow, hμ]
  have hkill := hcomm.mul_geom_sum₂ (d / Nat.gcd δ d)
  rw [hQN, sub_self] at hkill
  refine ⟨(∑ i ∈ Finset.range (d / Nat.gcd δ d), (ringStep g ^ δ) ^ i *
      (algebraMap 𝕜 (Module.End 𝕜 (ZMod d → 𝕜)) μ) ^ (d / Nat.gcd δ d - 1 - i))
      (Pi.single 0 1), ?_, ?_⟩
  · intro h0
    have hv := congrFun h0 0
    rw [LinearMap.sum_apply, Finset.sum_apply, Finset.sum_eq_single 0] at hv
    · rw [cycle_term_apply] at hv
      simp only [mul_zero, Nat.cast_zero, Pi.single_eq_same, ringWalk, walkTransport, mul_one,
        Nat.sub_zero, Pi.zero_apply] at hv
      have hhol : ringHolonomy g ≠ 0 := by
        rw [ringHolonomy_eq_prod]
        exact Finset.prod_ne_zero_iff.mpr fun y _ => (g y).ne_zero
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        rw [zero_pow hN.ne'] at hμ
        exact pow_ne_zero _ hhol hμ.symm
      exact pow_ne_zero _ hμ0 hv
    · intro i hi hi0
      rw [cycle_term_apply, Pi.single_eq_of_ne, mul_zero, mul_zero]
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact not_dvd_step_mul hd (Nat.pos_of_ne_zero hi0) (Finset.mem_range.mp hi)
    · intro h; exact absurd (Finset.mem_range.mpr hN) h
  · have h := congrArg (fun T : Module.End 𝕜 (ZMod d → 𝕜) => T (Pi.single 0 1)) hkill
    simp only [sub_mul, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
    rw [sub_eq_zero] at h
    rw [h, Module.algebraMap_end_apply]

/-- [proved-derived; formal-checked] **The carried turns of a transported cycle.** On the ring cell
of holonomy `hol`, the step `P^δ` carries the turn `μ` exactly when `μ^N = hol^(δ/g)`, with
`g = gcd(δ, d)` and `N = d/g`. -/
theorem ring_carries_iff [NeZero d] (g : ZMod d → 𝕜ˣ) (δ : ℕ) (μ : 𝕜) :
    Carries (ringStep g ^ δ) μ ↔
      μ ^ (d / Nat.gcd δ d) = ringHolonomy g ^ (δ / Nat.gcd δ d) := by
  constructor
  · exact carries_pow_eq (by rw [pow_step_cycle (ringStep_pow_period g) δ, map_pow])
  · exact ring_carries_of_pow_eq g δ

/-- [proved-derived; formal-checked] **The flat ring's cycle-order condition**: at holonomy `1`,
a turn `ζ` is carried by `P^δ` exactly when its order divides `d/gcd(δ, d)`. -/
theorem flat_ring_carries_iff [NeZero d] (g : ZMod d → 𝕜ˣ) (hflat : ringHolonomy g = 1) (δ : ℕ) (ζ : 𝕜) :
    Carries (ringStep g ^ δ) ζ ↔ orderOf ζ ∣ d / Nat.gcd δ d := by
  rw [ring_carries_iff, hflat, one_pow, orderOf_dvd_iff_pow_eq_one]

/-- [proved-derived; formal-checked] **The remainder is the holonomy**: when `δ ∣ d` (so
`δ/g = 1`), `ζ` is carried by `P^δ` exactly when `hol = ζ^(N mod ord ζ)`. -/
theorem carries_iff_remainder [NeZero d] (g : ZMod d → 𝕜ˣ) {δ : ℕ} (hδ0 : 0 < δ) (hδ : δ ∣ d) (ζ : 𝕜) :
    Carries (ringStep g ^ δ) ζ ↔ ringHolonomy g = ζ ^ ((d / δ) % orderOf ζ) := by
  rw [ring_carries_iff, Nat.gcd_eq_left hδ, Nat.div_self hδ0, pow_one, pow_mod_orderOf, eq_comm]

/-! ## 4. The order-2 ring: `d = 60`, `δ = 2`, `ζ = i` -/

theorem sixty_cycle : Nat.gcd 2 60 = 2 ∧ 60 / Nat.gcd 2 60 = 30 ∧ 2 / Nat.gcd 2 60 = 1 := by
  decide

theorem I_pow_thirty : Complex.I ^ 30 = -1 := by
  rw [show (30 : ℕ) = 2 * 15 by norm_num, pow_mul, Complex.I_sq]
  norm_num

/-- [counterexample; formal-checked] **Every Möbius ring of sixty carries `i` under two steps**:
`i^30 = −1 = hol^1`. -/
theorem sixty_mobius_carries_i (g : ZMod 60 → ℂˣ) (hg : ringHolonomy g = -1) :
    Carries (ringStep g ^ 2) Complex.I := by
  rw [ring_carries_iff, hg, sixty_cycle.1]
  norm_num [I_pow_thirty]

/-- [counterexample; formal-checked] **No flat ring of sixty carries `i` under two steps**:
`i^30 = −1 ≠ 1`, the order `4` does not divide `30`. -/
theorem sixty_flat_refuses_i (g : ZMod 60 → ℂˣ) (hg : ringHolonomy g = 1) :
    ¬ Carries (ringStep g ^ 2) Complex.I := by
  rw [ring_carries_iff, hg, sixty_cycle.1]
  norm_num [I_pow_thirty]

/-- [counterexample; formal-checked] The Möbius ring of sixty exists: one seam of `−1`. -/
theorem sixty_seam_carries_i : Carries (ringStep (seam (d := 60) (-1 : ℂˣ)) ^ 2) Complex.I :=
  sixty_mobius_carries_i _ (by rw [seam_ringHolonomy]; simp)

section Audit

#print axioms pow_step_cycle
#print axioms connectionIncidence_eq_step_sub_one
#print axioms ringHolonomy_eq_prod
#print axioms ring_cell_curvature
#print axioms ringHolonomy_regauge
#print axioms seam_ringHolonomy
#print axioms ringStep_pow_period
#print axioms carries_pow_eq
#print axioms ring_carries_iff
#print axioms flat_ring_carries_iff
#print axioms carries_iff_remainder
#print axioms sixty_mobius_carries_i
#print axioms sixty_flat_refuses_i
#print axioms sixty_seam_carries_i

end Audit

end Holonics.HolonCore.RingCell
