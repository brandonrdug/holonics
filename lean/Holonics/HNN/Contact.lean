import Holonics.HNN.Ring
import Holonics.Compression.Landmark.SiteKind
import Holonics.Aeon.Clock.Lock

/-!
# HNN.Contact: the contact's transfer, its site kind, its signed storage and its lock

[definition] Rebuild step 4 (#73), campaign 2, Lean item 8 (`docs/plans/THE_REBUILD.md`, (b) and
"Campaign 2", *The contact's site kind*, *Boosts*, *Locks and clocks*). A contact slips, dissipates
and addresses. Its own transfer, with its channel waves held at zero, is the transit of
`HNN/Propagation` on its state `(u, w)` (displacement, slip rate): for one channel direction with
storage `c`, stiffness `k`, dissipation `d` and port term `p` (`2h/G` for the two-port, `0` closed)

```text
m = 2c + p + h d + (h²/2) k ,     m ω = 2c w − h k u ,    u′ = u + hω ,  w′ = 2ω − w
T = (1/m) [[m − h²k, 2hc], [−2hk, 4c − m]] ,   tr T = (4c − h²k)/m ,   det T = (2c + h²k/2 − p − hd)/m
```

[proved-derived; formal-checked] What is proved.

1. **The transfer and its faces** (`transfer_solves`, `transfer_trace_det`,
   `transitOperator_scalar`): the transit's scalar operator is `m` (`HNN/Propagation.transitOperator`
   on `ℝ`), the transfer carries `(u, w)` to the transit's `(u′, w′)`, and its trace and determinant
   are the formulas above. A damped or port-loaded transfer is classified by these, its own faces
   (`Compression/Landmark/SiteKind.siteKind`).
2. **The site kind by the sign of the stiffness** (`contact_transfer_kind_by_storage_sign`): for the
   lossless closed transfer (`p = d = 0`) with `c > 0`, `h ≠ 0` and a nonsingular Cayley chart
   (`4c + h²k ≠ 0`), `det T = 1`, and `k > 0`, `k = 0`, `k < 0` give exactly a rotation, a
   nonidentity null shear (`T = [[1, h], [0, 1]]`) and a boost
   (`SiteKind.siteKind_eq_{rotation,null,boost}_iff`). On a contact of several directions, a
   generalized mode `K v = λ C v` spans a plane the closed transit keeps, on which it acts as the
   scalar transfer at `(c, k) = (1, λ)` (`contact_mode_transfer`): its kind is the sign of `λ`.
3. **Boosts need a certified solve** (`contact_boost_solve_or_singular_direction`): a contact's
   operator either solves every right side uniquely or has a singular direction `v ≠ 0`,
   `M_a v = 0`; the solve is certified for every conductance `G > 0` when the signed form
   `2C + hD + (h²/2) K` is positive semidefinite, whatever the sign of `K`. This replaces
   `HNN/Propagation.tick_well_defined`'s `K ⪰ 0` for a boost.
4. **The signed-storage balance** (`contact_signed_storage_balance`): the transit's balance
   (`HNN/Propagation.transit_balance`) needs only symmetric `C`, `K`, so it holds exactly for an
   indefinite stiffness; passivity does not follow: the closed boost at `c = 1`, `k = −1`, `h = 1`
   triples the state `(1, 1)` every tick while its signed storage `½w² − ½u²` stays `0`
   (`boost_grows_at_conserved_signed_storage`).
5. **The lock address from the measured winding pair** (`contact_lock_address`): whole windings
   `(m_g, m_h)`, `m_h > 0`, reduce to the coprime address `p/q` with `m_g = p·gcd`, `m_h = q·gcd`; the
   measured passage reads `(m_g, m_h)` and is a cycle of the two clocks at `p/q`, whose cycles are
   exactly the multiples of `q` (`Aeon/Clock/Lock.{lock_at_address, cycle_iff_period_dvd}`).

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.Contact

open Matrix
open Holonics.HNN.Propagation
open Holonics.Compression.Landmark.SiteKind

/-! ## 1. The scalar transfer, its faces and its kind -/

section Transfer

/-- [definition] The transit's scalar operator `m = 2c + p + h d + (h²/2) k`, with the port term
`p` (`2h/G` for the contact's two ports, `0` closed). -/
def transferDen (c k d p h : ℝ) : ℝ := 2 * c + p + h * d + h ^ 2 / 2 * k

/-- [definition] **The contact's transfer** on `(u, w)`. -/
def transfer (c k d p h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (transferDen c k d p h)⁻¹ •
    !![transferDen c k d p h - h ^ 2 * k, 2 * h * c; -(2 * h * k), 4 * c - transferDen c k d p h]

/-- [proved-derived; formal-checked] On `ℝ` the transit's operator at scalar forms is `m`:
`2c + (2h/G) + h d + (h²/2) k` times the identity. -/
theorem transitOperator_scalar (c k d G h : ℝ) :
    transitOperator (c • ContinuousLinearMap.id ℝ ℝ) (d • ContinuousLinearMap.id ℝ ℝ)
        (k • ContinuousLinearMap.id ℝ ℝ) G h =
      transferDen c k d (2 * h / G) h • ContinuousLinearMap.id ℝ ℝ := by
  ext
  simp only [transitOperator, transferDen, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  ring

/-- [proved-derived; formal-checked] **The transfer is the transit.** With the channel waves at zero,
the scalar solve `m ω = 2c w − h k u` carries `(u, w)` to `(u + hω, 2ω − w) = T (u, w)`. -/
theorem transfer_solves {c k d p h u w ω : ℝ} (hm : transferDen c k d p h ≠ 0)
    (hsolve : transferDen c k d p h * ω = 2 * c * w - h * k * u) :
    transfer c k d p h *ᵥ ![u, w] = ![u + h * ω, 2 * ω - w] := by
  have hω : ω = (2 * c * w - h * k * u) / transferDen c k d p h := by
    field_simp; linarith
  ext i
  fin_cases i <;>
    simp [transfer, mulVec, dotProduct, Fin.sum_univ_two, hω] <;> field_simp <;> ring

/-- [proved-derived; formal-checked] **The transfer's faces**: `tr T = (4c − h²k)/m` and
`det T = (2c + h²k/2 − p − hd)/m`. -/
theorem transfer_trace_det {c k d p h : ℝ} (hm : transferDen c k d p h ≠ 0) :
    (transfer c k d p h).trace = (4 * c - h ^ 2 * k) / transferDen c k d p h ∧
      (transfer c k d p h).det =
        (2 * c + h ^ 2 / 2 * k - p - h * d) / transferDen c k d p h := by
  constructor
  · simp [transfer, trace_fin_two]
    field_simp
    ring
  · rw [transfer, det_smul, det_fin_two_of]
    simp only [Fintype.card_fin]
    field_simp
    unfold transferDen
    ring

/-- [proved-derived; formal-checked] **The contact's site kind by the sign of its stiffness.** For
the lossless closed transfer with `c > 0`, `h ≠ 0` and a nonsingular Cayley chart
(`4c + h²k ≠ 0`): `det T = 1`, and `T` is a rotation exactly when `k > 0`, a null site exactly when
`k = 0` (then the nonidentity shear `[[1, h], [0, 1]]`), and a boost exactly when `k < 0`. -/
theorem contact_transfer_kind_by_storage_sign {c k h : ℝ} (hc : 0 < c) (hh : h ≠ 0)
    (hm : 4 * c + h ^ 2 * k ≠ 0) :
    (transfer c k 0 0 h).det = 1 ∧
      (siteKind (transfer c k 0 0 h).trace (transfer c k 0 0 h).det = .rotation ↔ 0 < k) ∧
      (siteKind (transfer c k 0 0 h).trace (transfer c k 0 0 h).det = .null ↔ k = 0) ∧
      (siteKind (transfer c k 0 0 h).trace (transfer c k 0 0 h).det = .boost ↔ k < 0) ∧
      (k = 0 → transfer c k 0 0 h = !![1, h; 0, 1] ∧ transfer c k 0 0 h ≠ 1) := by
  have hden : transferDen c k 0 0 h = (4 * c + h ^ 2 * k) / 2 := by
    unfold transferDen; ring
  have hm' : transferDen c k 0 0 h ≠ 0 := by rw [hden]; exact div_ne_zero hm two_ne_zero
  obtain ⟨htr, hdet⟩ := transfer_trace_det (c := c) (k := k) (d := 0) (p := 0) (h := h) hm'
  have hdet1 : (transfer c k 0 0 h).det = 1 := by
    rw [hdet, div_eq_one_iff_eq hm']; unfold transferDen; ring
  have htr' : (transfer c k 0 0 h).trace = 2 * (4 * c - h ^ 2 * k) / (4 * c + h ^ 2 * k) := by
    rw [htr, hden]; field_simp
  have hsq : 0 < (4 * c + h ^ 2 * k) ^ 2 := by positivity
  have hch : 0 < 64 * c * h ^ 2 := by positivity
  have hpos : 0 < 64 * c * h ^ 2 / (4 * c + h ^ 2 * k) ^ 2 := div_pos hch hsq
  -- `a² − 4q = −(64 c h²/(4c + h²k)²) k`: its sign is the sign of `−k`.
  have hdisc : (transfer c k 0 0 h).trace ^ 2 - 4 * (transfer c k 0 0 h).det =
      -(64 * c * h ^ 2 / (4 * c + h ^ 2 * k) ^ 2) * k := by
    rw [htr', hdet1]; field_simp; ring
  set t := (transfer c k 0 0 h).trace
  set q := (transfer c k 0 0 h).det
  set P := 64 * c * h ^ 2 / (4 * c + h ^ 2 * k) ^ 2
  refine ⟨hdet1, ?_, ?_, ?_, fun hk => ?_⟩
  · rw [siteKind_eq_rotation_iff]
    constructor
    · intro hr; nlinarith
    · intro hr; nlinarith [mul_pos hpos hr]
  · rw [siteKind_eq_null_iff]
    constructor
    · rintro ⟨-, hn⟩
      have : P * k = 0 := by linarith
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hpos.ne'
      · exact h0
    · intro hk
      refine ⟨by rw [hdet1]; exact one_pos, ?_⟩
      rw [hk, mul_zero] at hdisc
      linarith
  · rw [siteKind_eq_boost_iff]
    constructor
    · rintro ⟨-, hb⟩
      by_contra hk
      have hk' : 0 ≤ k := not_lt.mp hk
      nlinarith [mul_nonneg hpos.le hk']
    · intro hk
      refine ⟨by rw [hdet1]; exact one_pos, ?_⟩
      nlinarith [mul_pos hpos (neg_pos.mpr hk)]
  · subst hk
    have hc2 : (2 : ℝ) * c ≠ 0 := by positivity
    have hT : transfer c 0 0 0 h = !![1, h; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [transfer, transferDen]; field_simp
      · simp [transfer, transferDen]; field_simp
      · simp [transfer, transferDen]
      · simp [transfer, transferDen]; field_simp; ring
    refine ⟨hT, fun h1 => ?_⟩
    rw [hT] at h1
    have := congrFun (congrFun h1 0) 1
    simp at this
    exact hh this

end Transfer

/-! ## 2. A generalized mode of a contact is a plane of the scalar transfer -/

section Mode

open Holonics.HNN.Ring (closedOperator)

variable {Ch : Type*} [NormedAddCommGroup Ch] [InnerProductSpace ℝ Ch]

/-- [proved-derived; formal-checked] **A generalized mode's plane.** If `K v = μ C v`, the closed,
lossless transit (`M = 2C + (h²/2) K`, `Ring.closedOperator`) from `(u, w) = (a v, b v)` is solved
by `ω = ((2b − h μ a)/m) v`, `m = 2 + h²μ/2 ≠ 0`, and the state stays on the plane with coefficients
`T(1, μ)(a, b)`: the transfer at `(c, k) = (1, μ)`, whose kind is the sign of `μ`
(`contact_transfer_kind_by_storage_sign`). -/
theorem contact_mode_transfer (C K : Ch →L[ℝ] Ch) {v : Ch} {μ h a b : ℝ}
    (hmode : K v = μ • C v) (hm : transferDen 1 μ 0 0 h ≠ 0) :
    closedOperator C K h (((2 * b - h * μ * a) / transferDen 1 μ 0 0 h) • v) =
        (2 : ℝ) • C (b • v) - h • K (a • v) ∧
      a • v + h • (((2 * b - h * μ * a) / transferDen 1 μ 0 0 h) • v) =
        (transfer 1 μ 0 0 h *ᵥ ![a, b]) 0 • v ∧
      (2 : ℝ) • (((2 * b - h * μ * a) / transferDen 1 μ 0 0 h) • v) - b • v =
        (transfer 1 μ 0 0 h *ᵥ ![a, b]) 1 • v := by
  set s := (2 * b - h * μ * a) / transferDen 1 μ 0 0 h with hsdef
  have hden : transferDen 1 μ 0 0 h = 2 + h ^ 2 / 2 * μ := by unfold transferDen; ring
  have hT := transfer_solves (c := 1) (k := μ) (d := 0) (p := 0) (h := h) (u := a) (w := b)
    (ω := s) hm (by rw [hsdef]; field_simp)
  have h0 : (transfer 1 μ 0 0 h *ᵥ ![a, b]) 0 = a + h * s := by rw [hT]; rfl
  have h1 : (transfer 1 μ 0 0 h *ᵥ ![a, b]) 1 = 2 * s - b := by rw [hT]; rfl
  refine ⟨?_, ?_, ?_⟩
  · have hm' : 2 + h ^ 2 / 2 * μ ≠ 0 := by rw [← hden]; exact hm
    have hs : (2 : ℝ) * s + h ^ 2 / 2 * (s * μ) = 2 * b - h * (a * μ) := by
      rw [show (2 : ℝ) * s + h ^ 2 / 2 * (s * μ) = s * (2 + h ^ 2 / 2 * μ) by ring, hsdef, hden,
        div_mul_cancel₀ _ hm']
      ring
    calc closedOperator C K h (s • v)
        = ((2 : ℝ) * s + h ^ 2 / 2 * (s * μ)) • C v := by
          simp only [closedOperator, _root_.add_apply, _root_.smul_apply, map_smul, hmode]
          module
      _ = (2 * b - h * (a * μ)) • C v := by rw [hs]
      _ = (2 : ℝ) • C (b • v) - h • K (a • v) := by
          rw [map_smul, map_smul, hmode]
          module
  · rw [h0]; module
  · rw [h1]; module

end Mode

/-! ## 3. Boosts: the certified solve or its singular direction, and the signed storage -/

section Boost

variable {Ch : Type*} [NormedAddCommGroup Ch] [InnerProductSpace ℝ Ch] [FiniteDimensional ℝ Ch]

/-- [proved-derived; formal-checked] **A boost is admitted only with a certified solve, and a
refusal returns its singular direction.** (1) A contact's operator either solves every right side
uniquely or has a singular direction `v ≠ 0`, `M_a v = 0`: there is no third case. (2) The solve is
certified at every conductance `G > 0` and hop `h > 0` when the signed form `2C + hD + (h²/2) K`
is positive semidefinite, whatever the sign of `K` alone (`⟨v, M_a v⟩ ≥ (2h/G)|v|²`), which
extends `HNN/Propagation.tick_well_defined` beyond `K ⪰ 0`. -/
theorem contact_boost_solve_or_singular_direction (C D K : Ch →L[ℝ] Ch) (G h : ℝ) :
    ((∀ r, ∃! ω, transitOperator C D K G h ω = r) ∨
        ∃ v, v ≠ 0 ∧ transitOperator C D K G h v = 0) ∧
      (0 < G → 0 < h →
        (∀ v, 0 ≤ 2 * inner ℝ v (C v) + h * inner ℝ v (D v) + h ^ 2 / 2 * inner ℝ v (K v)) →
        (∀ v, 2 * h / G * ‖v‖ ^ 2 ≤ inner ℝ v (transitOperator C D K G h v)) ∧
          ∀ r, ∃! ω, transitOperator C D K G h ω = r) := by
  refine ⟨?_, fun hG hh hsigned => ?_⟩
  · by_cases hinj : ∀ v, transitOperator C D K G h v = 0 → v = 0
    · exact Or.inl (Ring.existsUnique_of_injective _ hinj)
    · push Not at hinj
      obtain ⟨v, hv, hne⟩ := hinj
      exact Or.inr ⟨v, hne, hv⟩
  · have hpos : ∀ v, 2 * h / G * ‖v‖ ^ 2 ≤ inner ℝ v (transitOperator C D K G h v) := by
      intro v
      simp only [transitOperator, _root_.add_apply, _root_.smul_apply,
        ContinuousLinearMap.id_apply, inner_add_right, inner_smul_right,
        real_inner_self_eq_norm_sq]
      linarith [hsigned v]
    refine ⟨hpos, Ring.existsUnique_of_injective _ fun v hv => ?_⟩
    have := hpos v
    rw [hv, inner_zero_right] at this
    have hc : 0 < 2 * h / G := by positivity
    have : ‖v‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])

omit [FiniteDimensional ℝ Ch] in
/-- [proved-derived; formal-checked] **The signed-storage balance.** The transit's two-port balance
(`HNN/Propagation.transit_balance`) uses only the symmetry of `C` and `K`, so for an indefinite
stiffness the signed storage `E_a = ½⟨w, C w⟩ + ½⟨u, K u⟩` still balances exactly:
`E_a′ − E_a + h⟨ω, D ω⟩ = (hG/4)(|α|² − |α_out|²)`. The storage may be negative; passivity is not
asserted (`boost_grows_at_conserved_signed_storage`). -/
theorem contact_signed_storage_balance (C D K : Ch →L[ℝ] Ch)
    (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y)) (hK : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y))
    {G h : ℝ} (hG : G ≠ 0) {u w αg αh ω : Ch} (hsolve : TransitSolves C D K G h u w αg αh ω) :
    contactEnergy C K (u + h • ω) ((2 : ℝ) • ω - w) - contactEnergy C K u w +
        h * inner ℝ ω (D ω) =
      h * G / 4 * (‖αg‖ ^ 2 + ‖αh‖ ^ 2 - ‖αg - (2 / G) • ω‖ ^ 2 - ‖αh + (2 / G) • ω‖ ^ 2) :=
  transit_balance C D K hC hK hG hsolve

/-- [counterexample; formal-checked] **An exact balance is not passivity.** The closed lossless
boost `c = 1`, `k = −1`, `h = 1` has transfer `[[5/3, 4/3], [4/3, 5/3]]` (a boost:
`tr = 10/3 > 2`, `det = 1`); it triples the state `(1, 1)` at every tick while the signed storage
`½w² − ½u²` of that state stays `0`. -/
theorem boost_grows_at_conserved_signed_storage :
    transfer 1 (-1) 0 0 1 = !![5 / 3, 4 / 3; 4 / 3, 5 / 3] ∧
      siteKind (transfer 1 (-1) 0 0 1).trace (transfer 1 (-1) 0 0 1).det = .boost ∧
      transfer 1 (-1) 0 0 1 *ᵥ ![1, 1] = ![3, 3] ∧
      (1 / 2 : ℝ) * 3 ^ 2 - (1 / 2) * 3 ^ 2 = (1 / 2) * 1 ^ 2 - (1 / 2) * 1 ^ 2 := by
  have hT : transfer 1 (-1) 0 0 1 = !![5 / 3, 4 / 3; 4 / 3, 5 / 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transfer, transferDen] <;> norm_num
  refine ⟨hT, ?_, ?_, by norm_num⟩
  · rw [hT, siteKind_eq_boost_iff, trace_fin_two_of, det_fin_two_of]
    norm_num
  · rw [hT]
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

end Boost

/-! ## 4. The lock address from the measured winding pair -/

section Lock

open Holonics.Aeon.Clock.Lock

/-- [proved-derived; formal-checked] **The contact's lock address from its measured winding pair.**
Whole windings `m_g` of the contact's first ring and `m_h > 0` of its second, over one passage,
reduce by their greatest common divisor `g` to the coprime address `p/q` (`m_g = p g`, `m_h = q g`,
`0 < q`). The passage reads `(m_g, m_h)` at the rate `p/q` and is a cycle of the two clocks there,
and the cycles at `p/q` are exactly the passages of a multiple of `q` turns of the second clock
(`Aeon/Clock/Lock.{lock_at_address, cycle_iff_period_dvd}`): `q` is the lock's period. -/
theorem contact_lock_address (mg : ℤ) (mh : ℕ) (hmh : 0 < mh) :
    0 < mh / Int.gcd mg mh ∧ IsCoprime ((mh / Int.gcd mg mh : ℕ) : ℤ) (mg / Int.gcd mg mh) ∧
      mg = mg / Int.gcd mg mh * Int.gcd mg mh ∧ mh = mh / Int.gcd mg mh * Int.gcd mg mh ∧
      jointReading (((mg / Int.gcd mg mh : ℤ) : ℚ) / (mh / Int.gcd mg mh : ℕ)) (mh : ℤ) =
        ((mg : ℚ), ((mh : ℤ) : ℚ)) ∧
      IsCycle (jointReading (((mg / Int.gcd mg mh : ℤ) : ℚ) / (mh / Int.gcd mg mh : ℕ)) (mh : ℤ)) ∧
      ∀ k : ℤ, IsCycle (jointReading (((mg / Int.gcd mg mh : ℤ) : ℚ) / (mh / Int.gcd mg mh : ℕ)) k) ↔
        ((mh / Int.gcd mg mh : ℕ) : ℤ) ∣ k := by
  set g := Int.gcd mg mh with hg
  have hgpos : 0 < g := Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hmh.ne')
  have hgmh : g ∣ mh := by
    have := Int.gcd_dvd_right mg (mh : ℤ)
    rw [← hg] at this
    exact_mod_cast this
  have hgmg : (g : ℤ) ∣ mg := Int.gcd_dvd_left mg mh
  set q := mh / g with hq
  set p := mg / (g : ℤ) with hp
  have hqg : mh = q * g := (Nat.div_mul_cancel hgmh).symm
  have hpg : mg = p * g := (Int.ediv_mul_cancel hgmg).symm
  have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd hmh hgmh) hgpos
  have hcop : IsCoprime (q : ℤ) p := by
    have hq' : ((q : ℕ) : ℤ) = (mh : ℤ) / (g : ℤ) := by rw [hq]; exact Int.natCast_div mh g
    have h1 := Int.gcd_div_gcd_div_gcd (i := mg) (j := (mh : ℤ)) (by rw [← hg]; exact_mod_cast hgpos)
    rw [← hg] at h1
    rw [Int.isCoprime_iff_gcd_eq_one, hq', Int.gcd_comm]
    exact h1
  have hlock := lock_at_address p q hqpos (g : ℤ)
  have hmhz : ((mh : ℕ) : ℤ) = (q : ℤ) * g := by exact_mod_cast hqg
  refine ⟨hqpos, hcop, hpg, hqg, ?_, ?_, fun k => cycle_iff_period_dvd p q hqpos hcop k⟩
  · rw [hmhz, hlock.1]
    refine Prod.ext ?_ ?_
    · show (((p * g : ℤ)) : ℚ) = (mg : ℚ)
      rw [hpg]
    · show (((q * g : ℤ)) : ℚ) = (((q : ℤ) * g : ℤ) : ℚ)
      rfl
  · rw [hmhz]; exact hlock.2.1

end Lock

section Audit

#print axioms transitOperator_scalar
#print axioms transfer_solves
#print axioms transfer_trace_det
#print axioms contact_transfer_kind_by_storage_sign
#print axioms contact_mode_transfer
#print axioms contact_boost_solve_or_singular_direction
#print axioms contact_signed_storage_balance
#print axioms boost_grows_at_conserved_signed_storage
#print axioms contact_lock_address

end Audit

end Holonics.HNN.Contact
