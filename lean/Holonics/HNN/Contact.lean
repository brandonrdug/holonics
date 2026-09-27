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
5. **The lock address: the least-denominator rate in the measured fibre** (`contact_lock_address`,
   the Rust owner `hnn::contact::lock_address`). Whole windings `(m_g, m_h)`, both at least one,
   leave the passage's rate in the open fibre `(m_g/(m_h + 1), (m_g + 1)/m_h)`. Its lock address
   (`IsLockAddress`: the least denominator of its rationals, then the least rate of that
   denominator) exists and is unique (`lockAddress_exists`, `lockAddress_unique`); past the
   integers the least denominator alone fixes it, because between two rationals of one denominator
   `q ≥ 2` lies a rational of smaller denominator (`exists_smaller_den_between`,
   `least_denominator_unique`, Bézout at the neighbour `m/t = p/q + 1/(qt)`). The address lies in
   the box `1 ≤ p ≤ m_g`, `1 ≤ q ≤ m_h`, and it closes at its period `q`: its cycles are exactly the
   multiples of `q` (`lockAddress_closes`, composing `Aeon/Clock/Lock.{lock_at_address,
   cycle_iff_period_dvd}`). The finite family these addresses land in, `Unlocked` and the reduced
   `(p, q)` within the derived bounds `(P, Q)`, is `Compression/Landmark/Context/Address.lock_partition_finite`, whose
   horizon clause (`Q = H`, the windings counted up to the closing tick) is this theorem's box read
   at the horizon: one object, its reading here and its partition there.

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

/-! ## 4. The lock address: the least-denominator rate in the measured fibre -/

section Lock

open Holonics.Aeon.Clock.Lock

/-- [definition] **The lock address of an open fibre `(a, b)`**: a rate `r` in it whose denominator
is the least of any rational in it and which is the least of the fibre's rationals of that
denominator (the Stern–Brocot ancestor the continued-fraction descent reaches first; the Rust owner
`navigator::address::simplest_between`). The numerator's order decides only a fibre holding several
integers (`least_denominator_unique`). -/
def IsLockAddress (a b r : ℚ) : Prop :=
  a < r ∧ r < b ∧ (∀ s : ℚ, a < s → s < b → r.den ≤ s.den) ∧
    ∀ s : ℚ, a < s → s < b → s.den = r.den → r ≤ s

/-- [proved-derived; formal-checked] **The lock address is unique.** -/
theorem lockAddress_unique {a b r r' : ℚ} (hr : IsLockAddress a b r)
    (hr' : IsLockAddress a b r') : r = r' := by
  obtain ⟨h1, h2, h3, h4⟩ := hr
  obtain ⟨h1', h2', h3', h4'⟩ := hr'
  have hden : r.den = r'.den := le_antisymm (h3 r' h1' h2') (h3' r h1 h2)
  exact le_antisymm (h4 r' h1' h2' hden.symm) (h4' r h1 h2 hden)

/-- [proved-derived; formal-checked] Two rationals of one denominator are ordered as their
numerators. -/
theorem le_of_num_le_of_den_eq {r s : ℚ} (hden : s.den = r.den) (hnum : r.num ≤ s.num) :
    r ≤ s := by
  rw [← Rat.num_div_den r, ← Rat.num_div_den s, hden]
  have hq : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  exact div_le_div_of_nonneg_right (by exact_mod_cast hnum) hq.le

/-- [proved-derived; formal-checked] Of two rationals of one denominator the greater has the greater
numerator. -/
theorem num_lt_of_lt_of_den_eq {r s : ℚ} (hden : s.den = r.den) (hlt : r < s) :
    r.num < s.num := by
  by_contra h
  exact absurd (le_of_num_le_of_den_eq hden.symm (not_lt.mp h)) (not_le.mpr hlt)

/-- [proved-derived; formal-checked] **Every nonempty open fibre has its lock address**: the least
denominator of its rationals (`Nat.find`), then the least numerator of that denominator, bounded
below by `⌊a q⌋`. -/
theorem lockAddress_exists {a b : ℚ} (hab : a < b) : ∃ r, IsLockAddress a b r := by
  classical
  have hS : ∃ q : ℕ, ∃ s : ℚ, a < s ∧ s < b ∧ s.den = q :=
    ⟨((a + b) / 2).den, (a + b) / 2, by linarith, by linarith, rfl⟩
  obtain ⟨s₀, hs₀a, hs₀b, hs₀q⟩ := Nat.find_spec hS
  have hbdd : ∃ lb : ℤ, ∀ z : ℤ,
      (∃ s : ℚ, a < s ∧ s < b ∧ s.den = Nat.find hS ∧ s.num = z) → lb ≤ z := by
    refine ⟨⌊a * (Nat.find hS : ℚ)⌋, fun z ⟨s, hsa, _, hsq, hsz⟩ => ?_⟩
    have hqpos : (0 : ℚ) < (Nat.find hS : ℚ) := by rw [← hsq]; exact_mod_cast s.den_pos
    have hs : s = (z : ℚ) / (Nat.find hS : ℚ) := by
      rw [← hsz, ← hsq]; exact (Rat.num_div_den s).symm
    have haz : a * (Nat.find hS : ℚ) < z := by
      rw [hs, lt_div_iff₀ hqpos] at hsa; exact hsa
    have hfl := Int.floor_le (a * (Nat.find hS : ℚ))
    have : ((⌊a * (Nat.find hS : ℚ)⌋ : ℤ) : ℚ) < z := lt_of_le_of_lt hfl haz
    exact le_of_lt (by exact_mod_cast this)
  obtain ⟨n, ⟨r, hra, hrb, hrq, hrn⟩, hmin⟩ :=
    Int.exists_least_of_bdd hbdd ⟨s₀.num, s₀, hs₀a, hs₀b, hs₀q, rfl⟩
  refine ⟨r, hra, hrb, fun s hsa hsb => ?_, fun s hsa hsb hsd => ?_⟩
  · rw [hrq]; exact Nat.find_min' hS ⟨s, hsa, hsb, rfl⟩
  · refine le_of_num_le_of_den_eq hsd ?_
    rw [hrn]
    exact hmin s.num ⟨s, hsa, hsb, hsd.trans hrq, rfl⟩

/-- [proved-derived; formal-checked] **Between two rationals of one denominator `q ≥ 2` lies a
rational of smaller denominator.** With `p/q` reduced, Bézout gives `q m − p t = 1` with
`0 < t < q` (`t ≡ −p⁻¹ mod q`, and `t = 0` would make `q ∣ 1`), and `m/t = p/q + 1/(qt)` lies in
`(p/q, (p + 1)/q]` with denominator at most `t` (the mediant cost of `Geometry/PairResonance`,
read at the neighbour `m/t`). -/
theorem exists_smaller_den_between {r s : ℚ} (hlt : r < s) (hden : s.den = r.den)
    (htwo : 2 ≤ r.den) : ∃ x : ℚ, r < x ∧ x ≤ s ∧ x.den < r.den := by
  set q : ℤ := (r.den : ℤ) with hqdef
  set p : ℤ := r.num with hpdef
  have hq : (0 : ℤ) < q := by rw [hqdef]; exact_mod_cast r.den_pos
  have hcop : Int.gcd p q = 1 := by
    have := r.reduced
    rw [Int.gcd, hqdef, Int.natAbs_natCast]
    exact this
  have hb := Int.gcd_eq_gcd_ab p q
  rw [hcop] at hb
  set A := Int.gcdA p q
  set B := Int.gcdB p q
  set t : ℤ := (-A) % q with htdef
  have ht0 : 0 ≤ t := Int.emod_nonneg _ (ne_of_gt hq)
  have htq : t < q := Int.emod_lt_of_pos _ hq
  have htexp : t = -A - q * ((-A) / q) := Int.emod_def _ _
  have hdvd : q ∣ 1 + p * t := ⟨B - p * ((-A) / q), by rw [htexp]; push_cast at hb ⊢; linear_combination hb⟩
  have ht1 : 0 < t := by
    rcases ht0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero, add_zero] at hdvd
      have h1 : q = 1 := Int.eq_one_of_dvd_one hq.le hdvd
      rw [hqdef] at h1
      have : r.den = 1 := by exact_mod_cast h1
      omega
  obtain ⟨m, hm⟩ := hdvd
  have hqQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have htQ : (0 : ℚ) < (t : ℚ) := by exact_mod_cast ht1
  have hr : r = (p : ℚ) / q := (Rat.num_div_den r).symm
  have hs : s = (s.num : ℚ) / q := by rw [hqdef, ← hden]; exact (Rat.num_div_den s).symm
  have hps : p + 1 ≤ s.num := num_lt_of_lt_of_den_eq hden hlt
  have hmQ : (q : ℚ) * m = 1 + p * t := by exact_mod_cast hm.symm
  refine ⟨(m : ℚ) / t, ?_, ?_, ?_⟩
  · -- m/t − p/q = 1/(qt) > 0
    rw [hr, div_lt_div_iff₀ hqQ htQ]
    nlinarith [hmQ]
  · -- m/t = p/q + 1/(qt) ≤ (p + 1)/q ≤ s
    rw [hs, div_le_div_iff₀ htQ hqQ]
    have hps' : ((p : ℚ) + 1) ≤ (s.num : ℚ) := by exact_mod_cast hps
    have ht1' : (1 : ℚ) ≤ t := by exact_mod_cast ht1
    nlinarith [hmQ]
  · have hd : (((m : ℚ) / t).den : ℤ) ∣ t := by
      rw [← Rat.divInt_eq_div]; exact Rat.den_dvd m t
    have := Int.le_of_dvd ht1 hd
    have : (((m : ℚ) / t).den : ℤ) < (r.den : ℤ) := lt_of_le_of_lt this (hqdef ▸ htq)
    exact_mod_cast this

/-- [proved-derived; formal-checked] **Past the integers the least denominator alone fixes the
address**: two rationals of an open interval with its least denominator `q ≥ 2` are equal. -/
theorem least_denominator_unique {a b r s : ℚ} (hra : a < r) (hrb : r < b) (hsa : a < s)
    (hsb : s < b) (hden : s.den = r.den)
    (hleast : ∀ x : ℚ, a < x → x < b → r.den ≤ x.den) (htwo : 2 ≤ r.den) : r = s := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨x, hrx, hxs, hx⟩ := exists_smaller_den_between hlt hden htwo
    exact absurd (hleast x (hra.trans hrx) (lt_of_le_of_lt hxs hsb)) (not_le.mpr hx)
  · obtain ⟨x, hsx, hxr, hx⟩ := exists_smaller_den_between hlt hden.symm (hden ▸ htwo)
    rw [hden] at hx
    exact absurd (hleast x (hsa.trans hsx) (lt_of_le_of_lt hxr hrb)) (not_le.mpr hx)

/-- [proved-derived; formal-checked] A rational's denominator and numerator are coprime. -/
theorem isCoprime_den_num (r : ℚ) : IsCoprime (r.den : ℤ) r.num := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd, Int.natAbs_natCast]
  exact r.reduced.symm

/-- [proved-derived; formal-checked] **A rate closes at its reduced denominator**: at `r = p/q`
every aeon of `q m` ticks reads `(p m, q m)` whole windings and is a cycle, and the cycles are
exactly the aeons of a multiple of `q` ticks (`Aeon/Clock/Lock.{lock_at_address,
cycle_iff_period_dvd}`): `q` is the lock's period. -/
theorem lockAddress_closes (r : ℚ) :
    (∀ m : ℤ, jointReading r (r.den * m) = (((r.num * m : ℤ) : ℚ), ((r.den * m : ℤ) : ℚ)) ∧
      IsCycle (jointReading r (r.den * m))) ∧
    ∀ k : ℤ, IsCycle (jointReading r k) ↔ (r.den : ℤ) ∣ k := by
  have hr : ((r.num : ℚ) / (r.den : ℕ)) = r := Rat.num_div_den r
  refine ⟨fun m => ?_, fun k => ?_⟩
  · have h := lock_at_address r.num r.den r.den_pos m
    rw [hr] at h
    exact ⟨h.1, h.2.1⟩
  · have h := cycle_iff_period_dvd r.num r.den r.den_pos (isCoprime_den_num r) k
    rwa [hr] at h

/-- [proved-derived; formal-checked] **The contact's lock address from its measured winding pair**
(the Rust owner `hnn::contact::lock_address`). Over a passage the contact `g → h` reads its rings'
whole windings `m_g, m_h ≥ 1`; their phases are the unresolved part, so the passage's rate
`x_g/x_h` (`m_g ≤ x_g < m_g + 1`, `m_h ≤ x_h < m_h + 1`) lies in the open fibre
`(m_g/(m_h + 1), (m_g + 1)/m_h)`, which holds the measured ratio `m_g/m_h`.
* The fibre has exactly one lock address `r = p/q` (`IsLockAddress`: the least denominator, then
  the least rate).
* It lands in the box `1 ≤ p ≤ m_g`, `1 ≤ q ≤ m_h`: its denominator is at most the measured ratio's,
  and `p/q < (m_g + 1)/m_h` bounds its numerator. So whenever the windings are within the lock
  letters' bounds `(P, Q)` the address is one of them (`Compression/Landmark/Context/Address.lock_partition_finite`).
* It closes at its period `q`: the cycles at `p/q` are exactly the passages of a multiple of `q`
  turns of ring `h` (`lockAddress_closes`). -/
theorem contact_lock_address (mg mh : ℕ) (hg : 0 < mg) (hh : 0 < mh) :
    (∀ xg xh : ℚ, (mg : ℚ) ≤ xg → xg < mg + 1 → (mh : ℚ) ≤ xh → xh < mh + 1 →
      (mg : ℚ) / (mh + 1) < xg / xh ∧ xg / xh < ((mg : ℚ) + 1) / mh) ∧
    (∃! r : ℚ, IsLockAddress ((mg : ℚ) / (mh + 1)) (((mg : ℚ) + 1) / mh) r) ∧
    ∀ r : ℚ, IsLockAddress ((mg : ℚ) / (mh + 1)) (((mg : ℚ) + 1) / mh) r →
      (1 ≤ r.num ∧ r.num ≤ mg ∧ 1 ≤ r.den ∧ r.den ≤ mh) ∧
        ∀ k : ℤ, IsCycle (jointReading r k) ↔ (r.den : ℤ) ∣ k := by
  have hgQ : (0 : ℚ) < mg := by exact_mod_cast hg
  have hhQ : (0 : ℚ) < mh := by exact_mod_cast hh
  have hrate : ∀ xg xh : ℚ, (mg : ℚ) ≤ xg → xg < mg + 1 → (mh : ℚ) ≤ xh → xh < mh + 1 →
      (mg : ℚ) / (mh + 1) < xg / xh ∧ xg / xh < ((mg : ℚ) + 1) / mh := by
    intro xg xh hg1 hg2 hh1 hh2
    have hxh : (0 : ℚ) < xh := lt_of_lt_of_le hhQ hh1
    constructor
    · rw [div_lt_div_iff₀ (by linarith) hxh]; nlinarith
    · rw [div_lt_div_iff₀ hxh hhQ]; nlinarith
  have hfibre : (mg : ℚ) / (mh + 1) < ((mg : ℚ) + 1) / mh := by
    have := hrate mg mh le_rfl (by linarith) le_rfl (by linarith)
    exact this.1.trans this.2
  obtain ⟨r₀, hr₀⟩ := lockAddress_exists hfibre
  refine ⟨hrate, ⟨r₀, hr₀, fun r hr => lockAddress_unique hr hr₀⟩, fun r hr => ⟨?_, (lockAddress_closes r).2⟩⟩
  obtain ⟨hra, hrb, hleast, -⟩ := hr
  have hmeas := hrate mg mh le_rfl (by linarith) le_rfl (by linarith)
  have hden : r.den ≤ mh := by
    have h1 := hleast ((mg : ℚ) / mh) hmeas.1 hmeas.2
    have h2 : ((((mg : ℤ) : ℚ) / ((mh : ℤ) : ℚ)).den : ℤ) ∣ (mh : ℤ) := by
      rw [← Rat.divInt_eq_div]; exact Rat.den_dvd _ _
    have h3 := Int.le_of_dvd (by exact_mod_cast hh) h2
    push_cast at h3
    have : (((mg : ℚ) / (mh : ℚ)).den : ℤ) ≤ (mh : ℤ) := h3
    omega
  have hpos : 0 < r := lt_of_le_of_lt (by positivity) hra
  have hnum1 : 1 ≤ r.num := Rat.num_pos.mpr hpos
  have hrd : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have hnumle : r.num ≤ mg := by
    have hr' : r = (r.num : ℚ) / r.den := (Rat.num_div_den r).symm
    rw [hr', div_lt_div_iff₀ hrd hhQ] at hrb
    have hdQ : (r.den : ℚ) ≤ mh := by exact_mod_cast hden
    have : (r.num : ℚ) * mh < ((mg : ℚ) + 1) * mh := by nlinarith
    have : (r.num : ℚ) < (mg : ℚ) + 1 := lt_of_mul_lt_mul_right this hhQ.le
    have : r.num < (mg : ℤ) + 1 := by exact_mod_cast this
    omega
  exact ⟨hnum1, hnumle, r.den_pos, hden⟩

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
#print axioms lockAddress_unique
#print axioms lockAddress_exists
#print axioms exists_smaller_den_between
#print axioms least_denominator_unique
#print axioms lockAddress_closes
#print axioms contact_lock_address

end Audit

end Holonics.HNN.Contact
