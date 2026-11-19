import Holonics.Physics.Spacetime.NonClosedClock
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# The frame-dragging clock: Einstein synchronization in a stationary metric reads the flux of `da`

[definition] The box of #410, "the frame-dragging clock of a stationary spacetime
(`Physics/Spacetime/NonClosedClock`)", from that owner's closing paragraph: "Frame dragging would be
the same law for a stationary non-static clock `ω = N dt − A`, whose cycle reading is the flux of
`dA` (`HodgeTime.cell_boundary_reading_is_curvature_flux`); only the Sagnac case `A = Ω(x dy − y dx)`
is stated here, first order in `Ω` … `[open]` A frame-dragging clock of a stationary spacetime is
owed (#62)." Sources: the null-cone record
`research/records/2026-09-24_THE_NULL_CONE_IS_THE_CONSTITUTIONS_LOCK_AND_CLOSURE_IS_A_RECEIVER_READING.md`
§1 ("Frame dragging: it is the `dω` of a stationary non-static clock"); the atlas rows
`lorentz.nonclosed-clock`, `clock.sagnac-production`, `gr.odd-part-motion-spin-charge` (spin as the
circulation over loops in space) and `gr.one-way-exact-part` (Einstein's `ε = 1/2` and the loop's
`2ΩA`).

A stationary metric at a point, in a chart adapted to its time translation, is `g₀₀`, the shift
`g₀ᵢ` and the spatial block `g_ij` (`Stationary`). Its synchronization one-form is
`a(v) = −g₀ᵢvⁱ/g₀₀` (`Stationary.sync`). The clock form of a cell complex whose passage values are
`a` along each passage (`syncClock`) is the frame-dragging clock: its passage values are Einstein's
synchronization gaps, and the cycle reading is the flux of its curvature.

[proved-standard; formal-checked] What is proved. Item 1 is over an ordered field (its linear algebra
over any field, its square root over ℝ), item 2 over ℚ (the owner's field), items 3 and 4 over ℝ
(their algebra over any field).

1. **Einstein synchronization, pointwise** (`null_sum`, `null_prod`, `null_opposite`,
   `future_null_unique`, `einstein_offset`, `null_times_exist`, `sync_add`, `sync_smul`,
   `interval_neg`). Two distinct null coordinate times `δt₁, δt₂` along a spatial step `v` (roots of
   `g₀₀ δt² + 2 g₀ᵢvⁱ δt + g_ij vⁱvʲ`) have midpoint `(δt₁ + δt₂)/2 = a(v)` and product
   `g_ij vⁱvʲ/g₀₀` (Vieta); for `g₀₀ < 0` and `g_ij vⁱvʲ > 0` one is positive and one negative, and a
   positive one is unique. A return along `−v` reverses the clock (`interval_neg`), so Einstein's
   offset, half the forward leg less half the return leg, is `a(v)` (`einstein_offset`); over ℝ both
   legs exist and every null time is one of them (`null_times_exist`). `a` is linear in `v`; a static
   metric (`g₀ᵢ = 0`) has `a = 0` and equal legs (`sync_static`, `static_legs_equal`).

[proved-derived; formal-checked]

2. **The loop reading is the flux of `da`** (`syncClock_cell_reading`, `syncClock_production`,
   `syncClock_closed_iff`, `static_syncClock_zero`, `uniform_syncClock_exact`,
   `uniform_syncClock_silent`). On any weighted complex with sites placed at `xᵥ`, the clock whose
   passage `e` reads `a_e(Δx_e)` (`syncClock`) reads every cell boundary as the flux of its
   curvature, every Hodge split's production part reads the same flux, and the clock is closed
   exactly when every flux vanishes, exactly when its production part is zero. A static metric gives
   the zero clock. A uniform metric gives an exact clock, `d₀` of the sites' offsets `a(xᵥ)` (a
   re-charting of the sites' clocks), silent on every cycle and with no production part.
   On the house's square (`square_displacement`, `square_syncClock_reading`,
   `square_syncClock_closed_iff`, `sagnac_is_syncClock`, `sagnac_sync_reading`): for any stationary
   metrics on the four passages the loop reads the flux through the face, so does the production
   part, and the clock is closed exactly when the loop reads zero; the owner's `sagnacForm` is the
   synchronization clock of the first-order rotating metric `g₀₀ = −1`, `g₀ = Ω(−y, x)` read at each
   passage's midpoint, so the owner's `2ΩA` is the Einstein gap around the loop. The all-orders
   Cartesian rotating metric divides each first-order gap by `1 − Ω²|m|²` (`rotatingCartesian_sync`).

[proved-standard; formal-checked]

3. **The rotating frame, to all orders** (`rotating_sync`, `rotating_lapse_neg`,
   `rotating_einstein`, `circleReading_eq`, `rotating_circle_reading`, `rotating_circle_proper`,
   `rotating_circle_area`, `rotating_first_order`, `rotating_first_order_bound`,
   `rotating_first_order_isBigO`, `rotating_curvature`, `rotating_disk_flux`). In the polar chart
   `(r, φ)` of Minkowski space rotating at `Ω` (`c = 1`): `a = Ωr² dφ/(1 − Ω²r²)`; for `Ω²r² < 1`
   it is Einstein's offset along a step of the circle; the circle of radius `r` reads
   `2πΩr²/(1 − Ω²r²) = 2ΩA/(1 − Ω²r²)` with `A = πr²` in coordinate time, and
   `2πΩr²/√(1 − Ω²r²)` in the rim's proper time (lapse `N = √(1 − Ω²r²)`); it exceeds the owner's
   first-order `2ΩA` by `2ΩA·Ω²r²/(1 − Ω²r²)`, at most `4πr⁴|Ω|³` for `Ω²r² ≤ 1/2`, so the
   difference is `O(Ω³)`. The curvature `∂_ρ a_φ = 2Ωρ/(1 − Ω²ρ²)²` integrated over the disk is the
   circle's reading (Stokes on the disk, by the fundamental theorem of calculus).
4. **Frame dragging** (`zamo_iff`, `circle_reading_zamo`, `corotate_interval`, `zamo_closes`,
   `corotate_closes_iff`, `rotating_circle_is_corotated`, `lenseThirring_sync`,
   `lenseThirring_circle_reading`, `lenseThirring_reading_eq`, `lenseThirring_zamo`,
   `lenseThirring_reading_zamo`, `lenseThirring_isotropic_zamo`, `lenseThirring_einstein`,
   `lenseThirring_annulus_flux`, `lenseThirring_reading_tendsto`, `rotating_shift_rigid`,
   `lenseThirring_shift_not_rigid`). For an axisymmetric stationary metric restricted to a circle
   (`g₀₀`, `g₀φ`, `g_φφ`): an observer at angular velocity `w` has zero angular momentum exactly when
   `w = ω := −g₀φ/g_φφ`; the static circle reads `2πa_φ = −2ω·πg_φφ/(−g₀₀)`, minus twice the
   zero-angular-momentum rate times the circumferential area over `−g₀₀`; the chart rotating at `w`
   keeps the interval, the chart rotating at `ω` closes the circle's synchronization, and where the
   rotated `g₀₀` is nonzero no other rate does. The rotating frame's circle is Minkowski's circle in
   the chart rotating at `Ω`. In the weak-field Lense–Thirring metric (`g₀₀ = −(1 − 2M/r)`,
   `g₀φ = −2J/r` in the equatorial plane, `g_φφ = r²`): `a = −2J dφ/(r(1 − 2M/r))`; the circle,
   traversed in increasing `φ`, reads `−4πJ/(r(1 − 2M/r)) = −4πJ/(r − 2M)`; the
   zero-angular-momentum rate is `2J/r³` (and `2J/(r³(1 + 2M/r))`, which differs from it at order
   `JM`, when `g_φφ = (1 + 2M/r)r²`); two circles outside `2M` differ by the flux of `da` through
   the annulus between them; and the reading tends to zero far out. A rigid rotation removes the
   rotating frame's shift on every circle; for `J ≠ 0` no rigid rotation removes the Lense–Thirring
   shift on two circles of distinct radii.

What is not claimed. No field equation: the Lense–Thirring components are taken as given, and no
statement says they solve Einstein's equation at first order. No Kerr metric, no geodesic and no
gyroscope precession. The circle readings over ℝ are integrals of `a` along a circle of constant
`r` in the `(r, φ)` chart, for components that do not depend on `φ`; the bridge from the square
over ℚ to the circle over ℝ is the shared law `a = −g₀ᵢdxⁱ/g₀₀`, with no limit of polygons taken.
That a passage's midpoint reading equals the line integral of a form linear in position (the
first-order rotating form is one) is classical and not formalized here; for the all-orders form the
square's passage values are midpoint readings by declaration. The proper-time reading is stated
only on the rotating circle, where the lapse is constant; where the lapse varies along a loop, the
flux of `d(Na)` and the flux of `da` differ, and only the second is stated.

The computational object is the helical pair interaction: a passage between two sites is a pair
contact, and its two null legs are the duplex of the pair; Einstein's offset is the pair's odd part
(half the difference of the legs), the part no round trip reads, and around a cell the odd parts
sum to the curvature flux. A rotating chart `φ = φ' + wt` is a screw (circle plus carry), and the
zero-angular-momentum rate is the carry that closes one circle. Of the winding guide's six general
objects this touches the pair (the two legs of a contact), the cell holonomy (the loop reading as
the flux of `da`) and the helix (the corotating chart and the circle's winding); faces and
placement, the tube and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.Spacetime.FrameDraggingClock

open Matrix Filter Topology Real
open Holonics.Foundation.HodgeReceiver
open Holonics.Aeon.Production.HodgeTime
open Holonics.Physics.Spacetime.NonClosedClock

/-! ## 1. Einstein synchronization in a stationary metric -/

/-- [definition] A stationary metric at a point, in a chart adapted to its time translation: `g₀₀`,
the shift `g₀ᵢ` and the spatial block `g_ij`. -/
structure Stationary (n : ℕ) (K : Type*) where
  g₀₀ : K
  g₀ : Fin n → K
  γ : Matrix (Fin n) (Fin n) K

namespace Stationary

variable {n : ℕ} {K : Type*}

section Field

variable [Field K]

/-- [definition] The interval of the displacement `(δt, v)`: `g₀₀ δt² + 2 g₀ᵢvⁱ δt + g_ij vⁱvʲ`. A
null coordinate time along `v` is a root in `δt`. -/
def interval (M : Stationary n K) (v : Fin n → K) (δt : K) : K :=
  M.g₀₀ * δt ^ 2 + 2 * (M.g₀ ⬝ᵥ v) * δt + v ⬝ᵥ (M.γ *ᵥ v)

/-- [definition] **The synchronization one-form** `a(v) = −g₀ᵢvⁱ/g₀₀`. -/
def sync (M : Stationary n K) (v : Fin n → K) : K := -(M.g₀ ⬝ᵥ v) / M.g₀₀

/-- [proved-standard; formal-checked] `a` is additive in the step. -/
theorem sync_add (M : Stationary n K) (u v : Fin n → K) : M.sync (u + v) = M.sync u + M.sync v := by
  unfold sync; rw [dotProduct_add]; ring

/-- [proved-standard; formal-checked] `a` is homogeneous in the step. -/
theorem sync_smul (M : Stationary n K) (k : K) (v : Fin n → K) : M.sync (k • v) = k * M.sync v := by
  unfold sync; rw [dotProduct_smul, smul_eq_mul]; ring

/-- [definition] `a` as a linear form on spatial steps. -/
def syncMap (M : Stationary n K) : (Fin n → K) →ₗ[K] K where
  toFun := M.sync
  map_add' := M.sync_add
  map_smul' := fun k v => by rw [sync_smul, RingHom.id_apply, smul_eq_mul]

/-- [proved-standard; formal-checked] **A static metric does not desynchronize**: `g₀ᵢ = 0` gives
`a = 0`. -/
theorem sync_static (M : Stationary n K) (h : M.g₀ = 0) (v : Fin n → K) : M.sync v = 0 := by
  simp [sync, h]

/-- [proved-standard; formal-checked] **The return reverses the clock**: the interval of `(−δt, −v)`
is that of `(δt, v)`, so a return leg along `−v` taking `τ` is a null time `−τ` along `v`. -/
theorem interval_neg (M : Stationary n K) (v : Fin n → K) (δt : K) :
    M.interval (-v) (-δt) = M.interval v δt := by
  simp only [interval, dotProduct_neg, Matrix.mulVec_neg, neg_dotProduct, neg_neg]
  ring

end Field

section Ordered

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- [proved-standard; formal-checked] **Vieta's sum**: two distinct null times along `v` satisfy
`g₀₀(δt₁ + δt₂) + 2g₀ᵢvⁱ = 0`, so their midpoint is `a(v)`. -/
theorem null_sum {M : Stationary n K} {v : Fin n → K} {t₁ t₂ : K} (hg : M.g₀₀ ≠ 0)
    (h₁ : M.interval v t₁ = 0) (h₂ : M.interval v t₂ = 0) (hne : t₁ ≠ t₂) :
    M.g₀₀ * (t₁ + t₂) + 2 * (M.g₀ ⬝ᵥ v) = 0 ∧ (t₁ + t₂) / 2 = M.sync v := by
  unfold interval at h₁ h₂
  have h : (t₁ - t₂) * (M.g₀₀ * (t₁ + t₂) + 2 * (M.g₀ ⬝ᵥ v)) = 0 := by linear_combination h₁ - h₂
  have hs : M.g₀₀ * (t₁ + t₂) + 2 * (M.g₀ ⬝ᵥ v) = 0 :=
    (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)
  refine ⟨hs, ?_⟩
  unfold sync
  rw [div_eq_div_iff two_ne_zero hg]
  linear_combination hs

/-- [proved-standard; formal-checked] **Vieta's product**: `g₀₀ δt₁δt₂ = g_ij vⁱvʲ`. -/
theorem null_prod {M : Stationary n K} {v : Fin n → K} {t₁ t₂ : K} (hg : M.g₀₀ ≠ 0)
    (h₁ : M.interval v t₁ = 0) (h₂ : M.interval v t₂ = 0) (hne : t₁ ≠ t₂) :
    M.g₀₀ * (t₁ * t₂) = v ⬝ᵥ (M.γ *ᵥ v) := by
  have hs := (null_sum hg h₁ h₂ hne).1
  unfold interval at h₁
  linear_combination t₁ * hs - h₁

/-- [proved-standard; formal-checked] Einstein's offset needs only `g₀₀ ≠ 0`: a forward leg `δt₊ > 0`
along `v` and a return leg `δt₋' > 0` along `−v` give `(δt₊ − δt₋')/2 = a(v)`. -/
theorem einstein_offset {M : Stationary n K} {v : Fin n → K} {tf tr : K} (hg : M.g₀₀ ≠ 0)
    (hf : 0 < tf) (hr : 0 < tr) (h₁ : M.interval v tf = 0) (h₂ : M.interval (-v) tr = 0) :
    (tf - tr) / 2 = M.sync v := by
  have h₂' : M.interval v (-tr) = 0 := by rw [← interval_neg, neg_neg]; exact h₂
  have hne : tf ≠ -tr := by intro h; linarith
  have := (null_sum hg h₁ h₂' hne).2
  rwa [← sub_eq_add_neg] at this

/-- [proved-standard; formal-checked] **One leg to the future, one to the past**: for `g₀₀ < 0` and
`g_ij vⁱvʲ > 0`, two distinct null times along `v` have negative product. -/
theorem null_opposite {M : Stationary n K} {v : Fin n → K} {t₁ t₂ : K} (hg : M.g₀₀ < 0)
    (hc : 0 < v ⬝ᵥ (M.γ *ᵥ v)) (h₁ : M.interval v t₁ = 0) (h₂ : M.interval v t₂ = 0)
    (hne : t₁ ≠ t₂) : t₁ * t₂ < 0 := by
  have hp := null_prod hg.ne h₁ h₂ hne
  by_contra h
  push Not at h
  nlinarith

/-- [proved-standard; formal-checked] **The future null time is unique**: two positive null times
along `v` coincide. -/
theorem future_null_unique {M : Stationary n K} {v : Fin n → K} {t₁ t₂ : K} (hg : M.g₀₀ < 0)
    (hc : 0 < v ⬝ᵥ (M.γ *ᵥ v)) (h₁ : M.interval v t₁ = 0) (h₂ : M.interval v t₂ = 0)
    (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) : t₁ = t₂ := by
  by_contra hne
  have := null_opposite hg hc h₁ h₂ hne
  nlinarith

end Ordered

/-- [proved-standard; formal-checked] **Both legs exist over ℝ**: for `g₀₀ < 0` and
`g_ij vⁱvʲ > 0` there are a forward leg `δt₊ > 0` along `v` and a return leg `δt₋' > 0` along `−v`,
every null time along `v` is `δt₊` or `−δt₋'`, and `(δt₊ − δt₋')/2 = a(v)`. -/
theorem null_times_exist {M : Stationary n ℝ} {v : Fin n → ℝ} (hg : M.g₀₀ < 0)
    (hc : 0 < v ⬝ᵥ (M.γ *ᵥ v)) :
    ∃ tf tr : ℝ, 0 < tf ∧ 0 < tr ∧ M.interval v tf = 0 ∧ M.interval (-v) tr = 0 ∧
      (∀ t, M.interval v t = 0 ↔ t = tf ∨ t = -tr) ∧ (tf - tr) / 2 = M.sync v := by
  set b := M.g₀ ⬝ᵥ v with hb
  set c := v ⬝ᵥ (M.γ *ᵥ v) with hc'
  set g := M.g₀₀ with hg'
  have hD : 0 < b ^ 2 - g * c := by nlinarith [sq_nonneg b]
  set s := Real.sqrt (b ^ 2 - g * c) with hs'
  have hs2 : s ^ 2 = b ^ 2 - g * c := Real.sq_sqrt hD.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsb : b < s := by nlinarith
  have hsb' : -b < s := by nlinarith
  have hg0 : g ≠ 0 := hg.ne
  have root : ∀ t, g * t = -b - s ∨ g * t = -b + s → M.interval v t = 0 := by
    intro t ht
    have key : M.interval v t * g = (g * t) ^ 2 + 2 * b * (g * t) + g * c := by
      simp only [interval, ← hb, ← hc', ← hg']; ring
    have : M.interval v t * g = 0 := by
      rw [key]
      rcases ht with h | h <;> rw [h] <;> linear_combination hs2
    exact (mul_eq_zero.mp this).resolve_right hg0
  refine ⟨(-b - s) / g, (b - s) / g, div_pos_of_neg_of_neg (by linarith) hg,
    div_pos_of_neg_of_neg (by linarith) hg, ?_, ?_, ?_, ?_⟩
  · exact root _ (Or.inl (by field_simp))
  · rw [← interval_neg, neg_neg]
    exact root _ (Or.inr (by field_simp; ring))
  · intro t
    constructor
    · intro ht
      by_cases h1 : t = (-b - s) / g
      · exact Or.inl h1
      · right
        have hf : M.interval v ((-b - s) / g) = 0 := root _ (Or.inl (by field_simp))
        have hsum := (null_sum hg0 ht hf h1).1
        rw [← hb, ← hg'] at hsum
        field_simp
        field_simp at hsum
        linear_combination hsum
    · rintro (h | h) <;> rw [h]
      · exact root _ (Or.inl (by field_simp))
      · exact root _ (Or.inr (by field_simp; ring))
  · simp only [sync, ← hb, ← hg']
    field_simp
    ring

/-- [proved-standard; formal-checked] **A static metric has equal legs**: with `g₀ᵢ = 0` the forward
and return null times along `v` coincide. -/
theorem static_legs_equal {M : Stationary n ℝ} {v : Fin n → ℝ} {tf tr : ℝ} (h : M.g₀ = 0)
    (hg : M.g₀₀ ≠ 0) (hf : 0 < tf) (hr : 0 < tr) (h₁ : M.interval v tf = 0)
    (h₂ : M.interval (-v) tr = 0) : tf = tr := by
  have := einstein_offset hg hf hr h₁ h₂
  rw [sync_static M h] at this
  linarith

end Stationary

/-! ## 2. The synchronization clock on a cell complex -/

section Complex

variable {p q r n : ℕ}

open Stationary

/-- [definition] The displacement of passage `e` between placed sites: `Δx_e = Σᵥ (d₀)_{ev} xᵥ`. -/
def displacement (C : WeightedComplex p q r) (x : Fin p → Fin n → ℚ) (e : Fin q) : Fin n → ℚ :=
  ∑ v, C.d₀ e v • x v

/-- [definition] **The synchronization clock**: passage `e` reads Einstein's offset `a_e(Δx_e)` of
the stationary metric `M e` declared on it. -/
def syncClock (C : WeightedComplex p q r) (M : Fin q → Stationary n ℚ) (x : Fin p → Fin n → ℚ) :
    Fin q → ℚ := fun e => (M e).sync (displacement C x e)

variable (C : WeightedComplex p q r) (M : Fin q → Stationary n ℚ) (x : Fin p → Fin n → ℚ)

/-- [proved-derived; formal-checked] **The loop reading is the flux of `da`**: a cell boundary reads
the synchronization clock as the flux of its curvature through the cell. -/
theorem syncClock_cell_reading (c : Fin r → ℚ) :
    reading (syncClock C M x) (cellBoundary C c) = (C.d₁ *ᵥ syncClock C M x) ⬝ᵥ c :=
  cell_boundary_reading_is_curvature_flux C _ c

/-- [proved-derived; formal-checked] **The flux is production time**: every Hodge split's production
part reads the cell boundary as the same flux. -/
theorem syncClock_production (s : TimeSplit C (syncClock C M x)) (c : Fin r → ℚ) :
    reading s.production (cellBoundary C c) = (C.d₁ *ᵥ syncClock C M x) ⬝ᵥ c := by
  rw [← cell_boundary_reads_production C s, syncClock_cell_reading]

/-- [proved-derived; formal-checked] **The clock is closed exactly when every flux vanishes**, and
exactly when its production part is zero. -/
theorem syncClock_closed_iff (s : TimeSplit C (syncClock C M x)) :
    (syncClock C M x ∈ C.cocycles ↔ ∀ c, (C.d₁ *ᵥ syncClock C M x) ⬝ᵥ c = 0) ∧
      (syncClock C M x ∈ C.cocycles ↔ s.production = 0) := by
  refine ⟨?_, ?_⟩
  · rw [closed_iff_silent_on_cell_boundaries]
    exact forall_congr' fun c => by rw [syncClock_cell_reading]
  · rw [← not_iff_not, ← production_ne_zero_iff_not_closed C s]

/-- [proved-derived; formal-checked] **A static metric gives the zero clock**: with `g₀ᵢ = 0` on
every passage the clock vanishes, so it reads zero on every aeon. -/
theorem static_syncClock_zero (h : ∀ e, (M e).g₀ = 0) :
    syncClock C M x = 0 ∧ ∀ γ, reading (syncClock C M x) γ = 0 := by
  have h0 : syncClock C M x = 0 := funext fun e => sync_static (M e) (h e) _
  exact ⟨h0, fun γ => by simp [h0, reading]⟩

/-- [proved-derived; formal-checked] **A uniform metric gives an exact clock**: one stationary metric
on every passage makes the clock `d₀` of the sites' offsets `a(xᵥ)`, a re-charting of the sites'
clocks. -/
theorem uniform_syncClock_exact (N : Stationary n ℚ) :
    syncClock C (fun _ => N) x = C.d₀ *ᵥ fun v => N.sync (x v) := by
  funext e
  simp only [syncClock, displacement, Matrix.mulVec, dotProduct]
  have := map_sum N.syncMap (fun v => C.d₀ e v • x v) Finset.univ
  simp only [syncMap, LinearMap.coe_mk, AddHom.coe_mk] at this
  rw [this]
  exact Finset.sum_congr rfl fun v _ => sync_smul N _ _

/-- [proved-derived; formal-checked] **A uniform metric reads nothing on a cycle and has no production
time.** -/
theorem uniform_syncClock_silent (N : Stationary n ℚ) (s : TimeSplit C (syncClock C (fun _ => N) x)) :
    (∀ z, IsCycle C z → reading (syncClock C (fun _ => N) x) z = 0) ∧ s.production = 0 := by
  have hex : syncClock C (fun _ => N) x ∈ C.exactPart :=
    (C.mem_exactPart_iff _).mpr ⟨_, (uniform_syncClock_exact C x N).symm⟩
  refine ⟨(exact_iff_silent_on_cycles C _).mp hex, ?_⟩
  by_contra h
  exact (production_ne_zero_iff_not_closed C s).mp h (C.exactPart_le_cocycles hex)

end Complex

/-! ### On the house's square -/

/-- [proved-derived; formal-checked] On the square, passage `e` displaces by `x_t − x_s`. -/
theorem square_displacement {n : ℕ} (x : Fin 4 → Fin n → ℚ) (e : Fin 4) :
    displacement square x e = x (tgt e) - x (src e) := by
  fin_cases e <;>
    simp [displacement, square, unitMetric, squareIncidence, Fin.sum_univ_four, src, tgt] <;>
    abel

/-- [proved-derived; formal-checked] **On the square, the loop reads the flux through the face**, and
so does every Hodge split's production part, for any stationary metrics on the four passages. -/
theorem square_syncClock_reading {n : ℕ} (M : Fin 4 → Stationary n ℚ) (x : Fin 4 → Fin n → ℚ)
    (s : TimeSplit square (syncClock square M x)) :
    reading (syncClock square M x) squareLoop = (square.d₁ *ᵥ syncClock square M x) ⬝ᵥ ![1] ∧
      reading s.production squareLoop = (square.d₁ *ᵥ syncClock square M x) ⬝ᵥ ![1] := by
  rw [← squareLoop_bounds]
  exact ⟨syncClock_cell_reading square M x _, syncClock_production square M x s _⟩

/-- [proved-derived; formal-checked] **On the square, the clock is closed exactly when the loop reads
zero.** -/
theorem square_syncClock_closed_iff {n : ℕ} (M : Fin 4 → Stationary n ℚ) (x : Fin 4 → Fin n → ℚ) :
    syncClock square M x ∈ square.cocycles ↔ reading (syncClock square M x) squareLoop = 0 := by
  rw [← squareLoop_bounds, syncClock_cell_reading, WeightedComplex.mem_cocycles_iff]
  constructor
  · intro h; rw [h, zero_dotProduct]
  · intro h; funext i; fin_cases i; simpa [dotProduct] using h

/-- [definition] The rotating metric at first order in `Ω`, at the point `m`, in the Cartesian chart:
`g₀₀ = −1`, `g₀ = Ω(−y, x)` (so `g₀ᵢdxⁱ = Ω(x dy − y dx)`), `g_ij = δ_ij`. -/
def rotatingFirstOrder {K : Type*} [Field K] (Ω : K) (m : Fin 2 → K) : Stationary 2 K :=
  ⟨-1, ![-(Ω * m 1), Ω * m 0], 1⟩

/-- [definition] The rotating metric to all orders at `m` in the Cartesian chart:
`g₀₀ = −(1 − Ω²(x² + y²))`, `g₀ = Ω(−y, x)`, `g_ij = δ_ij`. -/
def rotatingCartesian {K : Type*} [Field K] (Ω : K) (m : Fin 2 → K) : Stationary 2 K :=
  ⟨-(1 - Ω ^ 2 * (m 0 ^ 2 + m 1 ^ 2)), ![-(Ω * m 1), Ω * m 0], 1⟩

/-- [proved-standard; formal-checked] To all orders each Cartesian synchronization gap is the
first-order one divided by `1 − Ω²|m|²`. -/
theorem rotatingCartesian_sync {K : Type*} [Field K] (Ω : K) (m v : Fin 2 → K) :
    (rotatingCartesian Ω m).sync v =
      (rotatingFirstOrder Ω m).sync v / (1 - Ω ^ 2 * (m 0 ^ 2 + m 1 ^ 2)) := by
  simp only [Stationary.sync, rotatingCartesian, rotatingFirstOrder]
  rw [neg_div_neg_eq, div_neg, div_one, neg_neg]

/-- [definition] The midpoint of passage `e` of the square. -/
def squareMid (x y : Fin 4 → ℚ) (e : Fin 4) : Fin 2 → ℚ :=
  (1 / 2 : ℚ) • (![x (src e), y (src e)] + ![x (tgt e), y (tgt e)])

/-- [proved-derived; formal-checked] **The owner's Sagnac form is the synchronization clock** of the
first-order rotating metric read at each passage's midpoint. -/
theorem sagnac_is_syncClock (Ω : ℚ) (x y : Fin 4 → ℚ) :
    sagnacForm Ω x y =
      syncClock square (fun e => rotatingFirstOrder Ω (squareMid x y e)) (fun v => ![x v, y v]) := by
  funext e
  simp only [syncClock, square_displacement, sagnacForm, Stationary.sync, rotatingFirstOrder,
    squareMid]
  simp [dotProduct, Fin.sum_univ_two]
  ring

/-- [proved-derived; formal-checked] **The Sagnac reading is the Einstein gap around the loop**: the
first-order synchronization clock reads `2ΩA`, the flux of its curvature. -/
theorem sagnac_sync_reading (Ω : ℚ) (x y : Fin 4 → ℚ) :
    reading (syncClock square (fun e => rotatingFirstOrder Ω (squareMid x y e)) fun v => ![x v, y v])
        squareLoop = 2 * Ω * shoelaceArea x y ∧
      (square.d₁ *ᵥ syncClock square (fun e => rotatingFirstOrder Ω (squareMid x y e))
        fun v => ![x v, y v]) ⬝ᵥ ![1] = 2 * Ω * shoelaceArea x y := by
  rw [← sagnac_is_syncClock]
  exact ⟨sagnac_reading Ω x y, sagnac_is_curvature_flux Ω x y⟩

/-! ## 3. The rotating frame, to all orders -/

/-- [definition] Minkowski space in the frame rotating at `Ω`, polar chart `(r, φ)`, `c = 1`:
`g₀₀ = −(1 − Ω²r²)`, `g₀ = (0, Ωr²)`, `g_ij = diag(1, r²)`. -/
def rotating (Ω r : ℝ) : Stationary 2 ℝ :=
  ⟨-(1 - Ω ^ 2 * r ^ 2), ![0, Ω * r ^ 2], !![1, 0; 0, r ^ 2]⟩

/-- [proved-standard; formal-checked] `a = Ωr² dφ/(1 − Ω²r²)`. -/
theorem rotating_sync (Ω r : ℝ) (v : Fin 2 → ℝ) :
    (rotating Ω r).sync v = Ω * r ^ 2 * v 1 / (1 - Ω ^ 2 * r ^ 2) := by
  simp only [Stationary.sync, rotating]
  rw [neg_div_neg_eq]
  simp [dotProduct, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] Inside the light cylinder `Ω²r² < 1`, `g₀₀ < 0`. -/
theorem rotating_lapse_neg {Ω r : ℝ} (h : Ω ^ 2 * r ^ 2 < 1) : (rotating Ω r).g₀₀ < 0 := by
  simp only [rotating]; linarith

/-- [proved-standard; formal-checked] **Einstein's offset on the rotating circle**: for `Ω²r² < 1`,
`r ≠ 0`, `δφ ≠ 0`, both legs along `(0, δφ)` exist and `(δt₊ − δt₋')/2 = Ωr²δφ/(1 − Ω²r²)`. -/
theorem rotating_einstein {Ω r δφ : ℝ} (h : Ω ^ 2 * r ^ 2 < 1) (hr : r ≠ 0) (hφ : δφ ≠ 0) :
    ∃ tf tr : ℝ, 0 < tf ∧ 0 < tr ∧ (rotating Ω r).interval ![0, δφ] tf = 0 ∧
      (rotating Ω r).interval (-![0, δφ]) tr = 0 ∧
      (tf - tr) / 2 = Ω * r ^ 2 * δφ / (1 - Ω ^ 2 * r ^ 2) := by
  have hc : 0 < ![0, δφ] ⬝ᵥ ((rotating Ω r).γ *ᵥ ![0, δφ]) := by
    simp [rotating, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    rw [show δφ * (r ^ 2 * δφ) = r ^ 2 * δφ ^ 2 by ring]
    positivity
  obtain ⟨tf, tr, hf, htr, h₁, h₂, -, hoff⟩ := Stationary.null_times_exist (rotating_lapse_neg h) hc
  refine ⟨tf, tr, hf, htr, h₁, h₂, ?_⟩
  rw [hoff, rotating_sync]
  simp

/-- [definition] The reading of a circle of constant `r`, traversed in increasing `φ`, for a metric
whose components do not depend on `φ`: the integral of `a(∂_φ)` over one turn. -/
def circleReading (M : Stationary 2 ℝ) : ℝ := ∫ _ in (0 : ℝ)..2 * π, M.sync ![0, 1]

/-- [proved-standard; formal-checked] A form constant along the circle reads `2π a_φ`. -/
theorem circleReading_eq (M : Stationary 2 ℝ) : circleReading M = 2 * π * M.sync ![0, 1] := by
  simp [circleReading, intervalIntegral.integral_const]

/-- [proved-standard; formal-checked] **The rotating circle reads `2πΩr²/(1 − Ω²r²)`.** -/
theorem rotating_circle_reading (Ω r : ℝ) :
    circleReading (rotating Ω r) = 2 * π * Ω * r ^ 2 / (1 - Ω ^ 2 * r ^ 2) := by
  rw [circleReading_eq, rotating_sync]
  simp
  ring

/-- [proved-standard; formal-checked] **The rim's own clock reads `2πΩr²/√(1 − Ω²r²)`**: the lapse
`N = √(1 − Ω²r²)` is constant on the circle, so the proper-time form `N a` reads `N` times the gap. -/
theorem rotating_circle_proper {Ω r : ℝ} (h : Ω ^ 2 * r ^ 2 < 1) :
    Real.sqrt (1 - Ω ^ 2 * r ^ 2) * circleReading (rotating Ω r) =
      2 * π * Ω * r ^ 2 / Real.sqrt (1 - Ω ^ 2 * r ^ 2) := by
  have hpos : 0 < 1 - Ω ^ 2 * r ^ 2 := by linarith
  have hs := Real.sq_sqrt hpos.le
  have hs0 := Real.sqrt_pos.mpr hpos
  rw [rotating_circle_reading]
  field_simp
  rw [hs]

/-- [proved-standard; formal-checked] With `A = πr²` the reading is `2ΩA/(1 − Ω²r²)`. -/
theorem rotating_circle_area (Ω r : ℝ) :
    circleReading (rotating Ω r) = 2 * Ω * (π * r ^ 2) / (1 - Ω ^ 2 * r ^ 2) := by
  rw [rotating_circle_reading]; ring

/-- [proved-standard; formal-checked] **The first order is the owner's `2ΩA`**: the all-orders
reading exceeds `2ΩA` by `2ΩA·Ω²r²/(1 − Ω²r²)`. -/
theorem rotating_first_order {Ω r : ℝ} (h : 1 - Ω ^ 2 * r ^ 2 ≠ 0) :
    circleReading (rotating Ω r) - 2 * Ω * (π * r ^ 2) =
      2 * Ω * (π * r ^ 2) * (Ω ^ 2 * r ^ 2) / (1 - Ω ^ 2 * r ^ 2) := by
  rw [rotating_circle_area]
  field_simp
  ring

/-- [proved-standard; formal-checked] For `Ω²r² ≤ 1/2` the excess over `2ΩA` is at most
`4πr⁴|Ω|³`. -/
theorem rotating_first_order_bound {Ω r : ℝ} (h : Ω ^ 2 * r ^ 2 ≤ 1 / 2) :
    |circleReading (rotating Ω r) - 2 * Ω * (π * r ^ 2)| ≤ 4 * π * r ^ 4 * |Ω| ^ 3 := by
  have hpos : 0 < 1 - Ω ^ 2 * r ^ 2 := by linarith
  rw [rotating_first_order hpos.ne']
  have e : 2 * Ω * (π * r ^ 2) * (Ω ^ 2 * r ^ 2) / (1 - Ω ^ 2 * r ^ 2) =
      Ω ^ 3 * (2 * π * r ^ 4 / (1 - Ω ^ 2 * r ^ 2)) := by ring
  rw [e, abs_mul, abs_pow, abs_of_nonneg (div_nonneg (by positivity) hpos.le)]
  have hinv : 2 * π * r ^ 4 / (1 - Ω ^ 2 * r ^ 2) ≤ 4 * π * r ^ 4 := by
    rw [div_le_iff₀ hpos]
    nlinarith [pi_pos, pow_nonneg (sq_nonneg r) 2, mul_nonneg pi_pos.le (pow_nonneg (sq_nonneg r) 2)]
  calc |Ω| ^ 3 * (2 * π * r ^ 4 / (1 - Ω ^ 2 * r ^ 2)) ≤ |Ω| ^ 3 * (4 * π * r ^ 4) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 4 * π * r ^ 4 * |Ω| ^ 3 := by ring

/-- [proved-standard; formal-checked] **The excess is `O(Ω³)`** as `Ω → 0`, at fixed `r`. -/
theorem rotating_first_order_isBigO (r : ℝ) :
    (fun Ω => circleReading (rotating Ω r) - 2 * Ω * (π * r ^ 2)) =O[𝓝 0] fun Ω => Ω ^ 3 := by
  have hc : Continuous fun Ω : ℝ => Ω ^ 2 * r ^ 2 := by fun_prop
  have hev : ∀ᶠ Ω in 𝓝 (0 : ℝ), Ω ^ 2 * r ^ 2 < 1 / 2 :=
    (hc.tendsto 0).eventually_lt_const (by norm_num)
  refine Asymptotics.IsBigO.of_bound (4 * π * r ^ 4) ?_
  filter_upwards [hev] with Ω hΩ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  exact rotating_first_order_bound hΩ.le

/-- [proved-standard; formal-checked] **The curvature of the rotating frame's `a`**:
`∂_ρ (Ωρ²/(1 − Ω²ρ²)) = 2Ωρ/(1 − Ω²ρ²)²` where `1 − Ω²ρ² ≠ 0`. -/
theorem rotating_curvature {Ω ρ : ℝ} (h : 1 - Ω ^ 2 * ρ ^ 2 ≠ 0) :
    HasDerivAt (fun ρ => Ω * ρ ^ 2 / (1 - Ω ^ 2 * ρ ^ 2)) (2 * Ω * ρ / (1 - Ω ^ 2 * ρ ^ 2) ^ 2) ρ := by
  have h1 : HasDerivAt (fun y => Ω * y ^ 2) (Ω * (2 * ρ)) ρ :=
    ((hasDerivAt_pow 2 ρ).const_mul Ω).congr_deriv (by norm_num)
  have h2 : HasDerivAt (fun y => 1 - Ω ^ 2 * y ^ 2) (-(Ω ^ 2 * (2 * ρ))) ρ :=
    (((hasDerivAt_pow 2 ρ).const_mul (Ω ^ 2)).const_sub 1).congr_deriv (by norm_num)
  refine (h1.div h2 h).congr_deriv ?_
  field_simp
  ring

/-- [proved-standard; formal-checked] **Stokes on the disk**: for `Ω²r² < 1` the flux of `da`
through the disk of radius `r`, `∫₀^{2π} ∫₀^r 2Ωρ/(1 − Ω²ρ²)² dρ dφ`, is the circle's reading. -/
theorem rotating_disk_flux {Ω r : ℝ} (h : Ω ^ 2 * r ^ 2 < 1) :
    ∫ _ in (0 : ℝ)..2 * π, ∫ ρ in (0 : ℝ)..r, 2 * Ω * ρ / (1 - Ω ^ 2 * ρ ^ 2) ^ 2 =
      circleReading (rotating Ω r) := by
  have hne : ∀ ρ ∈ Set.uIcc (0 : ℝ) r, 1 - Ω ^ 2 * ρ ^ 2 ≠ 0 := by
    intro ρ hρ
    have hρ2 : ρ ^ 2 ≤ r ^ 2 := by
      rcases Set.mem_uIcc.mp hρ with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> nlinarith
    have : Ω ^ 2 * ρ ^ 2 ≤ Ω ^ 2 * r ^ 2 := mul_le_mul_of_nonneg_left hρ2 (sq_nonneg Ω)
    exact (by linarith : (0 : ℝ) < 1 - Ω ^ 2 * ρ ^ 2).ne'
  have hinner : ∫ ρ in (0 : ℝ)..r, 2 * Ω * ρ / (1 - Ω ^ 2 * ρ ^ 2) ^ 2 =
      Ω * r ^ 2 / (1 - Ω ^ 2 * r ^ 2) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun ρ => Ω * ρ ^ 2 / (1 - Ω ^ 2 * ρ ^ 2)) (fun ρ hρ => rotating_curvature (hne ρ hρ))]
    · simp
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro ρ hρ
      exact pow_ne_zero 2 (hne ρ hρ)
  rw [hinner, intervalIntegral.integral_const, rotating_circle_reading]
  simp only [sub_zero, smul_eq_mul]
  ring

/-! ## 4. Frame dragging -/

section Axisymmetric

variable {K : Type*} [Field K]

/-- [definition] The metric of an axisymmetric stationary spacetime restricted to a circle of its
symmetry: `g₀₀`, `g₀φ`, `g_φφ` in the chart `(t, φ)`. -/
def circleMetric (g₀₀ g₀φ gφφ : K) : Stationary 1 K := ⟨g₀₀, ![g₀φ], !![gφφ]⟩

/-- [definition] The zero-angular-momentum observers' angular velocity `ω = −g₀φ/g_φφ`. -/
def zamoRate (g₀φ gφφ : K) : K := -g₀φ / gφφ

/-- [proved-standard; formal-checked] **Zero angular momentum**: the observer `u ∝ (1, w)` has
`u_φ ∝ g₀φ + g_φφ w = 0` exactly when `w = −g₀φ/g_φφ`. -/
theorem zamo_iff {g₀φ gφφ w : K} (h : gφφ ≠ 0) : g₀φ + gφφ * w = 0 ↔ w = zamoRate g₀φ gφφ := by
  unfold zamoRate
  constructor
  · intro hw; field_simp; linear_combination hw
  · intro hw; rw [hw]; field_simp; ring

/-- [proved-standard; formal-checked] **The static circle reads minus twice the drag rate times the
circumferential area over `−g₀₀`**: `2π a_φ = −2ω(πg_φφ)/(−g₀₀)`. -/
theorem circle_reading_zamo {g₀₀ g₀φ gφφ : ℝ} (h : gφφ ≠ 0) :
    2 * π * (circleMetric g₀₀ g₀φ gφφ).sync ![1] = -2 * zamoRate g₀φ gφφ * (π * gφφ) / -g₀₀ := by
  simp only [Stationary.sync, circleMetric, zamoRate]
  simp [dotProduct]
  field_simp

/-- [definition] The circle's metric in the chart rotating at `w`, `φ = φ' + wt`:
`g₀₀ + 2wg₀φ + w²g_φφ`, `g₀φ + wg_φφ`, `g_φφ`. -/
def corotate (w g₀₀ g₀φ gφφ : K) : Stationary 1 K :=
  circleMetric (g₀₀ + 2 * w * g₀φ + w ^ 2 * gφφ) (g₀φ + w * gφφ) gφφ

/-- [proved-standard; formal-checked] **The rotating chart keeps the interval**: `(δt, δφ')` in the
chart rotating at `w` has the interval of `(δt, δφ' + wδt)`. -/
theorem corotate_interval (w g₀₀ g₀φ gφφ δt δφ : K) :
    (corotate w g₀₀ g₀φ gφφ).interval ![δφ] δt =
      (circleMetric g₀₀ g₀φ gφφ).interval ![δφ + w * δt] δt := by
  simp [corotate, circleMetric, Stationary.interval, dotProduct, Matrix.mulVec]
  ring

/-- [proved-standard; formal-checked] **The zero-angular-momentum chart closes the circle**: rotating
the chart at `ω = −g₀φ/g_φφ` makes the circle's synchronization form vanish. -/
theorem zamo_closes {g₀₀ g₀φ gφφ : K} (h : gφφ ≠ 0) (v : Fin 1 → K) :
    (corotate (zamoRate g₀φ gφφ) g₀₀ g₀φ gφφ).sync v = 0 := by
  have : g₀φ + zamoRate g₀φ gφφ * gφφ = 0 := by rw [mul_comm]; exact (zamo_iff h).mpr rfl
  simp [corotate, circleMetric, Stationary.sync, dotProduct, this]

/-- [proved-standard; formal-checked] **Only that chart closes it**: where the rotated `g₀₀` is
nonzero, the chart rotating at `w` closes the circle exactly when `w = ω`. -/
theorem corotate_closes_iff {g₀₀ g₀φ gφφ w : K} (h : gφφ ≠ 0)
    (h₀ : g₀₀ + 2 * w * g₀φ + w ^ 2 * gφφ ≠ 0) :
    (corotate w g₀₀ g₀φ gφφ).sync ![1] = 0 ↔ w = zamoRate g₀φ gφφ := by
  rw [← zamo_iff h]
  simp [corotate, circleMetric, Stationary.sync, dotProduct, h₀]
  constructor <;> intro hw <;> linear_combination -hw

end Axisymmetric

/-- [proved-standard; formal-checked] **The rotating frame's circle is Minkowski's circle in the chart
rotating at `Ω`.** -/
theorem rotating_circle_is_corotated (Ω r : ℝ) :
    circleMetric (rotating Ω r).g₀₀ ((rotating Ω r).g₀ 1) ((rotating Ω r).γ 1 1) =
      corotate Ω (-1) 0 (r ^ 2) := by
  simp only [rotating, corotate, circleMetric]
  congr 1
  · ring
  · simp

/-- [definition] The weak-field Lense–Thirring metric in the equatorial plane, outside a body of mass
`M` and angular momentum `J`, chart `(r, φ)`: `g₀₀ = −(1 − 2M/r)`, `g₀ = (0, −2J/r)`,
`g_ij = diag((1 − 2M/r)⁻¹, r²)`. -/
def lenseThirring (M J r : ℝ) : Stationary 2 ℝ :=
  ⟨-(1 - 2 * M / r), ![0, -(2 * J / r)], !![(1 - 2 * M / r)⁻¹, 0; 0, r ^ 2]⟩

/-- [proved-standard; formal-checked] `a = −2J dφ/(r(1 − 2M/r))`. -/
theorem lenseThirring_sync (M J r : ℝ) (v : Fin 2 → ℝ) :
    (lenseThirring M J r).sync v = -(2 * J * v 1) / (r * (1 - 2 * M / r)) := by
  simp only [Stationary.sync, lenseThirring]
  simp [dotProduct, Fin.sum_univ_two]
  rw [show 2 * M / r - 1 = -(1 - 2 * M / r) by ring, div_neg, div_mul_eq_mul_div, div_div, neg_div]

/-- [proved-standard; formal-checked] **The equatorial circle reads `−4πJ/(r(1 − 2M/r))`.** -/
theorem lenseThirring_circle_reading (M J r : ℝ) :
    circleReading (lenseThirring M J r) = -(4 * π * J) / (r * (1 - 2 * M / r)) := by
  rw [circleReading_eq, lenseThirring_sync]
  simp
  ring

/-- [proved-standard; formal-checked] **The drag rate** `ω = −g₀φ/g_φφ = 2J/r³`. -/
theorem lenseThirring_zamo (J r : ℝ) : zamoRate (-(2 * J / r)) (r ^ 2) = 2 * J / r ^ 3 := by
  unfold zamoRate; ring

/-- [proved-standard; formal-checked] The circle reads `−2ω(πr²)/(1 − 2M/r)` with `ω = 2J/r³`. -/
theorem lenseThirring_reading_zamo {M J r : ℝ} (hr : r ≠ 0) :
    circleReading (lenseThirring M J r) = -2 * (2 * J / r ^ 3) * (π * r ^ 2) / (1 - 2 * M / r) := by
  rw [lenseThirring_circle_reading]
  field_simp
  ring

/-- [proved-standard; formal-checked] In the isotropic chart, `g_φφ = (1 + 2M/r)r²`, the drag rate is
`2J/(r³(1 + 2M/r))`, which differs from `2J/r³` by `(2J/r³)(2M/r)/(1 + 2M/r)`, of order `JM`. -/
theorem lenseThirring_isotropic_zamo {M J r : ℝ} (hr : r ≠ 0) (hM : 1 + 2 * M / r ≠ 0) :
    zamoRate (-(2 * J / r)) ((1 + 2 * M / r) * r ^ 2) = 2 * J / (r ^ 3 * (1 + 2 * M / r)) ∧
      2 * J / r ^ 3 - 2 * J / (r ^ 3 * (1 + 2 * M / r)) =
        2 * J / r ^ 3 * (2 * M / r) / (1 + 2 * M / r) := by
  refine ⟨?_, ?_⟩
  · unfold zamoRate; field_simp
  · have h' : r + 2 * M ≠ 0 := by
      intro h0; apply hM; field_simp; linarith
    field_simp
    ring

/-- [proved-standard; formal-checked] **Einstein's offset on the equatorial circle**: for `r > 2M`,
`r > 0`, `δφ ≠ 0`, both legs along `(0, δφ)` exist and their offset is `−2Jδφ/(r(1 − 2M/r))`. -/
theorem lenseThirring_einstein {M J r δφ : ℝ} (hr : 0 < r) (hM : 2 * M < r) (hφ : δφ ≠ 0) :
    ∃ tf tr : ℝ, 0 < tf ∧ 0 < tr ∧ (lenseThirring M J r).interval ![0, δφ] tf = 0 ∧
      (lenseThirring M J r).interval (-![0, δφ]) tr = 0 ∧
      (tf - tr) / 2 = -(2 * J * δφ) / (r * (1 - 2 * M / r)) := by
  have hlap : 0 < 1 - 2 * M / r := by
    rw [sub_pos, div_lt_one hr]; exact hM
  have hc : 0 < ![0, δφ] ⬝ᵥ ((lenseThirring M J r).γ *ᵥ ![0, δφ]) := by
    simp [lenseThirring, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    rw [show δφ * (r ^ 2 * δφ) = r ^ 2 * δφ ^ 2 by ring]
    positivity
  obtain ⟨tf, tr, hf, htr, h₁, h₂, -, hoff⟩ :=
    Stationary.null_times_exist (M := lenseThirring M J r) (by simp [lenseThirring]; linarith) hc
  refine ⟨tf, tr, hf, htr, h₁, h₂, ?_⟩
  rw [hoff, lenseThirring_sync]
  simp

/-- [proved-standard; formal-checked] For `r ≠ 0` the circle reads `−4πJ/(r − 2M)`. -/
theorem lenseThirring_reading_eq {M J r : ℝ} (hr : r ≠ 0) :
    circleReading (lenseThirring M J r) = -(4 * π * J) / (r - 2 * M) := by
  rw [lenseThirring_circle_reading]
  congr 1
  field_simp

/-- [proved-standard; formal-checked] **Two circles differ by the flux of `da` through the annulus**:
for radii outside `2M` and `0`, `reading(r₂) − reading(r₁) = ∫₀^{2π} ∫_{r₁}^{r₂} 2J/(ρ − 2M)²`. -/
theorem lenseThirring_annulus_flux {M J r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) (hM₁ : 2 * M < r₁)
    (hM₂ : 2 * M < r₂) :
    circleReading (lenseThirring M J r₂) - circleReading (lenseThirring M J r₁) =
      ∫ _ in (0 : ℝ)..2 * π, ∫ ρ in r₁..r₂, 2 * J / (ρ - 2 * M) ^ 2 := by
  have hne : ∀ ρ ∈ Set.uIcc r₁ r₂, ρ - 2 * M ≠ 0 := by
    intro ρ hρ
    rcases Set.mem_uIcc.mp hρ with ⟨a, b⟩ | ⟨a, b⟩ <;> intro h0 <;> linarith
  have hd : ∀ ρ ∈ Set.uIcc r₁ r₂,
      HasDerivAt (fun ρ => -(2 * J) / (ρ - 2 * M)) (2 * J / (ρ - 2 * M) ^ 2) ρ := by
    intro ρ hρ
    have h1 : HasDerivAt (fun y => y - 2 * M) 1 ρ := (hasDerivAt_id' ρ).sub_const _
    refine ((hasDerivAt_const ρ (-(2 * J))).div h1 (hne ρ hρ)).congr_deriv ?_
    ring
  have hinner : ∫ ρ in r₁..r₂, 2 * J / (ρ - 2 * M) ^ 2 =
      -(2 * J) / (r₂ - 2 * M) - -(2 * J) / (r₁ - 2 * M) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro ρ hρ
    exact pow_ne_zero 2 (hne ρ hρ)
  rw [hinner, intervalIntegral.integral_const, lenseThirring_reading_eq h₂.ne',
    lenseThirring_reading_eq h₁.ne']
  simp only [sub_zero, smul_eq_mul]
  ring

/-- [proved-standard; formal-checked] **Far out the reading vanishes**: as `r → ∞` the equatorial
circle's reading tends to zero. -/
theorem lenseThirring_reading_tendsto (M J : ℝ) :
    Tendsto (fun r => circleReading (lenseThirring M J r)) atTop (𝓝 0) := by
  have hsub : Tendsto (fun r : ℝ => r - 2 * M) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(2 * M)) tendsto_id
  have h : Tendsto (fun r : ℝ => -(4 * π * J) / (r - 2 * M)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsub
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  rw [lenseThirring_reading_eq hr.ne']

/-- [proved-standard; formal-checked] **A rigid rotation removes the rotating frame's shift on every
circle**: at `w = −Ω` the rotated shift `Ωr² + wr²` vanishes for every `r`. -/
theorem rotating_shift_rigid (Ω : ℝ) : ∀ r : ℝ, (rotating Ω r).g₀ 1 + -Ω * (rotating Ω r).γ 1 1 = 0 := by
  intro r; simp [rotating]

/-- [proved-standard; formal-checked] **No rigid rotation removes the Lense–Thirring shift on two
circles**: for `J ≠ 0` and distinct positive radii, no `w` zeroes `−2J/r + wr²` at both. -/
theorem lenseThirring_shift_not_rigid {M J r₁ r₂ : ℝ} (hJ : J ≠ 0) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (hne : r₁ ≠ r₂) :
    ¬ ∃ w : ℝ, (lenseThirring M J r₁).g₀ 1 + w * (lenseThirring M J r₁).γ 1 1 = 0 ∧
      (lenseThirring M J r₂).g₀ 1 + w * (lenseThirring M J r₂).γ 1 1 = 0 := by
  rintro ⟨w, hw₁, hw₂⟩
  simp [lenseThirring] at hw₁ hw₂
  have e : ∀ {ρ : ℝ}, 0 < ρ → -(2 * J / ρ) + w * ρ ^ 2 = 0 → w * ρ ^ 3 = 2 * J := by
    intro ρ hρ hw
    field_simp at hw
    linear_combination hw
  have e₁ := e h₁ hw₁
  have e₂ := e h₂ hw₂
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hJ (by linarith)
  have h3 : r₁ ^ 3 = r₂ ^ 3 := mul_left_cancel₀ hw0 (e₁.trans e₂.symm)
  exact hne ((pow_left_inj₀ h₁.le h₂.le (by norm_num)).mp h3)

end Holonics.Physics.Spacetime.FrameDraggingClock
