import Holonics.HNN.Keys
import Holonics.HNN.LeakyCapacity

/-!
# Source capacity after phase re-keying

At a fixed opening, phase re-keying may change every current phase while preserving
its winding (`Keys.rekey_keeps_winding`). If `M` cells have been ingested since
that opening and every admitted cell advances ring `g` by at most `d_g`, then
the current lift lies in the winding window
`[d_g W_g, d_g (W_g + M) + (d_g - 1)]`, with exactly `d_g (M + 1)` values.

The open source histogram still records only its own `n` injected cells. Its
source-local endpoint phase and accumulated ticks remain independent of the
shared current after a zero-time re-key or sibling ingestion, contributing
`d_g (b_g n + 1)` per source ring. The histogram, pair histogram and held
suffix reuse `RangedMoment`'s source-count box at `n`. The reading has one fixed
true profile, opening, source partition and declared `n,M`; it is not a union
with the unreframed reading. This bound does not count adaptive constitutions
or key laws.
-/

noncomputable section

namespace Holonics.HNN.Moment

namespace SourceDecl

variable {A : Type*} (D : SourceDecl A)

/-- The exact interval of lift representatives with winding in `[W, W + M]`.
The residue is free in `[0, period - 1]`. -/
def windingWindow (D : SourceDecl A) (d W M : ℕ) : Finset ℕ :=
  Finset.Icc (d * W) (d * (W + M) + (d - 1))

theorem mem_windingWindow_of_div_mod {d W M t : ℕ} (hd : 0 < d)
    (hwind : W ≤ t / d ∧ t / d ≤ W + M) (hphase : t % d < d) :
    t ∈ D.windingWindow d W M := by
  rw [D.windingWindow, Finset.mem_Icc]
  have hdecomp : t = d * (t / d) + t % d := by
    calc
      t = t % d + d * (t / d) := (Nat.mod_add_div t d).symm
      _ = d * (t / d) + t % d := Nat.add_comm _ _
  have hlow := Nat.mul_le_mul_left d hwind.1
  have hhigh := Nat.mul_le_mul_left d hwind.2
  constructor <;> rw [hdecomp] <;> omega

/-- Re-keying preserves membership in the same ambient winding window. This
applies repeatedly because the conclusion supplies the next re-key's winding
premise, while `rekey_keeps_winding` leaves source bins and held cells alone. -/
theorem rekey_mem_windingWindow [hne : ∀ g, NeZero (D.period g)]
    (g key W M : ℕ) (hkey : key < D.period g) (s : D.StreamState)
    (hwind : W ≤ (s.lift g) / D.period g ∧
      (s.lift g) / D.period g ≤ W + M) :
    (Keys.rekey g key s).lift g ∈ D.windingWindow (D.period g) W M := by
  have hr := Keys.rekey_keeps_winding (D := D) g key hkey s
  have hd : 0 < D.period g := Nat.pos_of_ne_zero (hne g).out
  exact D.mem_windingWindow_of_div_mod hd
    ⟨by rw [hr.1]; exact hwind.1, by rw [hr.1]; exact hwind.2⟩
    (by rw [hr.2.1]; exact hkey)

theorem card_windingWindow {d : ℕ} (hd : 0 < d) (W M : ℕ) :
    (D.windingWindow d W M).card = d * (M + 1) := by
  rw [D.windingWindow, Nat.card_Icc]
  have hsum : d * (W + M) + (d - 1) + 1 = d * W + d * (M + 1) := by
    have hd' : d ≠ 0 := by omega
    cases d with
    | zero => contradiction
    | succ d => simp [Nat.mul_add, Nat.add_mul]; omega
  omega

/-- The carrier for a source's own `n` injections together with the shared
current's `G` ambient lift coordinates. `Persist 0` retains the existing
source bins, offset bins and held suffix while omitting its source-clock lift;
the ambient lift is represented separately at the `M`-cell count. -/
abbrev ReframedPersist (G : ℕ) :=
  ((Fin G → ℕ) × ((g : D.sources) → Fin (D.period g.1) × ℕ)) × D.Persist 0

/-- Source-local endpoint phases and accumulated ticks remain fixed to this
source passage's own `n` injections, independently of the shared current. -/
def sourceProfileBox [Fintype A] [DecidableEq A]
    (rate : ℕ → ℕ) (n : ℕ) :
    Finset ((g : D.sources) → Fin (D.period g.1) × ℕ) :=
  Fintype.piFinset fun g : D.sources =>
    (Finset.univ : Finset (Fin (D.period g.1))) ×ˢ Finset.Icc 0 (rate g * n)

/-- The joint ambient-lift and source-histogram box. `W` is the opening winding
profile; `M` counts all ingested cells since that opening; `n` counts this
source's own injections. -/
def reframedBox [Fintype A] [DecidableEq A]
    [hne : ∀ g, NeZero (D.period g)] (G : ℕ) (W : Fin G → ℕ)
    (M n : ℕ) (rate : ℕ → ℕ) :
    Finset (D.ReframedPersist G) :=
  ((Fintype.piFinset fun g : Fin G => D.windingWindow (D.period g) (W g) M) ×ˢ
    D.sourceProfileBox rate n) ×ˢ D.boxWith D.period (fun _ => 0) 0 n

/-- The consumer's separate checks place the shared current, source-local
profile and original source partition in the joint box. In particular, the
source partition still uses its original `n` and opening. -/
theorem reframed_mem_box [Fintype A] [DecidableEq A]
    [hne : ∀ g, NeZero (D.period g)]
    (G : ℕ) (W : Fin G → ℕ) (M n : ℕ) (rate : ℕ → ℕ)
    (current : Fin G → ℕ) (profile : (g : D.sources) → Fin (D.period g.1) × ℕ)
    (source : D.Persist 0)
    (hcurrent : ∀ g, current g ∈ D.windingWindow (D.period g) (W g) M)
    (hprofile : profile ∈ D.sourceProfileBox rate n)
    (hsource : source ∈ D.boxWith D.period (fun _ => 0) 0 n) :
    ((current, profile), source) ∈ D.reframedBox G W M n rate := by
  exact Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr hcurrent, hprofile⟩, hsource⟩

/-- The exact count of the ambient lift factor. -/
theorem card_reframedLiftBox [Fintype A] [DecidableEq A]
    [hne : ∀ g, NeZero (D.period g)] (G : ℕ)
    (W : Fin G → ℕ) (M : ℕ) :
    (Fintype.piFinset fun g : Fin G => D.windingWindow (D.period g) (W g) M).card =
      ∏ g : Fin G, (D.period g * (M + 1)) := by
  simp only [Fintype.card_piFinset, Finset.card_univ]
  exact Finset.prod_congr rfl fun g _ =>
    D.card_windingWindow (Nat.pos_of_ne_zero (hne g).out) _ _

theorem card_sourceProfileBox [Fintype A] [DecidableEq A]
    [hne : ∀ g, NeZero (D.period g)] (rate : ℕ → ℕ) (n : ℕ) :
    (D.sourceProfileBox rate n).card =
      ∏ g : D.sources, (D.period g.1 * (rate g * n + 1)) := by
  simp [sourceProfileBox, Nat.card_Icc]

/-- Reframed source capacity: ambient current lifts range over `d_g (M + 1)`
states per declared ring, while source histogram and suffix factors depend only
on the source's own `n` injections. -/
theorem card_reframedBox_le [Fintype A] [DecidableEq A]
    [hne : ∀ g, NeZero (D.period g)] [Nonempty A]
    (G : ℕ) (W : Fin G → ℕ) (M n : ℕ) (rate : ℕ → ℕ) :
    (D.reframedBox G W M n rate).card ≤
      ((∏ g : Fin G, (D.period g * (M + 1))) *
        (∏ g : D.sources, (D.period g.1 * (rate g * n + 1)))) *
          D.capacityBoundWith D.period 0 (Fintype.card A) n := by
  rw [reframedBox, Finset.card_product, Finset.card_product,
    D.card_reframedLiftBox, D.card_sourceProfileBox]
  calc
    _ = ((∏ g : Fin G, D.period g * (M + 1)) *
        (∏ g : D.sources, (D.period g.1 * (rate g * n + 1)))) *
          (D.boxWith D.period (fun _ => 0) 0 n).card := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (D.card_boxWith_le D.period (fun _ => 0) 0 n)

/-- Leaky coordinates multiply the reframed source-state count by their exact
`(n U + 1)` box factors. -/
theorem card_reframedBox_withCoordinates_le [Fintype A] [DecidableEq A]
    [hne : ∀ g, NeZero (D.period g)] [Nonempty A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ℕ) (W : Fin G → ℕ) (M n : ℕ) (rate : ℕ → ℕ)
    (U : ι → ℕ) :
    ((D.reframedBox G W M n rate ×ˢ LeakyCapacity.coordinateBox U n).card) ≤
      (((∏ g : Fin G, (D.period g * (M + 1))) *
        (∏ g : D.sources, (D.period g.1 * (rate g * n + 1)))) *
          D.capacityBoundWith D.period 0 (Fintype.card A) n) *
            (∏ i : ι, (n * U i + 1)) := by
  exact LeakyCapacity.joint_card_bound (D.reframedBox G W M n rate)
    (D.card_reframedBox_le G W M n rate) U n

/-- One admitted advance of at most one period cannot cross more than one
winding section. -/
theorem winding_step_range {d t t' : ℕ} (hd : 0 < d)
    (hadvance : t ≤ t' ∧ t' ≤ t + d) :
    t / d ≤ t' / d ∧ t' / d ≤ t / d + 1 := by
  constructor
  · exact Nat.div_le_div_right hadvance.1
  · rw [Nat.div_le_iff_le_mul_add_pred hd]
    have hdecomp : t = d * (t / d) + t % d := by
      calc
        t = t % d + d * (t / d) := (Nat.mod_add_div t d).symm
        _ = d * (t / d) + t % d := Nat.add_comm _ _
    have hphase := Nat.mod_lt t hd
    rw [Nat.mul_add]
    omega

#print axioms rekey_mem_windingWindow
#print axioms card_reframedBox_le
#print axioms card_reframedBox_withCoordinates_le
#print axioms winding_step_range

end SourceDecl

end Holonics.HNN.Moment
