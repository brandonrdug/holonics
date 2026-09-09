import ElementaryHolonics.Millennium.Crossings
import ElementaryHolonics.Millennium.RealizedMillenniumForms

/-!
# A circulation-weighted receiver on addressed crossing populations

[definition] This owner forms `Σ_i,j linkingNet(p,i,j) Γ_i Γ_j` on the actual finite crossing
population. It proves how insertion/deletion and a cancelling signed pair change that form.
The coefficient is the declared signed diagram-crossing count. Identifying it with physical
helicity requires the actual velocity/vorticity fields, Gauss-linking normalization, spatial
embedding, framing/internal twist and boundary assumptions.

[proved-derived] `helicity_cons` and `helicity_reconnect_single` are exact changes of this finite
form under the named population operation. `helicity_insertCancellingPair` is invariance under
that particular cancelling move. These are not proofs that every diagram move is an ambient
isotopy or a physical reconnection. Diagram writhe alone is not an ambient-isotopy invariant;
self-linking and physical helicity require their additional geometric data.

[proved-derived] `helicity_borromean` exhibits a nonempty crossing table invisible to the
quadratic receiver; a changed hand separates it. `helicityForm_not_positive` shows the finite
form is indefinite. The topology of a spatial Borromean embedding and an actual fluid evolution
are separate source realizations, not conclusions from that table.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HelicityAsLinking

open Soma.Holonics.Millennium.Crossings
open Soma.Holonics.Millennium.RealizedMillenniumForms
open Soma.Holonics.Millennium.MillenniumCoupling
open Finset

/-- Meeting is symmetric in the two strands. -/
theorem meets_symm (c : Crossing) (i j : Strand) : meets c i j = meets c j i := by
  simp only [meets]
  exact Bool.or_comm _ _

/-- The pairwise linking reading is symmetric. -/
theorem linkingNet_symm (p : Population) (i j : Strand) : linkingNet p i j = linkingNet p j i := by
  unfold linkingNet
  congr 1
  apply List.filter_congr
  intro c _
  rw [meets_symm]

/-- [definition] The linking array of a population, over `ℝ`. -/
def linkingArray (p : Population) : Fin 3 → Fin 3 → ℝ := fun i j => (linkingNet p i j : ℝ)

theorem linkingArray_symm (p : Population) : ∀ i j, linkingArray p i j = linkingArray p j i := by
  intro i j
  simp only [linkingArray, linkingNet_symm p i j]

/-- The declared circulation-weighted signed-crossing form. A physical helicity interpretation
additionally needs its geometry, normalization and framing. -/
def helicity (p : Population) (Γ : Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, linkingArray p i j * Γ i * Γ j

/-- [definition] The helicity form: the linking array as a receiver form on the circulation
carrier. -/
def helicityForm (p : Population) : ReceiverForm (Carrier 3) :=
  matrixForm (linkingArray p) (linkingArray_symm p)

theorem helicityForm_reading (p : Population) (Γ : Carrier 3) :
    (helicityForm p).B Γ Γ = helicity p Γ.ofLp := by
  rw [helicityForm, matrixForm_reading]
  rfl

/-! ## The reconnection jump -/

theorem net_cons (c : Crossing) (p : Population) : net (c :: p) = handSign c.hand + net p := by
  simp [net]

/-- One crossing moves the pairwise reading by its sign exactly on the pairs it meets. -/
theorem linkingNet_cons (c : Crossing) (p : Population) (i j : Strand) :
    linkingNet (c :: p) i j =
      linkingNet p i j + if meets c i j = true then handSign c.hand else 0 := by
  unfold linkingNet
  rw [List.filter_cons]
  by_cases h : meets c i j = true
  · rw [if_pos h, net_cons, if_pos h]
    ring
  · rw [if_neg h, if_neg h, add_zero]

/-- [proved-derived; formal-checked] **Adding one crossing changes the helicity by its sign times
the pairing of the circulations it meets.** -/
theorem helicity_cons (c : Crossing) (p : Population) (Γ : Fin 3 → ℝ) :
    helicity (c :: p) Γ =
      helicity p Γ +
        (handSign c.hand : ℝ) * ∑ i, ∑ j, (if meets c i j = true then Γ i * Γ j else 0) := by
  unfold helicity linkingArray
  simp only [linkingNet_cons, Int.cast_add, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · push_cast
    ring
  · push_cast
    ring

/-- The pairing a crossing between strands `o` and `u` meets: `2 Γₒ Γᵤ` for a linking crossing,
`Γₒ²` for a self-crossing (the writhe term). -/
theorem crossing_pairing (o u : Strand) (s : ℕ) (h : CrossingHand) (Γ : Fin 3 → ℝ) :
    (∑ i, ∑ j, (if meets ⟨o, u, s, h⟩ i j = true then Γ i * Γ j else 0)) =
      if o = u then Γ o * Γ o else 2 * (Γ o * Γ u) := by
  fin_cases o <;> fin_cases u <;> simp [meets, Fin.sum_univ_three] <;> ring

/-- [proved-derived; formal-checked] **The reconnection jump.**  A crossing between distinct
strands `o, u` with hand `s`, alone at its site, is removed by `reconnect`, and the helicity
drops by `s · 2 Γₒ Γᵤ`: Moffatt's law that helicity changes only through reconnection, and by
exactly the linking the reconnection destroys. -/
theorem helicity_reconnect_single (o u : Strand) (hou : o ≠ u) (site : ℕ) (h : CrossingHand)
    (q : Population) (hq : ∀ c ∈ q, c.site ≠ site) (Γ : Fin 3 → ℝ) :
    helicity (reconnect (⟨o, u, site, h⟩ :: q) site) Γ =
      helicity (⟨o, u, site, h⟩ :: q) Γ - (handSign h : ℝ) * (2 * (Γ o * Γ u)) := by
  have hrec : reconnect (⟨o, u, site, h⟩ :: q) site = q := by
    unfold reconnect
    rw [List.filter_cons]
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    apply List.filter_eq_self.mpr
    intro c hc
    have := hq c hc
    simp [this]
  rw [hrec, helicity_cons, crossing_pairing, if_neg hou]
  ring

/-! ## Invariance under the representational move -/

/-- [proved-derived; formal-checked] Inserting a cancelling pair leaves every helicity unchanged:
helicity reads the configuration, not the diagram. -/
theorem helicity_insertCancellingPair (p : Population) (i j : Strand) (s : ℕ) (Γ : Fin 3 → ℝ) :
    helicity (insertCancellingPair p i j s) Γ = helicity p Γ := by
  unfold helicity linkingArray
  simp only [theInsertedPairIsInvisibleToEveryLinkingReading]

/-! ## Blind to Borromean linking, and the hand is the sign -/

/-- [proved-derived; formal-checked] **Helicity is blind to Borromean linking**: every circulation
returns `0` on the six-crossing Borromean table. -/
theorem helicity_borromean (Γ : Fin 3 → ℝ) : helicity borromeanTable Γ = 0 := by
  unfold helicity linkingArray
  simp [theLinkingReadingsVanishWhileSixCrossingsStand.1]

/-- The linking readings of the flipped table: `2` on the pair `{0, 1}` in both orders, `0`
elsewhere. -/
theorem variant_linkingNet :
    linkingNet borromeanSameHandVariant 0 1 = 2 ∧ linkingNet borromeanSameHandVariant 1 0 = 2 ∧
    linkingNet borromeanSameHandVariant 0 0 = 0 ∧ linkingNet borromeanSameHandVariant 1 1 = 0 ∧
    linkingNet borromeanSameHandVariant 2 2 = 0 ∧ linkingNet borromeanSameHandVariant 0 2 = 0 ∧
    linkingNet borromeanSameHandVariant 2 0 = 0 ∧ linkingNet borromeanSameHandVariant 1 2 = 0 ∧
    linkingNet borromeanSameHandVariant 2 1 = 0 := by
  decide

/-- The flipped table's helicity in closed form: `4 Γ₀ Γ₁`. -/
theorem helicity_variant (Γ : Fin 3 → ℝ) :
    helicity borromeanSameHandVariant Γ = 4 * (Γ 0 * Γ 1) := by
  obtain ⟨h01, h10, h00, h11, h22, h02, h20, h12, h21⟩ := variant_linkingNet
  unfold helicity linkingArray
  rw [Fin.sum_univ_three]
  simp only [Fin.sum_univ_three, h01, h10, h00, h11, h22, h02, h20, h12, h21]
  push_cast
  ring

/-- [proved-derived; formal-checked] One flipped hand and the helicity is `4` at unit circulations,
while the Borromean table returned `0` at every circulation: the hands decide the reading. -/
theorem helicity_variant_unit : helicity borromeanSameHandVariant (fun _ => 1) = 4 := by
  rw [helicity_variant]
  norm_num

/-- The circulation `(1, 1, 0)`. -/
def parallel : Carrier 3 := WithLp.toLp 2 ![1, 1, 0]

/-- The circulation `(1, −1, 0)`. -/
def opposed : Carrier 3 := WithLp.toLp 2 ![1, -1, 0]

/-- [proved-derived; formal-checked] **The hand is the sign of the reading**: the helicity form of
the flipped table returns `4` on parallel circulations and `−4` on opposed ones.  Helicity is an
indefinite receiver form — the phase face of the flow — where the Stokes dissipation is coercive. -/
theorem helicityForm_variant_signs :
    (helicityForm borromeanSameHandVariant).B parallel parallel = 4 ∧
    (helicityForm borromeanSameHandVariant).B opposed opposed = -4 := by
  constructor
  · rw [helicityForm_reading, helicity_variant]
    simp [parallel]
  · rw [helicityForm_reading, helicity_variant]
    simp [opposed]

/-- [proved-derived; formal-checked] The helicity form is not positive: a reading of `−4` exists. -/
theorem helicityForm_not_positive : ¬ (helicityForm borromeanSameHandVariant).IsPositive := by
  intro hpos
  have := hpos opposed
  rw [helicityForm_variant_signs.2] at this
  norm_num at this

section Audit

#print axioms helicity_cons
#print axioms helicity_reconnect_single
#print axioms helicity_insertCancellingPair
#print axioms helicity_borromean
#print axioms helicityForm_variant_signs
#print axioms helicityForm_not_positive

end Audit

end Soma.Holonics.Millennium.HelicityAsLinking
