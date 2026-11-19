import HolonicsResearch.Objects.RetentionSeries

/-!
# The classes of the minimal retention on cycles, on the diamond, and under the Joule law

[definition] Object 8 of `docs/ELEMENTARY_OBJECTS.md` with `Foundation/Standing.lean`: retention
is the future-sufficient quotient of the present, never a record of what shaped it. Source: #410's
box "The explicit classes of the square law's minimal retention on a general weighted graph (the
orbit structure of deposition on projective classes beyond two parallel edges), and for other
deposition laws", the `[open]` paragraph of `Objects/Retention` (#552 characterizes the classes as
future agreement of the constitution). Part done in #1031 by `HolonicsResearch/Objects/RetentionClasses`
(forests, the `m`-edge bundle under the square and Joule laws, a pendant edge) and in #1033 by
`HolonicsResearch/Objects/RetentionSeries` (two bundles in series, the triangle under the square
law), whose "What is not claimed" left graphs with several cycles that do not share their two ends,
cycles of four or more edges, the Joule law on the triangle, and laws beyond the square and Joule
laws; its record is `2026-11-19_LEGENDRES_LOCAL_MOVES_FIX_GAMMA_TWO_BY_RIGIDITY_…_IN_LEAN`. Atlas
rows read: `deposition.triangle-retains-constitution`, `deposition.series-bundles-product-retention`,
`deposition.bundle-minimal-retention`, `deposition.joule-bundle-projective-retention`,
`deposition.solve-sees-projective-class`, `deposition.projective-class-not-retention`,
`deposition.minimal-retention-general`, `deposition.constitution-not-minimal` and
`ph.triangle-witness`. Every statement holds for every solver, including one that reads the flux
record to choose its gauge, as in the owners.

What is proved.

1. [proved-derived; formal-checked] **A stroke under a dilation of the constitution.** On every
   incidence `cΘ` and `Θ` carry one flux under every solvable source (`strokeFlux`,
   `strokeFlux_scale`, from the owner's `observeConstitution_scale`), and every drop on `cΘ` is the
   drop on `Θ` over `c` (`strokeDrop`, `strokeDrop_scale`). A square-law stroke deposits `j²`
   (`square_step_apply`) and is in proportion to the constitution (`SquareProportional`) iff every
   edge dissipates one power `j_e (dφ)_e` (`squareProportional_iff_equal_power`). A Joule-law stroke
   deposits `Γ_e = Θ_e (dφ)_e²` on `Θ` and `Γ_e/c` on `cΘ` (`joule_step_apply`,
   `joule_step_scale_apply`), and `Γ` is proportional to `Θ` iff the drops share one magnitude
   (`EqualDrops`, `joule_deposit_proportional_iff`).
2. [proved-derived; formal-checked] **The abstract lemma.** Say the present reads the projective
   class when two constitutions that agree on every source are projectively equal
   (`ReadsProjectiveClass`); it then reads that class and nothing more
   (`observe_iff_projectivelyEqual_of_reads`), and under any law future agreement keeps it after
   every history (`projectivelyEqual_of_futureAgreement`). On such a medium, if every constitution
   admits a source whose square-law stroke is out of proportion, two presents share every future
   under the square law iff their constitutions are equal (`square_futureAgreement_iff_of_reads`;
   read on two unit strokes that no constitution takes both in proportion,
   `square_futureAgreement_iff_of_two_strokes`: the triangle's argument, factored). If every
   constitution admits a source whose drops do not share one magnitude, the same holds under the
   Joule law (`joule_futureAgreement_iff_of_reads`). Where the classes are the constitutions every
   lawful retention separates distinct constitutions, so the owner's `constitutionStanding` is the
   minimal retention (`constitution_factors_through_every_standing_of_iff`), and a stroke after
   which the stepped constitutions are not projectively equal is read by a present source
   (`exists_separating_source`).
3. [proved-derived; formal-checked] **Two tests on the incidence alone.** The cycle test: if two
   constitutions agree on every source, then for every potential `ψ` and every cycle `z`
   (`dᵀ z = 0`) the weighted drops `(Θ_e/Θ'_e)(dψ)_e` are orthogonal to `z`, being the drops of the
   solve on `Θ'` of the source that `ψ` draws on `Θ` (`potentialSource`, `solves_potentialSource`,
   `cycle_test`); so if every weighting that passes the test is constant, the present reads the
   projective class (`readsProjectiveClass_of_weights`). A potential that drops across one edge and
   not across another (`SeparatesEdges`) draws, on every constitution, a stroke out of proportion
   under both laws, since one edge carries no flux and another does (`stroke_of_separatesEdges`);
   on every medium that passes both tests the square law's and the Joule law's classes are the
   constitutions (`square_futureAgreement_iff_of_separates`,
   `joule_futureAgreement_iff_of_separates`). The bundle passes neither the second test
   (`bundle_not_separatesEdges`) nor the Joule stroke premise: every stroke there has one drop
   (`bundle_equalDrops`), which is why its Joule classes are the projective classes.
4. [proved-derived; formal-checked] **The cycle of `N` nodes.** On `N` nodes in a ring with edge
   `e` from node `e` to node `e + 1 (mod N)` (`cycleGraph`, `cycleGraph_mulVec`,
   `cycleGraph_transpose_mulVec`, `cycleGraph_row_sum`, `sum_ite_arrive`, `sum_shift`), the drops
   of every potential close round the cycle (`cycleGraph_loop`), so the drop across an edge is minus
   the far path's drops (`cycle_drop_eq_neg_far`); every closed edge vector is a drop
   (`cycle_exact`); a flux that balances the source and closes the loop is carried by a solve
   (`cycle_solves_of_flux`); and a source admits a balance exactly when its total charge is zero
   (`cycle_solvable_iff`). The unit source across edge `k` (`unitAcross`, the edge's own row)
   sends `R_far/R` through edge `k` and `r_k/R` round the far path, against the edges'
   orientation, with `r = 1/Θ`, `R = Σ_f r_f` (`resTotal`, `resTotal_pos`) and `R_far = R − r_k`
   (`cycleUnitFlux`, `cycle_unit_solves`, `cycle_unit_solvable`, `cycle_unit_flux`,
   `strokeFlux_unitAcross`, `strokeDrop_unitAcross`, `cycleUnitFlux_self`, `cycleUnitFlux_of_ne`).
   The cycle test with the node potentials and the one cycle `(1, …, 1)` gives `w_(i−1) = w_i` at
   every node, so the present reads the projective class and nothing more, on every `N`
   (`cycle_readsProjectiveClass`, `cycle_observe_iff_projectivelyEqual`,
   `eq_zero_of_shift_invariant`).
5. [proved-derived; formal-checked] **On every cycle of three or more nodes the constitution is
   the minimal retention under both laws.** The stroke across `k` in proportion forces one
   conductance off `k` and `(R − r_k)²/Θ_k = r_k²/Θ_f` (`cycle_unit_squareProportional_forces`);
   the constitutions it takes in proportion are exactly those with `Θ_f = (N − 1)² Θ_k` on every
   other edge (`cycle_unit_squareProportional_iff`, `far_resistance_of_uniform`; at `N = 3` the
   owner's `(1, 4, 4)`). A second edge `l`, with a third edge `m` (`exists_third`), gives
   `Θ_k = Θ_l` and then `(N − 1)² = 1`, so no constitution takes two unit strokes across distinct
   edges in proportion (`cycle_not_two_strokes_proportional`), and under the square law two
   presents share every future iff their constitutions are equal
   (`cycle_square_futureAgreement_iff`, `cycle_square_constitution_factors_through_every_standing`).
   Under the Joule law the stroke across `k` drops `r_k R_far/R` across its edge and `r_k r_f/R`
   (against the orientation) across a far edge `f`, and `R_far ≥ r_f + r_m > r_f`
   (`three_le_resTotal`), so no unit stroke has one drop magnitude
   (`cycle_unit_not_equalDrops`) and the classes are again the constitutions
   (`cycle_joule_futureAgreement_iff`, `cycle_joule_constitution_factors_through_every_standing`).
6. [proved-derived; formal-checked] **The triangle through the abstract lemma, and the Joule law
   on it.** The owner's statement is recovered from the abstract lemma with the owner's
   `triangle_observe_iff_projectivelyEqual` and `not_both_strokes_proportional`
   (`triangle_readsProjectiveClass`, `triangle_strokeFlux`,
   `triangle_square_futureAgreement_iff_of_reads`). The unit stroke `0 → 1` drops `(Θ_b + Θ_c)/P`
   across `a` and `−Θ_c/P` across `b` (`triangle_strokeDrop`, `triangle_unit_not_equalDrops`), so
   under the Joule law two presents share every future iff their constitutions are equal
   (`triangle_joule_futureAgreement_iff`,
   `triangle_joule_constitution_factors_through_every_standing`). What differs from the bundle: on
   the bundle every edge sees one drop, the Joule law moves the constitution only along its
   dilation, and the projective class is the minimal retention; on a cycle through three nodes the
   source's own edge drops the far path's whole drop, so no unit stroke has one drop magnitude, a
   Joule unit stroke moves the constitution off its dilation, and the total is retained with the
   class.
7. [proved-derived; formal-checked] **The diamond, two triangles on one shared edge.** On four
   nodes with the edges `0 → 1`, `1 → 3`, `0 → 2`, `2 → 3` and the shared `0 → 3` (`diamond`,
   `diamond_mulVec`), the cycle test with the two triangles' cycles (`diamondCycleLeft`,
   `diamondCycleRight`, `diamond_cycleLeft`, `diamond_cycleRight`) and the node potentials at `0`,
   `1` and `2` reads the projective class (`diamond_readsProjectiveClass`), and the node potential
   at `1` drops across `0 → 1` and not across `0 → 2` (`diamond_separatesEdges`). Under both laws
   two presents share every future iff their constitutions are equal, and the constitution is the
   minimal retention (`diamond_square_futureAgreement_iff`, `diamond_joule_futureAgreement_iff`,
   `diamond_square_constitution_factors_through_every_standing`,
   `diamond_joule_constitution_factors_through_every_standing`).
8. [counterexample; formal-checked] **Witness** (`cycle4_witness`, with `uniformOn`,
   `uniformOn_two`, `cycleUnitFlux_uniform`, `cycle_square_unit_uniform`,
   `cycle_joule_unit_uniform`). On the four-cycle `(1, 1, 1, 1)` and `(2, 2, 2, 2)` agree on every
   present source. The unit stroke across edge `0`, which on a uniform ring of `N` nodes sends
   `(N − 1)/N` across its edge and `1/N` round the far path, leaves `(25, 17, 17, 17)/16` against
   `(41, 33, 33, 33)/16` under the square law and `(25, 17, 17, 17)/16` against
   `(73, 65, 65, 65)/32` under the Joule law, not projectively equal, so some source then separates
   them; on the bundle of four edges the two share every future under both laws (the owners'
   `uniform_futureAgreement` and `joule_bundle_futureAgreement_iff`).

What is not claimed.

- A general weighted graph. The abstract lemma and the two tests reduce the classes to two
  properties of the incidence: every weighting that passes the cycle test is constant (checked here
  on every cycle and on the diamond; the owner's two reads give it on the triangle), and every
  constitution admits a stroke out of proportion (checked by unit strokes on every cycle of three or
  more nodes and on the triangle, by a separating potential on the diamond). They are not derived
  for every graph whose cycles do not all share their two ends (a wheel, a grid, a complete graph).
  The box stays part done.
- Deposition laws other than the square and Joule laws: the abstract lemmas use how each law meets
  a dilation (`j²` unchanged, `Θ (dφ)²` divided by `c`); a law `Γ_e(j, g)` in general is not
  treated.
- A converse: the two premises are not shown to be needed. The bundle fails the stroke premise and
  keeps its uniform class, and a forest fails the projective premise and retains nothing; no
  statement says that every medium failing one of them has classes coarser than its constitutions.
- The diamond's solve (a balance for every source of zero charge) and its unit fluxes are not
  written: its classes need only the two tests.
- Convergence or the long-run orbit of repeated deposition.
- `MinimalRetention.IsMinimal` is not restated: the kernel, the lawful standing (the owner's
  `constitutionStanding`) and leastness are given in `Objects/Retention`'s form, as in the owners.

The computational object is the helical pair interaction read as a conducting contact, as in the
owners: each edge is a pair contact between two node potentials, its slip the drop `(dφ)_e`, its
current the flux `Θ_e (dφ)_e`, and deposition changes the contact's material by what crossed it. On
a cycle the source's contact and the far path's contacts carry one loop current, so the slip across
the source's contact is the far path's whole slip and the split reads every contact's material. A
dilation of the material leaves every current and divides every slip, the square law then deposits
one `j²` on both and the Joule law `Γ/c` against `Γ`, and on a cycle of three or more nodes some
unit stroke's deposit leaves the dilation under each law, so the minimal retention keeps the whole
material. Of the winding guide's six general
objects this touches the cell holonomy (the cycle test reads the material through the cycles, the
ring's one cycle and the diamond's two triangles, and the loop law is the drops' holonomy closing to
zero round each), faces and placement (the present face is conserved under dilation of the material
and reads exactly the projective class; a stroke's face of power per contact under the square law,
or of slip per contact under the Joule law, decides whether it moves the class), and the tube
(histories as ordered words of admitted sources, each step a transfer of the constitution). The
helix, the pair's modular address and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Objects.RetentionCycles

open Holonics
open Holonics.Objects.Deposition
open Holonics.Objects.RetentionClasses
open Holonics.Objects.RetentionSeries
open Holonics.Foundation.Standing
open Holonics.Foundation.CausalRelevance.NonLinear
open Holonics.Foundation.Chronology
open Matrix

/-! ## 1. A stroke under a dilation of the constitution -/

section Stroke

variable {p q : ℕ}

/-- [definition] **The stroke's flux**: the flux of the canonical solve of the source `σ` on `Θ`. -/
def strokeFlux (d : Matrix (Fin q) (Fin p) ℚ) (σ : Fin p → ℚ) (Θ : Constitution q) : Fin q → ℚ :=
  flux d Θ (canonicalSolve d Θ σ)

/-- [definition] **The stroke's drop**: the drop `dφ` of the canonical solve. -/
def strokeDrop (d : Matrix (Fin q) (Fin p) ℚ) (σ : Fin p → ℚ) (Θ : Constitution q) : Fin q → ℚ :=
  d *ᵥ canonicalSolve d Θ σ

/-- [proved-derived; formal-checked] The stroke's flux is the conductance times its drop. -/
theorem strokeFlux_apply (d : Matrix (Fin q) (Fin p) ℚ) (σ : Fin p → ℚ) (Θ : Constitution q)
    (e : Fin q) : strokeFlux d σ Θ e = Θ.1 e * strokeDrop d σ Θ e := rfl

/-- [proved-derived; formal-checked] Every solve carries the stroke's flux. -/
theorem strokeFlux_of_solves {d : Matrix (Fin q) (Fin p) ℚ} {Θ : Constitution q}
    {φ σ : Fin p → ℚ} (h : Solves d Θ φ σ) : strokeFlux d σ Θ = flux d Θ φ :=
  flux_unique (canonicalSolve_solves ⟨φ, h⟩) h

/-- [proved-derived; formal-checked] Every solve has the stroke's drop. -/
theorem strokeDrop_of_solves {d : Matrix (Fin q) (Fin p) ℚ} {Θ : Constitution q}
    {φ σ : Fin p → ℚ} (h : Solves d Θ φ σ) : strokeDrop d σ Θ = d *ᵥ φ :=
  drop_unique (canonicalSolve_solves ⟨φ, h⟩) h

/-- [proved-derived; formal-checked] A solvable source observes the stroke's flux. -/
theorem observeConstitution_of_solvable {d : Matrix (Fin q) (Fin p) ℚ} {Θ : Constitution q}
    {σ : Fin p → ℚ} (hs : ∃ φ, Solves d Θ φ σ) :
    observeConstitution d σ Θ = some (strokeFlux d σ Θ) := by
  rw [observeConstitution, if_pos hs]
  rfl

/-- [proved-derived; formal-checked] A source admits a balance on `cΘ` iff it admits one on `Θ`. -/
theorem solvable_scale_iff (d : Matrix (Fin q) (Fin p) ℚ) {c : ℚ} (hc : 0 < c)
    (Θ : Constitution q) (σ : Fin p → ℚ) :
    (∃ φ, Solves d (Retention.scaleConstitution c hc Θ) φ σ) ↔ ∃ φ, Solves d Θ φ σ := by
  constructor
  · rintro ⟨φ, h⟩
    exact ⟨c • φ, (Retention.solves_scale_iff d hc Θ φ σ).mp h⟩
  · rintro ⟨φ, h⟩
    refine ⟨c⁻¹ • φ, (Retention.solves_scale_iff d hc Θ _ σ).mpr ?_⟩
    rwa [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

/-- [proved-derived; formal-checked] **`cΘ` and `Θ` carry one flux** under every solvable source
(the owner's `observeConstitution_scale`). -/
theorem strokeFlux_scale {d : Matrix (Fin q) (Fin p) ℚ} {c : ℚ} (hc : 0 < c)
    {Θ : Constitution q} {σ : Fin p → ℚ} (hs : ∃ φ, Solves d Θ φ σ) :
    strokeFlux d σ (Retention.scaleConstitution c hc Θ) = strokeFlux d σ Θ := by
  have h := Retention.observeConstitution_scale d hc Θ σ
  rw [observeConstitution_of_solvable ((solvable_scale_iff d hc Θ σ).mpr hs),
    observeConstitution_of_solvable hs] at h
  exact Option.some.inj h

/-- [proved-derived; formal-checked] **On `cΘ` every drop is the drop on `Θ` over `c`.** -/
theorem strokeDrop_scale {d : Matrix (Fin q) (Fin p) ℚ} {c : ℚ} (hc : 0 < c)
    {Θ : Constitution q} {σ : Fin p → ℚ} (hs : ∃ φ, Solves d Θ φ σ) (e : Fin q) :
    strokeDrop d σ (Retention.scaleConstitution c hc Θ) e = strokeDrop d σ Θ e / c := by
  have h := congrFun (strokeFlux_scale hc hs) e
  rw [strokeFlux_apply, strokeFlux_apply] at h
  change c * Θ.1 e * strokeDrop d σ (Retention.scaleConstitution c hc Θ) e =
    Θ.1 e * strokeDrop d σ Θ e at h
  rw [eq_div_iff hc.ne']
  apply mul_left_cancel₀ (Θ.2 e).ne'
  linear_combination h

/-- [proved-derived; formal-checked] **One square-law stroke**: `Θ'_e = Θ_e + j_e²`. -/
theorem square_step_apply {d : Matrix (Fin q) (Fin p) ℚ} {Θ : Constitution q} {σ : Fin p → ℚ}
    (hs : ∃ φ, Solves d Θ φ σ) (e : Fin q) :
    (stepConstitution (squareLawOn q) d σ Θ).1 e = Θ.1 e + strokeFlux d σ Θ e ^ 2 := by
  rw [stepConstitution, if_pos hs]
  rfl

/-- [proved-derived; formal-checked] **One Joule-law stroke**: `Θ'_e = Θ_e + j_e (dφ)_e =
Θ_e + Θ_e (dφ)_e²`. -/
theorem joule_step_apply {d : Matrix (Fin q) (Fin p) ℚ} {Θ : Constitution q} {σ : Fin p → ℚ}
    (hs : ∃ φ, Solves d Θ φ σ) (e : Fin q) :
    (stepConstitution (jouleLawOn q) d σ Θ).1 e = Θ.1 e + Θ.1 e * strokeDrop d σ Θ e ^ 2 := by
  rw [stepConstitution, if_pos hs]
  change Θ.1 e + flux d Θ (canonicalSolve d Θ σ) e * (d *ᵥ canonicalSolve d Θ σ) e = _
  rw [flux, strokeDrop]
  ring

/-- [proved-derived; formal-checked] **A Joule stroke on `cΘ` deposits `Γ/c` where it deposits `Γ`
on `Θ`**: one flux, every drop over `c`. -/
theorem joule_step_scale_apply {d : Matrix (Fin q) (Fin p) ℚ} {c : ℚ} (hc : 0 < c)
    {Θ : Constitution q} {σ : Fin p → ℚ} (hs : ∃ φ, Solves d Θ φ σ) (e : Fin q) :
    (stepConstitution (jouleLawOn q) d σ (Retention.scaleConstitution c hc Θ)).1 e =
      c * Θ.1 e + Θ.1 e * strokeDrop d σ Θ e ^ 2 / c := by
  rw [joule_step_apply ((solvable_scale_iff d hc Θ σ).mpr hs), strokeDrop_scale hc hs]
  change c * Θ.1 e + c * Θ.1 e * (strokeDrop d σ Θ e / c) ^ 2 = _
  field_simp

/-- [definition] **A square-law stroke in proportion**: the squared flux `j²` is a multiple of
the constitution, `Θ_e j_f² = Θ_f j_e²` on every pair of edges. -/
def SquareProportional (d : Matrix (Fin q) (Fin p) ℚ) (σ : Fin p → ℚ) (Θ : Constitution q) :
    Prop :=
  ∀ e f, Θ.1 e * strokeFlux d σ Θ f ^ 2 = Θ.1 f * strokeFlux d σ Θ e ^ 2

/-- [definition] **A stroke with one drop magnitude**: `(dφ)_e² = (dφ)_f²` on every pair of edges. -/
def EqualDrops (d : Matrix (Fin q) (Fin p) ℚ) (σ : Fin p → ℚ) (Θ : Constitution q) : Prop :=
  ∀ e f, strokeDrop d σ Θ e ^ 2 = strokeDrop d σ Θ f ^ 2

/-- [proved-derived; formal-checked] **A square-law stroke is in proportion iff every edge
dissipates one power** `j_e (dφ)_e = Θ_e (dφ)_e²`. -/
theorem squareProportional_iff_equal_power (d : Matrix (Fin q) (Fin p) ℚ) (σ : Fin p → ℚ)
    (Θ : Constitution q) :
    SquareProportional d σ Θ ↔ ∀ e f, strokeFlux d σ Θ e * strokeDrop d σ Θ e =
      strokeFlux d σ Θ f * strokeDrop d σ Θ f := by
  simp only [SquareProportional, strokeFlux_apply]
  constructor
  · intro h e f
    have hz : Θ.1 e * Θ.1 f * (Θ.1 e * strokeDrop d σ Θ e ^ 2 - Θ.1 f * strokeDrop d σ Θ f ^ 2) =
        0 := by linear_combination -(h e f)
    rcases mul_eq_zero.mp hz with h0 | h0
    · exact absurd h0 (mul_pos (Θ.2 e) (Θ.2 f)).ne'
    · linear_combination h0
  · intro h e f
    linear_combination (-(Θ.1 e * Θ.1 f)) * h e f

/-- [proved-derived; formal-checked] **A Joule-law stroke deposits in proportion to the
constitution iff all its drops have one magnitude**: `Γ_e = Θ_e (dφ)_e²`. -/
theorem joule_deposit_proportional_iff (d : Matrix (Fin q) (Fin p) ℚ) (σ : Fin p → ℚ)
    (Θ : Constitution q) :
    (∀ e f, Θ.1 e * (Θ.1 f * strokeDrop d σ Θ f ^ 2) =
      Θ.1 f * (Θ.1 e * strokeDrop d σ Θ e ^ 2)) ↔ EqualDrops d σ Θ := by
  constructor
  · intro h e f
    have hz : Θ.1 e * Θ.1 f * (strokeDrop d σ Θ e ^ 2 - strokeDrop d σ Θ f ^ 2) = 0 := by
      linear_combination -(h e f)
    rcases mul_eq_zero.mp hz with h0 | h0
    · exact absurd h0 (mul_pos (Θ.2 e) (Θ.2 f)).ne'
    · linear_combination h0
  · intro h e f
    linear_combination (-(Θ.1 e * Θ.1 f)) * h e f

end Stroke

/-! ## 2. The abstract lemma: a present that reads the projective class, and a stroke out of
proportion -/

section Abstract

variable {p q : ℕ}

/-- [definition] **The present observation reads the projective class**: two constitutions that
agree on every source are projectively equal. -/
def ReadsProjectiveClass (d : Matrix (Fin q) (Fin p) ℚ) : Prop :=
  ∀ Θ Θ' : Constitution q, (∀ σ, observeConstitution d σ Θ = observeConstitution d σ Θ') →
    ProjectivelyEqual Θ Θ'

/-- [proved-derived; formal-checked] Where the present reads the projective class, it reads that
class and nothing more (the owner's `observeConstitution_scale`). -/
theorem observe_iff_projectivelyEqual_of_reads {d : Matrix (Fin q) (Fin p) ℚ}
    (hobs : ReadsProjectiveClass d) (Θ Θ' : Constitution q) :
    (∀ σ, observeConstitution d σ Θ = observeConstitution d σ Θ') ↔ ProjectivelyEqual Θ Θ' := by
  refine ⟨hobs Θ Θ', ?_⟩
  rintro ⟨c, hc, rfl⟩ σ
  rw [Retention.observeConstitution_scale]

/-- [proved-derived; formal-checked] **Future agreement keeps the projective class after every
history**, under any law, on every medium whose present reads that class. -/
theorem projectivelyEqual_of_futureAgreement {d : Matrix (Fin q) (Fin p) ℚ}
    (hobs : ReadsProjectiveClass d) (L : DepositionLaw q) (S : Solver d)
    {left right : DepositState q} (h : futureAgreement (observe S) (step L S) left right)
    (word : List (Fin p → ℚ)) :
    ProjectivelyEqual (transportWord (stepConstitution L d) word left.constitution)
      (transportWord (stepConstitution L d) word right.constitution) := by
  refine hobs _ _ fun σ => ?_
  have hw := h σ word
  rwa [observe_eq_observeConstitution, observe_eq_observeConstitution, transportWord_constitution,
    transportWord_constitution] at hw

/-- [proved-derived; formal-checked] Scaling by one is the identity. -/
theorem scaleConstitution_one_eq {Θ : Constitution q} {c : ℚ} (hc : 0 < c) (hc1 : c = 1) :
    Retention.scaleConstitution c hc Θ = Θ := by
  apply Subtype.ext
  funext e
  simp [Retention.scaleConstitution, hc1]

/-- [proved-derived; formal-checked] **The abstract lemma for the square law.** On a medium whose
present reads the projective class and where every constitution has an admitted source whose
stroke is out of proportion, two presents share every future iff their constitutions are equal:
`cΘ` and `Θ` carry one flux `j`, so `cΘ + j²` is a multiple of `Θ + j²` with `c ≠ 1` only when
`j²` is proportional to `Θ`. -/
theorem square_futureAgreement_iff_of_reads {d : Matrix (Fin q) (Fin p) ℚ}
    (hobs : ReadsProjectiveClass d)
    (hstroke : ∀ Θ : Constitution q, ∃ σ, (∃ φ, Solves d Θ φ σ) ∧ ¬ SquareProportional d σ Θ)
    (S : Solver d) (left right : DepositState q) :
    futureAgreement (observe S) (step (squareLawOn q) S) left right ↔
      left.constitution = right.constitution := by
  constructor
  · intro h
    obtain ⟨c, hc, hΘ⟩ := projectivelyEqual_of_futureAgreement hobs _ S h []
    simp only [transportWord_nil] at hΘ
    by_cases hc1 : c = 1
    · rw [hΘ, scaleConstitution_one_eq hc hc1]
    · obtain ⟨σ, hs, hnot⟩ := hstroke left.constitution
      refine (hnot fun e f => ?_).elim
      obtain ⟨k, hk, hkΘ⟩ := projectivelyEqual_of_futureAgreement hobs _ S h [σ]
      simp only [transportWord_cons, transportWord_nil, hΘ] at hkΘ
      refine proportional_of_scaled_stroke (J := fun e => strokeFlux d σ left.constitution e ^ 2)
        left.constitution.2 hc1 (k := k) (fun e => ?_) e f
      have he : (stepConstitution (squareLawOn q) d σ
          (Retention.scaleConstitution c hc left.constitution)).1 e =
            k * (stepConstitution (squareLawOn q) d σ left.constitution).1 e :=
        congrArg (fun Θ : Constitution q => Θ.1 e) hkΘ
      rw [square_step_apply ((solvable_scale_iff d hc _ σ).mpr hs), square_step_apply hs,
        strokeFlux_scale hc hs] at he
      exact he
  · exact equal_constitution_equal_future _ S

/-- [proved-derived; formal-checked] **The abstract lemma for the Joule law.** On a medium whose
present reads the projective class and where every constitution has an admitted source whose
drops do not all share one magnitude, two presents share every future iff their constitutions are
equal: a stroke deposits `Γ/c` on `cΘ` where it deposits `Γ` on `Θ`, so the two stay projectively
equal with `c ≠ 1` only when `Γ_e = Θ_e (dφ)_e²` is proportional to `Θ`. -/
theorem joule_futureAgreement_iff_of_reads {d : Matrix (Fin q) (Fin p) ℚ}
    (hobs : ReadsProjectiveClass d)
    (hstroke : ∀ Θ : Constitution q, ∃ σ, (∃ φ, Solves d Θ φ σ) ∧ ¬ EqualDrops d σ Θ)
    (S : Solver d) (left right : DepositState q) :
    futureAgreement (observe S) (step (jouleLawOn q) S) left right ↔
      left.constitution = right.constitution := by
  constructor
  · intro h
    obtain ⟨c, hc, hΘ⟩ := projectivelyEqual_of_futureAgreement hobs _ S h []
    simp only [transportWord_nil] at hΘ
    by_cases hc1 : c = 1
    · rw [hΘ, scaleConstitution_one_eq hc hc1]
    · obtain ⟨σ, hs, hnot⟩ := hstroke left.constitution
      refine (hnot ((joule_deposit_proportional_iff d σ _).mp fun e f => ?_)).elim
      obtain ⟨k, hk, hkΘ⟩ := projectivelyEqual_of_futureAgreement hobs _ S h [σ]
      simp only [transportWord_cons, transportWord_nil, hΘ] at hkΘ
      have hc2 : c ^ 2 ≠ 1 := by
        intro h2
        have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
        rcases mul_eq_zero.mp h3 with h0 | h0
        · exact hc1 (by linarith)
        · linarith
      refine proportional_of_scaled_stroke
        (J := fun e => left.constitution.1 e * strokeDrop d σ left.constitution e ^ 2)
        left.constitution.2 hc2 (k := k * c) (fun e => ?_) e f
      have he : (stepConstitution (jouleLawOn q) d σ
          (Retention.scaleConstitution c hc left.constitution)).1 e =
            k * (stepConstitution (jouleLawOn q) d σ left.constitution).1 e :=
        congrArg (fun Θ : Constitution q => Θ.1 e) hkΘ
      rw [joule_step_scale_apply hc hs, joule_step_apply hs] at he
      have h2 : left.constitution.1 e * strokeDrop d σ left.constitution e ^ 2 / c * c =
          left.constitution.1 e * strokeDrop d σ left.constitution e ^ 2 := by
        field_simp
      linear_combination c * he - h2
  · exact equal_constitution_equal_future _ S

/-- [proved-derived; formal-checked] **The abstract lemma read on two unit strokes**: where every
constitution admits both strokes and none takes both in proportion, the square law's classes are
the constitutions. -/
theorem square_futureAgreement_iff_of_two_strokes {d : Matrix (Fin q) (Fin p) ℚ}
    (hobs : ReadsProjectiveClass d) (σ₁ σ₂ : Fin p → ℚ)
    (hs₁ : ∀ Θ : Constitution q, ∃ φ, Solves d Θ φ σ₁)
    (hs₂ : ∀ Θ : Constitution q, ∃ φ, Solves d Θ φ σ₂)
    (hboth : ∀ Θ : Constitution q, SquareProportional d σ₁ Θ → SquareProportional d σ₂ Θ → False)
    (S : Solver d) (left right : DepositState q) :
    futureAgreement (observe S) (step (squareLawOn q) S) left right ↔
      left.constitution = right.constitution := by
  refine square_futureAgreement_iff_of_reads hobs (fun Θ => ?_) S left right
  by_cases h₁ : SquareProportional d σ₁ Θ
  · exact ⟨σ₂, hs₂ Θ, hboth Θ h₁⟩
  · exact ⟨σ₁, hs₁ Θ, h₁⟩

/-- [proved-derived; formal-checked] **Where the classes are the constitutions, the constitution is
the least lawful retention**: every retention carrying a `StandingLaw` for the medium separates
every two distinct constitutions (the owner's `constitutionStanding` is lawful, so it is minimal). -/
theorem constitution_factors_through_every_standing_of_iff {d : Matrix (Fin q) (Fin p) ℚ}
    {L : DepositionLaw q} {S : Solver d}
    (hiff : ∀ left right : DepositState q,
      futureAgreement (observe S) (step L S) left right ↔ left.constitution = right.constitution)
    {Retained : Type*}
    (M : StandingLaw (Fin p → ℚ) (Fin p → ℚ) (DepositState q) Retained (Option (Fin q → ℚ)))
    (htransport : M.transport = step L S) (hobserve : M.observe = observe S)
    {left right : DepositState q} (h : M.retain left = M.retain right) :
    left.constitution = right.constitution := by
  have hagree := M.futureAgreement_of_retain_eq h
  rw [htransport, hobserve] at hagree
  exact (hiff left right).mp hagree

/-- [proved-derived; formal-checked] **One stroke after which the stepped constitutions are not
projectively equal is read by a present source**: some source then separates the two presents. -/
theorem exists_separating_source {d : Matrix (Fin q) (Fin p) ℚ} (hobs : ReadsProjectiveClass d)
    (L : DepositionLaw q) (S : Solver d) (σ : Fin p → ℚ) (left right : DepositState q)
    (h : ¬ ProjectivelyEqual (stepConstitution L d σ left.constitution)
      (stepConstitution L d σ right.constitution)) :
    ∃ τ, observe S τ (step L S σ left) ≠ observe S τ (step L S σ right) := by
  by_contra hall
  push Not at hall
  refine h (hobs _ _ fun τ => ?_)
  have hτ := hall τ
  rwa [observe_eq_observeConstitution, observe_eq_observeConstitution, step_constitution,
    step_constitution] at hτ

end Abstract

/-! ## 3. Two tests a graph can pass: the cycle test and a potential that leaves one edge still -/

section Tests

variable {p q : ℕ}

/-- [definition] **The source a potential draws**: `σ = dᵀ (Θ · dψ)`, which `ψ` solves. -/
def potentialSource (d : Matrix (Fin q) (Fin p) ℚ) (Θ : Constitution q) (ψ : Fin p → ℚ) :
    Fin p → ℚ :=
  dᵀ *ᵥ flux d Θ ψ

/-- [proved-derived; formal-checked] A potential solves the source it draws. -/
theorem solves_potentialSource (d : Matrix (Fin q) (Fin p) ℚ) (Θ : Constitution q)
    (ψ : Fin p → ℚ) : Solves d Θ ψ (potentialSource d Θ ψ) :=
  (solves_iff_boundary_flux d Θ ψ _).mpr rfl

/-- [proved-derived; formal-checked] **The cycle test.** If two constitutions agree on every
source, then for every potential `ψ` and every cycle `z` (`dᵀ z = 0`) the weighted drops
`(Θ_e/Θ'_e)(dψ)_e` are orthogonal to `z`: they are the drops of the solve on `Θ'`, the drops of a
potential, and close round every cycle. -/
theorem cycle_test {d : Matrix (Fin q) (Fin p) ℚ} {Θ Θ' : Constitution q}
    (h : ∀ σ, observeConstitution d σ Θ = observeConstitution d σ Θ') (ψ : Fin p → ℚ)
    {z : Fin q → ℚ} (hz : dᵀ *ᵥ z = 0) :
    ∑ e, z e * (Θ.1 e / Θ'.1 e * (d *ᵥ ψ) e) = 0 := by
  have hs := solves_potentialSource d Θ ψ
  have hobs := h (potentialSource d Θ ψ)
  rw [observeConstitution_of_solvable ⟨ψ, hs⟩, strokeFlux_of_solves hs] at hobs
  have hs' : ∃ φ, Solves d Θ' φ (potentialSource d Θ ψ) := by
    by_contra hn
    rw [observeConstitution, if_neg hn] at hobs
    exact Option.some_ne_none _ hobs
  rw [observeConstitution_of_solvable hs'] at hobs
  have hj := Option.some.inj hobs
  have hdrop : ∀ e, Θ.1 e / Θ'.1 e * (d *ᵥ ψ) e =
      strokeDrop d (potentialSource d Θ ψ) Θ' e := by
    intro e
    have he := congrFun hj e
    rw [strokeFlux_apply] at he
    simp only [flux] at he
    rw [div_mul_eq_mul_div, div_eq_iff (Θ'.2 e).ne']
    linear_combination he
  simp_rw [hdrop]
  have hdot : z ⬝ᵥ strokeDrop d (potentialSource d Θ ψ) Θ' = 0 := by
    rw [strokeDrop, dotProduct_mulVec, ← mulVec_transpose, hz, zero_dotProduct]
  simpa [dotProduct] using hdot

/-- [proved-derived; formal-checked] **The cycle test reads the projective class**: if every
weighting `w` that passes the test against every potential and every cycle is constant, the
present observation reads the projective class. -/
theorem readsProjectiveClass_of_weights {d : Matrix (Fin q) (Fin p) ℚ} (e₀ : Fin q)
    (hw : ∀ w : Fin q → ℚ, (∀ (ψ : Fin p → ℚ) (z : Fin q → ℚ), dᵀ *ᵥ z = 0 →
      ∑ e, z e * (w e * (d *ᵥ ψ) e) = 0) → ∀ e, w e = w e₀) :
    ReadsProjectiveClass d := by
  intro Θ Θ' h
  have hc := hw (fun e => Θ.1 e / Θ'.1 e) (fun ψ z hz => cycle_test h ψ hz)
  refine ⟨Θ'.1 e₀ / Θ.1 e₀, div_pos (Θ'.2 e₀) (Θ.2 e₀), Subtype.ext (funext fun e => ?_)⟩
  change Θ'.1 e = Θ'.1 e₀ / Θ.1 e₀ * Θ.1 e
  have he := hc e
  rw [div_eq_div_iff (Θ'.2 e).ne' (Θ'.2 e₀).ne'] at he
  rw [div_mul_eq_mul_div, eq_div_iff (Θ.2 e₀).ne']
  linear_combination -he

/-- [definition] **A potential separates two edges**: it drops across one edge and not across
another (on a loopless graph, some node meets one edge and misses another: no bundle). -/
def SeparatesEdges (d : Matrix (Fin q) (Fin p) ℚ) : Prop :=
  ∃ ψ : Fin p → ℚ, ∃ e f : Fin q, (d *ᵥ ψ) e = 0 ∧ (d *ᵥ ψ) f ≠ 0

/-- [proved-derived; formal-checked] **A separating potential draws a stroke out of proportion
under both laws**, on every constitution: one edge carries no flux and another does. -/
theorem stroke_of_separatesEdges {d : Matrix (Fin q) (Fin p) ℚ} (hsep : SeparatesEdges d)
    (Θ : Constitution q) :
    ∃ σ, (∃ φ, Solves d Θ φ σ) ∧ ¬ SquareProportional d σ Θ ∧ ¬ EqualDrops d σ Θ := by
  obtain ⟨ψ, e, f, he, hf⟩ := hsep
  have hs := solves_potentialSource d Θ ψ
  refine ⟨potentialSource d Θ ψ, ⟨ψ, hs⟩, fun h => ?_, fun h => ?_⟩
  · have hef := h e f
    rw [strokeFlux_of_solves hs] at hef
    have hje : flux d Θ ψ e = 0 := by simp [flux, he]
    have hjf : flux d Θ ψ f ≠ 0 := mul_ne_zero (Θ.2 f).ne' hf
    rw [hje] at hef
    have hpos : 0 < Θ.1 e * flux d Θ ψ f ^ 2 := mul_pos (Θ.2 e) (by positivity)
    have hzero : Θ.1 f * (0 : ℚ) ^ 2 = 0 := by ring
    linarith
  · have hef := h e f
    rw [strokeDrop_of_solves hs, he] at hef
    have hf2 : (d *ᵥ ψ) f ^ 2 = 0 := by rw [← hef]; ring
    exact hf (pow_eq_zero_iff two_ne_zero |>.mp hf2)

/-- [proved-derived; formal-checked] **On every medium that reads the projective class and has a
separating potential, the square law's classes are the constitutions.** -/
theorem square_futureAgreement_iff_of_separates {d : Matrix (Fin q) (Fin p) ℚ}
    (hobs : ReadsProjectiveClass d) (hsep : SeparatesEdges d) (S : Solver d)
    (left right : DepositState q) :
    futureAgreement (observe S) (step (squareLawOn q) S) left right ↔
      left.constitution = right.constitution := by
  refine square_futureAgreement_iff_of_reads hobs (fun Θ => ?_) S left right
  obtain ⟨σ, hs, h, -⟩ := stroke_of_separatesEdges hsep Θ
  exact ⟨σ, hs, h⟩

/-- [proved-derived; formal-checked] **On every medium that reads the projective class and has a
separating potential, the Joule law's classes are the constitutions.** -/
theorem joule_futureAgreement_iff_of_separates {d : Matrix (Fin q) (Fin p) ℚ}
    (hobs : ReadsProjectiveClass d) (hsep : SeparatesEdges d) (S : Solver d)
    (left right : DepositState q) :
    futureAgreement (observe S) (step (jouleLawOn q) S) left right ↔
      left.constitution = right.constitution := by
  refine joule_futureAgreement_iff_of_reads hobs (fun Θ => ?_) S left right
  obtain ⟨σ, hs, -, h⟩ := stroke_of_separatesEdges hsep Θ
  exact ⟨σ, hs, h⟩

/-- [proved-derived; formal-checked] **No potential separates two edges of a bundle**: every edge
drops `ψ₁ − ψ₀`. -/
theorem bundle_not_separatesEdges {m : ℕ} : ¬ SeparatesEdges (bundle m) := by
  rintro ⟨ψ, e, f, he, hf⟩
  rw [bundle_mulVec] at he hf
  exact hf he

/-- [proved-derived; formal-checked] **On the bundle every stroke has one drop**, so every Joule
stroke deposits in proportion: the contrast with every cycle through three nodes. -/
theorem bundle_equalDrops {m : ℕ} [NeZero m] (Θ : Constitution m) {σ : Fin 2 → ℚ}
    (hσ : σ 0 + σ 1 = 0) : EqualDrops (bundle m) σ Θ := by
  intro e f
  rw [strokeDrop_of_solves (canonicalSolve_solves ((bundle_solvable_iff Θ σ).mpr hσ)),
    bundle_drop (canonicalSolve_solves ((bundle_solvable_iff Θ σ).mpr hσ))]

end Tests

/-! ## 4. The cycle of `N` nodes -/

section Cycle

variable {N : ℕ} [NeZero N]

/-- [definition] **The cycle of `N` nodes**: edge `e` runs from node `e` to node `e + 1 (mod N)`. -/
def cycleGraph (N : ℕ) [NeZero N] : Matrix (Fin N) (Fin N) ℚ :=
  fun e i => (if i = e + 1 then 1 else 0) - (if i = e then 1 else 0)

/-- [proved-derived; formal-checked] Summing over the edges that arrive at node `i` reads the edge
`i − 1`. -/
theorem sum_ite_arrive {β : Type*} [AddCommMonoid β] (f : Fin N → β) (i : Fin N) :
    ∑ e, (if e + 1 = i then f e else 0) = f (i - 1) := by
  rw [Finset.sum_eq_single (i - 1)]
  · rw [if_pos (sub_add_cancel i 1)]
  · intro e _ he
    rw [if_neg]
    intro hi
    exact he (by rw [← hi, add_sub_cancel_right])
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- [proved-derived; formal-checked] The cycle's drops: `(dφ)_e = φ_(e+1) − φ_e`. -/
theorem cycleGraph_mulVec (φ : Fin N → ℚ) (e : Fin N) :
    (cycleGraph N *ᵥ φ) e = φ (e + 1) - φ e := by
  simp [cycleGraph, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

/-- [proved-derived; formal-checked] The cycle's boundary: node `i` receives edge `i − 1` and sends
edge `i`. -/
theorem cycleGraph_transpose_mulVec (j : Fin N → ℚ) (i : Fin N) :
    ((cycleGraph N)ᵀ *ᵥ j) i = j (i - 1) - j i := by
  simp only [cycleGraph, mulVec, dotProduct, transpose_apply, sub_mul, Finset.sum_sub_distrib,
    boole_mul]
  rw [← sum_ite_arrive j i, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  congr 1
  exact Finset.sum_congr rfl fun e _ => by simp only [eq_comm]

/-- [proved-derived; formal-checked] Every edge of the cycle is a difference: its row sums to
zero. -/
theorem cycleGraph_row_sum (e : Fin N) : ∑ i, cycleGraph N e i = 0 := by
  simp [cycleGraph, Finset.sum_sub_distrib]

/-- [proved-derived; formal-checked] A sum over the cycle is unchanged by the shift `e ↦ e + 1`. -/
theorem sum_shift {β : Type*} [AddCommMonoid β] (f : Fin N → β) :
    ∑ e, f (e + 1) = ∑ e, f e :=
  Equiv.sum_comp (Equiv.addRight 1) f

/-- [proved-derived; formal-checked] **The loop law**: the drops of every potential sum to zero
round the cycle. -/
theorem cycleGraph_loop (φ : Fin N → ℚ) : ∑ e, (cycleGraph N *ᵥ φ) e = 0 := by
  simp only [cycleGraph_mulVec]
  rw [Finset.sum_sub_distrib, sum_shift φ, sub_self]

open Fin.NatCast in
/-- [proved-derived; formal-checked] **Every closed edge vector is a drop**: if `u` sums to zero,
the partial sums `v_i = Σ_(k < i) u_k` have `v_(e+1) − v_e = u_e` round the cycle. -/
theorem cycle_exact {u : Fin N → ℚ} (hu : ∑ e, u e = 0) :
    ∃ v : Fin N → ℚ, ∀ e, v (e + 1) - v e = u e := by
  refine ⟨fun i => ∑ k ∈ Finset.range i.val, u (k : Fin N), fun e => ?_⟩
  have hcast : ∀ k : Fin N, ((k.val : ℕ) : Fin N) = k := Fin.cast_val_eq_self
  have hval : ((e + 1 : Fin N) : ℕ) = (e.val + 1) % N := by
    rw [← Fin.val_natCast, Nat.cast_succ, hcast]
  have hsum : ∑ k ∈ Finset.range N, u (k : Fin N) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => u (k : Fin N)) N]
    simpa only [hcast] using hu
  show ∑ k ∈ Finset.range (e + 1 : Fin N).val, u (k : Fin N) -
    ∑ k ∈ Finset.range e.val, u (k : Fin N) = u e
  rw [hval]
  rcases Nat.lt_or_ge (e.val + 1) N with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt, Finset.sum_range_succ, hcast]
    ring
  · have heq : e.val + 1 = N := by
      have := e.isLt
      omega
    have hsum' : ∑ k ∈ Finset.range (e.val + 1), u (k : Fin N) = 0 := by
      rw [heq]
      exact hsum
    rw [heq, Nat.mod_self, Finset.range_zero, Finset.sum_empty]
    rw [Finset.sum_range_succ, hcast] at hsum'
    linarith

open Fin.NatCast in
/-- [proved-derived; formal-checked] A function on the cycle that the shift leaves fixed is
constant. -/
theorem eq_zero_of_shift_invariant {β : Type*} {w : Fin N → β} (h : ∀ e, w (e + 1) = w e)
    (e : Fin N) : w e = w 0 := by
  have key : ∀ m : ℕ, w (m : Fin N) = w 0 := by
    intro m
    induction m with
    | zero => rw [Nat.cast_zero]
    | succ m ih => rw [Nat.cast_succ, h, ih]
  rw [← key e.val, Fin.cast_val_eq_self]

/-- [definition] **The total resistance** `R = Σ_e r_e`, `r_e = 1/Θ_e`. -/
def resTotal {q : ℕ} (Θ : Constitution q) : ℚ := ∑ e, (Θ.1 e)⁻¹

/-- [proved-derived; formal-checked] A nonempty constitution has a positive total resistance. -/
theorem resTotal_pos {q : ℕ} [NeZero q] (Θ : Constitution q) : 0 < resTotal Θ :=
  Finset.sum_pos (fun e _ => inv_pos.mpr (Θ.2 e)) Finset.univ_nonempty

/-- [proved-derived; formal-checked] **A flux that balances the source and closes the loop is
carried by a solve**: if `j_(i−1) − j_i = σ_i` at every node and `Σ_e j_e/Θ_e = 0`, some potential
solves `σ` with flux `j`. -/
theorem cycle_solves_of_flux {Θ : Constitution N} {σ j : Fin N → ℚ}
    (hb : ∀ i, j (i - 1) - j i = σ i) (hl : ∑ e, j e / Θ.1 e = 0) :
    ∃ φ, Solves (cycleGraph N) Θ φ σ ∧ flux (cycleGraph N) Θ φ = j := by
  obtain ⟨φ, hφ⟩ := cycle_exact hl
  have hflux : flux (cycleGraph N) Θ φ = j := by
    funext e
    simp only [flux, cycleGraph_mulVec, hφ]
    field_simp [(Θ.2 e).ne']
  refine ⟨φ, ?_, hflux⟩
  rw [solves_iff_boundary_flux, hflux]
  funext i
  rw [cycleGraph_transpose_mulVec, hb]

/-- [proved-derived; formal-checked] **On the cycle a source admits a balance exactly when its
total charge is zero.** -/
theorem cycle_solvable_iff (Θ : Constitution N) (σ : Fin N → ℚ) :
    (∃ φ, Solves (cycleGraph N) Θ φ σ) ↔ ∑ i, σ i = 0 := by
  constructor
  · rintro ⟨φ, h⟩
    exact source_total_zero cycleGraph_row_sum h
  · intro hσ
    have hu : ∑ e, -σ (e + 1) = 0 := by
      rw [Finset.sum_neg_distrib, sum_shift σ, hσ, neg_zero]
    obtain ⟨j₀, hj₀⟩ := cycle_exact hu
    have hR := (resTotal_pos Θ).ne'
    have h2 : ∑ e, (∑ f, j₀ f / Θ.1 f) / resTotal Θ / Θ.1 e =
        (∑ f, j₀ f / Θ.1 f) / resTotal Θ * resTotal Θ := by
      rw [resTotal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => div_eq_mul_inv _ _
    have hb : ∀ i, (j₀ (i - 1) - (∑ f, j₀ f / Θ.1 f) / resTotal Θ) -
        (j₀ i - (∑ f, j₀ f / Θ.1 f) / resTotal Θ) = σ i := by
      intro i
      have hi := hj₀ (i - 1)
      rw [sub_add_cancel] at hi
      linarith
    have hl : ∑ e, (j₀ e - (∑ f, j₀ f / Θ.1 f) / resTotal Θ) / Θ.1 e = 0 := by
      simp only [sub_div, Finset.sum_sub_distrib, h2]
      rw [div_mul_cancel₀ _ hR, sub_self]
    obtain ⟨φ, hs, -⟩ := cycle_solves_of_flux
      (j := fun e => j₀ e - (∑ f, j₀ f / Θ.1 f) / resTotal Θ) hb hl
    exact ⟨φ, hs⟩

/-- [definition] **The unit source across edge `k`**: one unit leaves node `k` and arrives at node
`k + 1`; it is the edge's own row. -/
def unitAcross (k : Fin N) : Fin N → ℚ := cycleGraph N k

/-- [definition] **The unit flux across edge `k`**: `1 − r_k/R` on edge `k` and `−r_k/R` on every
other edge. -/
def cycleUnitFlux (Θ : Constitution N) (k : Fin N) : Fin N → ℚ :=
  fun e => (if e = k then 1 else 0) - (Θ.1 k)⁻¹ / resTotal Θ

/-- [proved-derived; formal-checked] The unit source across `k` is solved, with the unit flux. -/
theorem cycle_unit_solves (Θ : Constitution N) (k : Fin N) :
    ∃ φ, Solves (cycleGraph N) Θ φ (unitAcross k) ∧
      flux (cycleGraph N) Θ φ = cycleUnitFlux Θ k := by
  have hR := (resTotal_pos Θ).ne'
  refine cycle_solves_of_flux (fun i => ?_) ?_
  · have hiff : (i - 1 = k) ↔ (i = k + 1) := sub_eq_iff_eq_add
    simp only [cycleUnitFlux, unitAcross, cycleGraph, hiff]
    ring
  · have h1 : ∑ e, (if e = k then (1 : ℚ) else 0) / Θ.1 e = (Θ.1 k)⁻¹ := by
      simp [ite_div]
    have h2 : ∑ e, (Θ.1 k)⁻¹ / resTotal Θ / Θ.1 e = (Θ.1 k)⁻¹ / resTotal Θ * resTotal Θ := by
      rw [resTotal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => div_eq_mul_inv _ _
    simp only [cycleUnitFlux, sub_div, Finset.sum_sub_distrib, h1, h2]
    rw [div_mul_cancel₀ _ hR, sub_self]

/-- [proved-derived; formal-checked] Every constitution admits the unit source across every edge. -/
theorem cycle_unit_solvable (Θ : Constitution N) (k : Fin N) :
    ∃ φ, Solves (cycleGraph N) Θ φ (unitAcross k) := by
  obtain ⟨φ, h, -⟩ := cycle_unit_solves Θ k
  exact ⟨φ, h⟩

/-- [proved-derived; formal-checked] **Every solve of the unit source across `k` carries the unit
flux.** -/
theorem cycle_unit_flux {Θ : Constitution N} {k : Fin N} {φ : Fin N → ℚ}
    (h : Solves (cycleGraph N) Θ φ (unitAcross k)) :
    flux (cycleGraph N) Θ φ = cycleUnitFlux Θ k := by
  obtain ⟨φ', h', hf⟩ := cycle_unit_solves Θ k
  rw [flux_unique h h', hf]

/-- [proved-derived; formal-checked] The stroke across `k` carries the unit flux. -/
theorem strokeFlux_unitAcross (Θ : Constitution N) (k : Fin N) :
    strokeFlux (cycleGraph N) (unitAcross k) Θ = cycleUnitFlux Θ k :=
  cycle_unit_flux (canonicalSolve_solves (cycle_unit_solvable Θ k))

/-- [proved-derived; formal-checked] The stroke across `k` drops `j_e/Θ_e` on edge `e`. -/
theorem strokeDrop_unitAcross (Θ : Constitution N) (k e : Fin N) :
    strokeDrop (cycleGraph N) (unitAcross k) Θ e = cycleUnitFlux Θ k e / Θ.1 e := by
  have h := strokeFlux_apply (cycleGraph N) (unitAcross k) Θ e
  rw [strokeFlux_unitAcross] at h
  rw [h]
  field_simp [(Θ.2 e).ne']

/-- [proved-derived; formal-checked] **Across its own edge the unit source sends `R_far/R`**, with
`R_far = R − r_k` the far path's resistance. -/
theorem cycleUnitFlux_self (Θ : Constitution N) (k : Fin N) :
    cycleUnitFlux Θ k k = (resTotal Θ - (Θ.1 k)⁻¹) / resTotal Θ := by
  unfold cycleUnitFlux
  rw [if_pos rfl, sub_div, div_self (resTotal_pos Θ).ne']

omit [NeZero N] in
/-- [proved-derived; formal-checked] **Round the far path it sends `r_k/R`**, against the edges'
orientation. -/
theorem cycleUnitFlux_of_ne (Θ : Constitution N) {k f : Fin N} (hf : f ≠ k) :
    cycleUnitFlux Θ k f = -((Θ.1 k)⁻¹ / resTotal Θ) := by
  simp only [cycleUnitFlux, if_neg hf]
  ring

/-- [proved-derived; formal-checked] **The drop across an edge is minus the far path's drops**,
for every source: the drops close round the cycle. -/
theorem cycle_drop_eq_neg_far (σ : Fin N → ℚ) (Θ : Constitution N) (k : Fin N) :
    strokeDrop (cycleGraph N) σ Θ k =
      -∑ f ∈ Finset.univ.erase k, strokeDrop (cycleGraph N) σ Θ f := by
  have hloop := cycleGraph_loop (canonicalSolve (cycleGraph N) Θ σ)
  have hsplit := Finset.add_sum_erase Finset.univ (fun f => strokeDrop (cycleGraph N) σ Θ f)
    (Finset.mem_univ k)
  simp only [strokeDrop] at hsplit ⊢
  linarith

/-- [proved-derived; formal-checked] **The cycle's present observation reads the projective
class**: the cycle test with the node potentials `δ_i` and the one cycle `(1, …, 1)` gives
`w_(i−1) = w_i` at every node. -/
theorem cycle_readsProjectiveClass : ReadsProjectiveClass (cycleGraph N) := by
  refine readsProjectiveClass_of_weights 0 fun w hw => ?_
  have hone : (cycleGraph N)ᵀ *ᵥ (fun _ => (1 : ℚ)) = 0 := by
    funext i
    rw [cycleGraph_transpose_mulVec]
    simp
  have hsh : ∀ i, w (i - 1) = w i := by
    intro i
    have h := hw (Pi.single i 1) (fun _ => 1) hone
    simp only [cycleGraph_mulVec, Pi.single_apply, one_mul, mul_sub, mul_boole,
      Finset.sum_sub_distrib, sum_ite_arrive, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    linarith
  refine eq_zero_of_shift_invariant fun e => ?_
  have := hsh (e + 1)
  rwa [add_sub_cancel_right, eq_comm] at this

/-- [proved-derived; formal-checked] **The cycle's present reads the projective class and nothing
more**: two constitutions agree on every source iff one is a positive multiple of the other. -/
theorem cycle_observe_iff_projectivelyEqual (Θ Θ' : Constitution N) :
    (∀ σ, observeConstitution (cycleGraph N) σ Θ = observeConstitution (cycleGraph N) σ Θ') ↔
      ProjectivelyEqual Θ Θ' :=
  observe_iff_projectivelyEqual_of_reads cycle_readsProjectiveClass Θ Θ'

end Cycle

/-! ## 5. The square law and the Joule law on the cycle -/

section CycleLaws

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- [proved-derived; formal-checked] On three or more nodes, two edges leave a third. -/
theorem exists_third (hN : 3 ≤ N) (k l : Fin N) : ∃ m, m ≠ k ∧ m ≠ l := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin N)) ⊆ {k, l} := by
    intro m _
    by_cases hm : m = k
    · simp [hm]
    · simp [h m hm]
  have hcard := (Finset.card_le_card hsub).trans Finset.card_le_two
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- [proved-derived; formal-checked] Three distinct edges bound the total resistance below. -/
theorem three_le_resTotal {q : ℕ} {k l m : Fin q} (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m)
    (Θ : Constitution q) : (Θ.1 k)⁻¹ + (Θ.1 l)⁻¹ + (Θ.1 m)⁻¹ ≤ resTotal Θ := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {k, l, m})
    (fun e _ _ => (inv_pos.mpr (Θ.2 e)).le) (f := fun e => (Θ.1 e)⁻¹)
  rw [Finset.sum_insert (by simp [hkl, hkm]), Finset.sum_insert (by simp [hlm]),
    Finset.sum_singleton] at h
  unfold resTotal
  linarith

/-- [proved-derived; formal-checked] **The far path's resistance with one conductance `θ` off
`k`** is `(N − 1)/θ`. -/
theorem far_resistance_of_uniform {Θ : Constitution N} {k : Fin N} {θ : ℚ}
    (h : ∀ g, g ≠ k → Θ.1 g = θ) : resTotal Θ - (Θ.1 k)⁻¹ = ((N : ℚ) - 1) * θ⁻¹ := by
  have hsplit := Finset.add_sum_erase Finset.univ (fun g => (Θ.1 g)⁻¹) (Finset.mem_univ k)
  have hfar : ∑ g ∈ Finset.univ.erase k, (Θ.1 g)⁻¹ = ((N : ℚ) - 1) * θ⁻¹ := by
    rw [Finset.sum_congr rfl (g := fun _ => θ⁻¹)
        (fun g hg => by rw [h g (Finset.ne_of_mem_erase hg)]), Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)), Nat.cast_one]
  unfold resTotal
  linarith

/-- [proved-derived; formal-checked] **The stroke across `k` in proportion forces** one
conductance off `k` and `(R − r_k)² Θ_f = r_k² Θ_k`, that is `(R − r_k)²/Θ_k = r_k²/Θ_f`, for every
`f ≠ k`. -/
theorem cycle_unit_squareProportional_forces {Θ : Constitution N} {k : Fin N}
    (h : SquareProportional (cycleGraph N) (unitAcross k) Θ) :
    (∀ f g, f ≠ k → g ≠ k → Θ.1 f = Θ.1 g) ∧
      ∀ f, f ≠ k → (resTotal Θ - (Θ.1 k)⁻¹) ^ 2 * Θ.1 f = (Θ.1 k)⁻¹ ^ 2 * Θ.1 k := by
  have hR := resTotal_pos Θ
  have hr := inv_pos.mpr (Θ.2 k)
  refine ⟨fun f g hf hg => ?_, fun f hf => ?_⟩
  · have hfg := h f g
    rw [strokeFlux_unitAcross, cycleUnitFlux_of_ne Θ hf, cycleUnitFlux_of_ne Θ hg] at hfg
    have hx : 0 < (-((Θ.1 k)⁻¹ / resTotal Θ)) ^ 2 := by
      rw [neg_sq]
      positivity
    exact mul_right_cancel₀ hx.ne' hfg
  · have hfk := h f k
    rw [strokeFlux_unitAcross, cycleUnitFlux_of_ne Θ hf, cycleUnitFlux_self] at hfk
    have key : ((resTotal Θ - (Θ.1 k)⁻¹) ^ 2 * Θ.1 f - (Θ.1 k)⁻¹ ^ 2 * Θ.1 k) /
        resTotal Θ ^ 2 = 0 := by
      linear_combination hfk
    rcases div_eq_zero_iff.mp key with h0 | h0
    · linear_combination h0
    · exact absurd h0 (by positivity)

/-- [proved-derived; formal-checked] **The constitutions the stroke across `k` takes in
proportion** are exactly those with `Θ_f = (N − 1)² Θ_k` on every other edge (on the triangle the
owner's `(1, 4, 4)`). -/
theorem cycle_unit_squareProportional_iff (Θ : Constitution N) (k : Fin N) :
    SquareProportional (cycleGraph N) (unitAcross k) Θ ↔
      ∀ f, f ≠ k → Θ.1 f = ((N : ℚ) - 1) ^ 2 * Θ.1 k := by
  have hR := resTotal_pos Θ
  have hk := Θ.2 k
  constructor
  · intro h f hf
    obtain ⟨hoff, hrel⟩ := cycle_unit_squareProportional_forces h
    have hfar := far_resistance_of_uniform (θ := Θ.1 f) fun g hg => hoff g f hg hf
    have hrf := hrel f hf
    rw [hfar] at hrf
    have hf0 := Θ.2 f
    field_simp at hrf
    linear_combination -hrf
  · intro h
    have hN1 : ∀ f, f ≠ k → (N : ℚ) - 1 ≠ 0 := by
      intro f hf hN
      have hN' : N = 1 := by exact_mod_cast (sub_eq_zero.mp hN)
      subst hN'
      exact hf (Subsingleton.elim _ _)
    have hfar : ∀ f, f ≠ k → ((N : ℚ) - 1) * (resTotal Θ - (Θ.1 k)⁻¹) = (Θ.1 k)⁻¹ := by
      intro f hf
      rw [far_resistance_of_uniform (θ := ((N : ℚ) - 1) ^ 2 * Θ.1 k) h]
      field_simp [hN1 f hf]
    intro e f
    rw [strokeFlux_unitAcross]
    by_cases he : e = k <;> by_cases hf : f = k
    · rw [he, hf]
    · rw [he, cycleUnitFlux_self, cycleUnitFlux_of_ne Θ hf, h f hf]
      linear_combination (-(Θ.1 k) / resTotal Θ ^ 2 *
        ((Θ.1 k)⁻¹ + ((N : ℚ) - 1) * (resTotal Θ - (Θ.1 k)⁻¹))) * hfar f hf
    · rw [hf, cycleUnitFlux_self, cycleUnitFlux_of_ne Θ he, h e he]
      linear_combination (Θ.1 k / resTotal Θ ^ 2 *
        ((Θ.1 k)⁻¹ + ((N : ℚ) - 1) * (resTotal Θ - (Θ.1 k)⁻¹))) * hfar e he
    · rw [cycleUnitFlux_of_ne Θ he, cycleUnitFlux_of_ne Θ hf, h e he, h f hf]

/-- [proved-derived; formal-checked] **No constitution takes two unit strokes across distinct
edges in proportion** on three or more nodes: a third edge `m` gives `Θ_k = Θ_l`, and then
`Θ_l = (N − 1)² Θ_k` forces `(N − 1)² = 1`. -/
theorem cycle_not_two_strokes_proportional (hN : 3 ≤ N) {k l : Fin N} (hkl : k ≠ l)
    (Θ : Constitution N) (hk : SquareProportional (cycleGraph N) (unitAcross k) Θ)
    (hl : SquareProportional (cycleGraph N) (unitAcross l) Θ) : False := by
  obtain ⟨m, hmk, hml⟩ := exists_third hN k l
  have hk' := (cycle_unit_squareProportional_iff Θ k).mp hk
  have hl' := (cycle_unit_squareProportional_iff Θ l).mp hl
  have h1 := hk' m hmk
  have h2 := hl' m hml
  have h3 := hk' l (Ne.symm hkl)
  have hΘk := Θ.2 k
  have hkl' : Θ.1 k = Θ.1 l := by
    have hs : 0 < ((N : ℚ) - 1) ^ 2 := by
      have : (3 : ℚ) ≤ N := by exact_mod_cast hN
      nlinarith
    have := h1.symm.trans h2
    exact mul_left_cancel₀ hs.ne' this
  have hsq : ((N : ℚ) - 1) ^ 2 = 1 := by
    rw [← hkl'] at h3
    have := mul_right_cancel₀ hΘk.ne' (h3.symm.trans (one_mul _).symm)
    exact this
  have : (3 : ℚ) ≤ N := by exact_mod_cast hN
  nlinarith

/-- [proved-derived; formal-checked] **The future-agreement relation of the square law on the
cycle of `N ≥ 3` nodes.** Two presents share every future iff their constitutions are equal. -/
theorem cycle_square_futureAgreement_iff (hN : 3 ≤ N) (S : Solver (cycleGraph N))
    (left right : DepositState N) :
    futureAgreement (observe S) (step (squareLawOn N) S) left right ↔
      left.constitution = right.constitution := by
  obtain ⟨l, hl0, -⟩ := exists_third hN 0 0
  exact square_futureAgreement_iff_of_two_strokes cycle_readsProjectiveClass (unitAcross 0)
    (unitAcross l) (fun Θ => cycle_unit_solvable Θ 0) (fun Θ => cycle_unit_solvable Θ l)
    (fun Θ h0 hl => cycle_not_two_strokes_proportional hN (Ne.symm hl0) Θ h0 hl) S left right

/-- [proved-derived; formal-checked] **On the cycle of `N ≥ 3` nodes the constitution is the least
lawful retention under the square law.** -/
theorem cycle_square_constitution_factors_through_every_standing (hN : 3 ≤ N)
    (S : Solver (cycleGraph N)) {Retained : Type*}
    (M : StandingLaw (Fin N → ℚ) (Fin N → ℚ) (DepositState N) Retained (Option (Fin N → ℚ)))
    (htransport : M.transport = step (squareLawOn N) S) (hobserve : M.observe = observe S)
    {left right : DepositState N} (h : M.retain left = M.retain right) :
    left.constitution = right.constitution :=
  constitution_factors_through_every_standing_of_iff (cycle_square_futureAgreement_iff hN S) M
    htransport hobserve h

/-- [proved-derived; formal-checked] **A unit stroke on the cycle never has one drop magnitude**
(`N ≥ 3`): the drop across its edge is the sum of the far path's drops, `r_k (R − r_k)/R`, against
`r_k r_f/R` on a far edge `f`, and `R − r_k > r_f`. -/
theorem cycle_unit_not_equalDrops (hN : 3 ≤ N) (Θ : Constitution N) (k : Fin N) :
    ¬ EqualDrops (cycleGraph N) (unitAcross k) Θ := by
  intro h
  obtain ⟨l, hlk, -⟩ := exists_third hN k k
  obtain ⟨m, hmk, hml⟩ := exists_third hN k l
  have hkl := h k l
  rw [strokeDrop_unitAcross, strokeDrop_unitAcross, cycleUnitFlux_self,
    cycleUnitFlux_of_ne Θ hlk] at hkl
  have h3 := three_le_resTotal (Ne.symm hlk) (Ne.symm hmk) (Ne.symm hml) Θ
  have ha := inv_pos.mpr (Θ.2 k)
  have hb := inv_pos.mpr (Θ.2 l)
  have hc := inv_pos.mpr (Θ.2 m)
  have hR := resTotal_pos Θ
  have key : ((Θ.1 k)⁻¹ / resTotal Θ) ^ 2 *
      ((resTotal Θ - (Θ.1 k)⁻¹) ^ 2 - (Θ.1 l)⁻¹ ^ 2) = 0 := by
    linear_combination hkl
  rcases mul_eq_zero.mp key with h0 | h0
  · exact absurd h0 (by positivity)
  · nlinarith [mul_pos (show 0 < resTotal Θ - (Θ.1 k)⁻¹ - (Θ.1 l)⁻¹ by linarith)
      (show 0 < resTotal Θ - (Θ.1 k)⁻¹ + (Θ.1 l)⁻¹ by linarith)]

/-- [proved-derived; formal-checked] **The future-agreement relation of the Joule law on the cycle
of `N ≥ 3` nodes.** Two presents share every future iff their constitutions are equal. -/
theorem cycle_joule_futureAgreement_iff (hN : 3 ≤ N) (S : Solver (cycleGraph N))
    (left right : DepositState N) :
    futureAgreement (observe S) (step (jouleLawOn N) S) left right ↔
      left.constitution = right.constitution :=
  joule_futureAgreement_iff_of_reads cycle_readsProjectiveClass
    (fun Θ => ⟨unitAcross 0, cycle_unit_solvable Θ 0, cycle_unit_not_equalDrops hN Θ 0⟩) S left right

/-- [proved-derived; formal-checked] **On the cycle of `N ≥ 3` nodes the constitution is the least
lawful retention under the Joule law.** -/
theorem cycle_joule_constitution_factors_through_every_standing (hN : 3 ≤ N)
    (S : Solver (cycleGraph N)) {Retained : Type*}
    (M : StandingLaw (Fin N → ℚ) (Fin N → ℚ) (DepositState N) Retained (Option (Fin N → ℚ)))
    (htransport : M.transport = step (jouleLawOn N) S) (hobserve : M.observe = observe S)
    {left right : DepositState N} (h : M.retain left = M.retain right) :
    left.constitution = right.constitution :=
  constitution_factors_through_every_standing_of_iff (cycle_joule_futureAgreement_iff hN S) M
    htransport hobserve h

end CycleLaws

/-! ## 6. The triangle read through the abstract lemma, and the Joule law on it -/

section Triangle

/-- [proved-derived; formal-checked] The triangle's present reads the projective class (the
owner's `triangle_observe_iff_projectivelyEqual`). -/
theorem triangle_readsProjectiveClass : ReadsProjectiveClass triangle :=
  fun Θ Θ' h => (triangle_observe_iff_projectivelyEqual Θ Θ').mp h

/-- [proved-derived; formal-checked] On the triangle the stroke's flux is the owner's `triFlux`. -/
theorem triangle_strokeFlux {σ : Fin 3 → ℚ} (hσ : σ 0 + σ 1 + σ 2 = 0) (Θ : Constitution 3) :
    strokeFlux triangle σ Θ = triFlux Θ σ :=
  triangle_flux (canonicalSolve_solves ((triangle_solvable_iff Θ σ).mpr hσ))

/-- [proved-derived; formal-checked] On the triangle the stroke's drops are the owner's. -/
theorem triangle_strokeDrop {σ : Fin 3 → ℚ} (hσ : σ 0 + σ 1 + σ 2 = 0) (Θ : Constitution 3) :
    strokeDrop triangle σ Θ = ![dropA Θ σ, dropB Θ σ, dropA Θ σ + dropB Θ σ] :=
  triangle_drop (canonicalSolve_solves ((triangle_solvable_iff Θ σ).mpr hσ))

/-- [proved-derived; formal-checked] **The owner's square-law classes on the triangle, recovered
from the abstract lemma**: the present reads the projective class and no constitution takes both
unit strokes `0 → 1` and `1 → 2` in proportion (`not_both_strokes_proportional`). -/
theorem triangle_square_futureAgreement_iff_of_reads (S : Solver triangle)
    (left right : DepositState 3) :
    futureAgreement (observe S) (step (squareLawOn 3) S) left right ↔
      left.constitution = right.constitution := by
  refine square_futureAgreement_iff_of_two_strokes triangle_readsProjectiveClass source01 source12
    (fun Θ => (triangle_solvable_iff Θ _).mpr source01_charge)
    (fun Θ => (triangle_solvable_iff Θ _).mpr source12_charge) (fun Θ h01 h12 => ?_) S left right
  refine not_both_strokes_proportional Θ (fun e f => ?_) (fun e f => ?_)
  · have h := h01 e f
    rwa [triangle_strokeFlux source01_charge] at h
  · have h := h12 e f
    rwa [triangle_strokeFlux source12_charge] at h

/-- [proved-derived; formal-checked] **The unit stroke `0 → 1` on the triangle never has one drop
magnitude**: it drops `(Θ_b + Θ_c)/P` across `a` and `−Θ_c/P` across `b`. -/
theorem triangle_unit_not_equalDrops (Θ : Constitution 3) : ¬ EqualDrops triangle source01 Θ := by
  intro h
  have h01 := h 0 1
  rw [triangle_strokeDrop source01_charge] at h01
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at h01
  have hs0 : source01 0 = -1 := rfl
  have hs1 : source01 1 = 1 := rfl
  rw [dropA, dropB, hs0, hs1] at h01
  have hb := Θ.2 1
  have hc := Θ.2 2
  have hP := treeSum_pos Θ
  have key : Θ.1 1 * (Θ.1 1 + 2 * Θ.1 2) / treeSum Θ ^ 2 = 0 := by
    linear_combination h01
  rcases div_eq_zero_iff.mp key with h0 | h0
  · have : 0 < Θ.1 1 * (Θ.1 1 + 2 * Θ.1 2) := by positivity
    linarith
  · exact absurd h0 (by positivity)

/-- [proved-derived; formal-checked] **The future-agreement relation of the Joule law on the
triangle.** Two presents share every future iff their constitutions are equal, where on every
bundle the Joule classes are the projective classes. -/
theorem triangle_joule_futureAgreement_iff (S : Solver triangle) (left right : DepositState 3) :
    futureAgreement (observe S) (step (jouleLawOn 3) S) left right ↔
      left.constitution = right.constitution :=
  joule_futureAgreement_iff_of_reads triangle_readsProjectiveClass
    (fun Θ => ⟨source01, (triangle_solvable_iff Θ _).mpr source01_charge,
      triangle_unit_not_equalDrops Θ⟩) S left right

/-- [proved-derived; formal-checked] **On the triangle the constitution is the least lawful
retention under the Joule law.** -/
theorem triangle_joule_constitution_factors_through_every_standing (S : Solver triangle)
    {Retained : Type*}
    (M : StandingLaw (Fin 3 → ℚ) (Fin 3 → ℚ) (DepositState 3) Retained (Option (Fin 3 → ℚ)))
    (htransport : M.transport = step (jouleLawOn 3) S) (hobserve : M.observe = observe S)
    {left right : DepositState 3} (h : M.retain left = M.retain right) :
    left.constitution = right.constitution :=
  constitution_factors_through_every_standing_of_iff (triangle_joule_futureAgreement_iff S) M
    htransport hobserve h

end Triangle

/-! ## 7. The diamond: two triangles on one shared edge -/

section Diamond

/-- [definition] **The diamond**: four nodes and five edges, `0 → 1`, `1 → 3`, `0 → 2`, `2 → 3`
and the shared edge `0 → 3`; the triangles `(0, 1, 3)` and `(0, 2, 3)` meet on it. -/
def diamond : Matrix (Fin 5) (Fin 4) ℚ :=
  !![-1, 1, 0, 0; 0, -1, 0, 1; -1, 0, 1, 0; 0, 0, -1, 1; -1, 0, 0, 1]

/-- [proved-derived; formal-checked] The diamond's drops. -/
theorem diamond_mulVec (φ : Fin 4 → ℚ) :
    diamond *ᵥ φ = ![φ 1 - φ 0, φ 3 - φ 1, φ 2 - φ 0, φ 3 - φ 2, φ 3 - φ 0] := by
  funext e
  fin_cases e <;> simp [diamond, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- [definition] The cycle of the triangle `(0, 1, 3)`: `0 → 1`, `1 → 3`, back along `0 → 3`. -/
def diamondCycleLeft : Fin 5 → ℚ := ![1, 1, 0, 0, -1]

/-- [definition] The cycle of the triangle `(0, 2, 3)`: `0 → 2`, `2 → 3`, back along `0 → 3`. -/
def diamondCycleRight : Fin 5 → ℚ := ![0, 0, 1, 1, -1]

/-- [proved-derived; formal-checked] The left triangle's cycle carries no source. -/
theorem diamond_cycleLeft : diamondᵀ *ᵥ diamondCycleLeft = 0 := by
  funext i
  fin_cases i <;> simp [diamond, diamondCycleLeft, mulVec, dotProduct, Fin.sum_univ_five]

/-- [proved-derived; formal-checked] The right triangle's cycle carries no source. -/
theorem diamond_cycleRight : diamondᵀ *ᵥ diamondCycleRight = 0 := by
  funext i
  fin_cases i <;> simp [diamond, diamondCycleRight, mulVec, dotProduct, Fin.sum_univ_five]

/-- [proved-derived; formal-checked] **The diamond's present reads the projective class**: the
cycle test with the node potentials at `0`, `1`, `2` and the two triangles' cycles gives
`w₀ = w₁ = w₄` and `w₂ = w₃ = w₄`. -/
theorem diamond_readsProjectiveClass : ReadsProjectiveClass diamond := by
  refine readsProjectiveClass_of_weights 4 fun w hw => ?_
  have h1 := hw ![0, 1, 0, 0] _ diamond_cycleLeft
  have h2 := hw ![1, 0, 0, 0] _ diamond_cycleLeft
  have h3 := hw ![0, 0, 1, 0] _ diamond_cycleRight
  have h4 := hw ![1, 0, 0, 0] _ diamond_cycleRight
  simp [diamond_mulVec, diamondCycleLeft, diamondCycleRight, Fin.sum_univ_five] at h1 h2 h3 h4
  intro e
  fin_cases e <;> simp <;> linarith

/-- [proved-derived; formal-checked] **The node potential at `1` separates two edges**: it drops
across `0 → 1` and not across `0 → 2`. -/
theorem diamond_separatesEdges : SeparatesEdges diamond :=
  ⟨![0, 1, 0, 0], 2, 0, by simp [diamond_mulVec], by simp [diamond_mulVec]⟩

/-- [proved-derived; formal-checked] **The future-agreement relation of the square law on the
diamond.** Two presents share every future iff their constitutions are equal. -/
theorem diamond_square_futureAgreement_iff (S : Solver diamond) (left right : DepositState 5) :
    futureAgreement (observe S) (step (squareLawOn 5) S) left right ↔
      left.constitution = right.constitution :=
  square_futureAgreement_iff_of_separates diamond_readsProjectiveClass diamond_separatesEdges S
    left right

/-- [proved-derived; formal-checked] **The future-agreement relation of the Joule law on the
diamond.** Two presents share every future iff their constitutions are equal. -/
theorem diamond_joule_futureAgreement_iff (S : Solver diamond) (left right : DepositState 5) :
    futureAgreement (observe S) (step (jouleLawOn 5) S) left right ↔
      left.constitution = right.constitution :=
  joule_futureAgreement_iff_of_separates diamond_readsProjectiveClass diamond_separatesEdges S
    left right

/-- [proved-derived; formal-checked] **On the diamond the constitution is the least lawful
retention under the square law.** -/
theorem diamond_square_constitution_factors_through_every_standing (S : Solver diamond)
    {Retained : Type*}
    (M : StandingLaw (Fin 4 → ℚ) (Fin 4 → ℚ) (DepositState 5) Retained (Option (Fin 5 → ℚ)))
    (htransport : M.transport = step (squareLawOn 5) S) (hobserve : M.observe = observe S)
    {left right : DepositState 5} (h : M.retain left = M.retain right) :
    left.constitution = right.constitution :=
  constitution_factors_through_every_standing_of_iff (diamond_square_futureAgreement_iff S) M
    htransport hobserve h

/-- [proved-derived; formal-checked] **On the diamond the constitution is the least lawful
retention under the Joule law.** -/
theorem diamond_joule_constitution_factors_through_every_standing (S : Solver diamond)
    {Retained : Type*}
    (M : StandingLaw (Fin 4 → ℚ) (Fin 4 → ℚ) (DepositState 5) Retained (Option (Fin 5 → ℚ)))
    (htransport : M.transport = step (jouleLawOn 5) S) (hobserve : M.observe = observe S)
    {left right : DepositState 5} (h : M.retain left = M.retain right) :
    left.constitution = right.constitution :=
  constitution_factors_through_every_standing_of_iff (diamond_joule_futureAgreement_iff S) M
    htransport hobserve h

end Diamond

/-! ## 8. A witness on the four-cycle -/

section Witness

variable {N : ℕ} [NeZero N]

/-- [definition] The uniform constitution `c` on every edge. -/
def uniformOn (q : ℕ) (c : ℚ) (hc : 0 < c) : Constitution q := ⟨fun _ => c, fun _ => hc⟩

/-- [proved-derived; formal-checked] On a uniform ring the unit stroke across `k` sends
`(N − 1)/N` across its edge and `1/N` round the far path. -/
theorem cycleUnitFlux_uniform {c : ℚ} (hc : 0 < c) (k e : Fin N) :
    cycleUnitFlux (uniformOn N c hc) k e = (if e = k then 1 else 0) - 1 / N := by
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hR : resTotal (uniformOn N c hc) = N * c⁻¹ := by
    simp [resTotal, uniformOn]
  rw [cycleUnitFlux, hR]
  change (if e = k then 1 else 0) - c⁻¹ / (N * c⁻¹) = _
  field_simp

/-- [proved-derived; formal-checked] One square-law unit stroke on a uniform ring. -/
theorem cycle_square_unit_uniform {c : ℚ} (hc : 0 < c) (k e : Fin N) :
    (stepConstitution (squareLawOn N) (cycleGraph N) (unitAcross k) (uniformOn N c hc)).1 e =
      c + ((if e = k then 1 else 0) - 1 / N) ^ 2 := by
  rw [square_step_apply (cycle_unit_solvable _ k), strokeFlux_unitAcross, cycleUnitFlux_uniform]
  rfl

/-- [proved-derived; formal-checked] One Joule-law unit stroke on a uniform ring. -/
theorem cycle_joule_unit_uniform {c : ℚ} (hc : 0 < c) (k e : Fin N) :
    (stepConstitution (jouleLawOn N) (cycleGraph N) (unitAcross k) (uniformOn N c hc)).1 e =
      c + ((if e = k then 1 else 0) - 1 / N) ^ 2 / c := by
  rw [joule_step_apply (cycle_unit_solvable _ k), strokeDrop_unitAcross, cycleUnitFlux_uniform]
  change c + c * (((if e = k then 1 else 0) - 1 / N) / c) ^ 2 = _
  field_simp

/-- [proved-derived; formal-checked] The uniform constitution `2` is the double of the uniform
constitution `1`. -/
theorem uniformOn_two (q : ℕ) :
    uniformOn q 2 two_pos = Retention.scaleConstitution 2 two_pos (uniformOn q 1 one_pos) := by
  apply Subtype.ext
  funext e
  simp [uniformOn, Retention.scaleConstitution]

/-- [counterexample; formal-checked] **On the four-cycle one stroke separates uniform
constitutions, where they merge on every bundle.** `(1, 1, 1, 1)` and `(2, 2, 2, 2)` agree on
every present source; after the unit stroke across edge `0` some source separates them under the
square law (`(25, 17, 17, 17)/16` against `(41, 33, 33, 33)/16`) and under the Joule law (against
`(73, 65, 65, 65)/32`); on the bundle of four edges they share every future under both laws. -/
theorem cycle4_witness (S : Solver (cycleGraph 4)) (Sb : Solver (bundle 4)) :
    (∀ σ, observe S σ ⟨uniformOn 4 1 one_pos, []⟩ = observe S σ ⟨uniformOn 4 2 two_pos, []⟩) ∧
      (∃ σ, observe S σ (step (squareLawOn 4) S (unitAcross 0) ⟨uniformOn 4 1 one_pos, []⟩) ≠
        observe S σ (step (squareLawOn 4) S (unitAcross 0) ⟨uniformOn 4 2 two_pos, []⟩)) ∧
      (∃ σ, observe S σ (step (jouleLawOn 4) S (unitAcross 0) ⟨uniformOn 4 1 one_pos, []⟩) ≠
        observe S σ (step (jouleLawOn 4) S (unitAcross 0) ⟨uniformOn 4 2 two_pos, []⟩)) ∧
      futureAgreement (observe Sb) (step (squareLawOn 4) Sb) ⟨uniformOn 4 1 one_pos, []⟩
        ⟨uniformOn 4 2 two_pos, []⟩ ∧
      futureAgreement (observe Sb) (step (jouleLawOn 4) Sb) ⟨uniformOn 4 1 one_pos, []⟩
        ⟨uniformOn 4 2 two_pos, []⟩ := by
  refine ⟨fun σ => ?_, ?_, ?_, ?_, ?_⟩
  · rw [observe_eq_observeConstitution, observe_eq_observeConstitution]
    change observeConstitution _ σ (uniformOn 4 1 one_pos) =
      observeConstitution _ σ (uniformOn 4 2 two_pos)
    rw [uniformOn_two, Retention.observeConstitution_scale]
  · refine exists_separating_source cycle_readsProjectiveClass _ S _ _ _ ?_
    rintro ⟨κ, hκ, h⟩
    have h0 := congrArg (fun Θ : Constitution 4 => Θ.1 0) h
    have h1 := congrArg (fun Θ : Constitution 4 => Θ.1 1) h
    simp only [Retention.scaleConstitution] at h0 h1
    rw [cycle_square_unit_uniform, cycle_square_unit_uniform] at h0 h1
    norm_num at h0 h1
    linarith
  · refine exists_separating_source cycle_readsProjectiveClass _ S _ _ _ ?_
    rintro ⟨κ, hκ, h⟩
    have h0 := congrArg (fun Θ : Constitution 4 => Θ.1 0) h
    have h1 := congrArg (fun Θ : Constitution 4 => Θ.1 1) h
    simp only [Retention.scaleConstitution] at h0 h1
    rw [cycle_joule_unit_uniform, cycle_joule_unit_uniform] at h0 h1
    norm_num at h0 h1
    linarith
  · exact uniform_futureAgreement Sb (fun _ _ => rfl) (fun _ _ => rfl)
  · exact (joule_bundle_futureAgreement_iff Sb _ _).mpr ⟨2, two_pos, uniformOn_two 4⟩

end Witness


end Holonics.Objects.RetentionCycles
