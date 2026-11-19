import HolonicsResearch.Objects.RetentionClasses

/-!
# The classes of the minimal retention on two bundles in series and on the triangle

[definition] Object 8 of `docs/ELEMENTARY_OBJECTS.md` with `Foundation/Standing.lean`: retention
is the future-sufficient quotient of the present, never a record of what shaped it. Source: #410's
box "The explicit classes of the square law's minimal retention on a general weighted graph (the
orbit structure of deposition on projective classes beyond two parallel edges), and for other
deposition laws", part done in #1031 by `HolonicsResearch/Objects/RetentionClasses` (forests, the
`m`-edge bundle under the square and Joule laws, a pendant edge). Its "What is not claimed" left
the graphs whose cycles do not all share their two ends (a cycle of three edges among them) and
two bundles in series, whose classes it expected to be "the product of the two bundles', each
driven by the series current"; the record of that pass (`2026-11-19_PETROVS_TYPES_PLACE_…_IN_LEAN`,
its note 2) says the series composition had been written as the pendant instead. Atlas rows read:
`deposition.minimal-retention`, `deposition.minimal-retention-general`,
`deposition.constitution-not-minimal`, `deposition.forest-retains-nothing`,
`deposition.bundle-minimal-retention`, `deposition.joule-bundle-projective-retention`,
`deposition.pendant-edge-forgotten`, `deposition.solve-sees-projective-class`,
`deposition.projective-class-not-retention` and `ph.triangle-witness`. Every statement holds for
every solver, including one that reads the flux record to choose its gauge, as in the owners.

What is proved.

1. [proved-derived; formal-checked] **A part that steps as a smaller medium reads that medium's
   futures.** If a projection `P` carries each composite letter to a letter of a smaller medium
   through `f`, `P (T' i x) = T (f i) (P x)`, then the part of every history is the smaller
   medium's history under the mapped word (`part_transportWord`); when `f` has a section, a reading
   of the part after every composite history is the same reading after every history of the
   smaller medium (`part_reading_iff`). Both bundles of item 2 use this one reduction.
2. [proved-derived; formal-checked] **Two bundles in series are read part by part.** On `m₁` edges
   from node `0` to node `1` followed by `m₂` edges from node `1` to node `2` (`seriesBundles`, with
   the parts `firstPart`, `secondPart` and their join `joinParts`), a source admits a balance
   exactly when its total charge is zero (`series_solves_iff`, `series_solvable_iff`). The first
   bundle carries the series current `σ₁ + σ₂ = −σ₀` split by its own shares and the second carries
   `σ₂` split by its own (`series_flux`, `series_drop_castAdd`, `series_drop_natAdd`,
   `series_observeConstitution`). So each part steps as its bundle under its folded source,
   `(σ₀, σ₁ + σ₂)` (the owner's `fold`) for the first and `(σ₀ + σ₁, σ₂)` (`foldSecond`) for the
   second, under any composite law that deposits on each bundle's edges as that bundle's law does
   (`firstPart_stepConstitution`, `secondPart_stepConstitution`). The composite's futures are read
   by the two parts' shares after every history, one series unit source reading both
   (`series_futureAgreement_iff_shares`; for one bundle, `bundle_futureAgreement_iff_shares`), and
   with item 1 two composite presents share every future exactly when each part shares every future
   on its own bundle (`series_futureAgreement_iff`): the composite's futures are pairs of the
   bundles' futures, driven independently.
3. [proved-derived; formal-checked] **The classes in series are the product of the bundles'.**
   Under the square law two presents share every future iff each part is equal to the other's or
   both are uniform (`series_square_futureAgreement_iff`), and the minimal retention is the pair of
   the bundles' `minimalRetain` (`seriesMinimalRetain`, `seriesMinimalRetain_eq_iff_futureAgreement`,
   `seriesMinimalStanding_exists`, `seriesMinimalRetain_factors_through_every_standing`). Under the
   Joule law each bundle scales by its own factor, `1 + ((σ₁ + σ₂)/T₁)²` and `1 + (σ₂/T₂)²`
   (`series_joule_step_scales`), the classes are pairs of projective classes
   (`series_joule_futureAgreement_iff`), and the minimal retention is the pair of shares
   (`seriesJouleMinimalRetain`, `seriesJouleMinimalRetain_eq_iff_futureAgreement`,
   `seriesJouleMinimalStanding_exists`, `seriesJouleMinimalRetain_factors_through_every_standing`);
   the composite's own projective class is strictly finer (`series_joule_witness`). With one edge
   per bundle the composite is the owner's forest `series` (`seriesBundles_one_one`), where every
   part is uniform and the pair is a point, as the owner's item 1 says. Witness (`series_witness`):
   on bundles of two and three edges the uniform presents with totals `(2, 3)` and `(5, 7)` share
   every future, while `(1, 2)` against `(1, 3)` on the first bundle is separated by one source.
4. [proved-derived; formal-checked] **On the triangle the constitution is the minimal retention.**
   On three nodes with one edge per pair (`triangle`: `a = 0 → 1`, `b = 1 → 2`, `c = 0 → 2`) a
   source admits a balance exactly when its total charge is zero, with the drops
   `(Θ_c σ₁ − Θ_b σ₀)/P` on `a` and `−(Θ_a σ₀ + (Θ_a + Θ_c) σ₁)/P` on `b` over the spanning-tree
   sum `P = Θ_aΘ_b + Θ_aΘ_c + Θ_bΘ_c` (`treeSum`, `dropA`, `dropB`, `triFlux`,
   `triangle_solves_iff`, `triangle_solvable_iff`, `triangle_flux`, `triangle_drop`,
   `triangle_observeConstitution`, `triangle_square_step_apply`). The unit source `0 → 1` sends
   `Θ_bΘ_c/P` around the far path and `1 → 2` sends `Θ_aΘ_c/P` (`triFlux_source01`,
   `triFlux_source12`); these two reads fix every ratio `Θ_e/Θ_f`
   (`projectivelyEqual_of_two_reads`), so the present observation reads the projective class and
   nothing more (`triangle_observe_iff_projectivelyEqual`, with the owner's
   `observeConstitution_scale`), and under any law future agreement keeps it after every history
   (`triangle_projectivelyEqual_of_futureAgreement`). Under the square law `cΘ` and `Θ` carry one
   flux (`triFlux_scale`), so a stroke deposits one `J = j²` on both, and `cΘ + J` stays a multiple
   of `Θ + J` with `c ≠ 1` only when `J` is proportional to `Θ` (`proportional_of_scaled_stroke`).
   No constitution takes both unit strokes `0 → 1` and `1 → 2` in proportion
   (`not_both_strokes_proportional`: the first needs `Θ_b = Θ_c`, the second `Θ_a = Θ_c`, and the
   first then needs `Θ_a = 4Θ_a`). Hence two presents share every future iff their constitutions
   are equal (`triangle_square_futureAgreement_iff`), and every lawful retention separates distinct
   constitutions (`triangle_constitution_factors_through_every_standing`): the minimal retention is
   the constitution, the retention of the owner's `constitutionStanding`, which on the parallel pair
   is not minimal (`constitution_is_not_minimal`). The expectation that one source reads the ratios
   and a stroke then the total (`agent-inferred` in the brief) holds with one refinement: one fixed
   stroke need not read the total. Witness (`triangle_witness`): the uniform `(1, 1, 1)` and
   `(2, 2, 2)` are separated, where uniform constitutions merge on every bundle; `(1, 4, 4)` and
   `(2, 8, 8)` agree on every source now and after the stroke `0 → 1`, which deposits `(1, 4, 4)/9`
   (`stroke01_oneFourFour`), and the stroke `1 → 2` separates them.

What is not claimed.

- Graphs with several independent cycles that do not share their two ends (a wheel, a grid, two
  triangles on one edge) and cycles of four or more edges: the triangle's argument uses its
  spanning-tree sum and its explicit unit fluxes, and no statement for a general graph is made. The
  box stays part done.
- Deposition laws other than the square and Joule laws, beyond item 2's reduction (every law that
  deposits on each bundle's edges as that bundle's law); the Joule law on the triangle is not
  computed.
- Series of three or more bundles, or bundles in series with a pendant, are not written, though
  item 1 applies part by part.
- Convergence or the long-run orbit of repeated deposition.
- `MinimalRetention.IsMinimal` is not restated: the kernel, the lawful standing and leastness are
  given in `Objects/Retention`'s form, as in the owner.

The computational object is the helical pair interaction read as a conducting contact, as in the
owner: each edge is a pair contact between two node potentials, its slip the drop `(dφ)_e`, its
current the flux `Θ_e (dφ)_e`, and deposition changes the contact's material by what crossed it.
In series the two bundles are two families of contacts joined at node `1`; the source fixes the
current that crosses node `1`, so each family's split reads only its own material and the retention
is the product of the two families'. On the triangle the far path couples each contact's split to
the material of the other two, and the minimal retention keeps all of it. Of the winding guide's six
general objects this touches the cell holonomy (the series' `m₁ + m₂ − 2` independent cycles each
lie inside one bundle and share its two ends; the triangle's one cycle runs through all three nodes,
so its split reads every edge), faces and placement (the solve's face is conserved under dilation of
the material: in series each bundle dilates on its own under the Joule law, and on the triangle the
present face reads exactly the projective class), and the tube (histories as ordered words of
admitted sources; a part's history is its bundle's history under the folded word). The helix, the
pair's modular address and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Objects.RetentionSeries

open Holonics
open Holonics.Objects.Deposition
open Holonics.Objects.RetentionClasses
open Holonics.Foundation.Standing
open Holonics.Foundation.CausalRelevance.NonLinear
open Holonics.Foundation.Chronology
open Matrix

/-! ## 1. A transport that factors through a section reads the same words -/

section Intertwine

variable {ι κ X Y β : Type*}

/-- [proved-derived; formal-checked] **A part that steps as a smaller medium steps along every
word**: if `P (T' i x) = T (f i) (P x)` for every letter, then the part of a history is the smaller
medium's history under the mapped word. -/
theorem part_transportWord (T' : ι → X → X) (T : κ → Y → Y) (P : X → Y) (f : ι → κ)
    (h : ∀ i x, P (T' i x) = T (f i) (P x)) (w : List ι) (x : X) :
    P (transportWord T' w x) = transportWord T (w.map f) (P x) := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [transportWord_cons, h, ih, List.map_cons, transportWord_cons]

/-- [proved-derived; formal-checked] **When the letter map has a section, the part's reading after
every composite word is the smaller medium's reading after every word of its own.** -/
theorem part_reading_iff (T' : ι → X → X) (T : κ → Y → Y) (P : X → Y) (f : ι → κ) (g : κ → ι)
    (hfg : ∀ k, f (g k) = k) (h : ∀ i x, P (T' i x) = T (f i) (P x)) (R : Y → β) (x y : X) :
    (∀ w : List ι, R (P (transportWord T' w x)) = R (P (transportWord T' w y))) ↔
      ∀ v : List κ, R (transportWord T v (P x)) = R (transportWord T v (P y)) := by
  have hfg' : f ∘ g = id := funext hfg
  constructor
  · intro H v
    have hv := H (v.map g)
    rwa [part_transportWord T' T P f h, part_transportWord T' T P f h, List.map_map, hfg',
      List.map_id] at hv
  · intro H w
    rw [part_transportWord T' T P f h, part_transportWord T' T P f h]
    exact H _

end Intertwine

/-! ## 2. Two bundles in series -/

section Series

variable {m₁ m₂ : ℕ}

/-- [definition] **Two bundles in series**: `m₁` edges from node `0` to node `1`, then `m₂` edges
from node `1` to node `2`. -/
def seriesBundles (m₁ m₂ : ℕ) : Matrix (Fin (m₁ + m₂)) (Fin 3) ℚ :=
  Fin.append (fun _ : Fin m₁ => ![-1, 1, 0]) (fun _ : Fin m₂ => ![0, -1, 1])

/-- [definition] The first bundle's part of a composite constitution. -/
def firstPart (Θ : Constitution (m₁ + m₂)) : Constitution m₁ :=
  ⟨fun e => Θ.1 (Fin.castAdd m₂ e), fun _ => Θ.2 _⟩

/-- [definition] The second bundle's part of a composite constitution. -/
def secondPart (Θ : Constitution (m₁ + m₂)) : Constitution m₂ :=
  ⟨fun f => Θ.1 (Fin.natAdd m₁ f), fun _ => Θ.2 _⟩

/-- [definition] Two bundle constitutions joined into one composite constitution. -/
def joinParts (Θ₁ : Constitution m₁) (Θ₂ : Constitution m₂) : Constitution (m₁ + m₂) :=
  ⟨Fin.append Θ₁.1 Θ₂.1, fun e => by
    refine Fin.addCases (fun e => ?_) (fun f => ?_) e
    · rw [Fin.append_left]; exact Θ₁.2 e
    · rw [Fin.append_right]; exact Θ₂.2 f⟩

/-- [proved-derived; formal-checked] The first part of a join is its first constitution. -/
@[simp] theorem firstPart_joinParts (Θ₁ : Constitution m₁) (Θ₂ : Constitution m₂) :
    firstPart (joinParts Θ₁ Θ₂) = Θ₁ := by
  apply Subtype.ext
  funext e
  simp [firstPart, joinParts]

/-- [proved-derived; formal-checked] The second part of a join is its second constitution. -/
@[simp] theorem secondPart_joinParts (Θ₁ : Constitution m₁) (Θ₂ : Constitution m₂) :
    secondPart (joinParts Θ₁ Θ₂) = Θ₂ := by
  apply Subtype.ext
  funext f
  simp [secondPart, joinParts]

/-- [definition] The source the second bundle sees: nodes `0` and `1` merged. (The first bundle
sees `RetentionClasses.fold`, nodes `1` and `2` merged.) -/
def foldSecond (σ : Fin 3 → ℚ) : Fin 2 → ℚ := ![σ 0 + σ 1, σ 2]

/-- [definition] A second-bundle source lifted to the composite with no charge at node `0`. -/
def liftSecond (τ : Fin 2 → ℚ) : Fin 3 → ℚ := ![0, τ 0, τ 1]

/-- [proved-derived; formal-checked] Folding a lifted second-bundle source returns it. -/
theorem foldSecond_liftSecond (τ : Fin 2 → ℚ) : foldSecond (liftSecond τ) = τ := by
  funext i
  fin_cases i <;> simp [foldSecond, liftSecond]

/-- [proved-derived; formal-checked] The second fold keeps the total charge. -/
theorem foldSecond_charge (σ : Fin 3 → ℚ) :
    foldSecond σ 0 + foldSecond σ 1 = σ 0 + σ 1 + σ 2 := by
  simp [foldSecond]

/-- [proved-derived; formal-checked] The rows of the first bundle are `(−1, 1, 0)`. -/
@[simp] theorem seriesBundles_castAdd (e : Fin m₁) :
    seriesBundles m₁ m₂ (Fin.castAdd m₂ e) = ![-1, 1, 0] := by
  simp [seriesBundles]

/-- [proved-derived; formal-checked] The rows of the second bundle are `(0, −1, 1)`. -/
@[simp] theorem seriesBundles_natAdd (f : Fin m₂) :
    seriesBundles m₁ m₂ (Fin.natAdd m₁ f) = ![0, -1, 1] := by
  simp [seriesBundles]

/-- [proved-derived; formal-checked] Every edge of the first bundle reads the drop `φ₁ − φ₀`. -/
theorem seriesBundles_mulVec_castAdd (φ : Fin 3 → ℚ) (e : Fin m₁) :
    (seriesBundles m₁ m₂ *ᵥ φ) (Fin.castAdd m₂ e) = φ 1 - φ 0 := by
  simp [mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- [proved-derived; formal-checked] Every edge of the second bundle reads the drop `φ₂ − φ₁`. -/
theorem seriesBundles_mulVec_natAdd (φ : Fin 3 → ℚ) (f : Fin m₂) :
    (seriesBundles m₁ m₂ *ᵥ φ) (Fin.natAdd m₁ f) = φ 2 - φ 1 := by
  simp [mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- [proved-derived; formal-checked] The composite's boundary of an edge vector. -/
theorem seriesBundles_transpose_mulVec (j : Fin (m₁ + m₂) → ℚ) :
    (seriesBundles m₁ m₂)ᵀ *ᵥ j =
      ![-(∑ e : Fin m₁, j (Fin.castAdd m₂ e)),
        (∑ e : Fin m₁, j (Fin.castAdd m₂ e)) - ∑ f : Fin m₂, j (Fin.natAdd m₁ f),
        ∑ f : Fin m₂, j (Fin.natAdd m₁ f)] := by
  funext i
  simp only [mulVec, dotProduct, transpose_apply, Fin.sum_univ_add, seriesBundles_castAdd,
    seriesBundles_natAdd]
  fin_cases i
  · simp [Finset.sum_neg_distrib]
  · simp
    ring
  · simp

/-- [proved-derived; formal-checked] **The composite's balance.** `φ` solves `σ` exactly when `σ`
has zero total charge, the first bundle's common drop is `(σ₁ + σ₂)/T₁` and the second's is
`σ₂/T₂`, each over its own bundle's total. -/
theorem series_solves_iff [NeZero m₁] [NeZero m₂] (Θ : Constitution (m₁ + m₂)) (φ σ : Fin 3 → ℚ) :
    Solves (seriesBundles m₁ m₂) Θ φ σ ↔
      σ 0 + σ 1 + σ 2 = 0 ∧ φ 1 - φ 0 = (σ 1 + σ 2) / total (firstPart Θ) ∧
        φ 2 - φ 1 = σ 2 / total (secondPart Θ) := by
  have hT₁ := (total_pos (firstPart Θ)).ne'
  have hT₂ := (total_pos (secondPart Θ)).ne'
  rw [solves_iff_boundary_flux, seriesBundles_transpose_mulVec]
  have hsum₁ : ∑ e : Fin m₁, flux (seriesBundles m₁ m₂) Θ φ (Fin.castAdd m₂ e) =
      total (firstPart Θ) * (φ 1 - φ 0) := by
    simp only [flux, seriesBundles_mulVec_castAdd, total, firstPart, Finset.sum_mul]
  have hsum₂ : ∑ f : Fin m₂, flux (seriesBundles m₁ m₂) Θ φ (Fin.natAdd m₁ f) =
      total (secondPart Θ) * (φ 2 - φ 1) := by
    simp only [flux, seriesBundles_mulVec_natAdd, total, secondPart, Finset.sum_mul]
  rw [hsum₁, hsum₂]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp at h0 h1 h2
    refine ⟨by linarith, ?_, ?_⟩
    · rw [eq_div_iff hT₁]
      linarith
    · rw [eq_div_iff hT₂]
      linarith
  · rintro ⟨h012, hg₁, hg₂⟩
    rw [hg₁, hg₂]
    funext i
    fin_cases i
    · simp
      field_simp
      linarith
    · simp
      field_simp
      ring
    · simp
      field_simp

/-- [proved-derived; formal-checked] On the composite a source admits a balance exactly when its
total charge is zero. -/
theorem series_solvable_iff [NeZero m₁] [NeZero m₂] (Θ : Constitution (m₁ + m₂)) (σ : Fin 3 → ℚ) :
    (∃ φ, Solves (seriesBundles m₁ m₂) Θ φ σ) ↔ σ 0 + σ 1 + σ 2 = 0 := by
  constructor
  · rintro ⟨φ, h⟩
    exact ((series_solves_iff Θ φ σ).mp h).1
  · intro h
    refine ⟨![0, (σ 1 + σ 2) / total (firstPart Θ),
      (σ 1 + σ 2) / total (firstPart Θ) + σ 2 / total (secondPart Θ)],
      (series_solves_iff Θ _ σ).mpr ⟨h, by simp, by simp⟩⟩

/-- [proved-derived; formal-checked] **The series current splits in each bundle by that bundle's
shares**: `j_e = r_e (σ₁ + σ₂)` on the first bundle and `j_f = r_f σ₂` on the second. -/
theorem series_flux [NeZero m₁] [NeZero m₂] {Θ : Constitution (m₁ + m₂)} {φ σ : Fin 3 → ℚ}
    (h : Solves (seriesBundles m₁ m₂) Θ φ σ) :
    flux (seriesBundles m₁ m₂) Θ φ =
      Fin.append (fun e => share (firstPart Θ) e * (σ 1 + σ 2))
        (fun f => share (secondPart Θ) f * σ 2) := by
  obtain ⟨-, hg₁, hg₂⟩ := (series_solves_iff Θ φ σ).mp h
  funext e
  refine Fin.addCases (fun e => ?_) (fun f => ?_) e
  · rw [Fin.append_left]
    simp only [flux, seriesBundles_mulVec_castAdd, hg₁, share, firstPart]
    ring
  · rw [Fin.append_right]
    simp only [flux, seriesBundles_mulVec_natAdd, hg₂, share, secondPart]
    ring

/-- [proved-derived; formal-checked] Every edge of the first bundle sees the drop `(σ₁ + σ₂)/T₁`. -/
theorem series_drop_castAdd [NeZero m₁] [NeZero m₂] {Θ : Constitution (m₁ + m₂)}
    {φ σ : Fin 3 → ℚ} (h : Solves (seriesBundles m₁ m₂) Θ φ σ) (e : Fin m₁) :
    (seriesBundles m₁ m₂ *ᵥ φ) (Fin.castAdd m₂ e) = (σ 1 + σ 2) / total (firstPart Θ) := by
  rw [seriesBundles_mulVec_castAdd, ((series_solves_iff Θ φ σ).mp h).2.1]

/-- [proved-derived; formal-checked] Every edge of the second bundle sees the drop `σ₂/T₂`. -/
theorem series_drop_natAdd [NeZero m₁] [NeZero m₂] {Θ : Constitution (m₁ + m₂)}
    {φ σ : Fin 3 → ℚ} (h : Solves (seriesBundles m₁ m₂) Θ φ σ) (f : Fin m₂) :
    (seriesBundles m₁ m₂ *ᵥ φ) (Fin.natAdd m₁ f) = σ 2 / total (secondPart Θ) := by
  rw [seriesBundles_mulVec_natAdd, ((series_solves_iff Θ φ σ).mp h).2.2]

/-- [proved-derived; formal-checked] **The composite's present observation reads the two bundles'
shares**, each driven by its series current. -/
theorem series_observeConstitution [NeZero m₁] [NeZero m₂] (σ : Fin 3 → ℚ)
    (Θ : Constitution (m₁ + m₂)) :
    observeConstitution (seriesBundles m₁ m₂) σ Θ =
      if σ 0 + σ 1 + σ 2 = 0 then
        some (Fin.append (fun e => share (firstPart Θ) e * (σ 1 + σ 2))
          (fun f => share (secondPart Θ) f * σ 2))
      else none := by
  by_cases h : σ 0 + σ 1 + σ 2 = 0
  · have hs := (series_solvable_iff Θ σ).mpr h
    rw [observeConstitution, if_pos hs, if_pos h, series_flux (canonicalSolve_solves hs)]
  · rw [observeConstitution, if_neg (fun hs => h ((series_solvable_iff Θ σ).mp hs)), if_neg h]

/-- [proved-derived; formal-checked] **The first part steps as the first bundle under its folded
source**, for any composite law that deposits on the first bundle's edges as that bundle's law. -/
theorem firstPart_stepConstitution [NeZero m₁] [NeZero m₂] (L' : DepositionLaw (m₁ + m₂))
    (L : DepositionLaw m₁) (hL : ∀ e j g, L'.Γ (Fin.castAdd m₂ e) j g = L.Γ e j g)
    (σ : Fin 3 → ℚ) (Θ : Constitution (m₁ + m₂)) :
    firstPart (stepConstitution L' (seriesBundles m₁ m₂) σ Θ) =
      stepConstitution L (bundle m₁) (fold σ) (firstPart Θ) := by
  by_cases h : σ 0 + σ 1 + σ 2 = 0
  · have hs := (series_solvable_iff Θ σ).mpr h
    have hb : fold σ 0 + fold σ 1 = 0 := by rw [fold_charge]; exact h
    apply Subtype.ext
    funext e
    rw [bundle_stepConstitution_apply L hb]
    show (stepConstitution L' (seriesBundles m₁ m₂) σ Θ).1 (Fin.castAdd m₂ e) = _
    rw [stepConstitution, if_pos hs]
    simp only [deposit]
    rw [series_flux (canonicalSolve_solves hs), series_drop_castAdd (canonicalSolve_solves hs),
      Fin.append_left, hL]
    simp [fold, firstPart]
  · have hb : fold σ 0 + fold σ 1 ≠ 0 := by rw [fold_charge]; exact h
    rw [bundle_stepConstitution_of_ne L hb, stepConstitution,
      if_neg (fun hs => h ((series_solvable_iff Θ σ).mp hs))]

/-- [proved-derived; formal-checked] **The second part steps as the second bundle under its folded
source**, for any composite law that deposits on the second bundle's edges as that bundle's law. -/
theorem secondPart_stepConstitution [NeZero m₁] [NeZero m₂] (L' : DepositionLaw (m₁ + m₂))
    (L : DepositionLaw m₂) (hL : ∀ f j g, L'.Γ (Fin.natAdd m₁ f) j g = L.Γ f j g)
    (σ : Fin 3 → ℚ) (Θ : Constitution (m₁ + m₂)) :
    secondPart (stepConstitution L' (seriesBundles m₁ m₂) σ Θ) =
      stepConstitution L (bundle m₂) (foldSecond σ) (secondPart Θ) := by
  by_cases h : σ 0 + σ 1 + σ 2 = 0
  · have hs := (series_solvable_iff Θ σ).mpr h
    have hb : foldSecond σ 0 + foldSecond σ 1 = 0 := by rw [foldSecond_charge]; exact h
    apply Subtype.ext
    funext f
    rw [bundle_stepConstitution_apply L hb]
    show (stepConstitution L' (seriesBundles m₁ m₂) σ Θ).1 (Fin.natAdd m₁ f) = _
    rw [stepConstitution, if_pos hs]
    simp only [deposit]
    rw [series_flux (canonicalSolve_solves hs), series_drop_natAdd (canonicalSolve_solves hs),
      Fin.append_right, hL]
    simp [foldSecond, secondPart]
  · have hb : foldSecond σ 0 + foldSecond σ 1 ≠ 0 := by rw [foldSecond_charge]; exact h
    rw [bundle_stepConstitution_of_ne L hb, stepConstitution,
      if_neg (fun hs => h ((series_solvable_iff Θ σ).mp hs))]

/-- [definition] **The series unit source**: one unit leaves node `0` and arrives at node `2`,
crossing both bundles. -/
def seriesUnit : Fin 3 → ℚ := ![-1, 0, 1]

/-- [proved-derived; formal-checked] **The composite's futures are read by the two parts'
shares**: two presents share every future exactly when, after every history, the first parts
have equal shares and the second parts have equal shares. One series unit source reads both. -/
theorem series_futureAgreement_iff_shares [NeZero m₁] [NeZero m₂] (L' : DepositionLaw (m₁ + m₂))
    (S : Solver (seriesBundles m₁ m₂)) (left right : DepositState (m₁ + m₂)) :
    futureAgreement (observe S) (step L' S) left right ↔
      ∀ word : List (Fin 3 → ℚ),
        share (firstPart (transportWord (stepConstitution L' (seriesBundles m₁ m₂)) word
            left.constitution)) =
          share (firstPart (transportWord (stepConstitution L' (seriesBundles m₁ m₂)) word
            right.constitution)) ∧
        share (secondPart (transportWord (stepConstitution L' (seriesBundles m₁ m₂)) word
            left.constitution)) =
          share (secondPart (transportWord (stepConstitution L' (seriesBundles m₁ m₂)) word
            right.constitution)) := by
  have hc : seriesUnit 0 + seriesUnit 1 + seriesUnit 2 = 0 := by simp [seriesUnit]
  constructor
  · intro h word
    have hw := h seriesUnit word
    rw [observe_eq_observeConstitution, observe_eq_observeConstitution, transportWord_constitution,
      transportWord_constitution, series_observeConstitution, series_observeConstitution,
      if_pos hc, if_pos hc] at hw
    have hj := Option.some.inj hw
    refine ⟨funext fun e => ?_, funext fun f => ?_⟩
    · have he := congrFun hj (Fin.castAdd m₂ e)
      simpa [seriesUnit] using he
    · have hf := congrFun hj (Fin.natAdd m₁ f)
      simpa [seriesUnit] using hf
  · intro h σ word
    rw [observe_eq_observeConstitution, observe_eq_observeConstitution, transportWord_constitution,
      transportWord_constitution, series_observeConstitution, series_observeConstitution,
      (h word).1, (h word).2]

/-- [proved-derived; formal-checked] **A bundle's futures are read by its shares**: two bundle
presents share every future under a law exactly when their shares agree after every history. -/
theorem bundle_futureAgreement_iff_shares {m : ℕ} [NeZero m] (L : DepositionLaw m)
    (S : Solver (bundle m)) (left right : DepositState m) :
    futureAgreement (observe S) (step L S) left right ↔
      ∀ word : List (Fin 2 → ℚ),
        share (transportWord (stepConstitution L (bundle m)) word left.constitution) =
          share (transportWord (stepConstitution L (bundle m)) word right.constitution) := by
  constructor
  · intro h word
    exact funext (share_eq_of_futureAgreement L S h word)
  · intro h σ word
    rw [observe_eq_observeConstitution, observe_eq_observeConstitution, transportWord_constitution,
      transportWord_constitution, bundle_observeConstitution, bundle_observeConstitution, h word]

/-- [proved-derived; formal-checked] **The composite's futures are the pairs of the bundles'
futures, driven independently.** For any solvers and any composite law that deposits on each
bundle's edges as that bundle's law, two composite presents share every future exactly when their
first parts share every future on the first bundle and their second parts on the second. -/
theorem series_futureAgreement_iff [NeZero m₁] [NeZero m₂] (L' : DepositionLaw (m₁ + m₂))
    (L₁ : DepositionLaw m₁) (L₂ : DepositionLaw m₂)
    (hL₁ : ∀ e j g, L'.Γ (Fin.castAdd m₂ e) j g = L₁.Γ e j g)
    (hL₂ : ∀ f j g, L'.Γ (Fin.natAdd m₁ f) j g = L₂.Γ f j g) (S : Solver (seriesBundles m₁ m₂))
    (S₁ : Solver (bundle m₁)) (S₂ : Solver (bundle m₂)) (left right : DepositState (m₁ + m₂)) :
    futureAgreement (observe S) (step L' S) left right ↔
      futureAgreement (observe S₁) (step L₁ S₁) ⟨firstPart left.constitution, []⟩
          ⟨firstPart right.constitution, []⟩ ∧
        futureAgreement (observe S₂) (step L₂ S₂) ⟨secondPart left.constitution, []⟩
          ⟨secondPart right.constitution, []⟩ := by
  rw [series_futureAgreement_iff_shares, bundle_futureAgreement_iff_shares,
    bundle_futureAgreement_iff_shares, forall_and]
  exact and_congr
    (part_reading_iff _ _ firstPart fold lift fold_lift
      (firstPart_stepConstitution L' L₁ hL₁) share _ _)
    (part_reading_iff _ _ secondPart foldSecond liftSecond foldSecond_liftSecond
      (secondPart_stepConstitution L' L₂ hL₂) share _ _)

/-- [proved-derived; formal-checked] **The square law on two bundles in series.** Two presents
share every future iff each bundle's part satisfies the bundle's criterion on its own: equal, or
both uniform. -/
theorem series_square_futureAgreement_iff [NeZero m₁] [NeZero m₂]
    (S : Solver (seriesBundles m₁ m₂)) (left right : DepositState (m₁ + m₂)) :
    futureAgreement (observe S) (step (squareLawOn (m₁ + m₂)) S) left right ↔
      (firstPart left.constitution = firstPart right.constitution ∨
          (Uniform (firstPart left.constitution) ∧ Uniform (firstPart right.constitution))) ∧
        (secondPart left.constitution = secondPart right.constitution ∨
          (Uniform (secondPart left.constitution) ∧ Uniform (secondPart right.constitution))) :=
  (series_futureAgreement_iff _ (squareLawOn m₁) (squareLawOn m₂) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) S (canonicalSolver _) (canonicalSolver _) left right).trans
    (and_congr (bundle_futureAgreement_iff _ _ _) (bundle_futureAgreement_iff _ _ _))

/-- [proved-derived; formal-checked] **The Joule law on two bundles in series.** Two presents share
every future iff each bundle's part is projectively equal to the other's, each by its own factor. -/
theorem series_joule_futureAgreement_iff [NeZero m₁] [NeZero m₂]
    (S : Solver (seriesBundles m₁ m₂)) (left right : DepositState (m₁ + m₂)) :
    futureAgreement (observe S) (step (jouleLawOn (m₁ + m₂)) S) left right ↔
      ProjectivelyEqual (firstPart left.constitution) (firstPart right.constitution) ∧
        ProjectivelyEqual (secondPart left.constitution) (secondPart right.constitution) :=
  (series_futureAgreement_iff _ (jouleLawOn m₁) (jouleLawOn m₂) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) S (canonicalSolver _) (canonicalSolver _) left right).trans
    (and_congr (joule_bundle_futureAgreement_iff _ _ _) (joule_bundle_futureAgreement_iff _ _ _))

/-- [proved-derived; formal-checked] **Under the Joule law each bundle scales by its own factor**:
one step multiplies the first part by `1 + ((σ₁ + σ₂)/T₁)²` and the second by `1 + (σ₂/T₂)²`
(or both by `1` when the source admits no balance). -/
theorem series_joule_step_scales [NeZero m₁] [NeZero m₂] (σ : Fin 3 → ℚ)
    (Θ : Constitution (m₁ + m₂)) :
    (∃ c : ℚ, ∃ hc : 0 < c, firstPart (stepConstitution (jouleLawOn (m₁ + m₂))
        (seriesBundles m₁ m₂) σ Θ) = Retention.scaleConstitution c hc (firstPart Θ)) ∧
      ∃ c : ℚ, ∃ hc : 0 < c, secondPart (stepConstitution (jouleLawOn (m₁ + m₂))
        (seriesBundles m₁ m₂) σ Θ) = Retention.scaleConstitution c hc (secondPart Θ) := by
  rw [firstPart_stepConstitution _ (jouleLawOn m₁) (fun _ _ _ => rfl),
    secondPart_stepConstitution _ (jouleLawOn m₂) (fun _ _ _ => rfl)]
  exact ⟨joule_stepConstitution_scale _ _, joule_stepConstitution_scale _ _⟩

/-- [definition] **The minimal retention of the square law on two bundles in series**: the pair of
the bundles' minimal retentions, each bundle's uniform class collapsed to one point. -/
def seriesMinimalRetain (state : DepositState (m₁ + m₂)) :
    Option (Constitution m₁) × Option (Constitution m₂) :=
  (minimalRetain (⟨firstPart state.constitution, []⟩ : DepositState m₁),
    minimalRetain (⟨secondPart state.constitution, []⟩ : DepositState m₂))

/-- [proved-derived; formal-checked] **Its kernel is future agreement.** -/
theorem seriesMinimalRetain_eq_iff_futureAgreement [NeZero m₁] [NeZero m₂]
    (S : Solver (seriesBundles m₁ m₂)) (left right : DepositState (m₁ + m₂)) :
    seriesMinimalRetain left = seriesMinimalRetain right ↔
      futureAgreement (observe S) (step (squareLawOn (m₁ + m₂)) S) left right := by
  rw [series_futureAgreement_iff _ (squareLawOn m₁) (squareLawOn m₂) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) S (canonicalSolver _) (canonicalSolver _),
    ← minimalRetain_eq_iff_futureAgreement, ← minimalRetain_eq_iff_futureAgreement,
    seriesMinimalRetain, seriesMinimalRetain, Prod.mk.injEq]

/-- [proved-derived; formal-checked] **It is a lawful standing.** -/
theorem seriesMinimalStanding_exists [NeZero m₁] [NeZero m₂] (S : Solver (seriesBundles m₁ m₂)) :
    ∃ L : StandingLaw (Fin 3 → ℚ) (Fin 3 → ℚ) (DepositState (m₁ + m₂))
        (Option (Constitution m₁) × Option (Constitution m₂)) (Option (Fin (m₁ + m₂) → ℚ)),
      L.transport = step (squareLawOn (m₁ + m₂)) S ∧ L.observe = observe S ∧
        L.retain = seriesMinimalRetain := by
  rw [standingLaw_exists_iff_future_factors]
  intro left right h
  exact (causalSignature_eq_iff_futureAgreement _ _ _ _).mpr
    ((seriesMinimalRetain_eq_iff_futureAgreement S left right).mp h)

/-- [proved-derived; formal-checked] **It is least**: every retention carrying a `StandingLaw` for
the same composite medium refines it. -/
theorem seriesMinimalRetain_factors_through_every_standing [NeZero m₁] [NeZero m₂]
    (S : Solver (seriesBundles m₁ m₂)) {Retained : Type*}
    (L : StandingLaw (Fin 3 → ℚ) (Fin 3 → ℚ) (DepositState (m₁ + m₂)) Retained
      (Option (Fin (m₁ + m₂) → ℚ)))
    (htransport : L.transport = step (squareLawOn (m₁ + m₂)) S) (hobserve : L.observe = observe S)
    {left right : DepositState (m₁ + m₂)} (h : L.retain left = L.retain right) :
    seriesMinimalRetain left = seriesMinimalRetain right := by
  have hagree := L.futureAgreement_of_retain_eq h
  rw [htransport, hobserve] at hagree
  exact (seriesMinimalRetain_eq_iff_futureAgreement S left right).mpr hagree

/-- [definition] **The minimal retention of the Joule law on two bundles in series**: the pair of
the bundles' shares, one normalized projective class per bundle. -/
def seriesJouleMinimalRetain (state : DepositState (m₁ + m₂)) : (Fin m₁ → ℚ) × (Fin m₂ → ℚ) :=
  (share (firstPart state.constitution), share (secondPart state.constitution))

/-- [proved-derived; formal-checked] **Its kernel is future agreement.** -/
theorem seriesJouleMinimalRetain_eq_iff_futureAgreement [NeZero m₁] [NeZero m₂]
    (S : Solver (seriesBundles m₁ m₂)) (left right : DepositState (m₁ + m₂)) :
    seriesJouleMinimalRetain left = seriesJouleMinimalRetain right ↔
      futureAgreement (observe S) (step (jouleLawOn (m₁ + m₂)) S) left right := by
  rw [series_joule_futureAgreement_iff, seriesJouleMinimalRetain, seriesJouleMinimalRetain,
    Prod.mk.injEq, share_eq_iff_projectivelyEqual, share_eq_iff_projectivelyEqual]

/-- [proved-derived; formal-checked] **It is a lawful standing.** -/
theorem seriesJouleMinimalStanding_exists [NeZero m₁] [NeZero m₂]
    (S : Solver (seriesBundles m₁ m₂)) :
    ∃ L : StandingLaw (Fin 3 → ℚ) (Fin 3 → ℚ) (DepositState (m₁ + m₂))
        ((Fin m₁ → ℚ) × (Fin m₂ → ℚ)) (Option (Fin (m₁ + m₂) → ℚ)),
      L.transport = step (jouleLawOn (m₁ + m₂)) S ∧ L.observe = observe S ∧
        L.retain = seriesJouleMinimalRetain := by
  rw [standingLaw_exists_iff_future_factors]
  intro left right h
  exact (causalSignature_eq_iff_futureAgreement _ _ _ _).mpr
    ((seriesJouleMinimalRetain_eq_iff_futureAgreement S left right).mp h)

/-- [proved-derived; formal-checked] **It is least**: every retention carrying a `StandingLaw` for
the Joule composite refines it. -/
theorem seriesJouleMinimalRetain_factors_through_every_standing [NeZero m₁] [NeZero m₂]
    (S : Solver (seriesBundles m₁ m₂)) {Retained : Type*}
    (L : StandingLaw (Fin 3 → ℚ) (Fin 3 → ℚ) (DepositState (m₁ + m₂)) Retained
      (Option (Fin (m₁ + m₂) → ℚ)))
    (htransport : L.transport = step (jouleLawOn (m₁ + m₂)) S) (hobserve : L.observe = observe S)
    {left right : DepositState (m₁ + m₂)} (h : L.retain left = L.retain right) :
    seriesJouleMinimalRetain left = seriesJouleMinimalRetain right := by
  have hagree := L.futureAgreement_of_retain_eq h
  rw [htransport, hobserve] at hagree
  exact (seriesJouleMinimalRetain_eq_iff_futureAgreement S left right).mpr hagree

/-! ### The witness -/

/-- [definition] A bundle constitution of two edges from its two conductances. -/
def pairOf (a b : ℚ) (ha : 0 < a) (hb : 0 < b) : Constitution 2 :=
  ⟨![a, b], by intro e; fin_cases e <;> simpa⟩

/-- [definition] A uniform bundle constitution of three edges. -/
def uniformThree (a : ℚ) (ha : 0 < a) : Constitution 3 := ⟨fun _ => a, fun _ => ha⟩

/-- [proved-derived; formal-checked] Two equal conductances are a uniform pair. -/
theorem pairOf_uniform (a : ℚ) (ha : 0 < a) : Uniform (pairOf a a ha ha) := by
  intro e f
  fin_cases e <;> fin_cases f <;> rfl

/-- [proved-derived; formal-checked] One conductance on every edge is uniform. -/
theorem uniformThree_uniform (a : ℚ) (ha : 0 < a) : Uniform (uniformThree a ha) := fun _ _ => rfl

/-- [counterexample; formal-checked] **The witness.** On a bundle of two edges in series with a
bundle of three, under the square law: the uniform presents with totals `(2, 3)` and `(5, 7)`
share every future, whatever their records; and `(1, 2)` on the first bundle against `(1, 3)`
(shares `(1/3, 2/3)` against `(1/4, 3/4)`), each with a uniform second bundle of a different total,
are separated by the one series unit source, so they do not share every future. -/
theorem series_witness (S : Solver (seriesBundles 2 3)) (rl rr : List (Fin 5 → ℚ)) :
    futureAgreement (observe S) (step (squareLawOn 5) S)
        ⟨joinParts (pairOf 1 1 one_pos one_pos) (uniformThree 1 one_pos), rl⟩
        ⟨joinParts (pairOf (5 / 2) (5 / 2) (by norm_num) (by norm_num))
          (uniformThree (7 / 3) (by norm_num)), rr⟩ ∧
      observe S seriesUnit ⟨joinParts (pairOf 1 2 one_pos two_pos) (uniformThree 1 one_pos), rl⟩ ≠
        observe S seriesUnit
          ⟨joinParts (pairOf 1 3 one_pos three_pos) (uniformThree 2 two_pos), rr⟩ ∧
      ¬ futureAgreement (observe S) (step (squareLawOn 5) S)
        ⟨joinParts (pairOf 1 2 one_pos two_pos) (uniformThree 1 one_pos), rl⟩
        ⟨joinParts (pairOf 1 3 one_pos three_pos) (uniformThree 2 two_pos), rr⟩ := by
  have hne : observe S seriesUnit
      ⟨joinParts (pairOf 1 2 one_pos two_pos) (uniformThree 1 one_pos), rl⟩ ≠
        observe S seriesUnit
          ⟨joinParts (pairOf 1 3 one_pos three_pos) (uniformThree 2 two_pos), rr⟩ := by
    have hc : seriesUnit 0 + seriesUnit 1 + seriesUnit 2 = 0 := by simp [seriesUnit]
    rw [observe_eq_observeConstitution, observe_eq_observeConstitution, series_observeConstitution,
      series_observeConstitution, if_pos hc, if_pos hc]
    intro h
    have h0 := congrFun (Option.some.inj h) (Fin.castAdd 3 0)
    simp only [Fin.append_left, firstPart_joinParts] at h0
    have hu : seriesUnit 1 + seriesUnit 2 = 1 := by simp [seriesUnit]
    rw [hu] at h0
    norm_num [share, total, pairOf, Fin.sum_univ_two] at h0
  refine ⟨(series_square_futureAgreement_iff S _ _).mpr ?_, hne, fun h => hne (h seriesUnit [])⟩
  simp only [firstPart_joinParts, secondPart_joinParts]
  exact ⟨Or.inr ⟨pairOf_uniform _ _, pairOf_uniform _ _⟩,
    Or.inr ⟨uniformThree_uniform _ _, uniformThree_uniform _ _⟩⟩

/-- [counterexample; formal-checked] **Under the Joule law the composite's own projective class
is finer than the retention**: `(1, 2 | 1, 1, 1)` and `(1, 2 | 2, 2, 2)` share every future (each
bundle keeps its own class) though neither composite constitution is a multiple of the other. -/
theorem series_joule_witness (S : Solver (seriesBundles 2 3)) :
    futureAgreement (observe S) (step (jouleLawOn 5) S)
        ⟨joinParts (pairOf 1 2 one_pos two_pos) (uniformThree 1 one_pos), []⟩
        ⟨joinParts (pairOf 1 2 one_pos two_pos) (uniformThree 2 two_pos), []⟩ ∧
      ¬ ProjectivelyEqual (joinParts (pairOf 1 2 one_pos two_pos) (uniformThree 1 one_pos))
        (joinParts (pairOf 1 2 one_pos two_pos) (uniformThree 2 two_pos)) := by
  refine ⟨(series_joule_futureAgreement_iff S _ _).mpr ?_, ?_⟩
  · simp only [firstPart_joinParts, secondPart_joinParts]
    refine ⟨⟨1, one_pos, Subtype.ext (funext fun e => ?_)⟩,
      ⟨2, two_pos, Subtype.ext (funext fun e => ?_)⟩⟩
    · simp [Retention.scaleConstitution]
    · simp [Retention.scaleConstitution, uniformThree]
  · rintro ⟨c, hc, h⟩
    have h1 := congrArg (fun Θ : Constitution 5 => Θ.1 (Fin.castAdd 3 0)) h
    have h2 := congrArg (fun Θ : Constitution 5 => Θ.1 (Fin.natAdd 2 (0 : Fin 3))) h
    simp only [joinParts, Retention.scaleConstitution, Fin.append_left, Fin.append_right] at h1 h2
    simp [pairOf, uniformThree] at h1 h2
    linarith

/-- [proved-derived; formal-checked] **One edge per bundle is the owner's path of two edges**, a
forest (`RetentionClasses.series`): there each bundle is uniform and nothing is retained. -/
theorem seriesBundles_one_one : seriesBundles 1 1 = RetentionClasses.series := by
  ext e i
  fin_cases e <;> fin_cases i <;> rfl

end Series

/-! ## 3. The triangle: a cycle whose edges do not share two ends -/

section Triangle

/-- [definition] **The triangle**: three nodes, one edge per pair, `a = 0 → 1`, `b = 1 → 2`,
`c = 0 → 2`. -/
def triangle : Matrix (Fin 3) (Fin 3) ℚ := !![-1, 1, 0; 0, -1, 1; -1, 0, 1]

/-- [definition] **The spanning-tree sum** `P = Θ_a Θ_b + Θ_a Θ_c + Θ_b Θ_c`: the sum over the
triangle's three spanning trees of their conductance products. -/
def treeSum (Θ : Constitution 3) : ℚ := Θ.1 0 * Θ.1 1 + Θ.1 0 * Θ.1 2 + Θ.1 1 * Θ.1 2

/-- [proved-derived; formal-checked] The spanning-tree sum is positive. -/
theorem treeSum_pos (Θ : Constitution 3) : 0 < treeSum Θ := by
  have h0 := Θ.2 0
  have h1 := Θ.2 1
  have h2 := Θ.2 2
  unfold treeSum
  positivity

/-- [definition] The drop `φ₁ − φ₀` of edge `a` under the source `σ`: `(Θ_c σ₁ − Θ_b σ₀)/P`. -/
def dropA (Θ : Constitution 3) (σ : Fin 3 → ℚ) : ℚ := (Θ.1 2 * σ 1 - Θ.1 1 * σ 0) / treeSum Θ

/-- [definition] The drop `φ₂ − φ₁` of edge `b` under the source `σ`:
`−(Θ_a σ₀ + (Θ_a + Θ_c) σ₁)/P`. -/
def dropB (Θ : Constitution 3) (σ : Fin 3 → ℚ) : ℚ :=
  -(Θ.1 0 * σ 0 + (Θ.1 0 + Θ.1 2) * σ 1) / treeSum Θ

/-- [definition] **The triangle's flux** under the source `σ`: each edge's conductance times its
drop, the drop of `c` being the sum of the drops of `a` and `b`. -/
def triFlux (Θ : Constitution 3) (σ : Fin 3 → ℚ) : Fin 3 → ℚ :=
  ![Θ.1 0 * dropA Θ σ, Θ.1 1 * dropB Θ σ, Θ.1 2 * (dropA Θ σ + dropB Θ σ)]

/-- [proved-derived; formal-checked] The triangle's drops: `c` reads the sum of `a` and `b`. -/
theorem triangle_mulVec (φ : Fin 3 → ℚ) :
    triangle *ᵥ φ = ![φ 1 - φ 0, φ 2 - φ 1, (φ 1 - φ 0) + (φ 2 - φ 1)] := by
  funext e
  fin_cases e <;> simp [triangle, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- [proved-derived; formal-checked] The triangle's boundary of its flux, node by node. -/
theorem triangle_boundary_flux (Θ : Constitution 3) (φ : Fin 3 → ℚ) :
    triangleᵀ *ᵥ flux triangle Θ φ =
      ![-(Θ.1 0 * (φ 1 - φ 0)) - Θ.1 2 * ((φ 1 - φ 0) + (φ 2 - φ 1)),
        Θ.1 0 * (φ 1 - φ 0) - Θ.1 1 * (φ 2 - φ 1),
        Θ.1 1 * (φ 2 - φ 1) + Θ.1 2 * ((φ 1 - φ 0) + (φ 2 - φ 1))] := by
  have hf : flux triangle Θ φ =
      ![Θ.1 0 * (φ 1 - φ 0), Θ.1 1 * (φ 2 - φ 1), Θ.1 2 * ((φ 1 - φ 0) + (φ 2 - φ 1))] := by
    funext e
    simp only [flux, triangle_mulVec]
    fin_cases e <;> rfl
  rw [hf]
  funext i
  fin_cases i <;> simp [triangle, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- [proved-derived; formal-checked] **The triangle's balance.** `φ` solves `σ` exactly when `σ`
has zero total charge and the drops of `a` and `b` are `dropA` and `dropB`. -/
theorem triangle_solves_iff (Θ : Constitution 3) (φ σ : Fin 3 → ℚ) :
    Solves triangle Θ φ σ ↔
      σ 0 + σ 1 + σ 2 = 0 ∧ φ 1 - φ 0 = dropA Θ σ ∧ φ 2 - φ 1 = dropB Θ σ := by
  have hP := (treeSum_pos Θ).ne'
  rw [solves_iff_boundary_flux, triangle_boundary_flux]
  generalize φ 1 - φ 0 = ga
  generalize φ 2 - φ 1 = gb
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp at h0 h1 h2
    refine ⟨by linarith, ?_, ?_⟩
    · rw [dropA, eq_div_iff hP, treeSum]
      linear_combination Θ.1 2 * h1 - Θ.1 1 * h0
    · rw [dropB, eq_div_iff hP, treeSum]
      linear_combination (-Θ.1 0) * h0 - (Θ.1 0 + Θ.1 2) * h1
  · rintro ⟨h012, rfl, rfl⟩
    have ha : dropA Θ σ * treeSum Θ = Θ.1 2 * σ 1 - Θ.1 1 * σ 0 := div_mul_cancel₀ _ hP
    have hb : dropB Θ σ * treeSum Θ = -(Θ.1 0 * σ 0 + (Θ.1 0 + Θ.1 2) * σ 1) :=
      div_mul_cancel₀ _ hP
    have hPdef : treeSum Θ = Θ.1 0 * Θ.1 1 + Θ.1 0 * Θ.1 2 + Θ.1 1 * Θ.1 2 := rfl
    funext i
    apply mul_left_cancel₀ hP
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      linear_combination (-(Θ.1 0 + Θ.1 2)) * ha + (-Θ.1 2) * hb + (-σ 0) * hPdef
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      linear_combination Θ.1 0 * ha - Θ.1 1 * hb - σ 1 * hPdef
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons]
      linear_combination Θ.1 2 * ha + (Θ.1 1 + Θ.1 2) * hb + (σ 0 + σ 1) * hPdef -
        treeSum Θ * h012

/-- [proved-derived; formal-checked] On the triangle a source admits a balance exactly when its
total charge is zero. -/
theorem triangle_solvable_iff (Θ : Constitution 3) (σ : Fin 3 → ℚ) :
    (∃ φ, Solves triangle Θ φ σ) ↔ σ 0 + σ 1 + σ 2 = 0 := by
  constructor
  · rintro ⟨φ, h⟩
    exact ((triangle_solves_iff Θ φ σ).mp h).1
  · intro h
    exact ⟨![0, dropA Θ σ, dropA Θ σ + dropB Θ σ],
      (triangle_solves_iff Θ _ σ).mpr ⟨h, by simp, by simp⟩⟩

/-- [proved-derived; formal-checked] **Every solve on the triangle carries `triFlux`.** -/
theorem triangle_flux {Θ : Constitution 3} {φ σ : Fin 3 → ℚ} (h : Solves triangle Θ φ σ) :
    flux triangle Θ φ = triFlux Θ σ := by
  obtain ⟨-, ha, hb⟩ := (triangle_solves_iff Θ φ σ).mp h
  funext e
  simp only [flux, triangle_mulVec]
  fin_cases e <;> simp [triFlux, ha, hb]

/-- [proved-derived; formal-checked] Every solve on the triangle has the drops of `triFlux`. -/
theorem triangle_drop {Θ : Constitution 3} {φ σ : Fin 3 → ℚ} (h : Solves triangle Θ φ σ) :
    triangle *ᵥ φ = ![dropA Θ σ, dropB Θ σ, dropA Θ σ + dropB Θ σ] := by
  obtain ⟨-, ha, hb⟩ := (triangle_solves_iff Θ φ σ).mp h
  rw [triangle_mulVec, ha, hb]

/-- [proved-derived; formal-checked] **The triangle's present observation.** -/
theorem triangle_observeConstitution (σ : Fin 3 → ℚ) (Θ : Constitution 3) :
    observeConstitution triangle σ Θ =
      if σ 0 + σ 1 + σ 2 = 0 then some (triFlux Θ σ) else none := by
  by_cases h : σ 0 + σ 1 + σ 2 = 0
  · have hs := (triangle_solvable_iff Θ σ).mpr h
    rw [observeConstitution, if_pos hs, if_pos h, triangle_flux (canonicalSolve_solves hs)]
  · rw [observeConstitution, if_neg (fun hs => h ((triangle_solvable_iff Θ σ).mp hs)), if_neg h]

/-- [proved-derived; formal-checked] **One square-law step on the triangle**: a solvable source
deposits the squared flux, `Θ'_e = Θ_e + j_e²`. -/
theorem triangle_square_step_apply {σ : Fin 3 → ℚ} (hσ : σ 0 + σ 1 + σ 2 = 0)
    (Θ : Constitution 3) (e : Fin 3) :
    (stepConstitution (squareLawOn 3) triangle σ Θ).1 e = Θ.1 e + triFlux Θ σ e ^ 2 := by
  have hs := (triangle_solvable_iff Θ σ).mpr hσ
  rw [stepConstitution, if_pos hs]
  simp only [deposit, squareLawOn]
  rw [triangle_flux (canonicalSolve_solves hs)]

/-- [proved-derived; formal-checked] Scaling the constitution leaves the flux of every solvable
source unchanged (the owner's `observeConstitution_scale` read on the triangle). -/
theorem triFlux_scale {c : ℚ} (hc : 0 < c) (Θ : Constitution 3) {σ : Fin 3 → ℚ}
    (hσ : σ 0 + σ 1 + σ 2 = 0) :
    triFlux (Retention.scaleConstitution c hc Θ) σ = triFlux Θ σ := by
  have h := Retention.observeConstitution_scale triangle hc Θ σ
  rw [triangle_observeConstitution, triangle_observeConstitution, if_pos hσ, if_pos hσ] at h
  exact Option.some.inj h

/-- [definition] The unit source from node `0` to node `1`. -/
def source01 : Fin 3 → ℚ := ![-1, 1, 0]

/-- [definition] The unit source from node `1` to node `2`. -/
def source12 : Fin 3 → ℚ := ![0, -1, 1]

/-- [proved-derived; formal-checked] The unit source `0 → 1` has zero total charge. -/
theorem source01_charge : source01 0 + source01 1 + source01 2 = 0 := by simp [source01]

/-- [proved-derived; formal-checked] The unit source `1 → 2` has zero total charge. -/
theorem source12_charge : source12 0 + source12 1 + source12 2 = 0 := by simp [source12]

/-- [proved-derived; formal-checked] **The unit source from `0` to `1`** sends
`Θ_a (Θ_b + Θ_c)/P` along `a` and `Θ_b Θ_c/P` around `c` and back along `b`. -/
theorem triFlux_source01 (Θ : Constitution 3) :
    triFlux Θ source01 = ![Θ.1 0 * (Θ.1 1 + Θ.1 2) / treeSum Θ, -(Θ.1 1 * Θ.1 2) / treeSum Θ,
      Θ.1 1 * Θ.1 2 / treeSum Θ] := by
  funext e
  fin_cases e <;> simp [triFlux, dropA, dropB, source01] <;> ring

/-- [proved-derived; formal-checked] **The unit source from `1` to `2`** sends
`Θ_b (Θ_a + Θ_c)/P` along `b` and `Θ_a Θ_c/P` back along `a` and around `c`. -/
theorem triFlux_source12 (Θ : Constitution 3) :
    triFlux Θ source12 = ![-(Θ.1 0 * Θ.1 2) / treeSum Θ, Θ.1 1 * (Θ.1 0 + Θ.1 2) / treeSum Θ,
      Θ.1 0 * Θ.1 2 / treeSum Θ] := by
  funext e
  fin_cases e <;> simp [triFlux, dropA, dropB, source12] <;> ring

/-- [proved-derived; formal-checked] **Two unit sources read the projective class.** If the
flux of `b` under the source `0 → 1` and the flux of `a` under the source `1 → 2` agree on two
constitutions, they are projectively equal: `Θ_bΘ_c/P` and `Θ_aΘ_c/P` fix every ratio `Θ_e/Θ_f`. -/
theorem projectivelyEqual_of_two_reads {Θ Θ' : Constitution 3}
    (h01 : triFlux Θ source01 1 = triFlux Θ' source01 1)
    (h12 : triFlux Θ source12 0 = triFlux Θ' source12 0) : ProjectivelyEqual Θ Θ' := by
  have hP := (treeSum_pos Θ).ne'
  have hP' := (treeSum_pos Θ').ne'
  have hA := Θ.2 0
  have hB := Θ.2 1
  have hA' := Θ'.2 0
  have hB' := Θ'.2 1
  have hC' := Θ'.2 2
  rw [triFlux_source01, triFlux_source01] at h01
  rw [triFlux_source12, triFlux_source12] at h12
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at h01 h12
  rw [div_eq_div_iff hP hP'] at h01 h12
  have e1 : Θ.1 1 * Θ.1 2 * treeSum Θ' = Θ'.1 1 * Θ'.1 2 * treeSum Θ := by linear_combination -h01
  have e2 : Θ.1 0 * Θ.1 2 * treeSum Θ' = Θ'.1 0 * Θ'.1 2 * treeSum Θ := by linear_combination -h12
  have h3 : Θ.1 1 * Θ'.1 0 = Θ.1 0 * Θ'.1 1 := by
    have hz : (Θ.1 1 * Θ'.1 0 - Θ.1 0 * Θ'.1 1) * (Θ'.1 2 * treeSum Θ) = 0 := by
      linear_combination (-Θ.1 1) * e2 + Θ.1 0 * e1
    rcases mul_eq_zero.mp hz with hz | hz
    · linarith
    · exact absurd hz (mul_ne_zero hC'.ne' hP)
  have h4 : Θ'.1 0 * Θ.1 2 = Θ.1 0 * Θ'.1 2 := by
    unfold treeSum at e2
    have hz : Θ'.1 0 * Θ.1 1 * (Θ'.1 0 * Θ.1 2 - Θ.1 0 * Θ'.1 2) = 0 := by
      linear_combination e2 + Θ.1 2 * (Θ'.1 0 + Θ'.1 2) * h3
    rcases mul_eq_zero.mp hz with hz | hz
    · exact absurd hz (mul_ne_zero hA'.ne' hB.ne')
    · linarith
  refine ⟨Θ'.1 0 / Θ.1 0, div_pos hA' hA, Subtype.ext (funext fun e => ?_)⟩
  change Θ'.1 e = Θ'.1 0 / Θ.1 0 * Θ.1 e
  fin_cases e
  · simp only [Fin.zero_eta, Fin.isValue]
    field_simp
  · simp only [Fin.mk_one, Fin.isValue]
    field_simp
    linarith
  · simp only [Fin.reduceFinMk, Fin.isValue]
    field_simp
    linarith

/-- [proved-derived; formal-checked] **The triangle's present observation reads the projective
class and nothing more**: two constitutions agree on every source iff one is a positive multiple of
the other. -/
theorem triangle_observe_iff_projectivelyEqual (Θ Θ' : Constitution 3) :
    (∀ σ, observeConstitution triangle σ Θ = observeConstitution triangle σ Θ') ↔
      ProjectivelyEqual Θ Θ' := by
  constructor
  · intro h
    have h01 := h source01
    have h12 := h source12
    rw [triangle_observeConstitution, triangle_observeConstitution, if_pos source01_charge,
      if_pos source01_charge] at h01
    rw [triangle_observeConstitution, triangle_observeConstitution, if_pos source12_charge,
      if_pos source12_charge] at h12
    exact projectivelyEqual_of_two_reads (congrFun (Option.some.inj h01) 1)
      (congrFun (Option.some.inj h12) 0)
  · rintro ⟨c, hc, rfl⟩ σ
    rw [Retention.observeConstitution_scale]

/-- [proved-derived; formal-checked] **Future agreement keeps the projective class on the
triangle**: under any law, two presents that share every future are projectively equal after every
history. -/
theorem triangle_projectivelyEqual_of_futureAgreement (L : DepositionLaw 3) (S : Solver triangle)
    {left right : DepositState 3} (h : futureAgreement (observe S) (step L S) left right)
    (word : List (Fin 3 → ℚ)) :
    ProjectivelyEqual (transportWord (stepConstitution L triangle) word left.constitution)
      (transportWord (stepConstitution L triangle) word right.constitution) := by
  refine (triangle_observe_iff_projectivelyEqual _ _).mp fun σ => ?_
  have hw := h σ word
  rwa [observe_eq_observeConstitution, observe_eq_observeConstitution, transportWord_constitution,
    transportWord_constitution] at hw

/-- [proved-derived; formal-checked] **A stroke that keeps a scaled pair projectively equal
deposits in proportion to the constitution.** If `cΘ + J` is a positive multiple of `Θ + J` with
`c ≠ 1`, then `Θ_e J_f = Θ_f J_e` on every pair of edges. -/
theorem proportional_of_scaled_stroke {q : ℕ} {Θ J : Fin q → ℚ} (hΘ : ∀ e, 0 < Θ e) {c k : ℚ}
    (hc1 : c ≠ 1) (h : ∀ e, c * Θ e + J e = k * (Θ e + J e)) (e f : Fin q) :
    Θ e * J f = Θ f * J e := by
  have he := h e
  have hf := h f
  have hk1 : k - 1 ≠ 0 := by
    intro hk
    have hk' : k = 1 := by linarith
    rw [hk'] at he
    have : (c - 1) * Θ e = 0 := by linear_combination he
    rcases mul_eq_zero.mp this with h0 | h0
    · exact hc1 (by linarith)
    · exact (hΘ e).ne' h0
  have hz : (k - 1) * (Θ e * J f - Θ f * J e) = 0 := by
    linear_combination (-Θ e) * hf + Θ f * he
  rcases mul_eq_zero.mp hz with h0 | h0
  · exact absurd h0 hk1
  · linarith

/-- [proved-derived; formal-checked] **No constitution on the triangle takes both unit strokes in
proportion.** The stroke `0 → 1` deposits in proportion only if `Θ_b = Θ_c` and `Θ_b = 4Θ_a`; the
stroke `1 → 2` only if `Θ_a = Θ_c`; together they force `Θ_a = 4Θ_a`. -/
theorem not_both_strokes_proportional (Θ : Constitution 3)
    (h01 : ∀ e f, Θ.1 e * triFlux Θ source01 f ^ 2 = Θ.1 f * triFlux Θ source01 e ^ 2)
    (h12 : ∀ e f, Θ.1 e * triFlux Θ source12 f ^ 2 = Θ.1 f * triFlux Θ source12 e ^ 2) : False := by
  have hA := Θ.2 0
  have hB := Θ.2 1
  have hC := Θ.2 2
  have hP := treeSum_pos Θ
  have k1 := h01 1 2
  have k2 := h12 0 2
  have k3 := h01 0 1
  rw [triFlux_source01] at k1 k3
  rw [triFlux_source12] at k2
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, neg_div, neg_sq] at k1 k2 k3
  have hbc : Θ.1 1 = Θ.1 2 := by
    have hz : (Θ.1 1 - Θ.1 2) * (Θ.1 1 * Θ.1 2 / treeSum Θ) ^ 2 = 0 := by linear_combination k1
    rcases mul_eq_zero.mp hz with h0 | h0
    · linarith
    · exact absurd h0 (by positivity)
  have hac : Θ.1 0 = Θ.1 2 := by
    have hz : (Θ.1 0 - Θ.1 2) * (Θ.1 0 * Θ.1 2 / treeSum Θ) ^ 2 = 0 := by linear_combination k2
    rcases mul_eq_zero.mp hz with h0 | h0
    · linarith
    · exact absurd h0 (by positivity)
  rw [hbc, hac] at k3
  have hz : 3 * (Θ.1 2 * (Θ.1 2 * Θ.1 2 / treeSum Θ) ^ 2) = 0 := by linear_combination -k3
  have hpos : 0 < 3 * (Θ.1 2 * (Θ.1 2 * Θ.1 2 / treeSum Θ) ^ 2) := by positivity
  linarith

/-- [proved-derived; formal-checked] **The future-agreement relation of the square law on the
triangle.** Two presents share every future (for a given solver) iff their constitutions are
equal: no two distinct constitutions merge, and the constitution is the minimal retention. -/
theorem triangle_square_futureAgreement_iff (S : Solver triangle) (left right : DepositState 3) :
    futureAgreement (observe S) (step (squareLawOn 3) S) left right ↔
      left.constitution = right.constitution := by
  constructor
  · intro h
    obtain ⟨c, hc, hΘ⟩ := triangle_projectivelyEqual_of_futureAgreement _ S h []
    simp only [transportWord_nil] at hΘ
    have hstroke : ∀ σ : Fin 3 → ℚ, σ 0 + σ 1 + σ 2 = 0 → c ≠ 1 →
        ∀ e f, left.constitution.1 e * triFlux left.constitution σ f ^ 2 =
          left.constitution.1 f * triFlux left.constitution σ e ^ 2 := by
      intro σ hσ hc1
      obtain ⟨k, hk, hkΘ⟩ := triangle_projectivelyEqual_of_futureAgreement _ S h [σ]
      simp only [transportWord_cons, transportWord_nil, hΘ] at hkΘ
      refine proportional_of_scaled_stroke left.constitution.2 hc1 (k := k) (fun e => ?_)
      have he : (stepConstitution (squareLawOn 3) triangle σ
          (Retention.scaleConstitution c hc left.constitution)).1 e =
            k * (stepConstitution (squareLawOn 3) triangle σ left.constitution).1 e :=
        congrArg (fun Θ : Constitution 3 => Θ.1 e) hkΘ
      rw [triangle_square_step_apply hσ, triangle_square_step_apply hσ, triFlux_scale hc _ hσ]
        at he
      exact he
    by_cases hc1 : c = 1
    · rw [hΘ]
      apply Subtype.ext
      funext e
      simp [Retention.scaleConstitution, hc1]
    · exact (not_both_strokes_proportional _ (hstroke _ source01_charge hc1)
        (hstroke _ source12_charge hc1)).elim
  · exact equal_constitution_equal_future _ S

/-- [proved-derived; formal-checked] **On the triangle the constitution is the least lawful
retention**: every retention carrying a `StandingLaw` for the square-law triangle separates every
two distinct constitutions. -/
theorem triangle_constitution_factors_through_every_standing (S : Solver triangle)
    {Retained : Type*}
    (L : StandingLaw (Fin 3 → ℚ) (Fin 3 → ℚ) (DepositState 3) Retained (Option (Fin 3 → ℚ)))
    (htransport : L.transport = step (squareLawOn 3) S) (hobserve : L.observe = observe S)
    {left right : DepositState 3} (h : L.retain left = L.retain right) :
    left.constitution = right.constitution := by
  have hagree := L.futureAgreement_of_retain_eq h
  rw [htransport, hobserve] at hagree
  exact (triangle_square_futureAgreement_iff S left right).mp hagree

/-- [definition] The constitution `(1, 4, 4)` on the triangle. -/
def triOneFourFour : Constitution 3 := ⟨![1, 4, 4], by intro e; fin_cases e <;> norm_num⟩

/-- [proved-derived; formal-checked] **The stroke `0 → 1` on `(1, 4, 4)` deposits in proportion**:
the flux is `(1/3, −2/3, 2/3)`, its square `(1, 4, 4)/9`. -/
theorem stroke01_oneFourFour :
    stepConstitution (squareLawOn 3) triangle source01 triOneFourFour =
      Retention.scaleConstitution (10 / 9) (by norm_num) triOneFourFour := by
  apply Subtype.ext
  funext e
  rw [triangle_square_step_apply source01_charge, triFlux_source01]
  fin_cases e <;> simp [triOneFourFour, treeSum, Retention.scaleConstitution] <;> norm_num

/-- [counterexample; formal-checked] **The triangle keeps every total, but one fixed stroke need not
show it.** The uniform `(1, 1, 1)` and `(2, 2, 2)` (uniform constitutions merge on every bundle) do
not share every future on the triangle; and `(1, 4, 4)` and `(2, 8, 8)` agree on every source both now and after the
stroke `0 → 1` (it deposits in proportion to each), yet they do not share every future: the stroke
`1 → 2` separates them (`not_both_strokes_proportional`). -/
theorem triangle_witness (S : Solver triangle) :
    ¬ futureAgreement (observe S) (step (squareLawOn 3) S) ⟨uniformThree 1 one_pos, []⟩
        ⟨uniformThree 2 two_pos, []⟩ ∧
      (∀ σ, observeConstitution triangle σ triOneFourFour =
        observeConstitution triangle σ (Retention.scaleConstitution 2 two_pos triOneFourFour)) ∧
      (∀ σ, observeConstitution triangle σ
          (stepConstitution (squareLawOn 3) triangle source01 triOneFourFour) =
        observeConstitution triangle σ (stepConstitution (squareLawOn 3) triangle source01
          (Retention.scaleConstitution 2 two_pos triOneFourFour))) ∧
      ¬ futureAgreement (observe S) (step (squareLawOn 3) S) ⟨triOneFourFour, []⟩
        ⟨Retention.scaleConstitution 2 two_pos triOneFourFour, []⟩ := by
  have hscaled : stepConstitution (squareLawOn 3) triangle source01
      (Retention.scaleConstitution 2 two_pos triOneFourFour) =
        Retention.scaleConstitution (19 / 9) (by norm_num) triOneFourFour := by
    apply Subtype.ext
    funext e
    rw [triangle_square_step_apply source01_charge, triFlux_scale two_pos _ source01_charge,
      triFlux_source01]
    fin_cases e <;> simp [triOneFourFour, treeSum, Retention.scaleConstitution] <;> norm_num
  refine ⟨?_, fun σ => by rw [Retention.observeConstitution_scale], fun σ => ?_, ?_⟩
  · rw [triangle_square_futureAgreement_iff]
    intro h
    have := congrArg (fun Θ : Constitution 3 => Θ.1 0) h
    norm_num [uniformThree] at this
  · rw [stroke01_oneFourFour, hscaled, Retention.observeConstitution_scale,
      Retention.observeConstitution_scale]
  · rw [triangle_square_futureAgreement_iff]
    intro h
    have := congrArg (fun Θ : Constitution 3 => Θ.1 0) h
    norm_num [triOneFourFour, Retention.scaleConstitution] at this

end Triangle

end Holonics.Objects.RetentionSeries
