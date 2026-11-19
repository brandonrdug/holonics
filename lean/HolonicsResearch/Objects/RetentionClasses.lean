import Holonics.Objects.Retention
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The classes of the minimal retention: forests, the parallel bundle, the Joule law, a pendant edge

[definition] Object 8 of `docs/ELEMENTARY_OBJECTS.md` with `Foundation/Standing.lean`: retention
is the future-sufficient quotient of the present, never a record of what shaped it. Source: #410's
box "The explicit classes of the square law's minimal retention on a general weighted graph (the
orbit structure of deposition on projective classes beyond two parallel edges), and for other
deposition laws". It is the `[open]` paragraph of `Objects/Retention`, which found the classes on
two parallel edges (`parallel_futureAgreement_iff`, `minimalRetain`), and of
`HolonicsResearch/Foundation/MinimalRetention` (#552), which characterized them on every medium as
future agreement of the constitution under the constitution-only machine
(`futureAgreement_iff_constitution`) and computed them only on the parallel pair. Record:
`2026-09-22_RETENTION_IS_A_QUOTIENT_NOT_A_TAPE_AND_THE_SOURCE_ENTERS_AS_PHASE_CARRIED_MOMENTS`.
Atlas rows read: `deposition.constitution-not-minimal`, `deposition.minimal-retention`,
`deposition.minimal-retention-witness`, `deposition.minimal-retention-general` (its scope:
"explicit classes computed only on the parallel pair"), `deposition.solve-sees-projective-class`,
`deposition.projective-class-not-retention`, `deposition.joule-law-keeps-split` and
`compression.future-agreement-greatest-stable`. This module computes the classes on four families:
the forests, the `m`-edge parallel bundle under the square law and under the Joule law, and the
bundle with a pendant edge. Every statement holds for every solver, including one that reads the
flux record to choose its gauge, as in the owner.

What is proved.

1. [proved-derived; formal-checked] **A forest retains nothing.** Call an incidence `d` a forest
   when `dᵀ y = 0` forces `y = 0` (`IsForest`: no edge vector circulates without a source). Then
   `d` maps onto the edge space (`IsForest.drop_surjective`, [proved-standard]:
   `rank d = rank dᵀ = q`), so a source admits a balance on a constitution exactly when it is a
   boundary `dᵀ j`
   (`IsForest.solvable_iff`), and every solve on every constitution carries the one `j` with
   `dᵀ j = σ` (`IsForest.flux_eq`). The present observation does not read the constitution
   (`IsForest.observeConstitution_eq`), so under every deposition law any two presents share every
   future (`IsForest.all_futureAgreement`), and retaining a point carries a lawful `StandingLaw`
   (`IsForest.pointStanding_exists`): the minimal retention on a forest is a point. Witness: on two
   edges in series (`series`, `series_isForest`), `(1, 1)` and `(1, 5)` share every future under
   every law (`series_witness`).
2. [proved-derived; formal-checked] **The `m`-edge bundle reads the shares.** On `m ≥ 1` parallel
   edges (`bundle`; `bundle_two : bundle 2 = parallel`) a source admits a balance exactly when its
   total charge is zero (`bundle_solves_iff`, `bundle_solvable_iff`), every edge sees the one drop
   `σ₁/T` (`bundle_drop`) and carries `r_e σ₁`, with the share `r_e = Θ_e/T` (`bundle_flux`). The
   present observation reads the shares alone (`bundle_observeConstitution`), one step under any
   law deposits `Γ_e(r_e σ₁, σ₁/T)` (`bundle_stepConstitution_apply`), and under any law two
   presents that share every future have equal shares after every history
   (`share_eq_of_futureAgreement`).
3. [proved-derived; formal-checked] **The square law on the bundle collapses the uniform class and
   keeps every other constitution.** Under `Γ_e = j_e²` (`squareLawOn`;
   `squareLawOn_two : squareLawOn 2 = squareLaw`) two presents share every future iff their
   constitutions are equal or both uniform (`bundle_futureAgreement_iff`; `Uniform`, which on two
   edges is the owner's `Symmetric`, `uniform_two_iff_symmetric`). A uniform constitution stays
   uniform and observes the even split `σ₁/m` whatever its total (`uniform_stepConstitution`,
   `uniform_observe`, `uniform_futureAgreement`). One unit source separates unequal shares; for
   equal shares on totals `T ≠ T'`, one unit stroke moves the share of edge `e` to
   `(r_e T + r_e²)/(T + R₂)` against `(r_e T' + r_e²)/(T' + R₂)`, `R₂ = Σ_f r_f²` (`stroke_apply`,
   `total_stroke`), and these differ by `r_e (R₂ − r_e)(T − T')/((T + R₂)(T' + R₂))`
   (`stroke_share_difference`), which vanishes at every edge only when every share is `R₂`, that
   is, when the constitution is uniform (`stroke_separates_equal_shares`). On two edges
   `R₂ − r = (2r − 1)(r − 1)`, the owner's factor. The minimal retention `minimalRetain` keeps
   `none` on a uniform constitution and the constitution otherwise: its kernel is future agreement
   (`minimalRetain_eq_iff_futureAgreement`), it carries a lawful `StandingLaw`
   (`minimalStanding_exists`), and every lawful retention refines it
   (`minimalRetain_factors_through_every_standing`).
4. [proved-derived; formal-checked] **The Joule law on the bundle keeps the projective class.**
   Under `Γ_e = j_e (dφ)_e` (`jouleLawOn`; `jouleLawOn_two`) every edge sees one drop `g`, so a
   step scales the constitution, `Θ'_e = (1 + g²) Θ_e` (`joule_stepConstitution_apply`,
   `joule_stepConstitution_scale`), and so does every history (`joule_transportWord_scale`). With
   the owner's `observeConstitution_scale`, two presents share every future iff their
   constitutions are projectively equal (`ProjectivelyEqual`, `joule_bundle_futureAgreement_iff`),
   that is, iff their shares agree (`share_eq_iff_projectivelyEqual`): the shares are the minimal
   retention (`jouleMinimalRetain`, `jouleMinimalRetain_eq_iff_futureAgreement`,
   `jouleMinimalStanding_exists`, `jouleMinimalRetain_factors_through_every_standing`). The square
   law does not keep this class on any bundle of two or more edges: the ramp `(1, 2, …, m)` and its
   double merge under the Joule law and are separated under the square law
   (`square_bundle_projective_class_is_not_a_retention`, the `m`-edge form of the owner's
   `projective_class_is_not_a_retention`).
5. [proved-derived; formal-checked] **A pendant edge is forgotten.** On the bundle with one more
   edge from node `1` to a leaf `2` (`pendantBundle`), the pendant carries the leaf's charge `σ₂`
   whatever its conductance, and the bundle's edges carry the bundle's solve at the folded source
   `(σ₀, σ₁ + σ₂)` (`pendant_solves_iff`, `pendant_solvable_iff`, `pendant_flux`,
   `pendant_observeConstitution`), so the bundle part steps as the bundle
   (`restrict_stepConstitution`, `restrict_transportWord`). For any composite law that deposits on
   the bundle's edges as the bundle's law does, two composite presents share every future exactly
   when their bundle parts do (`pendant_futureAgreement_iff`). Under the square law the classes are
   the bundle part's, equal or both uniform (`pendant_square_futureAgreement_iff`), and the minimal
   retention is the bundle's `minimalRetain` of the bundle part, the product of the bundle's factor
   with the pendant's point (`pendantMinimalRetain`, `pendantMinimalRetain_eq_iff_futureAgreement`,
   `pendantMinimalStanding_exists`, `pendantMinimalRetain_factors_through_every_standing`); under
   the Joule law they are the bundle part's projective class (`pendant_joule_futureAgreement_iff`).

What is not claimed.

- The classes on a general weighted graph whose cycles do not all share their two ends (a cycle of
  three edges, a wheel, a grid): there the solve couples the split of one cycle to the conductances
  of the others, and the orbit structure of square-law deposition on projective classes is not
  computed. Two bundles joined in series are not written either; the expected classes are the
  product of the two bundles', each driven by the series current. The box stays part done.
- Deposition laws other than the square and Joule laws, beyond what item 1 (every law on a forest)
  and item 5's reduction (every law pair on the pendant composite) say.
- Convergence or the long-run orbit of repeated deposition, and the existence of a solve on a
  general incidence (the owner carries it as a hypothesis; it is proved here on forests, on the
  bundle and on the pendant composite).
- `MinimalRetention.IsMinimal` is not restated: the kernel, the lawful standing and leastness are
  given in `Objects/Retention`'s form, from which `IsMinimal` follows as in
  `MinimalRetention.parallel_minimalRetain_isMinimal`.

The computational object is the helical pair interaction read as a conducting contact: each edge
is a pair contact between two node potentials, its slip the drop `(dφ)_e`, its current the flux
`Θ_e (dφ)_e`, and deposition changes the contact's material by what crossed it. The minimal
retention keeps exactly the differences of contact material that a later source reads through the
contacts. Of the winding guide's six general objects this touches the cell holonomy (a forest has
no cycle, so the source fixes every current and nothing is retained; a bundle's `m − 1`
independent cycles carry its split, which the shares fix), faces and placement (the solve's face is
conserved under dilation of the material, `observeConstitution_scale`, and the Joule law moves the
material only along that dilation), and the tube (histories as ordered words of admitted sources,
each step a transfer of the constitution). The helix, the pair's modular address and the tower
thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Objects.RetentionClasses

open Holonics
open Holonics.Objects.Deposition
open Holonics.Foundation.Standing
open Holonics.Foundation.CausalRelevance.NonLinear
open Holonics.Foundation.Chronology
open Matrix

/-! ## 1. A forest retains nothing -/

section Forest

variable {p q : ℕ}

/-- [definition] **A forest**: no edge vector circulates without a source, `dᵀ y = 0 → y = 0`. -/
def IsForest (d : Matrix (Fin q) (Fin p) ℚ) : Prop := ∀ y : Fin q → ℚ, dᵀ *ᵥ y = 0 → y = 0

/-- [proved-standard; formal-checked] **On a forest every edge drop is reached by a potential**:
`dᵀ` is injective, so `rank d = rank dᵀ = q` and `d` maps onto the edge space. -/
theorem IsForest.drop_surjective {d : Matrix (Fin q) (Fin p) ℚ} (hd : IsForest d) :
    Function.Surjective (fun φ : Fin p → ℚ => d *ᵥ φ) := by
  have hker : LinearMap.ker dᵀ.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    exact hd
  have hrankT : dᵀ.rank = q := by
    have := LinearMap.finrank_range_add_finrank_ker dᵀ.mulVecLin
    rw [hker, finrank_bot, add_zero, Module.finrank_fin_fun] at this
    exact this
  have hrank : Module.finrank ℚ (LinearMap.range d.mulVecLin) = q := by
    have := rank_transpose d
    rw [hrankT] at this
    exact this.symm
  have htop : LinearMap.range d.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hrank, Module.finrank_fin_fun]
  intro j
  obtain ⟨φ, hφ⟩ : j ∈ LinearMap.range d.mulVecLin := htop ▸ Submodule.mem_top
  exact ⟨φ, hφ⟩

/-- [proved-derived; formal-checked] **On a forest solvability does not read the constitution**:
`σ` admits a balance exactly when it is the boundary `dᵀ j` of some edge vector. -/
theorem IsForest.solvable_iff {d : Matrix (Fin q) (Fin p) ℚ} (hd : IsForest d)
    (Θ : Constitution q) (σ : Fin p → ℚ) :
    (∃ φ, Solves d Θ φ σ) ↔ ∃ j : Fin q → ℚ, dᵀ *ᵥ j = σ := by
  constructor
  · rintro ⟨φ, h⟩
    exact ⟨flux d Θ φ, (solves_iff_boundary_flux d Θ φ σ).mp h⟩
  · rintro ⟨j, hj⟩
    obtain ⟨φ, hφ⟩ := hd.drop_surjective (fun e => j e / Θ.1 e)
    refine ⟨φ, (solves_iff_boundary_flux d Θ φ σ).mpr ?_⟩
    have hflux : flux d Θ φ = j := by
      funext e
      have he := congrFun hφ e
      simp only at he
      simp only [flux, he]
      field_simp [(Θ.2 e).ne']
    rw [hflux, hj]

/-- [proved-derived; formal-checked] **On a forest the source alone fixes the flux**: every solve
under `σ`, on every constitution, carries the one `j` with `dᵀ j = σ`. -/
theorem IsForest.flux_eq {d : Matrix (Fin q) (Fin p) ℚ} (hd : IsForest d) {Θ Θ' : Constitution q}
    {φ φ' σ : Fin p → ℚ} (h : Solves d Θ φ σ) (h' : Solves d Θ' φ' σ) :
    flux d Θ φ = flux d Θ' φ' := by
  rw [solves_iff_boundary_flux] at h h'
  have hzero : dᵀ *ᵥ (flux d Θ φ - flux d Θ' φ') = 0 := by
    rw [mulVec_sub, h, h', sub_self]
  exact sub_eq_zero.mp (hd _ hzero)

/-- [proved-derived; formal-checked] **On a forest the present observation does not read the
constitution.** -/
theorem IsForest.observeConstitution_eq {d : Matrix (Fin q) (Fin p) ℚ} (hd : IsForest d)
    (σ : Fin p → ℚ) (Θ Θ' : Constitution q) :
    observeConstitution d σ Θ = observeConstitution d σ Θ' := by
  by_cases h : ∃ φ, Solves d Θ φ σ
  · have h' : ∃ φ, Solves d Θ' φ σ := (hd.solvable_iff Θ' σ).mpr ((hd.solvable_iff Θ σ).mp h)
    rw [observeConstitution, if_pos h, observeConstitution, if_pos h',
      hd.flux_eq (canonicalSolve_solves h) (canonicalSolve_solves h')]
  · have h' : ¬ ∃ φ, Solves d Θ' φ σ := fun h' =>
      h ((hd.solvable_iff Θ σ).mpr ((hd.solvable_iff Θ' σ).mp h'))
    rw [observeConstitution, if_neg h, observeConstitution, if_neg h']

/-- [proved-derived; formal-checked] **A forest retains nothing**: under every deposition law and
every solver, any two presents agree in every admitted future. -/
theorem IsForest.all_futureAgreement {d : Matrix (Fin q) (Fin p) ℚ} (hd : IsForest d)
    (L : DepositionLaw q) (S : Solver d) (left right : DepositState q) :
    futureAgreement (observe S) (step L S) left right := by
  intro σ word
  rw [observe_eq_observeConstitution, observe_eq_observeConstitution]
  exact hd.observeConstitution_eq σ _ _

/-- [proved-derived; formal-checked] **The minimal retention on a forest is a point**: retaining
nothing carries a lawful `StandingLaw`, for every deposition law and every solver. -/
theorem IsForest.pointStanding_exists {d : Matrix (Fin q) (Fin p) ℚ} (hd : IsForest d)
    (L : DepositionLaw q) (S : Solver d) :
    ∃ St : StandingLaw (Fin p → ℚ) (Fin p → ℚ) (DepositState q) Unit (Option (Fin q → ℚ)),
      St.transport = step L S ∧ St.observe = observe S ∧ St.retain = fun _ => () := by
  rw [standingLaw_exists_iff_future_factors]
  intro left right _
  exact (causalSignature_eq_iff_futureAgreement _ _ _ _).mpr (hd.all_futureAgreement L S left right)

/-- [definition] **Two edges in series**: the path `0 → 1 → 2` through three nodes. -/
def series : Matrix (Fin 2) (Fin 3) ℚ := !![-1, 1, 0; 0, -1, 1]

/-- [proved-derived; formal-checked] The path of two edges is a forest. -/
theorem series_isForest : IsForest series := by
  intro y hy
  have h0 := congrFun hy 0
  have h2 := congrFun hy 2
  simp [series, mulVec, dotProduct, Fin.sum_univ_two] at h0 h2
  funext e
  fin_cases e
  · exact h0
  · exact h2

/-- [definition] The constitution `(1, 5)`. -/
def ΘoneFive : Constitution 2 := ⟨![1, 5], by intro e; fin_cases e <;> norm_num⟩

/-- [counterexample; formal-checked] **On two edges in series `(1, 1)` and `(1, 5)` share every
future**, under every deposition law and every solver, whatever their records: the constitution is
not minimal there, and the minimal retention is a point. -/
theorem series_witness (L : DepositionLaw 2) (S : Solver series) (left right : List (Fin 2 → ℚ)) :
    Θone ≠ ΘoneFive ∧ futureAgreement (observe S) (step L S) ⟨Θone, left⟩ ⟨ΘoneFive, right⟩ := by
  refine ⟨fun h => ?_, series_isForest.all_futureAgreement L S _ _⟩
  have := congrArg (fun Θ : Constitution 2 => Θ.1 1) h
  norm_num [Θone, ΘoneFive] at this

end Forest

/-! ## 2. The `m`-edge parallel bundle: the solve reads the shares -/

section Bundle

variable {m : ℕ}

/-- [definition] **The `m`-edge parallel bundle**: two nodes joined by `m` edges, each row
`(−1, 1)`. -/
def bundle (m : ℕ) : Matrix (Fin m) (Fin 2) ℚ := fun _ => ![-1, 1]

/-- [proved-derived; formal-checked] The bundle of two edges is the owner's parallel pair. -/
theorem bundle_two : bundle 2 = parallel := by
  ext e i
  fin_cases e <;> fin_cases i <;> rfl

/-- [definition] **The square law** `Γ_e = j_e²` on any number of edges. -/
def squareLawOn (q : ℕ) : DepositionLaw q where
  Γ _ j _ := j ^ 2
  keepsPositive _ _ _ hθ := by positivity

/-- [proved-derived; formal-checked] On two edges it is the owner's square law. -/
theorem squareLawOn_two : squareLawOn 2 = squareLaw := rfl

/-- [definition] **The Joule law** `Γ_e = j_e (dφ)_e` on any number of edges. -/
def jouleLawOn (q : ℕ) : DepositionLaw q where
  Γ _ j g := j * g
  keepsPositive _ θ g hθ := by nlinarith [sq_nonneg g, mul_pos hθ hθ]

/-- [proved-derived; formal-checked] On two edges it is the owner's Joule law. -/
theorem jouleLawOn_two : jouleLawOn 2 = jouleLaw := rfl

/-- [definition] The total conductance of a bundle constitution. -/
def total (Θ : Constitution m) : ℚ := ∑ e, Θ.1 e

/-- [proved-derived; formal-checked] A nonempty bundle has a positive total. -/
theorem total_pos [NeZero m] (Θ : Constitution m) : 0 < total Θ :=
  Finset.sum_pos (fun e _ => Θ.2 e) Finset.univ_nonempty

/-- [definition] **The share** `r_e = Θ_e / T` of an edge. -/
def share (Θ : Constitution m) (e : Fin m) : ℚ := Θ.1 e / total Θ

/-- [proved-derived; formal-checked] A share times the total is the conductance. -/
theorem share_mul_total [NeZero m] (Θ : Constitution m) (e : Fin m) :
    share Θ e * total Θ = Θ.1 e := by
  rw [share, div_mul_cancel₀ _ (total_pos Θ).ne']

/-- [proved-derived; formal-checked] Every edge of the bundle reads the drop `φ₁ − φ₀`. -/
theorem bundle_mulVec (φ : Fin 2 → ℚ) (e : Fin m) : (bundle m *ᵥ φ) e = φ 1 - φ 0 := by
  simp [bundle, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- [proved-derived; formal-checked] The bundle's boundary of an edge vector is `(−Σ j, Σ j)`. -/
theorem bundle_transpose_mulVec (j : Fin m → ℚ) :
    (bundle m)ᵀ *ᵥ j = ![-(∑ e, j e), ∑ e, j e] := by
  funext i
  fin_cases i <;> simp [bundle, mulVec, dotProduct, Finset.sum_neg_distrib]

/-- [proved-derived; formal-checked] **The bundle's balance.** `φ` solves `σ` exactly when `σ` has
zero total charge and the common drop is `σ₁ / T`. -/
theorem bundle_solves_iff [NeZero m] (Θ : Constitution m) (φ σ : Fin 2 → ℚ) :
    Solves (bundle m) Θ φ σ ↔ σ 0 + σ 1 = 0 ∧ φ 1 - φ 0 = σ 1 / total Θ := by
  have hT := (total_pos Θ).ne'
  rw [solves_iff_boundary_flux, bundle_transpose_mulVec]
  have hsum : ∑ e, flux (bundle m) Θ φ e = total Θ * (φ 1 - φ 0) := by
    simp only [flux, bundle_mulVec, total, Finset.sum_mul]
  rw [hsum]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    refine ⟨by linarith, ?_⟩
    rw [eq_div_iff hT]
    linarith
  · rintro ⟨h01, hg⟩
    rw [hg]
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      field_simp
      linarith
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      field_simp

/-- [proved-derived; formal-checked] On the bundle a source admits a balance exactly when its total
charge is zero. -/
theorem bundle_solvable_iff [NeZero m] (Θ : Constitution m) (σ : Fin 2 → ℚ) :
    (∃ φ, Solves (bundle m) Θ φ σ) ↔ σ 0 + σ 1 = 0 := by
  constructor
  · rintro ⟨φ, h⟩
    exact ((bundle_solves_iff Θ φ σ).mp h).1
  · intro h
    refine ⟨![0, σ 1 / total Θ], (bundle_solves_iff Θ _ σ).mpr ⟨h, ?_⟩⟩
    simp

/-- [proved-derived; formal-checked] **Every solve splits the source by the shares**:
`j_e = r_e σ₁`. -/
theorem bundle_flux [NeZero m] {Θ : Constitution m} {φ σ : Fin 2 → ℚ}
    (h : Solves (bundle m) Θ φ σ) : flux (bundle m) Θ φ = fun e => share Θ e * σ 1 := by
  have hg := ((bundle_solves_iff Θ φ σ).mp h).2
  funext e
  simp only [flux, bundle_mulVec, hg, share]
  ring

/-- [proved-derived; formal-checked] Every edge of the bundle sees the one drop `σ₁ / T`. -/
theorem bundle_drop [NeZero m] {Θ : Constitution m} {φ σ : Fin 2 → ℚ}
    (h : Solves (bundle m) Θ φ σ) : bundle m *ᵥ φ = fun _ => σ 1 / total Θ := by
  have hg := ((bundle_solves_iff Θ φ σ).mp h).2
  funext e
  rw [bundle_mulVec, hg]

/-- [proved-derived; formal-checked] **The bundle's present observation reads only the shares.** -/
theorem bundle_observeConstitution [NeZero m] (σ : Fin 2 → ℚ) (Θ : Constitution m) :
    observeConstitution (bundle m) σ Θ =
      if σ 0 + σ 1 = 0 then some (fun e => share Θ e * σ 1) else none := by
  by_cases h : σ 0 + σ 1 = 0
  · have hs := (bundle_solvable_iff Θ σ).mpr h
    rw [observeConstitution, if_pos hs, if_pos h, bundle_flux (canonicalSolve_solves hs)]
  · rw [observeConstitution, if_neg (fun hs => h ((bundle_solvable_iff Θ σ).mp hs)), if_neg h]

/-- [proved-derived; formal-checked] **One step on the bundle under any law**: a solvable source
deposits `Γ_e(r_e σ₁, σ₁ / T)` on each edge. -/
theorem bundle_stepConstitution_apply [NeZero m] (L : DepositionLaw m) {σ : Fin 2 → ℚ}
    (hσ : σ 0 + σ 1 = 0) (Θ : Constitution m) (e : Fin m) :
    (stepConstitution L (bundle m) σ Θ).1 e =
      Θ.1 e + L.Γ e (share Θ e * σ 1) (σ 1 / total Θ) := by
  have hs := (bundle_solvable_iff Θ σ).mpr hσ
  rw [stepConstitution, if_pos hs]
  simp only [deposit]
  rw [bundle_flux (canonicalSolve_solves hs), bundle_drop (canonicalSolve_solves hs)]

/-- [proved-derived; formal-checked] A source with nonzero total charge leaves the bundle unchanged. -/
theorem bundle_stepConstitution_of_ne [NeZero m] (L : DepositionLaw m) {σ : Fin 2 → ℚ}
    (hσ : σ 0 + σ 1 ≠ 0) (Θ : Constitution m) : stepConstitution L (bundle m) σ Θ = Θ := by
  rw [stepConstitution, if_neg (fun hs => hσ ((bundle_solvable_iff Θ σ).mp hs))]

/-- [proved-derived; formal-checked] The unit source has zero total charge. -/
theorem unitSource_charge : unitSource 0 + unitSource 1 = 0 := by norm_num [unitSource]

/-- [proved-derived; formal-checked] **Future agreement keeps the shares**: under any law, two
presents that agree in every future have equal shares after every history (one unit source reads
them). -/
theorem share_eq_of_futureAgreement [NeZero m] (L : DepositionLaw m) (S : Solver (bundle m))
    {left right : DepositState m} (h : futureAgreement (observe S) (step L S) left right)
    (word : List (Fin 2 → ℚ)) (e : Fin m) :
    share (transportWord (stepConstitution L (bundle m)) word left.constitution) e =
      share (transportWord (stepConstitution L (bundle m)) word right.constitution) e := by
  have hw := h unitSource word
  rw [observe_eq_observeConstitution, observe_eq_observeConstitution, transportWord_constitution,
    transportWord_constitution, bundle_observeConstitution, bundle_observeConstitution,
    if_pos unitSource_charge, if_pos unitSource_charge] at hw
  have he := congrFun (Option.some.inj hw) e
  simpa [unitSource] using he

/-! ## 3. The square law on the bundle: uniform constitutions collapse, every other is kept -/

/-- [definition] **A uniform constitution**: every edge of the bundle carries one conductance. -/
def Uniform (Θ : Constitution m) : Prop := ∀ e f, Θ.1 e = Θ.1 f

/-- [proved-derived; formal-checked] On two edges, uniform is the owner's symmetric. -/
theorem uniform_two_iff_symmetric (Θ : Constitution 2) : Uniform Θ ↔ Deposition.Symmetric Θ := by
  constructor
  · intro hu
    exact hu 0 1
  · intro hs e f
    fin_cases e <;> fin_cases f
    · rfl
    · exact hs
    · exact hs.symm
    · rfl

/-- [proved-derived; formal-checked] A uniform constitution gives every edge the share `1/m`. -/
theorem uniform_share [NeZero m] {Θ : Constitution m} (hu : Uniform Θ) (e : Fin m) :
    share Θ e = 1 / m := by
  have hm : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hT : total Θ = m * Θ.1 e := by
    rw [total, Finset.sum_congr rfl (fun f _ => hu f e), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [share, hT]
  field_simp [(Θ.2 e).ne']

/-- [proved-derived; formal-checked] **One share at every edge is uniform**: a constitution whose
shares are all one value is uniform. -/
theorem uniform_of_share_eq [NeZero m] {Θ : Constitution m} {r : ℚ} (hr : ∀ e, share Θ e = r) :
    Uniform Θ := by
  intro e f
  rw [← share_mul_total Θ e, ← share_mul_total Θ f, hr e, hr f]

/-- [proved-derived; formal-checked] **The square law keeps a uniform constitution uniform.** -/
theorem uniform_stepConstitution [NeZero m] {Θ : Constitution m} (hu : Uniform Θ)
    (σ : Fin 2 → ℚ) : Uniform (stepConstitution (squareLawOn m) (bundle m) σ Θ) := by
  by_cases hσ : σ 0 + σ 1 = 0
  · intro e f
    rw [bundle_stepConstitution_apply _ hσ, bundle_stepConstitution_apply _ hσ]
    simp only [squareLawOn]
    rw [uniform_share hu e, uniform_share hu f, hu e f]
  · rw [bundle_stepConstitution_of_ne _ hσ]
    exact hu

/-- [proved-derived; formal-checked] Along every history the square law keeps a uniform constitution
uniform. -/
theorem uniform_transportWord [NeZero m] {Θ : Constitution m} (hu : Uniform Θ)
    (word : List (Fin 2 → ℚ)) :
    Uniform (transportWord (stepConstitution (squareLawOn m) (bundle m)) word Θ) := by
  induction word with
  | nil => exact hu
  | cons σ word ih => exact uniform_stepConstitution ih σ

/-- [proved-derived; formal-checked] **A uniform constitution observes the even split** `σ₁/m`,
whatever its total. -/
theorem uniform_observe [NeZero m] {Θ : Constitution m} (hu : Uniform Θ) (σ : Fin 2 → ℚ) :
    observeConstitution (bundle m) σ Θ =
      if σ 0 + σ 1 = 0 then some (fun _ => σ 1 / m) else none := by
  rw [bundle_observeConstitution]
  split_ifs
  · congr 1
    funext e
    rw [uniform_share hu e]
    ring
  · rfl

/-- [proved-derived; formal-checked] **Two uniform presents share every future**, for every solver
and every record, whatever their totals. -/
theorem uniform_futureAgreement [NeZero m] (S : Solver (bundle m)) {left right : DepositState m}
    (hl : Uniform left.constitution) (hr : Uniform right.constitution) :
    futureAgreement (observe S) (step (squareLawOn m) S) left right := by
  intro σ word
  rw [observe_eq_observeConstitution, observe_eq_observeConstitution,
    transportWord_constitution, transportWord_constitution,
    uniform_observe (uniform_transportWord hl word), uniform_observe (uniform_transportWord hr word)]

/-- [proved-derived; formal-checked] **One unit stroke deposits the squared shares**:
`Θ'_e = Θ_e + r_e²`. -/
theorem stroke_apply [NeZero m] (Θ : Constitution m) (e : Fin m) :
    (stepConstitution (squareLawOn m) (bundle m) unitSource Θ).1 e = Θ.1 e + share Θ e ^ 2 := by
  rw [bundle_stepConstitution_apply _ unitSource_charge]
  simp [squareLawOn, unitSource]

/-- [proved-derived; formal-checked] After one unit stroke the total is `T + R₂`, with
`R₂ = Σ_f r_f²`. -/
theorem total_stroke [NeZero m] (Θ : Constitution m) :
    total (stepConstitution (squareLawOn m) (bundle m) unitSource Θ) =
      total Θ + ∑ f, share Θ f ^ 2 := by
  rw [total, Finset.sum_congr rfl (fun e _ => stroke_apply Θ e), Finset.sum_add_distrib, total]

/-- [proved-derived; formal-checked] **The stroke's share difference.** With one share `r` on the
totals `T` and `T'`, one unit stroke moves the edge's share to `(rT + r²)/(T + R₂)` and
`(rT' + r²)/(T' + R₂)`, which differ by `r (R₂ − r)(T − T')/((T + R₂)(T' + R₂))`. -/
theorem stroke_share_difference {T T' r R : ℚ} (hT : T + R ≠ 0) (hT' : T' + R ≠ 0) :
    (r * T + r ^ 2) / (T + R) - (r * T' + r ^ 2) / (T' + R) =
      r * (R - r) * (T - T') / ((T + R) * (T' + R)) := by
  rw [div_sub_div _ _ hT hT']
  ring

/-- [proved-derived; formal-checked] **Equal shares, unequal totals: one stroke separates unless the
constitution is uniform.** If the shares agree before and after one unit stroke and the totals
differ, every share equals `R₂`, so the constitution is uniform. -/
theorem stroke_separates_equal_shares [NeZero m] {Θ Θ' : Constitution m}
    (hs : ∀ e, share Θ e = share Θ' e) (htotal : total Θ ≠ total Θ')
    (hs1 : ∀ e, share (stepConstitution (squareLawOn m) (bundle m) unitSource Θ) e =
      share (stepConstitution (squareLawOn m) (bundle m) unitSource Θ') e) :
    Uniform Θ := by
  set R := ∑ f, share Θ f ^ 2 with hR
  have hR' : ∑ f, share Θ' f ^ 2 = R := by
    rw [hR]
    exact Finset.sum_congr rfl (fun f _ => by rw [hs f])
  have hRnn : 0 ≤ R := Finset.sum_nonneg (fun f _ => sq_nonneg _)
  have hTR : total Θ + R ≠ 0 := by linarith [total_pos Θ]
  have hT'R : total Θ' + R ≠ 0 := by linarith [total_pos Θ']
  refine uniform_of_share_eq (r := R) (fun e => ?_)
  have key := hs1 e
  rw [share, share, stroke_apply, stroke_apply, total_stroke, total_stroke, hR', ← hR,
    ← share_mul_total Θ e, ← share_mul_total Θ' e, ← hs e] at key
  have hdiff := stroke_share_difference (r := share Θ e) hTR hT'R
  rw [key, sub_self] at hdiff
  have hnum : share Θ e * (R - share Θ e) * (total Θ - total Θ') = 0 := by
    rcases div_eq_zero_iff.mp hdiff.symm with h | h
    · exact h
    · exact absurd h (mul_ne_zero hTR hT'R)
  have hr0 : share Θ e ≠ 0 := (div_pos (Θ.2 e) (total_pos Θ)).ne'
  have hTT : total Θ - total Θ' ≠ 0 := sub_ne_zero.mpr htotal
  rcases mul_eq_zero.mp hnum with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd h hr0
    · linarith
  · exact absurd h hTT

/-- [proved-derived; formal-checked] **The future-agreement relation on the `m`-bundle.** Under the
square law two presents have identical admitted futures (for a given solver) iff their
constitutions are equal or both uniform. -/
theorem bundle_futureAgreement_iff [NeZero m] (S : Solver (bundle m)) (left right : DepositState m) :
    futureAgreement (observe S) (step (squareLawOn m) S) left right ↔
      left.constitution = right.constitution ∨
        (Uniform left.constitution ∧ Uniform right.constitution) := by
  constructor
  · intro h
    have hs : ∀ e, share left.constitution e = share right.constitution e :=
      share_eq_of_futureAgreement _ S h []
    by_cases htotal : total left.constitution = total right.constitution
    · left
      apply Subtype.ext
      funext e
      rw [← share_mul_total left.constitution e, ← share_mul_total right.constitution e, hs e,
        htotal]
    · right
      have hs1 := share_eq_of_futureAgreement _ S h [unitSource]
      simp only [transportWord_cons, transportWord_nil] at hs1
      have hl := stroke_separates_equal_shares hs htotal hs1
      refine ⟨hl, ?_⟩
      have hr := uniform_share hl
      exact uniform_of_share_eq (r := 1 / m) (fun e => by rw [← hs e, hr e])
  · rintro (h | ⟨hl, hr⟩)
    · exact equal_constitution_equal_future _ S h
    · exact uniform_futureAgreement S hl hr

open Classical in
/-- [definition] **The minimal retention** of the square-law `m`-bundle: the uniform class collapses
to one point; every other constitution is retained. -/
def minimalRetain (state : DepositState m) : Option (Constitution m) :=
  if Uniform state.constitution then none else some state.constitution

/-- [proved-derived; formal-checked] **The kernel of the minimal retention is future agreement.** -/
theorem minimalRetain_eq_iff_futureAgreement [NeZero m] (S : Solver (bundle m))
    (left right : DepositState m) :
    minimalRetain left = minimalRetain right ↔
      futureAgreement (observe S) (step (squareLawOn m) S) left right := by
  rw [bundle_futureAgreement_iff]
  unfold minimalRetain
  by_cases hl : Uniform left.constitution <;>
    by_cases hr : Uniform right.constitution <;>
    simp only [hl, hr, if_true, if_false, reduceCtorEq, Option.some.injEq, and_true,
      and_false, or_false, or_true, false_iff]
  · intro h; exact hr (h ▸ hl)
  · intro h; exact hl (h ▸ hr)

/-- [proved-derived; formal-checked] **The minimal retention is a lawful standing**, by
`Standing.standingLaw_exists_iff_future_factors`. -/
theorem minimalStanding_exists [NeZero m] (S : Solver (bundle m)) :
    ∃ L : StandingLaw (Fin 2 → ℚ) (Fin 2 → ℚ) (DepositState m) (Option (Constitution m))
        (Option (Fin m → ℚ)),
      L.transport = step (squareLawOn m) S ∧ L.observe = observe S ∧ L.retain = minimalRetain := by
  rw [standingLaw_exists_iff_future_factors]
  intro left right h
  exact (causalSignature_eq_iff_futureAgreement _ _ _ _).mpr
    ((minimalRetain_eq_iff_futureAgreement S left right).mp h)

/-- [proved-derived; formal-checked] **The minimal retention is least**: every retention that
carries a `StandingLaw` for the same medium refines it. -/
theorem minimalRetain_factors_through_every_standing [NeZero m] (S : Solver (bundle m))
    {Retained : Type*}
    (L : StandingLaw (Fin 2 → ℚ) (Fin 2 → ℚ) (DepositState m) Retained (Option (Fin m → ℚ)))
    (htransport : L.transport = step (squareLawOn m) S) (hobserve : L.observe = observe S)
    {left right : DepositState m} (h : L.retain left = L.retain right) :
    minimalRetain left = minimalRetain right := by
  have hagree := L.futureAgreement_of_retain_eq h
  rw [htransport, hobserve] at hagree
  exact (minimalRetain_eq_iff_futureAgreement S left right).mpr hagree

/-! ## 4. The Joule law on the bundle keeps the projective class -/

/-- [definition] **Projective equality**: one constitution is a positive multiple of the other. -/
def ProjectivelyEqual {q : ℕ} (Θ Θ' : Constitution q) : Prop :=
  ∃ c : ℚ, ∃ hc : 0 < c, Θ' = Retention.scaleConstitution c hc Θ

/-- [proved-derived; formal-checked] On the bundle, projective equality is equality of the shares. -/
theorem share_eq_iff_projectivelyEqual [NeZero m] (Θ Θ' : Constitution m) :
    share Θ = share Θ' ↔ ProjectivelyEqual Θ Θ' := by
  have hT := total_pos Θ
  have hT' := total_pos Θ'
  constructor
  · intro hs
    refine ⟨total Θ' / total Θ, div_pos hT' hT, Subtype.ext (funext fun e => ?_)⟩
    change Θ'.1 e = total Θ' / total Θ * Θ.1 e
    rw [← share_mul_total Θ' e, ← congrFun hs e, share]
    field_simp
  · rintro ⟨c, hc, rfl⟩
    have htc : total (Retention.scaleConstitution c hc Θ) = c * total Θ := by
      simp only [total, Retention.scaleConstitution, Finset.mul_sum]
    funext e
    rw [share, share, htc]
    change Θ.1 e / total Θ = c * Θ.1 e / (c * total Θ)
    field_simp

/-- [proved-derived; formal-checked] **The Joule law on the bundle scales the constitution**: every
edge sees the one drop `g = σ₁ / T`, so `Θ'_e = Θ_e (1 + g²)`. -/
theorem joule_stepConstitution_apply [NeZero m] {σ : Fin 2 → ℚ} (hσ : σ 0 + σ 1 = 0)
    (Θ : Constitution m) (e : Fin m) :
    (stepConstitution (jouleLawOn m) (bundle m) σ Θ).1 e = (1 + (σ 1 / total Θ) ^ 2) * Θ.1 e := by
  rw [bundle_stepConstitution_apply _ hσ]
  simp only [jouleLawOn, share]
  ring

/-- [proved-derived; formal-checked] Each Joule step on the bundle is a positive scaling. -/
theorem joule_stepConstitution_scale [NeZero m] (σ : Fin 2 → ℚ) (Θ : Constitution m) :
    ∃ c : ℚ, ∃ hc : 0 < c,
      stepConstitution (jouleLawOn m) (bundle m) σ Θ = Retention.scaleConstitution c hc Θ := by
  by_cases hσ : σ 0 + σ 1 = 0
  · refine ⟨1 + (σ 1 / total Θ) ^ 2, by positivity, Subtype.ext (funext fun e => ?_)⟩
    rw [joule_stepConstitution_apply hσ]
    rfl
  · refine ⟨1, one_pos, ?_⟩
    rw [bundle_stepConstitution_of_ne _ hσ]
    apply Subtype.ext
    funext e
    simp [Retention.scaleConstitution]

/-- [proved-derived; formal-checked] Along every history the Joule law on the bundle scales the
constitution: the projective class never moves. -/
theorem joule_transportWord_scale [NeZero m] (word : List (Fin 2 → ℚ)) (Θ : Constitution m) :
    ∃ c : ℚ, ∃ hc : 0 < c,
      transportWord (stepConstitution (jouleLawOn m) (bundle m)) word Θ =
        Retention.scaleConstitution c hc Θ := by
  induction word with
  | nil =>
    refine ⟨1, one_pos, Subtype.ext (funext fun e => ?_)⟩
    simp [Retention.scaleConstitution]
  | cons σ word ih =>
    obtain ⟨c, hc, hw⟩ := ih
    obtain ⟨k, hk, hs⟩ := joule_stepConstitution_scale σ
      (transportWord (stepConstitution (jouleLawOn m) (bundle m)) word Θ)
    refine ⟨k * c, mul_pos hk hc, ?_⟩
    rw [transportWord_cons, hs, hw]
    apply Subtype.ext
    funext e
    simp only [Retention.scaleConstitution]
    ring

/-- [proved-derived; formal-checked] **The future-agreement relation of the Joule law on the
`m`-bundle.** Two presents have identical admitted futures (for a given solver) iff their
constitutions are projectively equal. -/
theorem joule_bundle_futureAgreement_iff [NeZero m] (S : Solver (bundle m))
    (left right : DepositState m) :
    futureAgreement (observe S) (step (jouleLawOn m) S) left right ↔
      ProjectivelyEqual left.constitution right.constitution := by
  constructor
  · intro h
    exact (share_eq_iff_projectivelyEqual _ _).mp
      (funext (share_eq_of_futureAgreement _ S h []))
  · rintro ⟨c, hc, hΘ⟩ σ word
    rw [observe_eq_observeConstitution, observe_eq_observeConstitution,
      transportWord_constitution, transportWord_constitution]
    obtain ⟨a, ha, hA⟩ := joule_transportWord_scale word left.constitution
    obtain ⟨b, hb, hB⟩ := joule_transportWord_scale word right.constitution
    rw [hA, hB, Retention.observeConstitution_scale, Retention.observeConstitution_scale, hΘ,
      Retention.observeConstitution_scale]

/-- [definition] **The minimal retention of the Joule law on the bundle**: the shares, the
normalized representative of the projective class. -/
def jouleMinimalRetain (state : DepositState m) : Fin m → ℚ := share state.constitution

/-- [proved-derived; formal-checked] **Its kernel is future agreement.** -/
theorem jouleMinimalRetain_eq_iff_futureAgreement [NeZero m] (S : Solver (bundle m))
    (left right : DepositState m) :
    jouleMinimalRetain left = jouleMinimalRetain right ↔
      futureAgreement (observe S) (step (jouleLawOn m) S) left right := by
  rw [joule_bundle_futureAgreement_iff]
  exact share_eq_iff_projectivelyEqual _ _

/-- [proved-derived; formal-checked] **The shares are a lawful standing for the Joule law.** -/
theorem jouleMinimalStanding_exists [NeZero m] (S : Solver (bundle m)) :
    ∃ L : StandingLaw (Fin 2 → ℚ) (Fin 2 → ℚ) (DepositState m) (Fin m → ℚ) (Option (Fin m → ℚ)),
      L.transport = step (jouleLawOn m) S ∧ L.observe = observe S ∧
        L.retain = jouleMinimalRetain := by
  rw [standingLaw_exists_iff_future_factors]
  intro left right h
  exact (causalSignature_eq_iff_futureAgreement _ _ _ _).mpr
    ((jouleMinimalRetain_eq_iff_futureAgreement S left right).mp h)

/-- [proved-derived; formal-checked] **The shares are least**: every retention carrying a
`StandingLaw` for the Joule bundle refines them. -/
theorem jouleMinimalRetain_factors_through_every_standing [NeZero m] (S : Solver (bundle m))
    {Retained : Type*}
    (L : StandingLaw (Fin 2 → ℚ) (Fin 2 → ℚ) (DepositState m) Retained (Option (Fin m → ℚ)))
    (htransport : L.transport = step (jouleLawOn m) S) (hobserve : L.observe = observe S)
    {left right : DepositState m} (h : L.retain left = L.retain right) :
    jouleMinimalRetain left = jouleMinimalRetain right := by
  have hagree := L.futureAgreement_of_retain_eq h
  rw [htransport, hobserve] at hagree
  exact (jouleMinimalRetain_eq_iff_futureAgreement S left right).mpr hagree

/-- [definition] The ramp `(1, 2, …, m)` on the bundle. -/
def ramp (m : ℕ) : Constitution m := ⟨fun e => (e : ℚ) + 1, fun e => by positivity⟩

/-- [counterexample; formal-checked] **The square law does not keep the projective class on any
bundle of two or more edges**: the ramp and its double are projectively equal, so the Joule law
merges them, and the square law separates them. -/
theorem square_bundle_projective_class_is_not_a_retention [NeZero m] (hm : 2 ≤ m)
    (S : Solver (bundle m)) :
    ProjectivelyEqual (ramp m) (Retention.scaleConstitution 2 two_pos (ramp m)) ∧
      futureAgreement (observe S) (step (jouleLawOn m) S) ⟨ramp m, []⟩
        ⟨Retention.scaleConstitution 2 two_pos (ramp m), []⟩ ∧
      ¬ futureAgreement (observe S) (step (squareLawOn m) S) ⟨ramp m, []⟩
        ⟨Retention.scaleConstitution 2 two_pos (ramp m), []⟩ := by
  have hproj : ProjectivelyEqual (ramp m) (Retention.scaleConstitution 2 two_pos (ramp m)) :=
    ⟨2, two_pos, rfl⟩
  refine ⟨hproj, (joule_bundle_futureAgreement_iff S _ _).mpr hproj, ?_⟩
  rw [bundle_futureAgreement_iff]
  rintro (h | ⟨hl, -⟩)
  · have := congrArg (fun Θ : Constitution m => Θ.1 ⟨0, by omega⟩) h
    simp only [ramp, Retention.scaleConstitution] at this
    norm_num at this
  · have := hl ⟨0, by omega⟩ ⟨1, by omega⟩
    simp only [ramp] at this
    norm_num at this

end Bundle

/-! ## 5. A bundle with a pendant edge: the pendant is forgotten, the bundle is kept -/

section Pendant

variable {m : ℕ}

/-- [definition] **The bundle with a pendant edge**: `m` parallel edges from node `0` to node `1`,
and the last edge from node `1` to the leaf `2`. -/
def pendantBundle (m : ℕ) : Matrix (Fin (m + 1)) (Fin 3) ℚ :=
  fun e => if (e : ℕ) < m then ![-1, 1, 0] else ![0, -1, 1]

/-- [definition] The bundle part of a composite constitution: its first `m` edges. -/
def restrict (Θ : Constitution (m + 1)) : Constitution m :=
  ⟨fun e => Θ.1 e.castSucc, fun _ => Θ.2 _⟩

/-- [definition] The source the bundle sees: the leaf's charge moves to node `1`. -/
def fold (σ : Fin 3 → ℚ) : Fin 2 → ℚ := ![σ 0, σ 1 + σ 2]

/-- [definition] A bundle source lifted to the composite with no charge at the leaf. -/
def lift (τ : Fin 2 → ℚ) : Fin 3 → ℚ := ![τ 0, τ 1, 0]

/-- [proved-derived; formal-checked] Folding a lifted source returns it. -/
theorem fold_lift (τ : Fin 2 → ℚ) : fold (lift τ) = τ := by
  funext i
  fin_cases i <;> simp [fold, lift]

/-- [proved-derived; formal-checked] Folding keeps the total charge. -/
theorem fold_charge (σ : Fin 3 → ℚ) : fold σ 0 + fold σ 1 = σ 0 + σ 1 + σ 2 := by
  simp [fold]
  ring

/-- [definition] A bundle flux `j` and a pendant flux `s`, glued into a composite flux. -/
def glue (j : Fin m → ℚ) (s : ℚ) : Fin (m + 1) → ℚ := Fin.lastCases (motive := fun _ => ℚ) s j

/-- [proved-derived; formal-checked] The glued flux carries `j` on the bundle edges. -/
@[simp] theorem glue_castSucc (j : Fin m → ℚ) (s : ℚ) (e : Fin m) : glue j s e.castSucc = j e := by
  simp [glue]

/-- [proved-derived; formal-checked] The glued flux carries `s` on the pendant. -/
@[simp] theorem glue_last (j : Fin m → ℚ) (s : ℚ) : glue j s (Fin.last m) = s := by
  simp [glue]

/-- [proved-derived; formal-checked] Gluing forgets no bundle flux. -/
theorem glue_injective (s : ℚ) : Function.Injective (fun j : Fin m → ℚ => glue j s) := by
  intro j j' h
  funext e
  simpa using congrFun h e.castSucc

/-- [proved-derived; formal-checked] Every bundle edge of the composite reads the drop `φ₁ − φ₀`. -/
theorem pendantBundle_mulVec_castSucc (φ : Fin 3 → ℚ) (e : Fin m) :
    (pendantBundle m *ᵥ φ) e.castSucc = φ 1 - φ 0 := by
  simp [pendantBundle, mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- [proved-derived; formal-checked] The pendant reads the drop `φ₂ − φ₁`. -/
theorem pendantBundle_mulVec_last (φ : Fin 3 → ℚ) :
    (pendantBundle m *ᵥ φ) (Fin.last m) = φ 2 - φ 1 := by
  simp [pendantBundle, mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- [proved-derived; formal-checked] The composite's boundary of an edge vector. -/
theorem pendantBundle_transpose_mulVec (j : Fin (m + 1) → ℚ) :
    (pendantBundle m)ᵀ *ᵥ j =
      ![-(∑ e : Fin m, j e.castSucc), (∑ e : Fin m, j e.castSucc) - j (Fin.last m),
        j (Fin.last m)] := by
  funext i
  fin_cases i
  · simp [pendantBundle, mulVec, dotProduct, Fin.sum_univ_castSucc, Finset.sum_neg_distrib]
  · simp [pendantBundle, mulVec, dotProduct, Fin.sum_univ_castSucc]
    ring
  · simp [pendantBundle, mulVec, dotProduct, Fin.sum_univ_castSucc]

/-- [proved-derived; formal-checked] **The composite's balance.** `φ` solves `σ` exactly when `σ`
has zero total charge, the bundle's common drop is `(σ₁ + σ₂)/T` over the bundle's total, and the
pendant's drop is `σ₂` over its conductance. -/
theorem pendant_solves_iff [NeZero m] (Θ : Constitution (m + 1)) (φ σ : Fin 3 → ℚ) :
    Solves (pendantBundle m) Θ φ σ ↔
      σ 0 + σ 1 + σ 2 = 0 ∧ φ 1 - φ 0 = (σ 1 + σ 2) / total (restrict Θ) ∧
        φ 2 - φ 1 = σ 2 / Θ.1 (Fin.last m) := by
  have hT := (total_pos (restrict Θ)).ne'
  have hp := (Θ.2 (Fin.last m)).ne'
  rw [solves_iff_boundary_flux, pendantBundle_transpose_mulVec]
  have hsum : ∑ e : Fin m, flux (pendantBundle m) Θ φ e.castSucc =
      total (restrict Θ) * (φ 1 - φ 0) := by
    simp only [flux, pendantBundle_mulVec_castSucc, total, restrict, Finset.sum_mul]
  have hlast : flux (pendantBundle m) Θ φ (Fin.last m) = Θ.1 (Fin.last m) * (φ 2 - φ 1) := by
    simp only [flux, pendantBundle_mulVec_last]
  rw [hsum, hlast]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp at h0 h1 h2
    refine ⟨by linarith, ?_, ?_⟩
    · rw [eq_div_iff hT]
      linarith
    · rw [eq_div_iff hp]
      linarith
  · rintro ⟨h012, hg, hg'⟩
    rw [hg, hg']
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
theorem pendant_solvable_iff [NeZero m] (Θ : Constitution (m + 1)) (σ : Fin 3 → ℚ) :
    (∃ φ, Solves (pendantBundle m) Θ φ σ) ↔ σ 0 + σ 1 + σ 2 = 0 := by
  constructor
  · rintro ⟨φ, h⟩
    exact ((pendant_solves_iff Θ φ σ).mp h).1
  · intro h
    refine ⟨![0, (σ 1 + σ 2) / total (restrict Θ),
      (σ 1 + σ 2) / total (restrict Θ) + σ 2 / Θ.1 (Fin.last m)],
      (pendant_solves_iff Θ _ σ).mpr ⟨h, by simp, by simp⟩⟩

/-- [proved-derived; formal-checked] **The composite splits the folded source by the bundle's
shares and sends the leaf's charge down the pendant**: `j_e = r_e (σ₁ + σ₂)` on the bundle and
`σ₂` on the pendant, whatever the pendant's conductance. -/
theorem pendant_flux [NeZero m] {Θ : Constitution (m + 1)} {φ σ : Fin 3 → ℚ}
    (h : Solves (pendantBundle m) Θ φ σ) :
    flux (pendantBundle m) Θ φ = glue (fun e => share (restrict Θ) e * (σ 1 + σ 2)) (σ 2) := by
  obtain ⟨-, hg, hg'⟩ := (pendant_solves_iff Θ φ σ).mp h
  funext e
  induction e using Fin.lastCases with
  | last =>
    rw [glue_last]
    simp only [flux, pendantBundle_mulVec_last, hg']
    field_simp [(Θ.2 (Fin.last m)).ne']
  | cast e =>
    rw [glue_castSucc]
    simp only [flux, pendantBundle_mulVec_castSucc, hg, share, restrict]
    ring

/-- [proved-derived; formal-checked] Every bundle edge of the composite sees the drop
`(σ₁ + σ₂)/T`. -/
theorem pendant_drop_castSucc [NeZero m] {Θ : Constitution (m + 1)} {φ σ : Fin 3 → ℚ}
    (h : Solves (pendantBundle m) Θ φ σ) (e : Fin m) :
    (pendantBundle m *ᵥ φ) e.castSucc = (σ 1 + σ 2) / total (restrict Θ) := by
  rw [pendantBundle_mulVec_castSucc, ((pendant_solves_iff Θ φ σ).mp h).2.1]

/-- [proved-derived; formal-checked] **The composite's observation is the bundle's at the folded
source**, with the leaf's charge on the pendant. -/
theorem pendant_observeConstitution [NeZero m] (σ : Fin 3 → ℚ) (Θ : Constitution (m + 1)) :
    observeConstitution (pendantBundle m) σ Θ =
      (observeConstitution (bundle m) (fold σ) (restrict Θ)).map (fun j => glue j (σ 2)) := by
  rw [bundle_observeConstitution, fold_charge]
  by_cases h : σ 0 + σ 1 + σ 2 = 0
  · have hs := (pendant_solvable_iff Θ σ).mpr h
    rw [observeConstitution, if_pos hs, if_pos h, Option.map_some,
      pendant_flux (canonicalSolve_solves hs)]
    simp [fold]
  · rw [observeConstitution, if_neg (fun hs => h ((pendant_solvable_iff Θ σ).mp hs)), if_neg h,
      Option.map_none]

/-- [proved-derived; formal-checked] **The bundle part steps as the bundle under the folded
source**, for any composite law that deposits on the bundle's edges as the bundle's law does. -/
theorem restrict_stepConstitution [NeZero m] (L' : DepositionLaw (m + 1)) (L : DepositionLaw m)
    (hL : ∀ e j g, L'.Γ e.castSucc j g = L.Γ e j g) (σ : Fin 3 → ℚ) (Θ : Constitution (m + 1)) :
    restrict (stepConstitution L' (pendantBundle m) σ Θ) =
      stepConstitution L (bundle m) (fold σ) (restrict Θ) := by
  by_cases h : σ 0 + σ 1 + σ 2 = 0
  · have hs := (pendant_solvable_iff Θ σ).mpr h
    have hb : fold σ 0 + fold σ 1 = 0 := by rw [fold_charge]; exact h
    apply Subtype.ext
    funext e
    rw [bundle_stepConstitution_apply L hb]
    show (stepConstitution L' (pendantBundle m) σ Θ).1 e.castSucc = _
    rw [stepConstitution, if_pos hs]
    simp only [deposit]
    rw [pendant_flux (canonicalSolve_solves hs), pendant_drop_castSucc (canonicalSolve_solves hs),
      glue_castSucc, hL]
    simp [fold, restrict]
  · have hb : fold σ 0 + fold σ 1 ≠ 0 := by rw [fold_charge]; exact h
    rw [bundle_stepConstitution_of_ne L hb, stepConstitution,
      if_neg (fun hs => h ((pendant_solvable_iff Θ σ).mp hs))]

/-- [proved-derived; formal-checked] Along every history the bundle part steps as the bundle under
the folded word. -/
theorem restrict_transportWord [NeZero m] (L' : DepositionLaw (m + 1)) (L : DepositionLaw m)
    (hL : ∀ e j g, L'.Γ e.castSucc j g = L.Γ e j g) (word : List (Fin 3 → ℚ))
    (Θ : Constitution (m + 1)) :
    restrict (transportWord (stepConstitution L' (pendantBundle m)) word Θ) =
      transportWord (stepConstitution L (bundle m)) (word.map fold) (restrict Θ) := by
  induction word with
  | nil => rfl
  | cons σ word ih =>
    rw [transportWord_cons, restrict_stepConstitution L' L hL, ih, List.map_cons,
      transportWord_cons]

/-- [definition] The solver that returns the canonical potential. -/
def canonicalSolver {p q : ℕ} (d : Matrix (Fin q) (Fin p) ℚ) : Solver d :=
  ⟨fun _ Θ σ => canonicalSolve d Θ σ, fun _ _ _ h => canonicalSolve_solves h⟩

/-- [proved-derived; formal-checked] **The pendant is forgotten.** Two composite presents share
every future exactly when their bundle parts share every future on the bundle, for any solvers and
any composite law that deposits on the bundle's edges as the bundle's law does. -/
theorem pendant_futureAgreement_iff [NeZero m] (L' : DepositionLaw (m + 1)) (L : DepositionLaw m)
    (hL : ∀ e j g, L'.Γ e.castSucc j g = L.Γ e j g) (S : Solver (pendantBundle m))
    (Sb : Solver (bundle m)) (left right : DepositState (m + 1)) :
    futureAgreement (observe S) (step L' S) left right ↔
      futureAgreement (observe Sb) (step L Sb) ⟨restrict left.constitution, []⟩
        ⟨restrict right.constitution, []⟩ := by
  constructor
  · intro h τ word
    have hw := h (lift τ) (word.map lift)
    have hfl : fold ∘ lift = id := funext fold_lift
    rw [observe_eq_observeConstitution, observe_eq_observeConstitution, transportWord_constitution,
      transportWord_constitution, pendant_observeConstitution, pendant_observeConstitution,
      restrict_transportWord L' L hL, restrict_transportWord L' L hL, List.map_map, hfl,
      List.map_id, fold_lift] at hw
    rw [observe_eq_observeConstitution, observe_eq_observeConstitution, transportWord_constitution,
      transportWord_constitution]
    exact Option.map_injective (glue_injective _) hw
  · intro h σ word
    have hw := h (fold σ) (word.map fold)
    rw [observe_eq_observeConstitution, observe_eq_observeConstitution, transportWord_constitution,
      transportWord_constitution] at hw
    rw [observe_eq_observeConstitution, observe_eq_observeConstitution, transportWord_constitution,
      transportWord_constitution, pendant_observeConstitution, pendant_observeConstitution,
      restrict_transportWord L' L hL, restrict_transportWord L' L hL]
    exact congrArg (Option.map fun j => glue j (σ 2)) hw

/-- [proved-derived; formal-checked] **The future-agreement relation of the square law on the
bundle with a pendant edge.** Two presents share every future iff their bundle parts are equal or
both uniform. -/
theorem pendant_square_futureAgreement_iff [NeZero m] (S : Solver (pendantBundle m))
    (left right : DepositState (m + 1)) :
    futureAgreement (observe S) (step (squareLawOn (m + 1)) S) left right ↔
      restrict left.constitution = restrict right.constitution ∨
        (Uniform (restrict left.constitution) ∧ Uniform (restrict right.constitution)) :=
  (pendant_futureAgreement_iff _ (squareLawOn m) (fun _ _ _ => rfl) S (canonicalSolver _) left
    right).trans (bundle_futureAgreement_iff _ _ _)

/-- [proved-derived; formal-checked] **Under the Joule law the composite keeps the bundle part's
projective class**, and forgets the pendant. -/
theorem pendant_joule_futureAgreement_iff [NeZero m] (S : Solver (pendantBundle m))
    (left right : DepositState (m + 1)) :
    futureAgreement (observe S) (step (jouleLawOn (m + 1)) S) left right ↔
      ProjectivelyEqual (restrict left.constitution) (restrict right.constitution) :=
  (pendant_futureAgreement_iff _ (jouleLawOn m) (fun _ _ _ => rfl) S (canonicalSolver _) left
    right).trans (joule_bundle_futureAgreement_iff _ _ _)

/-- [definition] **The minimal retention of the square law on the bundle with a pendant edge**: the
bundle's minimal retention of the bundle part, the product of the bundle's factor with the
pendant's point. -/
def pendantMinimalRetain (state : DepositState (m + 1)) : Option (Constitution m) :=
  minimalRetain (⟨restrict state.constitution, []⟩ : DepositState m)

/-- [proved-derived; formal-checked] **Its kernel is future agreement.** -/
theorem pendantMinimalRetain_eq_iff_futureAgreement [NeZero m] (S : Solver (pendantBundle m))
    (left right : DepositState (m + 1)) :
    pendantMinimalRetain left = pendantMinimalRetain right ↔
      futureAgreement (observe S) (step (squareLawOn (m + 1)) S) left right := by
  rw [pendant_square_futureAgreement_iff, pendantMinimalRetain, pendantMinimalRetain,
    minimalRetain_eq_iff_futureAgreement (canonicalSolver (bundle m)), bundle_futureAgreement_iff]

/-- [proved-derived; formal-checked] **It is a lawful standing.** -/
theorem pendantMinimalStanding_exists [NeZero m] (S : Solver (pendantBundle m)) :
    ∃ L : StandingLaw (Fin 3 → ℚ) (Fin 3 → ℚ) (DepositState (m + 1)) (Option (Constitution m))
        (Option (Fin (m + 1) → ℚ)),
      L.transport = step (squareLawOn (m + 1)) S ∧ L.observe = observe S ∧
        L.retain = pendantMinimalRetain := by
  rw [standingLaw_exists_iff_future_factors]
  intro left right h
  exact (causalSignature_eq_iff_futureAgreement _ _ _ _).mpr
    ((pendantMinimalRetain_eq_iff_futureAgreement S left right).mp h)

/-- [proved-derived; formal-checked] **It is least**: every retention carrying a `StandingLaw` for
the same composite medium refines it. -/
theorem pendantMinimalRetain_factors_through_every_standing [NeZero m]
    (S : Solver (pendantBundle m)) {Retained : Type*}
    (L : StandingLaw (Fin 3 → ℚ) (Fin 3 → ℚ) (DepositState (m + 1)) Retained
      (Option (Fin (m + 1) → ℚ)))
    (htransport : L.transport = step (squareLawOn (m + 1)) S) (hobserve : L.observe = observe S)
    {left right : DepositState (m + 1)} (h : L.retain left = L.retain right) :
    pendantMinimalRetain left = pendantMinimalRetain right := by
  have hagree := L.futureAgreement_of_retain_eq h
  rw [htransport, hobserve] at hagree
  exact (pendantMinimalRetain_eq_iff_futureAgreement S left right).mpr hagree

end Pendant

end Holonics.Objects.RetentionClasses
