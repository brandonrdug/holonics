import Holonics.Compression.Landmark.Identity
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Nat.Nth

/-!
# A chart's density: an infinite subset of an irreducible plane curve carries its identities

[definition] A configuration cut out by one polynomial is its **zero set** `V(f)` (`zeroSet`). A
**rational chart** is `t ↦ (p(t)/q(t), r(t)/s(t))` on the parameters where neither denominator
vanishes (`chartDomain`, `rationalChart`); a coordinate `p/q` is **nonconstant** when no `p − c·q`
is the zero polynomial (`NonconstantRatio`). For monomials `σ →₀ ℕ` the order `≤` is divisibility,
and an index of a sequence of monomials is **new** when no earlier term divides it (`IsNew`): a
leading monomial that Buchberger's loop adds because it lies outside the ideal of the earlier ones.

Sources: #410's box "The identity atlas: Gröbner completion and the face-kernel equality; Richardson
undecidability; a nonconstant rational chart is Zariski-dense in an irreducible curve
(`Compression/Landmark/Identity`)"; the `[open]` paragraph of `Holonics/Compression/Landmark/Identity`,
its third item ("an infinite subset of an irreducible curve is Zariski dense in it", "a nonzero
generator in every single coordinate") and its first (Buchberger's halting by Dickson's lemma); the
identity-atlas plan that module links, held at commit `13f8c734` as
`docs/plans/THE_IDENTITIES_OF_A_CONFIGURATION_ARE_THE_KERNEL_OF_ITS_FACE_MAP.md`; the atlas rows
`landmark.identity-kernel`, `landmark.coverage-law`, `landmark.one-winding-invents` and
`poly.bareiss-resultant` (the resultant that eliminates one parameter, used here as the certificate).

[proved-standard; formal-checked] What is proved.

1. **The resultant certificate.** In `K[x][y]`, an irreducible `f` of positive degree in `y` that
   does not divide `g` has `a·f + b·g = r(x)` with `r ≠ 0`: `r` is the Sylvester resultant, nonzero
   because `f` stays irreducible over `K(x)` and so is coprime to `g` there (Gauss's lemma)
   (`exists_resultant_certificate`). So the common zeros of `f` and `g` have finitely many first
   coordinates (`finite_fst_common_zeros`, the case of `f` in `x` alone included), and, by the swap
   of the two variables, finitely many second ones: they are finite
   (`finite_common_zeros`, `evalEval_swap`, `eval_equivMvPolynomial`).
2. **An infinite subset of an irreducible plane curve is dense in it.** For `f` irreducible in
   `K[x₀, x₁]` and `g ∉ (f)`, `V(f) ∩ V(g)` is finite (`finite_zeroSet_inter`). So every `g` that
   vanishes on an infinite `S ⊆ V(f)` is a multiple of `f` (`dvd_of_vanishes_on_infinite`), the
   identity ideal of `S` is `(f)` (`identityIdeal_eq_span_of_infinite`), that of an infinite `V(f)`
   is `(f)` (`identityIdeal_zeroSet`), and the Zariski closure of `S` is `V(f)`
   (`zariskiClosure_eq_zeroSet`, `zeroSet_subset_zariskiClosure`).
3. **A nonconstant rational chart certifies the curve's identities and no others.** Over an infinite
   field, a chart with nonzero denominators and one nonconstant coordinate has an infinite image
   (`chartDomain_infinite`, `range_infinite_of_ratio`, `rationalChart_range_infinite`); landing in an
   irreducible `V(f)`, its image ideal is `(f)` (`rationalChart_image_ideal`), the ideal of `V(f)`,
   so by `certifies_exactly_iff` it certifies a polynomial when and only when the polynomial vanishes
   on `V(f)`, and by `identityIdeal_eq_iff_dense` `V(f)` lies in the closure of its image
   (`rationalChart_certifies`). Polynomial charts with a coordinate of positive degree are the case
   `q = s = 1` (`nonconstantRatio_one`, `polynomialChart_image_ideal`).
4. **The circle and the recorded case.** `x₀² + x₁² − 1` is irreducible over `ℚ`
   (`unitCircle_irreducible`: monic in `x₁`, and its fibre `x₁² + 3` at `x₀ = 2` has no rational
   root), and the chart `((1 − t²)/(1 + t²), 2t/(1 + t²))` lands in it (`circleChart_lands`) with image ideal
   `(x₀² + x₁² − 1)`, certifying the circle's identities and no others (`circleChart_image_ideal`).
   The contrast: the Galilean fibre `x₀² = 1` of `Identity` is the zero set of the reducible
   `(x₀ − 1)(x₀ + 1)`, and the principal winding's image is infinite inside it while its identity
   ideal is strictly larger (`reducible_fibre_contrast`): an infinite subset of a reducible fibre
   need not be dense, since it can fill one component and miss the other.
5. **Dickson's lemma and Buchberger's halting.** Every sequence of monomials in finitely many
   variables has a term dividing a later one (`dickson`, from Mathlib's well-quasi-order on
   `σ →₀ ℕ`); so a sequence has finitely many new terms (`finite_isNew`). A monomial lies in the
   ideal of earlier monomials when and only when one of them divides it
   (`monomial_mem_span_earlier_iff`), so in any sequence of leading monomials only finitely many fall
   outside the ideal of the earlier ones, and from some index on none does: the loop that adds such a
   monomial at each round halts (`buchberger_halts`, `buchberger_eventually_inside`,
   `no_infinite_buchberger_run`), and the chain of monomial ideals the sequence generates stabilizes
   (`monomial_chain_stabilizes`).
6. **The dimension certificate of a point configuration.** In finitely many variables, `V` is finite
   when and only when its identity ideal holds, for every coordinate `i`, a nonzero polynomial in
   `x_i` alone (`finite_of_coordinate_certificates`, `coordinate_certificates_of_finite`,
   `finite_iff_coordinate_certificates`).

What is not claimed. Richardson undecidability and the holonomic search are not attempted. The
face-kernel equality `J = ker(face)` for a supplied presentation (elimination with saturation, or a
certified Hilbert bound) is not formalized, nor is Buchberger's criterion (S-polynomials reducing to
zero); item 5 states the halting for any sequence of leading monomials, the property the loop's
termination rests on, and no monomial order or division algorithm is modelled. The density of item 2
is stated in the plane, for one irreducible `f`; a curve in more variables, a reducible curve taken
component by component are not stated (a curve's dimension certificate by every pair of coordinates
is `Compression/Landmark/EliminantCertificate`'s). Item 3's nonconstancy is stated on the
polynomials (`p − c·q ≠ 0` for every `c`), which for `q ≠ 0` says that `p/q` is no constant of
`K(t)`; that reading in `K(t)` is not written. The circle's irreducibility is proved over `ℚ` (by the
specialization at `x₀ = 2`); over any field of characteristic other than 2 it holds by the degree of
`1 − x₀²`, which is not written.

The computational object is the helical pair interaction: a chart is a navigator's path into a
configuration, one parameter carried into the configuration's points (the circle's chart is the
half-angle substitution of the turn, `t = tan(θ/2)`), and the identity ideal is the kernel of the
receiver's face, the pairing of a polynomial construction with the points the chart places. Density
says when a path reaches enough of the configuration for that kernel to be the configuration's own:
on an irreducible curve any infinite reach suffices, and on a reducible fibre a path that stays on
one component invents an identity. Of the winding guide's six general objects this touches the helix
(the chart's parameter and the circle it winds) and the faces and placement (the evaluation face
and the points a chart places); the pair, the cell holonomy, the tube and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.Landmark.ChartDensity

open Polynomial Polynomial.Bivariate Holonics.Compression.Landmark.Identity

/-! ## 1. The resultant certificate in `K[x][y]` -/

section Bivariate

variable {K : Type*} [Field K]

/-- [proved-standard; formal-checked] An irreducible `f` of positive `y`-degree not dividing `g` has
`a·f + b·g = r(x)` with `r ≠ 0` (the resultant). -/
theorem exists_resultant_certificate {f g : K[X][Y]} (hf : Irreducible f) (hdeg : f.natDegree ≠ 0)
    (hfg : ¬ f ∣ g) : ∃ r : K[X], r ≠ 0 ∧ ∃ a b : K[X][Y], f * a + g * b = C r := by
  obtain ⟨a, b, -, -, hab⟩ := exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl (Or.inl hdeg)
  refine ⟨f.resultant g, ?_, a, b, hab⟩
  intro h0
  have hprim : f.IsPrimitive := hf.isPrimitive hdeg
  have hinj : Function.Injective (algebraMap K[X] (FractionRing K[X])) :=
    IsFractionRing.injective _ _
  have hmap : (f.map (algebraMap K[X] (FractionRing K[X]))).resultant
      (g.map (algebraMap K[X] (FractionRing K[X]))) = 0 := by
    rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj, resultant_map_map,
      h0, map_zero]
  have hirr := (hprim.irreducible_iff_irreducible_map_fraction_map
    (K := FractionRing K[X])).mp hf
  have hnd : ¬ f.map (algebraMap K[X] (FractionRing K[X])) ∣
      g.map (algebraMap K[X] (FractionRing K[X])) :=
    fun h => hfg ((hprim.dvd_iff_fraction_map_dvd_fraction_map (FractionRing K[X])).mpr h)
  exact (resultant_eq_zero_iff.mp hmap).2 (hirr.coprime_iff_not_dvd.mpr hnd)

/-- [proved-standard; formal-checked] The common zeros of an irreducible `f` and a `g ∉ (f)` have
finitely many first coordinates. -/
theorem finite_fst_common_zeros {f g : K[X][Y]} (hf : Irreducible f) (hfg : ¬ f ∣ g) :
    {x : K | ∃ y, f.evalEval x y = 0 ∧ g.evalEval x y = 0}.Finite := by
  by_cases hdeg : f.natDegree = 0
  · have hfC := eq_C_of_natDegree_eq_zero hdeg
    have hp : f.coeff 0 ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hfC
      exact hf.ne_zero hfC
    apply (finite_setOfPred_isRoot hp).subset
    rintro x ⟨y, hx, -⟩
    rw [hfC, evalEval_C] at hx
    exact hx
  · obtain ⟨r, hr, a, b, hab⟩ := exists_resultant_certificate hf hdeg hfg
    apply (finite_setOfPred_isRoot hr).subset
    rintro x ⟨y, hx, hy⟩
    have := congrArg (evalEval x y) hab
    rw [evalEval_add, evalEval_mul, evalEval_mul, hx, hy, evalEval_C] at this
    show r.eval x = 0
    rw [← this]
    ring

/-- [proved-standard; formal-checked] The swap of the two variables exchanges the evaluation
point's coordinates. -/
theorem evalEval_swap (x y : K) (p : K[X][Y]) :
    (Bivariate.swap p).evalEval x y = p.evalEval y x := by
  have := Bivariate.aevalAeval_swap (R := K) x y p
  rwa [coe_aevalAeval_eq_evalEval, coe_aevalAeval_eq_evalEval] at this

/-- [proved-standard; formal-checked] An irreducible `f` and a `g ∉ (f)` have finitely many common
zeros. -/
theorem finite_common_zeros {f g : K[X][Y]} (hf : Irreducible f) (hfg : ¬ f ∣ g) :
    {z : K × K | f.evalEval z.1 z.2 = 0 ∧ g.evalEval z.1 z.2 = 0}.Finite := by
  have h1 := finite_fst_common_zeros hf hfg
  have hf' : Irreducible (Bivariate.swap f) := (MulEquiv.irreducible_iff _).mpr hf
  have hfg' : ¬ Bivariate.swap f ∣ Bivariate.swap g := by rwa [map_dvd_iff]
  have h2 := finite_fst_common_zeros hf' hfg'
  apply (h1.prod h2).subset
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  refine ⟨⟨y, hx, hy⟩, x, ?_, ?_⟩
  · rw [evalEval_swap]
    exact hx
  · rw [evalEval_swap]
    exact hy

/-- [proved-standard; formal-checked] Evaluation through Mathlib's `K[X][Y] ≃ K[x₀, x₁]`
(`C X ↦ x₀`, `Y ↦ x₁`). -/
theorem eval_equivMvPolynomial (x : Fin 2 → K) (p : K[X][Y]) :
    MvPolynomial.eval x (Bivariate.equivMvPolynomial K p) = p.evalEval (x 0) (x 1) := by
  have h : (MvPolynomial.aeval x).comp (Bivariate.equivMvPolynomial K).toAlgHom =
      aevalAeval (x 0) (x 1) := by
    ext <;> simp
  have := AlgHom.congr_fun h p
  rw [AlgHom.comp_apply, coe_aevalAeval_eq_evalEval] at this
  rw [← this, ← MvPolynomial.coe_aeval_eq_eval]
  rfl

end Bivariate

/-! ## 2. An infinite subset of an irreducible plane curve is dense in it -/

section Curve

variable {σ K : Type*} [Field K]

/-- [definition] The zero set `V(f)`: the configuration cut out by one polynomial. -/
def zeroSet (f : MvPolynomial σ K) : Set (σ → K) := {x | MvPolynomial.eval x f = 0}

/-- [definition] Membership in `V(f)` is the vanishing of `f`. -/
theorem mem_zeroSet {f : MvPolynomial σ K} {x : σ → K} :
    x ∈ zeroSet f ↔ MvPolynomial.eval x f = 0 := Iff.rfl

/-- [proved-standard; formal-checked] For `f` irreducible in `K[x₀, x₁]` and `f ∤ g`, `V(f) ∩ V(g)` is
finite. -/
theorem finite_zeroSet_inter {f g : MvPolynomial (Fin 2) K} (hf : Irreducible f) (hfg : ¬ f ∣ g) :
    (zeroSet f ∩ zeroSet g).Finite := by
  have hf₀ : Irreducible ((Bivariate.equivMvPolynomial K).symm f) :=
    (MulEquiv.irreducible_iff _).mpr hf
  have hfg₀ : ¬ (Bivariate.equivMvPolynomial K).symm f ∣ (Bivariate.equivMvPolynomial K).symm g := by
    rwa [map_dvd_iff]
  apply ((finite_common_zeros hf₀ hfg₀).image fun z : K × K => ![z.1, z.2]).subset
  rintro x ⟨hx, hy⟩
  refine ⟨(x 0, x 1), ⟨?_, ?_⟩, ?_⟩
  · rw [← eval_equivMvPolynomial, AlgEquiv.apply_symm_apply]
    exact hx
  · rw [← eval_equivMvPolynomial, AlgEquiv.apply_symm_apply]
    exact hy
  · funext i
    fin_cases i <;> rfl

/-- [proved-standard; formal-checked] A polynomial vanishing on an infinite subset of an irreducible
plane curve `V(f)` is a multiple of `f`. -/
theorem dvd_of_vanishes_on_infinite {f g : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    {S : Set (Fin 2 → K)} (hS : S ⊆ zeroSet f) (hinf : S.Infinite) (hg : g ∈ identityIdeal S) :
    f ∣ g := by
  by_contra hfg
  exact hinf ((finite_zeroSet_inter hf hfg).subset fun x hx =>
    ⟨hS hx, (mem_identityIdeal_iff S g).mp hg x hx⟩)

/-- [proved-standard; formal-checked] The identity ideal of an infinite subset of an irreducible
plane curve `V(f)` is `(f)`. -/
theorem identityIdeal_eq_span_of_infinite {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    {S : Set (Fin 2 → K)} (hS : S ⊆ zeroSet f) (hinf : S.Infinite) :
    identityIdeal S = Ideal.span {f} := by
  ext g
  rw [Ideal.mem_span_singleton]
  refine ⟨dvd_of_vanishes_on_infinite hf hS hinf, ?_⟩
  rintro ⟨c, rfl⟩
  rw [mem_identityIdeal_iff]
  intro x hx
  rw [map_mul, mem_zeroSet.mp (hS hx), zero_mul]

/-- [proved-standard; formal-checked] An infinite irreducible plane curve `V(f)` has identity ideal
`(f)`. -/
theorem identityIdeal_zeroSet {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hinf : (zeroSet f).Infinite) : identityIdeal (zeroSet f) = Ideal.span {f} :=
  identityIdeal_eq_span_of_infinite hf subset_rfl hinf

/-- [proved-standard; formal-checked] The Zariski closure of an infinite subset of an irreducible
plane curve is the curve. -/
theorem zariskiClosure_eq_zeroSet {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    {S : Set (Fin 2 → K)} (hS : S ⊆ zeroSet f) (hinf : S.Infinite) :
    zariskiClosure S = zeroSet f := by
  have hI := identityIdeal_eq_span_of_infinite hf hS hinf
  ext x
  constructor
  · intro hx
    exact hx f (by rw [hI]; exact Ideal.mem_span_singleton_self f)
  · intro hx p hp
    rw [hI, Ideal.mem_span_singleton] at hp
    obtain ⟨c, rfl⟩ := hp
    rw [map_mul, mem_zeroSet.mp hx, zero_mul]

/-- [proved-standard; formal-checked] **Density.** An infinite subset of an irreducible plane curve
is Zariski dense in it. -/
theorem zeroSet_subset_zariskiClosure {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    {S : Set (Fin 2 → K)} (hS : S ⊆ zeroSet f) (hinf : S.Infinite) :
    zeroSet f ⊆ zariskiClosure S :=
  (zariskiClosure_eq_zeroSet hf hS hinf).ge

end Curve

/-! ## 3. A nonconstant rational chart -/

section Chart

variable {K : Type*} [Field K]

/-- [definition] The parameters where a chart's two denominators do not vanish. -/
def chartDomain (q s : K[X]) : Set K := {t | q.eval t ≠ 0 ∧ s.eval t ≠ 0}

/-- [definition] The rational chart `t ↦ (p(t)/q(t), r(t)/s(t))` on its domain, as a one-member
family. -/
noncomputable def rationalChart (p q r s : K[X]) : Unit → chartDomain q s → Fin 2 → K :=
  fun _ t => ![p.eval (t : K) / q.eval (t : K), r.eval (t : K) / s.eval (t : K)]

/-- [definition] The coordinate `p/q` is nonconstant: no `p − c·q` is the zero polynomial. -/
def NonconstantRatio (p q : K[X]) : Prop := ∀ c : K, p - C c * q ≠ 0

/-- [definition] The polynomial chart `t ↦ (p(t), r(t))`, as a one-member family. -/
noncomputable def polynomialChart (p r : K[X]) : Unit → K → Fin 2 → K :=
  fun _ t => ![p.eval t, r.eval t]

/-- [proved-standard; formal-checked] Over an infinite field, nonzero denominators leave infinitely
many parameters. -/
theorem chartDomain_infinite [Infinite K] {q s : K[X]} (hq : q ≠ 0) (hs : s ≠ 0) :
    (chartDomain q s).Infinite := by
  have hfin : ({t | q.IsRoot t} ∪ {t | s.IsRoot t}).Finite :=
    (finite_setOfPred_isRoot hq).union (finite_setOfPred_isRoot hs)
  refine hfin.infinite_compl.mono ?_
  intro t ht
  simp only [Set.mem_compl_iff, Set.mem_union, not_or] at ht
  exact ht

/-- [proved-standard; formal-checked] A map whose coordinate `i` is a nonconstant ratio of the
parameter, on infinitely many parameters, has an infinite image. -/
theorem range_infinite_of_ratio {T : Type*} (τ : T → K) (hτ : (Set.range τ).Infinite)
    (χ : T → Fin 2 → K) (i : Fin 2) {p q : K[X]} (hnc : NonconstantRatio p q)
    (hχ : ∀ t, q.eval (τ t) ≠ 0 ∧ χ t i = p.eval (τ t) / q.eval (τ t)) :
    (Set.range χ).Infinite := by
  intro hfin
  apply hτ
  refine ((hfin.image fun x => x i).biUnion fun c _ => finite_setOfPred_isRoot (hnc c)).subset ?_
  rintro _ ⟨t, rfl⟩
  rw [Set.mem_iUnion₂]
  refine ⟨χ t i, ⟨χ t, ⟨t, rfl⟩, rfl⟩, ?_⟩
  show (p - C (χ t i) * q).eval (τ t) = 0
  rw [eval_sub, eval_mul, eval_C, (hχ t).2, div_mul_cancel₀ _ (hχ t).1, sub_self]

/-- [proved-standard; formal-checked] A rational chart with nonzero denominators and one nonconstant
coordinate has an infinite image over an infinite field. -/
theorem rationalChart_range_infinite [Infinite K] {p q r s : K[X]} (hq : q ≠ 0) (hs : s ≠ 0)
    (hnc : NonconstantRatio p q ∨ NonconstantRatio r s) :
    (Set.range (rationalChart p q r s ())).Infinite := by
  have hτ : (Set.range ((↑) : chartDomain q s → K)).Infinite := by
    rw [Subtype.range_coe]
    exact chartDomain_infinite hq hs
  rcases hnc with hnc | hnc
  · exact range_infinite_of_ratio _ hτ _ 0 hnc fun t => ⟨t.2.1, rfl⟩
  · exact range_infinite_of_ratio _ hτ _ 1 hnc fun t => ⟨t.2.2, rfl⟩

/-- [proved-standard; formal-checked] **A nonconstant rational chart landing in an irreducible
plane curve `V(f)` has image ideal `(f)`.** -/
theorem rationalChart_image_ideal [Infinite K] {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    {p q r s : K[X]} (hq : q ≠ 0) (hs : s ≠ 0) (hnc : NonconstantRatio p q ∨ NonconstantRatio r s)
    (hland : ∀ t, rationalChart p q r s () t ∈ zeroSet f) :
    identityIdeal (⋃ i, Set.range (rationalChart p q r s i)) = Ideal.span {f} := by
  apply identityIdeal_eq_span_of_infinite hf
  · intro x hx
    obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp hx
    exact hland t
  · exact (rationalChart_range_infinite hq hs hnc).mono
      (Set.subset_iUnion (fun i => Set.range (rationalChart p q r s i)) ())

/-- [proved-standard; formal-checked] **Such a chart certifies `V(f)`'s identities and no others**,
and `V(f)` lies in the Zariski closure of its image. -/
theorem rationalChart_certifies [Infinite K] {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    {p q r s : K[X]} (hq : q ≠ 0) (hs : s ≠ 0) (hnc : NonconstantRatio p q ∨ NonconstantRatio r s)
    (hland : ∀ t, rationalChart p q r s () t ∈ zeroSet f) :
    identityIdeal (⋃ i, Set.range (rationalChart p q r s i)) = identityIdeal (zeroSet f) ∧
      (∀ g, Certified (rationalChart p q r s) (fun x => MvPolynomial.eval x g) ↔
        g ∈ identityIdeal (zeroSet f)) ∧
      zeroSet f ⊆ zariskiClosure (⋃ i, Set.range (rationalChart p q r s i)) := by
  have hsound : ∀ i t, rationalChart p q r s i t ∈ zeroSet f := fun _ t => hland t
  have hinf : (zeroSet f).Infinite := by
    refine (rationalChart_range_infinite hq hs hnc).mono ?_
    rintro _ ⟨t, rfl⟩
    exact hland t
  have heq : identityIdeal (⋃ i, Set.range (rationalChart p q r s i)) =
      identityIdeal (zeroSet f) := by
    rw [rationalChart_image_ideal hf hq hs hnc hland, identityIdeal_zeroSet hf hinf]
  exact ⟨heq, certifies_exactly_iff.mpr heq, (identityIdeal_eq_iff_dense hsound).mp heq⟩

/-- [proved-standard; formal-checked] A polynomial coordinate of positive degree is a nonconstant
ratio over `1`. -/
theorem nonconstantRatio_one {p : K[X]} (hp : p.natDegree ≠ 0) : NonconstantRatio p 1 := by
  intro c h
  rw [mul_one] at h
  have := congrArg natDegree h
  rw [natDegree_sub_C, natDegree_zero] at this
  exact hp this

/-- [proved-standard; formal-checked] A polynomial chart with a coordinate of positive degree,
landing in an irreducible plane curve `V(f)`, has image ideal `(f)`. -/
theorem polynomialChart_image_ideal [Infinite K] {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    {p r : K[X]} (hnc : p.natDegree ≠ 0 ∨ r.natDegree ≠ 0)
    (hland : ∀ t, polynomialChart p r () t ∈ zeroSet f) :
    identityIdeal (⋃ i, Set.range (polynomialChart p r i)) = Ideal.span {f} := by
  apply identityIdeal_eq_span_of_infinite hf
  · intro x hx
    obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp hx
    exact hland t
  · have hτ : (Set.range (id : K → K)).Infinite := by
      rw [Set.range_id]
      exact Set.infinite_univ
    have hrange : (Set.range (polynomialChart p r ())).Infinite := by
      rcases hnc with hnc | hnc
      · exact range_infinite_of_ratio id hτ _ 0 (nonconstantRatio_one hnc) fun t =>
          ⟨by simp, by simp [polynomialChart]⟩
      · exact range_infinite_of_ratio id hτ _ 1 (nonconstantRatio_one hnc) fun t =>
          ⟨by simp, by simp [polynomialChart]⟩
    exact hrange.mono (Set.subset_iUnion (fun i => Set.range (polynomialChart p r i)) ())

end Chart

/-! ## 4. The circle, and the recorded case's reducible fibre -/

section Circle

/-- [definition] The unit circle `x₀² + x₁² − 1` over `ℚ`. -/
noncomputable def unitCircle : MvPolynomial (Fin 2) ℚ :=
  MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - 1

/-- [proved-standard; formal-checked] **The unit circle is irreducible over `ℚ`**: monic of degree two in
`x₁`, with the fibre `x₁² + 3` at `x₀ = 2` irreducible. -/
theorem unitCircle_irreducible : Irreducible unitCircle := by
  have he : Bivariate.equivMvPolynomial ℚ (Y ^ 2 + C (X ^ 2 - 1)) = unitCircle := by
    simp [unitCircle]
    ring
  rw [← he, MulEquiv.irreducible_iff]
  apply Monic.irreducible_of_irreducible_map (evalRingHom (2 : ℚ))
  · exact monic_X_pow_add_C _ two_ne_zero
  · have hmap : (Y ^ 2 + C (X ^ 2 - 1) : ℚ[X][Y]).map (evalRingHom (2 : ℚ)) = X ^ 2 + C 3 := by
      simp only [Polynomial.map_add, Polynomial.map_pow, map_X, map_C, coe_evalRingHom, eval_sub,
        eval_pow, eval_X, eval_one]
      norm_num
    rw [hmap]
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [natDegree_X_pow_add_C]
      simp
    · intro x hx
      simp only [IsRoot, eval_add, eval_pow, eval_X, eval_C] at hx
      nlinarith [sq_nonneg x]

/-- [definition] The circle's rational chart `t ↦ ((1 − t²)/(1 + t²), 2t/(1 + t²))`. -/
noncomputable def circleChart : Unit → chartDomain (1 + X ^ 2 : ℚ[X]) (1 + X ^ 2) → Fin 2 → ℚ :=
  rationalChart (1 - X ^ 2) (1 + X ^ 2) (C 2 * X) (1 + X ^ 2)

/-- [proved-standard; formal-checked] The circle's chart lands in the circle. -/
theorem circleChart_lands (t : chartDomain (1 + X ^ 2 : ℚ[X]) (1 + X ^ 2)) :
    circleChart () t ∈ zeroSet unitCircle := by
  have ht : (1 + (t : ℚ) ^ 2) ≠ 0 := by
    have := t.2.1
    simpa using this
  rw [mem_zeroSet]
  simp [circleChart, rationalChart, unitCircle]
  field_simp
  ring

/-- [proved-standard; formal-checked] **The circle's chart certifies the circle's identities and no
others**: its image ideal is `(x₀² + x₁² − 1)`, the circle's. -/
theorem circleChart_image_ideal :
    identityIdeal (⋃ i, Set.range (circleChart i)) = Ideal.span {unitCircle} ∧
      identityIdeal (⋃ i, Set.range (circleChart i)) = identityIdeal (zeroSet unitCircle) ∧
      (∀ g, Certified circleChart (fun x => MvPolynomial.eval x g) ↔
        g ∈ identityIdeal (zeroSet unitCircle)) := by
  have hq : (1 + X ^ 2 : ℚ[X]) ≠ 0 := by
    intro h
    have := congrArg (eval 0) h
    simp at this
  have hnc : NonconstantRatio (C 2 * X : ℚ[X]) (1 + X ^ 2) := by
    intro c h
    have h0 := congrArg (eval 0) h
    have h1 := congrArg (eval 1) h
    simp at h0 h1
    linarith
  have hc := rationalChart_certifies unitCircle_irreducible hq hq (Or.inr hnc) circleChart_lands
  exact ⟨rationalChart_image_ideal unitCircle_irreducible hq hq (Or.inr hnc) circleChart_lands,
    hc.1, hc.2.1⟩

/-- [counterexample; formal-checked] **The recorded case's fibre is reducible, and density fails
there**: `x₀² − 1 = (x₀ − 1)(x₀ + 1)` cuts out the Galilean fibre, the principal winding's image is
infinite inside it, and its identity ideal is strictly larger than the fibre's. -/
theorem reducible_fibre_contrast :
    galileanFibre = zeroSet (MvPolynomial.X 0 ^ 2 - 1 : MvPolynomial (Fin 2) ℚ) ∧
      ¬ Irreducible (MvPolynomial.X 0 ^ 2 - 1 : MvPolynomial (Fin 2) ℚ) ∧
      (⋃ i, Set.range (principalFamily i)).Infinite ∧
      identityIdeal galileanFibre < identityIdeal (⋃ i, Set.range (principalFamily i)) := by
  refine ⟨?_, ?_, ?_, principal_image_ideal_strictly_larger⟩
  · ext x
    simp [galileanFibre, zeroSet, sub_eq_zero]
  · intro h
    have hfac : (MvPolynomial.X 0 ^ 2 - 1 : MvPolynomial (Fin 2) ℚ) =
        (MvPolynomial.X 0 - 1) * (MvPolynomial.X 0 + 1) := by ring
    rcases h.isUnit_or_isUnit hfac with hu | hu
    · have := hu.map (MvPolynomial.eval ![1, 0])
      simp at this
    · have := hu.map (MvPolynomial.eval ![-1, 0])
      simp at this
  · have hinj : Function.Injective (principalFamily ()) := by
      intro a b h
      have := congrFun h 1
      simp only [principalFamily] at this
      rw [(windingChart_apply 1 a).2, (windingChart_apply 1 b).2] at this
      linarith
    exact (Set.infinite_range_of_injective hinj).mono
      (Set.subset_iUnion (fun i => Set.range (principalFamily i)) ())

end Circle

/-! ## 5. Dickson's lemma and Buchberger's halting -/

section Dickson

variable {σ : Type*} [Finite σ]

/-- [proved-standard; formal-checked] **Dickson's lemma**: in every sequence of monomials in finitely
many variables some term divides a later one. -/
theorem dickson (m : ℕ → σ →₀ ℕ) : ∃ i j, i < j ∧ m i ≤ m j :=
  wellQuasiOrdered_le m

/-- [definition] The index `n` is new in the sequence `m`: no earlier term divides `m n`. -/
def IsNew (m : ℕ → σ →₀ ℕ) (n : ℕ) : Prop := ∀ i < n, ¬ m i ≤ m n

/-- [proved-standard; formal-checked] A sequence of monomials has finitely many new terms. -/
theorem finite_isNew (m : ℕ → σ →₀ ℕ) : {n | IsNew m n}.Finite := by
  by_contra hinf
  obtain ⟨i, j, hij, hle⟩ := dickson (m ∘ Nat.nth (IsNew m))
  exact Nat.nth_mem_of_infinite hinf j _ (Nat.nth_strictMono hinf hij) hle

variable (K : Type*) [Field K]

omit [Finite σ] in
/-- [proved-standard; formal-checked] A monomial lies in the ideal of the earlier monomials when and
only when an earlier one divides it. -/
theorem monomial_mem_span_earlier_iff (m : ℕ → σ →₀ ℕ) (n : ℕ) :
    MvPolynomial.monomial (m n) (1 : K) ∈
        Ideal.span ((fun s => MvPolynomial.monomial s (1 : K)) '' (m '' Set.Iio n)) ↔
      ∃ i < n, m i ≤ m n := by
  classical
  rw [MvPolynomial.mem_ideal_span_monomial_image, MvPolynomial.support_monomial, if_neg one_ne_zero]
  simp

/-- [proved-standard; formal-checked] **Buchberger's halting**: in any sequence of leading monomials,
only finitely many lie outside the ideal of the earlier ones. -/
theorem buchberger_halts (m : ℕ → σ →₀ ℕ) :
    {n | MvPolynomial.monomial (m n) (1 : K) ∉
      Ideal.span ((fun s => MvPolynomial.monomial s (1 : K)) '' (m '' Set.Iio n))}.Finite := by
  refine (finite_isNew m).subset ?_
  intro n hn i hi hle
  exact hn ((monomial_mem_span_earlier_iff K m n).mpr ⟨i, hi, hle⟩)

/-- [proved-standard; formal-checked] From some index on, every leading monomial of the sequence lies
in the ideal of the earlier ones. -/
theorem buchberger_eventually_inside (m : ℕ → σ →₀ ℕ) : ∃ N, ∀ n ≥ N,
    MvPolynomial.monomial (m n) (1 : K) ∈
      Ideal.span ((fun s => MvPolynomial.monomial s (1 : K)) '' (m '' Set.Iio n)) := by
  obtain ⟨N, hN⟩ := (buchberger_halts K m).bddAbove
  refine ⟨N + 1, fun n hn => ?_⟩
  by_contra h
  have := hN h
  omega

/-- [proved-standard; formal-checked] No run of the loop adds, at every round, a leading monomial
outside the ideal of the earlier ones. -/
theorem no_infinite_buchberger_run (m : ℕ → σ →₀ ℕ) : ¬ ∀ n,
    MvPolynomial.monomial (m n) (1 : K) ∉
      Ideal.span ((fun s => MvPolynomial.monomial s (1 : K)) '' (m '' Set.Iio n)) := by
  intro h
  obtain ⟨N, hN⟩ := buchberger_eventually_inside K m
  exact h N (hN N le_rfl)

/-- [proved-standard; formal-checked] The chain of monomial ideals generated by the first `n` terms
of a sequence of monomials stabilizes. -/
theorem monomial_chain_stabilizes (m : ℕ → σ →₀ ℕ) : ∃ N, ∀ n ≥ N,
    Ideal.span ((fun s => MvPolynomial.monomial s (1 : K)) '' (m '' Set.Iio n)) =
      Ideal.span ((fun s => MvPolynomial.monomial s (1 : K)) '' (m '' Set.Iio N)) := by
  obtain ⟨N, hN⟩ := buchberger_eventually_inside K m
  refine ⟨N, fun n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have hset : Set.Iio (n + 1) = insert n (Set.Iio n) := by
      ext k
      simp only [Set.mem_Iio, Set.mem_insert_iff]
      omega
    rw [← ih, hset, Set.image_insert_eq, Set.image_insert_eq, Ideal.span_insert, sup_eq_right,
      Ideal.span_singleton_le_iff_mem]
    exact hN n hn

end Dickson

/-! ## 6. The dimension certificate of a point configuration -/

section Dimension

variable {σ K : Type*} [Field K]

/-- [proved-standard; formal-checked] Evaluating a polynomial in `x_i` alone reads the coordinate
`i`. -/
theorem eval_aeval_X (x : σ → K) (i : σ) (q : K[X]) :
    MvPolynomial.eval x (Polynomial.aeval (MvPolynomial.X i) q) = q.eval (x i) := by
  have := Polynomial.aeval_algHom_apply (MvPolynomial.aeval x : MvPolynomial σ K →ₐ[K] K)
    (MvPolynomial.X i) q
  rw [MvPolynomial.aeval_X, Polynomial.coe_aeval_eq_eval] at this
  rw [this]
  rfl

/-- [proved-standard; formal-checked] **The dimension certificate of a point configuration**: if
for every coordinate the identity ideal holds a nonzero polynomial in that coordinate alone, the
configuration is finite. -/
theorem finite_of_coordinate_certificates [Finite σ] (V : Set (σ → K))
    (h : ∀ i, ∃ q : K[X], q ≠ 0 ∧ Polynomial.aeval (MvPolynomial.X i) q ∈ identityIdeal V) :
    V.Finite := by
  choose q hq hmem using h
  refine (Set.Finite.pi fun i => finite_setOfPred_isRoot (hq i)).subset ?_
  intro x hx i _
  have := (mem_identityIdeal_iff V _).mp (hmem i) x hx
  rw [eval_aeval_X] at this
  exact this

/-- [proved-standard; formal-checked] A finite configuration has, in every coordinate, a nonzero
polynomial in that coordinate alone among its identities. -/
theorem coordinate_certificates_of_finite (V : Set (σ → K)) (hV : V.Finite) (i : σ) :
    ∃ q : K[X], q ≠ 0 ∧ Polynomial.aeval (MvPolynomial.X i) q ∈ identityIdeal V := by
  refine ⟨∏ x ∈ hV.toFinset, (X - C (x i)), ?_, ?_⟩
  · exact (monic_prod_of_monic _ _ fun x _ => monic_X_sub_C (x i)).ne_zero
  · rw [mem_identityIdeal_iff]
    intro x hx
    rw [eval_aeval_X, eval_prod]
    exact Finset.prod_eq_zero (hV.mem_toFinset.mpr hx) (by simp)

/-- [proved-standard; formal-checked] In finitely many variables, a configuration is finite when and
only when every coordinate has a nonzero one-variable identity. -/
theorem finite_iff_coordinate_certificates [Finite σ] (V : Set (σ → K)) :
    V.Finite ↔
      ∀ i, ∃ q : K[X], q ≠ 0 ∧ Polynomial.aeval (MvPolynomial.X i) q ∈ identityIdeal V :=
  ⟨coordinate_certificates_of_finite V, finite_of_coordinate_certificates V⟩

end Dimension

end Holonics.Compression.Landmark.ChartDensity
