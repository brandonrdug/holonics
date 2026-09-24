import Holonics.Foundation.CausalRelevance
import Holonics.Foundation.Standing
import Holonics.Geometry.ExteriorBoundary
import Holonics.Transport.WorldTube
import Holonics.Millennium.Ricci
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Relative completeness (the globe), first formal owner

[definition] Object 7 of `docs/ELEMENTARY_OBJECTS.md`. A region with boundary map
`β : state → boundary data` and a declared exterior receiver family `R` reading that boundary is
**relatively complete** for `R` when

1. **coupled** (`Region.Coupled`): two admitted states with one present boundary datum are
   separated by some admitted boundary future — the boundary datum depends on the interior state.
   This is the governing clause (coordinator ruling, 2026-09-22): coupling through a conserved
   charge counts, as in Birkhoff and Gauss, so `β` need not vary along the interior dynamics;
2. **not determined** (`Region.NotDetermined`): every admitted state's fibre of the boundary
   history — `Foundation/CausalRelevance.lean::futureAgreement` for the receivers `R ∘ β` — holds a
   second state whose difference moves **persistently** (`Region.PersistentMotion`): after every
   admitted word the difference still moves under some generator, and it recurs exactly (returns
   to itself after a nonempty word). A quenched or decaying fibre therefore fails;
3. **bounds** (`Membrane.BoundsInterior`): the declared membrane chain is the boundary of the
   region's declared interior chain, `∂Ω = S`. A bounding membrane is closed and carries zero net
   exact flux (`Membrane.Bounds.closed`, `Membrane.closed_iff_no_exact_flux`, composing
   `Geometry/ExteriorBoundary.lean::stokes_pairing`).

**Declared, not joined.** `β` is the second projection of `Interior × Boundary`, and the membrane
lives on a separate chain complex. Which cochain values or faces on `S` the boundary datum returns
is not formalized; clause (3) is a condition on the declared membrane only, and the membrane
witnesses below say nothing about the dynamics.

[definition; agent-inferred] Persistence is stated as exact recurrence of the fibre difference (a
discrete Poincaré recurrence). This excludes conservative but quasi-periodic interiors, e.g. the
irrational `3-4-5` rotation of `Foundation/Standing.lean`. Admitting them needs an approximate
recurrence against a declared metric, which is `[open]`.

[proved-derived; formal-checked]

* **Linear chart.** For additive regions (`Region.ofAdditive`), future agreement is membership of
  the difference in `CausalRelevance.futureCollapsed` (`ofAdditive_agree_iff`). With one generator,
  persistent motion of a difference `d` holds exactly when `Eⁿ d = d` for some `n > 0` and
  `E d ≠ d` (`ofAdditive_persistent_iff`).
* **Linear block criterion.** For the unit-clock Euler step `E = 1 + M` of
  `[x_int; x_bd]' = [[A,B],[C,D]] [x_int; x_bd]` read on `x_bd`, the future-blind population is
  exactly `{(u,0) | u ∈ ⋂ₖ ker (C Aᵏ)}` for every `B`, `D` (`mem_blockCollapsed_iff`). Hence:
  coupled ⇔ `C ≠ 0` (`block_coupled_iff`); not determined ⇔ some `u ∈ ⋂ₖ ker (C Aᵏ)` has
  `A u ≠ 0` and `(1 + A)ⁿ u = u` for some `n > 0` (`block_notDetermined_iff`). The kernel is the
  greatest `A`-invariant subspace of `ker C` (`observabilityKernel_greatest`). In finite dimension
  the horizon `finrank` suffices by Cayley–Hamilton (`observabilityKernel_eq_horizonKernel_finrank`).
  A nonzero world-tube interior current in the kernel is lawful silence for outward receiver `C`,
  and `C (Aᵏ current) = 0` for every `k` (`observabilityKernel_lawfulSilence`).
* **Receiver relativity.** Clause (2) is antitone and clause (1) monotone under receiver
  refinement (`Refines.notDetermined`, `Refines.coupled`). Clause (2) makes every admitted fibre
  nontrivial, so the receivers do not separate the region's states
  (`NotDetermined.fibre_nontrivial`).

[established-bounded; formal-checked] Positive instances over `ℚ`:

* the linear globe: a quarter-turning interior pair, with the exterior reading only a conserved
  mass (`linearGlobe_relativelyComplete`);
* the nonlinear Birkhoff globe: a quarter-turn read only through `Standing.planeEnergy`, separated
  across two admitted energies (`birkhoffGlobe_relativelyComplete`);
* the coarse half of `relativity_witness`.

[counterexample; formal-checked] Each of these refutes the claim that the listed region is
relatively complete:

* a cold lattice `A = 0`, and a quench `A = −1` (the Euler step sends the interior to zero), fail
  (2), although both are coupled with a nonzero fibre;
* the `Millennium/Ricci.lean` triangle flow read by its conserved total fails (2): its fibre is
  nonzero and moving, but it contracts at `1 − 3τ` (`theDeviationContractsAtTheWindingRate`);
* a fully observable interior fails (2), and a sealed interior `C = 0` fails (1);
* the lateral membrane of a strip with open ends fails (3), as does a hollow cycle that is closed
  but bounds nothing;
* the finer half of `relativity_witness`: one dynamics is relatively complete for the mass channel
  alone, and not once a second channel that reads the fibre is added.

[open] The relative completeness theorem of object 7 (a globe criterion from the Einstein lifts
paired with complex Euler/Navier–Stokes, with the bounding radius against dimension) is not
proved here. The band-limited relevance join is also open: `NavierStokesBandLimitedRelevance`
proves, at one band-limited time slice, zero transfer into the complement of the double cube
(`tsum_compl_transfer_eq_zero`) and exchange-free dissipation of the double-cube mass. Read with
band = interior and far tail = exterior, that is a *decoupling* statement at that instant, so
clause (1) fails there rather than holds. Relative completeness in the spectral chart would need
(i) a time-extended frontier current, since band limitation is a single-slice hypothesis the owner
does not propagate; (ii) a nonzero frontier transfer from the band into the chosen exterior shell;
and (iii) a fibre statement that the exterior shell readings do not determine the band modes, with
persistent motion in that fibre. No owner states (ii) or (iii).
-/

noncomputable section

namespace Holonics.Objects.RelativeCompleteness

open Holonics.Millennium.Chronology
open Holonics.Foundation.CausalRelevance
open Holonics.Foundation.CausalRelevance.NonLinear

/-! ## 1. Region, membrane and the three clauses -/

/-- [definition] Persistent motion of the difference of two states under a step family: after
every admitted word the difference still moves under some generator, and it recurs — some
nonempty word returns it exactly. -/
def PersistentMotion {Generator X : Type*} [AddCommGroup X] (step : Generator → X → X)
    (state other : X) : Prop :=
  (∀ word, ∃ generator,
      step generator (transportWord step word other) -
          step generator (transportWord step word state) ≠
        transportWord step word other - transportWord step word state) ∧
  (∀ word, ∃ word', word' ≠ [] ∧
      transportWord step (word' ++ word) other - transportWord step (word' ++ word) state =
        transportWord step word other - transportWord step word state)

/-- [definition] A region: a joint interior/boundary state moved by admitted generators, an
exterior receiver family reading the boundary datum only (`β = Prod.snd`), and the admitted
states. -/
structure Region (Generator Receiver Interior Boundary Face : Type*)
    [AddCommGroup Interior] [AddCommGroup Boundary] where
  step : Generator → Interior × Boundary → Interior × Boundary
  exterior : Receiver → Boundary → Face
  admitted : Set (Interior × Boundary)

namespace Region

variable {Generator Receiver Interior Boundary Face : Type*}
  [AddCommGroup Interior] [AddCommGroup Boundary]
  (Ω : Region Generator Receiver Interior Boundary Face)

/-- [definition] The exterior receiver composed with the boundary map `β = Prod.snd`. -/
def observe : Receiver → Interior × Boundary → Face := fun receiver state =>
  Ω.exterior receiver state.2

/-- [definition] Two states lie in one fibre of the boundary history: `futureAgreement` for the
exterior receivers after every admitted ordered word. -/
def Agree (left right : Interior × Boundary) : Prop :=
  futureAgreement Ω.observe Ω.step left right

/-- [definition] Clause (1): two admitted states with one boundary datum are separated by an
admitted boundary future — the boundary datum depends on the interior state. -/
def Coupled : Prop :=
  ∃ interior interior' boundary, (interior, boundary) ∈ Ω.admitted ∧
    (interior', boundary) ∈ Ω.admitted ∧ ¬ Ω.Agree (interior, boundary) (interior', boundary)

/-- [definition] Clause (2): every admitted state's boundary-history fibre holds a state whose
difference moves persistently. -/
def NotDetermined : Prop :=
  ∀ state ∈ Ω.admitted, ∃ other, Ω.Agree state other ∧ PersistentMotion Ω.step state other

/-- [proved-derived; formal-checked] The fibre over every admitted state is nontrivial: the
exterior receivers do not separate the region's states. -/
theorem NotDetermined.fibre_nontrivial {Ω : Region Generator Receiver Interior Boundary Face}
    (h : Ω.NotDetermined) :
    ∀ state ∈ Ω.admitted, ∃ other, other ≠ state ∧ Ω.Agree state other := by
  intro state hstate
  obtain ⟨other, hagree, hmove, _⟩ := h state hstate
  refine ⟨other, ?_, hagree⟩
  rintro rfl
  obtain ⟨generator, hne⟩ := hmove []
  simp at hne

/-- [definition] Receiver refinement: the same dynamics and admitted states, and every coarse
receiver face is a function of some fine receiver face. -/
structure Refines {Receiver' Face' : Type*}
    (fine : Region Generator Receiver' Interior Boundary Face')
    (coarse : Region Generator Receiver Interior Boundary Face) : Prop where
  step_eq : fine.step = coarse.step
  admitted_eq : fine.admitted = coarse.admitted
  realizes : ∀ receiver, ∃ (receiver' : Receiver') (read : Face' → Face),
    ∀ boundary, read (fine.exterior receiver' boundary) = coarse.exterior receiver boundary

variable {Receiver' Face' : Type*}

/-- [proved-derived; formal-checked] Agreement for a finer family implies agreement for the
coarser one. -/
theorem Refines.agree {fine : Region Generator Receiver' Interior Boundary Face'}
    {coarse : Region Generator Receiver Interior Boundary Face} (h : fine.Refines coarse)
    {left right : Interior × Boundary} (hagree : fine.Agree left right) :
    coarse.Agree left right := by
  intro receiver word
  obtain ⟨receiver', read, hread⟩ := h.realizes receiver
  have hfine := hagree receiver' word
  simp only [observe] at hfine ⊢
  rw [← hread, ← hread, ← h.step_eq, hfine]

/-- [proved-derived; formal-checked] Refining the receivers can only remove clause (2). -/
theorem Refines.notDetermined {fine : Region Generator Receiver' Interior Boundary Face'}
    {coarse : Region Generator Receiver Interior Boundary Face} (h : fine.Refines coarse)
    (hfine : fine.NotDetermined) : coarse.NotDetermined := by
  intro state hstate
  rw [← h.admitted_eq] at hstate
  obtain ⟨other, hagree, hpersist⟩ := hfine state hstate
  exact ⟨other, h.agree hagree, by rwa [← h.step_eq]⟩

/-- [proved-derived; formal-checked] Refining the receivers can only add clause (1). -/
theorem Refines.coupled {fine : Region Generator Receiver' Interior Boundary Face'}
    {coarse : Region Generator Receiver Interior Boundary Face} (h : fine.Refines coarse)
    (hcoarse : coarse.Coupled) : fine.Coupled := by
  obtain ⟨interior, interior', boundary, hleft, hright, hsep⟩ := hcoarse
  rw [← h.admitted_eq] at hleft hright
  exact ⟨interior, interior', boundary, hleft, hright, fun hagree => hsep (h.agree hagree)⟩

end Region

/-- [definition] A declared membrane on three consecutive grades of a chain complex, with the
region's declared interior chain. -/
structure Membrane (K C₀ C₁ C₂ : Type*) [Field K]
    [AddCommGroup C₀] [Module K C₀] [AddCommGroup C₁] [Module K C₁]
    [AddCommGroup C₂] [Module K C₂] where
  boundary₁ : C₁ →ₗ[K] C₀
  boundary₂ : C₂ →ₗ[K] C₁
  boundary_squared : boundary₁.comp boundary₂ = 0
  interiorChain : C₂
  surface : C₁

namespace Membrane

variable {K C₀ C₁ C₂ : Type*} [Field K]
  [AddCommGroup C₀] [Module K C₀] [AddCommGroup C₁] [Module K C₁]
  [AddCommGroup C₂] [Module K C₂] (S : Membrane K C₀ C₁ C₂)

/-- [definition] Clause (3): the membrane is the boundary of the region's interior chain. -/
def BoundsInterior : Prop := S.boundary₂ S.interiorChain = S.surface

/-- [definition] The membrane bounds some chain of the next grade. -/
def Bounds : Prop := ∃ region, S.boundary₂ region = S.surface

/-- [definition] The membrane is a cycle. -/
def Closed : Prop := S.boundary₁ S.surface = 0

theorem BoundsInterior.bounds {S : Membrane K C₀ C₁ C₂} (h : S.BoundsInterior) : S.Bounds :=
  ⟨S.interiorChain, h⟩

/-- [proved-derived; formal-checked] A bounding membrane is closed (`∂∂ = 0`). -/
theorem Bounds.closed {S : Membrane K C₀ C₁ C₂} (h : S.Bounds) : S.Closed := by
  obtain ⟨region, hregion⟩ := h
  unfold Closed
  rw [← hregion]
  exact LinearMap.congr_fun S.boundary_squared region

/-- [proved-derived; formal-checked] **Closed ⇔ no exact flux escapes.** Composing
`ExteriorBoundary.stokes_pairing`: the membrane is closed exactly when every exact coholon
`dφ` pairs to zero with it. -/
theorem closed_iff_no_exact_flux :
    S.Closed ↔ ∀ potential : Module.Dual K C₀, S.boundary₁.dualMap potential S.surface = 0 := by
  simp only [Holonics.Geometry.ExteriorBoundary.stokes_pairing]
  exact (Module.forall_dual_apply_eq_zero_iff K _).symm

end Membrane

/-- [definition] **Relative completeness** of a region for its exterior receiver family, over a
declared membrane that bounds the region's declared interior chain. -/
structure RelativelyComplete {Generator Receiver Interior Boundary Face K C₀ C₁ C₂ : Type*}
    [AddCommGroup Interior] [AddCommGroup Boundary] [Field K]
    [AddCommGroup C₀] [Module K C₀] [AddCommGroup C₁] [Module K C₁]
    [AddCommGroup C₂] [Module K C₂]
    (Ω : Region Generator Receiver Interior Boundary Face) (S : Membrane K C₀ C₁ C₂) : Prop where
  coupled : Ω.Coupled
  notDetermined : Ω.NotDetermined
  bounds : S.BoundsInterior

/-! ## 2. The linear chart: fibres are cosets of the future-blind population -/

universe u

section Additive

variable {G R I Bd V : Type u} [AddCommGroup I] [AddCommGroup Bd] [AddCommGroup V]

/-- [definition] A region whose generators and receivers are additive. -/
def Region.ofAdditive (transport : G → (I × Bd →+ I × Bd)) (read : R → (Bd →+ V))
    (admitted : Set (I × Bd)) : Region G R I Bd V where
  step generator state := transport generator state
  exterior receiver boundary := read receiver boundary
  admitted := admitted
/-- [definition] The exterior receivers composed with `β = Prod.snd`, as additive maps. -/
def outwardRead (read : R → (Bd →+ V)) : R → (I × Bd →+ V) := fun receiver =>
  (read receiver).comp (AddMonoidHom.snd I Bd)

theorem transportWord_sub (transport : G → (I × Bd →+ I × Bd)) (word : List G)
    (left right : I × Bd) :
    transportWord (fun generator state => transport generator state) word (right - left) =
      transportWord (fun generator state => transport generator state) word right -
        transportWord (fun generator state => transport generator state) word left := by
  induction word with
  | nil => rfl
  | cons generator word ih => simp only [transportWord_cons, ih, map_sub]

/-- [proved-derived; formal-checked] In the additive chart the boundary-history fibre of a state
is its coset of `CausalRelevance.futureCollapsed`. -/
theorem ofAdditive_agree_iff (transport : G → (I × Bd →+ I × Bd)) (read : R → (Bd →+ V))
    (admitted : Set (I × Bd)) (left right : I × Bd) :
    (Region.ofAdditive transport read admitted).Agree left right ↔
      right - left ∈ futureCollapsed (outwardRead read) transport := by
  rw [mem_futureCollapsed_iff]
  simp only [Region.Agree, futureAgreement, Region.observe, Region.ofAdditive, outwardRead,
    AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_snd, transportWord_sub,
    map_sub]
  constructor
  · intro h receiver word
    rw [h receiver word, sub_self]
  · intro h receiver word
    exact (sub_eq_zero.mp (h receiver word)).symm


/-- [proved-derived; formal-checked] Iterates of an additive map carry differences. -/
theorem iterate_sub (E : I × Bd →+ I × Bd) (n : ℕ) (a b : I × Bd) :
    (⇑E)^[n] a - (⇑E)^[n] b = (⇑E)^[n] (a - b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ← ih, map_sub]

theorem ofAdditive_word (E : I × Bd →+ I × Bd) (read : R → (Bd →+ V))
    (admitted : Set (I × Bd)) (word : List PUnit.{u + 1}) (z : I × Bd) :
    transportWord (Region.ofAdditive (fun _ : PUnit.{u + 1} => E) read admitted).step word z =
      (⇑E)^[word.length] z := by
  induction word with
  | nil => rfl
  | cons g word ih =>
    rw [transportWord_cons, ih, List.length_cons, Function.iterate_succ_apply']
    rfl

/-- [proved-derived; formal-checked] A recurrent point that moves at the start moves after every
number of steps: it never reaches a fixed point. -/
theorem periodic_moves_forever {X : Type*} (f : X → X) (d : X) {n : ℕ} (hn : 0 < n)
    (hper : f^[n] d = d) (hmove : f d ≠ d) (k : ℕ) : f (f^[k] d) ≠ f^[k] d := by
  intro hfix
  have hall : ∀ j, f^[j] (f^[k] d) = f^[k] d := Function.iterate_fixed hfix
  have hm : f^[n * (k + 1)] d = d := by
    rw [Function.iterate_mul]; exact Function.iterate_fixed hper _
  have hk : k ≤ n * (k + 1) := by nlinarith
  have hd : f^[k] d = d := by
    calc f^[k] d = f^[n * (k + 1) - k] (f^[k] d) := (hall _).symm
      _ = f^[n * (k + 1)] d := by rw [← Function.iterate_add_apply, Nat.sub_add_cancel hk]
      _ = d := hm
  rw [hd] at hfix
  exact hmove hfix

/-- [proved-derived; formal-checked] **Persistent motion in a one-generator additive region**
holds exactly when the difference `d` is periodic, `Eⁿ d = d` with `n > 0`, and moves, `E d ≠ d`. -/
theorem ofAdditive_persistent_iff (E : I × Bd →+ I × Bd) (read : R → (Bd →+ V))
    (admitted : Set (I × Bd)) (state other : I × Bd) :
    PersistentMotion (Region.ofAdditive (fun _ : PUnit.{u + 1} => E) read admitted).step
        state other ↔
      ∃ n, 0 < n ∧ (⇑E)^[n] (other - state) = other - state ∧
        E (other - state) ≠ other - state := by
  have hstep : ∀ g z,
      (Region.ofAdditive (fun _ : PUnit.{u + 1} => E) read admitted).step g z = E z :=
    fun _ _ => rfl
  have hdiff : ∀ word : List PUnit.{u + 1},
      transportWord (Region.ofAdditive (fun _ : PUnit.{u + 1} => E) read admitted).step word
          other -
        transportWord (Region.ofAdditive (fun _ : PUnit.{u + 1} => E) read admitted).step word
          state = (⇑E)^[word.length] (other - state) := by
    intro word
    rw [ofAdditive_word, ofAdditive_word, iterate_sub]
  constructor
  · rintro ⟨hmove, hrec⟩
    obtain ⟨w', hw', heq⟩ := hrec []
    obtain ⟨g, hm⟩ := hmove []
    rw [hdiff, hdiff, List.append_nil] at heq
    refine ⟨w'.length, List.length_pos_iff.mpr hw', heq, ?_⟩
    rw [transportWord_nil, transportWord_nil, hstep, hstep, ← map_sub] at hm
    exact hm
  · rintro ⟨n, hn, hper, hmove⟩
    refine ⟨fun word => ⟨PUnit.unit, ?_⟩, fun word => ⟨List.replicate n PUnit.unit, ?_, ?_⟩⟩
    · rw [hstep, hstep, ← map_sub, hdiff]
      exact periodic_moves_forever E (other - state) hn hper hmove _
    · simpa using hn.ne'
    · rw [hdiff, hdiff, List.length_append, List.length_replicate, add_comm,
        Function.iterate_add_apply, hper]

end Additive

/-! ## 3. The linear block criterion -/

section Block

variable {K : Type*} [Field K] {I Bd : Type u}
  [AddCommGroup I] [Module K I] [AddCommGroup Bd] [Module K Bd]

/-- [definition] The block velocity `[[A,B],[C,D]]` on `x_int × x_bd`. -/
def blockVelocity (A : I →ₗ[K] I) (B : Bd →ₗ[K] I) (C : I →ₗ[K] Bd) (D : Bd →ₗ[K] Bd) :
    I × Bd →ₗ[K] I × Bd :=
  (A.coprod B).prod (C.coprod D)

@[simp] theorem blockVelocity_apply (A : I →ₗ[K] I) (B : Bd →ₗ[K] I) (C : I →ₗ[K] Bd)
    (D : Bd →ₗ[K] Bd) (state : I × Bd) :
    blockVelocity A B C D state = (A state.1 + B state.2, C state.1 + D state.2) := rfl

/-- [definition] The unit-clock Euler step `1 + M` of the block velocity. -/
def blockStep (A : I →ₗ[K] I) (B : Bd →ₗ[K] I) (C : I →ₗ[K] Bd) (D : Bd →ₗ[K] Bd) :
    I × Bd →+ I × Bd :=
  (LinearMap.id + blockVelocity A B C D).toAddMonoidHom

theorem blockStep_apply (A : I →ₗ[K] I) (B : Bd →ₗ[K] I) (C : I →ₗ[K] Bd) (D : Bd →ₗ[K] Bd)
    (state : I × Bd) : blockStep A B C D state = state + blockVelocity A B C D state := rfl

/-- [definition] The block region read on the full boundary datum. -/
def blockRegion (A : I →ₗ[K] I) (B : Bd →ₗ[K] I) (C : I →ₗ[K] Bd) (D : Bd →ₗ[K] Bd) :
    Region PUnit.{u + 1} PUnit.{u + 1} I Bd Bd :=
  Region.ofAdditive (fun _ => blockStep A B C D) (fun _ => AddMonoidHom.id Bd) Set.univ

/-- [definition] The unobservable subspace `⋂ₖ ker (C Aᵏ)` of `(A, C)`. -/
def observabilityKernel (A : I →ₗ[K] I) (C : I →ₗ[K] Bd) : Submodule K I :=
  ⨅ k : ℕ, LinearMap.ker (C ∘ₗ A ^ k)

/-- [definition] The finite-horizon kernel `⋂_{k<N} ker (C Aᵏ)`. -/
def horizonKernel (A : I →ₗ[K] I) (C : I →ₗ[K] Bd) (N : ℕ) : Submodule K I :=
  ⨅ (k : ℕ) (_ : k < N), LinearMap.ker (C ∘ₗ A ^ k)

theorem mem_observabilityKernel_iff (A : I →ₗ[K] I) (C : I →ₗ[K] Bd) (v : I) :
    v ∈ observabilityKernel A C ↔ ∀ k : ℕ, C ((A ^ k) v) = 0 := by
  simp [observabilityKernel, Submodule.mem_iInf]

theorem mem_horizonKernel_iff (A : I →ₗ[K] I) (C : I →ₗ[K] Bd) (N : ℕ) (v : I) :
    v ∈ horizonKernel A C N ↔ ∀ k < N, C ((A ^ k) v) = 0 := by
  simp [horizonKernel, Submodule.mem_iInf]

/-- [proved-derived; formal-checked] The unobservable subspace is `A`-invariant. -/
theorem observabilityKernel_invariant (A : I →ₗ[K] I) (C : I →ₗ[K] Bd) {v : I}
    (hv : v ∈ observabilityKernel A C) : A v ∈ observabilityKernel A C := by
  rw [mem_observabilityKernel_iff] at hv ⊢
  intro k
  have := hv (k + 1)
  rwa [pow_succ, Module.End.mul_apply] at this

theorem observabilityKernel_le_ker (A : I →ₗ[K] I) (C : I →ₗ[K] Bd) :
    observabilityKernel A C ≤ LinearMap.ker C := by
  intro v hv
  simpa using (mem_observabilityKernel_iff A C v).mp hv 0

/-- [proved-derived; formal-checked] It is the greatest `A`-invariant subspace of `ker C`: the
part of the outward radical that stays silent after every admitted history. -/
theorem observabilityKernel_greatest (A : I →ₗ[K] I) (C : I →ₗ[K] Bd) (p : Submodule K I)
    (hker : p ≤ LinearMap.ker C) (hinv : ∀ v ∈ p, A v ∈ p) :
    p ≤ observabilityKernel A C := by
  intro v hv
  rw [mem_observabilityKernel_iff]
  intro k
  have hpow : (A ^ k) v ∈ p := by
    induction k with
    | zero => simpa using hv
    | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact hinv _ ih
  exact hker hpow

/-- [proved-derived; formal-checked] **The future-blind population of the block region is exactly
`{(u, 0) | u ∈ ⋂ₖ ker (C Aᵏ)}`**, independently of `B` and `D`. Composes
`CausalRelevance.mem_futureCollapsed_iff` and `futureCollapsed_invariant`. -/
theorem mem_blockCollapsed_iff (A : I →ₗ[K] I) (B : Bd →ₗ[K] I) (C : I →ₗ[K] Bd)
    (D : Bd →ₗ[K] Bd) (state : I × Bd) :
    state ∈ futureCollapsed (outwardRead (I := I) (fun _ : PUnit.{u + 1} => AddMonoidHom.id Bd))
        (fun _ : PUnit.{u + 1} => blockStep A B C D) ↔
      state.2 = 0 ∧ state.1 ∈ observabilityKernel A C := by
  set F := futureCollapsed (outwardRead (I := I) (fun _ : PUnit.{u + 1} => AddMonoidHom.id Bd))
    (fun _ : PUnit.{u + 1} => blockStep A B C D) with hF
  have blind : ∀ z ∈ F, z.2 = 0 := by
    intro z hz
    have := (mem_futureCollapsed_iff _ _ z).mp hz PUnit.unit []
    simpa [outwardRead] using this
  constructor
  · intro hstate
    have hzero := blind state hstate
    -- the interior population carried with zero boundary datum
    have key : ∀ k : ℕ, ∀ v : I, ((v, (0 : Bd)) ∈ F) → C ((A ^ k) v) = 0 := by
      intro k
      induction k with
      | zero =>
        intro v hv
        have hstep := futureCollapsed_invariant _ _ PUnit.unit hv
        have := blind _ hstep
        simpa [blockStep_apply] using this
      | succ k ih =>
        intro v hv
        have hstep := futureCollapsed_invariant _ _ PUnit.unit hv
        have hC : C v = 0 := by simpa [blockStep_apply] using blind _ hstep
        have hmove : ((A v, (0 : Bd)) : I × Bd) ∈ F := by
          have := F.sub_mem hstep hv
          convert this using 1
          simp [blockStep_apply, hC]
        rw [pow_succ, Module.End.mul_apply]
        exact ih (A v) hmove
    refine ⟨hzero, (mem_observabilityKernel_iff A C _).mpr fun k => key k state.1 ?_⟩
    have : state = (state.1, 0) := Prod.ext rfl hzero
    rw [← this]; exact hstate
  · rintro ⟨hzero, hobs⟩
    rw [mem_futureCollapsed_iff]
    intro _ word
    have carried : ∀ word : List PUnit.{u + 1},
        (transportWord (fun g z => (fun _ : PUnit.{u + 1} => blockStep A B C D) g z) word
          state).2 = 0 ∧
        (transportWord (fun g z => (fun _ : PUnit.{u + 1} => blockStep A B C D) g z) word
          state).1 ∈ observabilityKernel A C := by
      intro word
      induction word with
      | nil => exact ⟨hzero, hobs⟩
      | cons g word ih =>
        rw [transportWord_cons]
        generalize transportWord _ word state = s at ih ⊢
        obtain ⟨h2, h1⟩ := ih
        have hC : C s.1 = 0 := observabilityKernel_le_ker A C h1
        rw [blockStep_apply, blockVelocity_apply]
        refine ⟨?_, ?_⟩
        · simp [h2, hC]
        · simp only [Prod.fst_add, h2, map_zero, add_zero]
          exact (observabilityKernel A C).add_mem h1 (observabilityKernel_invariant A C h1)
    simpa [outwardRead] using (carried word).1

/-- [proved-derived; formal-checked] The fibre of the block region: same boundary datum and
interior difference in `⋂ₖ ker (C Aᵏ)`. -/
theorem block_agree_iff (A : I →ₗ[K] I) (B : Bd →ₗ[K] I) (C : I →ₗ[K] Bd) (D : Bd →ₗ[K] Bd)
    (left right : I × Bd) :
    (blockRegion A B C D).Agree left right ↔
      right.2 = left.2 ∧ right.1 - left.1 ∈ observabilityKernel A C := by
  rw [blockRegion, ofAdditive_agree_iff, mem_blockCollapsed_iff]
  simp [sub_eq_zero]

theorem observabilityKernel_eq_top_iff (A : I →ₗ[K] I) (C : I →ₗ[K] Bd) :
    observabilityKernel A C = ⊤ ↔ C = 0 := by
  constructor
  · intro h
    ext v
    have hv : v ∈ observabilityKernel A C := h ▸ Submodule.mem_top
    simpa using (mem_observabilityKernel_iff A C v).mp hv 0
  · rintro rfl
    ext v
    simp [mem_observabilityKernel_iff]

theorem one_add_apply (A : I →ₗ[K] I) (u : I) : (1 + A) u = u + A u := rfl

theorem one_add_pow_mem (A : I →ₗ[K] I) (C : I →ₗ[K] Bd) {u : I}
    (hu : u ∈ observabilityKernel A C) (k : ℕ) :
    ((1 + A) ^ k) u ∈ observabilityKernel A C := by
  induction k with
  | zero => simpa using hu
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, one_add_apply]
    exact add_mem ih (observabilityKernel_invariant A C ih)

theorem blockStep_kernel (A : I →ₗ[K] I) (B : Bd →ₗ[K] I) (C : I →ₗ[K] Bd) (D : Bd →ₗ[K] Bd)
    {u : I} (hu : u ∈ observabilityKernel A C) :
    blockStep A B C D (u, 0) = ((1 + A) u, 0) := by
  have hC : C u = 0 := observabilityKernel_le_ker A C hu
  rw [blockStep_apply, blockVelocity_apply, one_add_apply]
  ext <;> simp [hC]

/-- [proved-derived; formal-checked] On the unobservable subspace the block step is `1 + A`. -/
theorem blockStep_iterate_kernel (A : I →ₗ[K] I) (B : Bd →ₗ[K] I) (C : I →ₗ[K] Bd)
    (D : Bd →ₗ[K] Bd) {u : I} (hu : u ∈ observabilityKernel A C) (k : ℕ) :
    (⇑(blockStep A B C D))^[k] (u, 0) = (((1 + A) ^ k) u, 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, blockStep_kernel A B C D (one_add_pow_mem A C hu k),
      pow_succ', Module.End.mul_apply]

/-- [proved-derived; formal-checked] **Clause (1) for the block region: coupled ⇔ `C ≠ 0`.** -/
theorem block_coupled_iff (A : I →ₗ[K] I) (B : Bd →ₗ[K] I) (C : I →ₗ[K] Bd) (D : Bd →ₗ[K] Bd) :
    (blockRegion A B C D).Coupled ↔ C ≠ 0 := by
  rw [← not_iff_not, not_not, ← observabilityKernel_eq_top_iff A C]
  constructor
  · intro h
    rw [eq_top_iff]
    intro v _
    by_contra hv
    apply h
    refine ⟨0, v, 0, trivial, trivial, ?_⟩
    rw [block_agree_iff]
    simpa using hv
  · rintro htop ⟨interior, interior', boundary, _, _, hsep⟩
    apply hsep
    rw [block_agree_iff]
    exact ⟨rfl, htop ▸ Submodule.mem_top⟩

/-- [proved-derived; formal-checked] **Clause (2) for the block region.** Not determined ⇔ some
`u` in the unobservable subspace of `(A,C)` moves, `A u ≠ 0`, and recurs, `(1 + A)ⁿ u = u` for
some `n > 0`. A quench (`1 + A` nilpotent on `u`) and a strict contraction fail the recurrence. -/
theorem block_notDetermined_iff (A : I →ₗ[K] I) (B : Bd →ₗ[K] I) (C : I →ₗ[K] Bd)
    (D : Bd →ₗ[K] Bd) :
    (blockRegion A B C D).NotDetermined ↔
      ∃ u ∈ observabilityKernel A C, A u ≠ 0 ∧ ∃ n, 0 < n ∧ ((1 + A) ^ n) u = u := by
  have key : ∀ state other : I × Bd, other.2 = state.2 →
      other.1 - state.1 ∈ observabilityKernel A C →
      (PersistentMotion (blockRegion A B C D).step state other ↔
        A (other.1 - state.1) ≠ 0 ∧
          ∃ n, 0 < n ∧ ((1 + A) ^ n) (other.1 - state.1) = other.1 - state.1) := by
    intro state other h2 h1
    have hd : other - state = (other.1 - state.1, 0) := Prod.ext rfl (by simp [h2])
    unfold blockRegion
    rw [ofAdditive_persistent_iff, hd, blockStep_kernel A B C D h1]
    simp only [blockStep_iterate_kernel A B C D h1, Prod.mk.injEq, and_true, one_add_apply]
    constructor
    · rintro ⟨n, hn, hper, hmove⟩
      refine ⟨fun hA => hmove (by rw [hA, add_zero]), n, hn, hper⟩
    · rintro ⟨hA, n, hn, hper⟩
      exact ⟨n, hn, hper, fun h => hA (by simpa using h)⟩
  constructor
  · intro h
    obtain ⟨other, hagree, hpersist⟩ := h 0 trivial
    rw [block_agree_iff] at hagree
    have := (key 0 other hagree.1 hagree.2).mp hpersist
    simp only [Prod.fst_zero, sub_zero] at this hagree
    exact ⟨other.1, hagree.2, this⟩
  · rintro ⟨u, hu, hA, hper⟩ state _
    refine ⟨state + (u, 0), ?_, ?_⟩
    · rw [block_agree_iff]; simpa using hu
    · rw [key state (state + (u, 0)) (by simp) (by simpa using hu)]
      simpa using ⟨hA, hper⟩

/-- [proved-derived; formal-checked] **Finite horizon suffices.** In finite dimension the
unobservable subspace is the horizon-`finrank` kernel (Cayley–Hamilton,
`LinearMap.pow_eq_aeval_mod_charpoly`). -/
theorem observabilityKernel_eq_horizonKernel_finrank [FiniteDimensional K I]
    (A : I →ₗ[K] I) (C : I →ₗ[K] Bd) :
    observabilityKernel A C = horizonKernel A C (Module.finrank K I) := by
  apply le_antisymm
  · intro v hv
    rw [mem_horizonKernel_iff]
    intro k _
    exact (mem_observabilityKernel_iff A C v).mp hv k
  · intro v hv
    rw [mem_horizonKernel_iff] at hv
    rw [mem_observabilityKernel_iff]
    intro k
    set r := Polynomial.X ^ k %ₘ A.charpoly
    have hdeg : r.degree < (Module.finrank K I : WithBot ℕ) := by
      have h := Polynomial.degree_modByMonic_lt (Polynomial.X ^ k) (LinearMap.charpoly_monic A)
      rwa [Polynomial.degree_eq_natDegree (LinearMap.charpoly_monic A).ne_zero,
        LinearMap.charpoly_natDegree] at h
    rw [LinearMap.pow_eq_aeval_mod_charpoly, Polynomial.aeval_eq_sum_range,
      LinearMap.sum_apply, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [LinearMap.smul_apply, map_smul]
    by_cases hi : i < Module.finrank K I
    · rw [hv i hi, smul_zero]
    · have : r.coeff i = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        exact lt_of_lt_of_le hdeg (by exact_mod_cast not_lt.mp hi)
      rw [this, zero_smul]

open Holonics.Millennium.HolonicSensoryWorldTube in
/-- [proved-derived; formal-checked] **Join to `WorldTube`.** When a world tube's outward receiver
is `C`, a nonzero interior current in the unobservable subspace is lawful silence
(`WorldTube.IsLawfulSilence`), and `C` also vanishes on its image under every `Aᵏ`. Only
`C (Aᵏ current) = 0` is proved for those images; the images are not shown to be nonzero
occurrences of the tube. -/
theorem observabilityKernel_lawfulSilence
    {ExteriorBoundary InteriorBoundary ClockFace Face Obstruction Occurrence World Morphology
      Generator Receiver Quotient ReceiverFace : Type*} [AddCommGroup Morphology]
    (tube : WorldTube ExteriorBoundary InteriorBoundary ClockFace Face Obstruction Occurrence
      I Bd World Morphology Generator Receiver Quotient ReceiverFace)
    (A : I →ₗ[K] I) (C : I →ₗ[K] Bd) (houtward : tube.outward = C.toAddMonoidHom)
    (occurrence : Occurrence) (hne : tube.interiorCurrent occurrence ≠ 0)
    (hobs : tube.interiorCurrent occurrence ∈ observabilityKernel A C) (k : ℕ) :
    tube.IsLawfulSilence occurrence ∧ C ((A ^ k) (tube.interiorCurrent occurrence)) = 0 := by
  refine ⟨⟨hne, ?_⟩, (mem_observabilityKernel_iff A C _).mp hobs k⟩
  change tube.outward (tube.interiorCurrent occurrence) = 0
  rw [houtward]
  exact observabilityKernel_le_ker A C hobs

end Block

/-! ## 4. Concrete instances over `ℚ` -/

section Witnesses

/-- The interior `(x, y, m)`: a turning pair and a mass. -/
abbrev Interior3 : Type := ℚ × ℚ × ℚ

/-- [definition] The generator whose unit-clock step `1 + A` is the quarter turn
`(x, y, m) ↦ (-y, x, m)`. -/
def quarterA : Interior3 →ₗ[ℚ] Interior3 where
  toFun v := (-v.1 - v.2.1, v.1 - v.2.1, 0)
  map_add' a b := by ext <;> simp only [Prod.fst_add, Prod.snd_add, add_zero] <;> ring
  map_smul' c a := by ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    RingHom.id_apply, mul_zero] <;> ring

theorem quarter_step (v : Interior3) : (1 + quarterA) v = (-v.2.1, v.1, v.2.2) := by
  rw [one_add_apply]
  ext <;> (simp [quarterA]; try ring)

theorem quarter_pow_four (v : Interior3) :
    ((1 + quarterA : Module.End ℚ Interior3) ^ 4) v = v := by
  rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_add, pow_add, pow_add, pow_one]
  simp only [Module.End.mul_apply, quarter_step, neg_neg]

/-- [definition] The mass receiver `(x, y, m) ↦ m`. -/
def massC : Interior3 →ₗ[ℚ] ℚ where
  toFun v := v.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem quarterA_pow_succ_mass (k : ℕ) (v : Interior3) : ((quarterA ^ (k + 1)) v).2.2 = 0 := by
  rw [pow_succ', Module.End.mul_apply]; rfl

theorem mass_observabilityKernel_iff (v : Interior3) :
    v ∈ observabilityKernel quarterA massC ↔ v.2.2 = 0 := by
  rw [mem_observabilityKernel_iff]
  constructor
  · intro h; simpa [massC] using h 0
  · intro h k
    cases k with
    | zero => simpa [massC] using h
    | succ k => exact quarterA_pow_succ_mass k v

theorem massC_ne_zero : massC ≠ 0 := by
  intro h
  have := LinearMap.congr_fun h ((0, 0, 1) : Interior3)
  simp [massC] at this

/-- [definition] The linear globe: the interior pair turns by a quarter each tick; the boundary
reads only the conserved mass. -/
def linearGlobe : Region PUnit PUnit Interior3 ℚ ℚ :=
  blockRegion quarterA 0 massC 0

/-! ### The square complex: one face, four edges, four vertices -/

/-- [definition] Edge boundary of the unit square: `e₀ : v₀→v₁`, `e₁ : v₁→v₂`, `e₂ : v₃→v₂`,
`e₃ : v₀→v₃`, with `∂e = target − source`. -/
def squareBoundary₁ : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) :=
  Matrix.mulVecLin !![-1, 0, 0, -1; 1, -1, 0, 0; 0, 1, 1, 0; 0, 0, -1, 1]

/-- [definition] Face boundary: `∂f = e₀ + e₁ − e₂ − e₃`. -/
def squareBoundary₂ : ℚ →ₗ[ℚ] (Fin 4 → ℚ) :=
  LinearMap.smulRight LinearMap.id ![1, 1, -1, -1]

theorem square_boundary_squared : squareBoundary₁.comp squareBoundary₂ = 0 := by
  apply LinearMap.ext
  intro c
  funext i
  fin_cases i <;>
    simp [squareBoundary₁, squareBoundary₂, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- [definition] The globe membrane: the whole boundary of the face, with the face as the
region's interior chain. -/
def globeMembrane : Membrane ℚ (Fin 4 → ℚ) (Fin 4 → ℚ) ℚ where
  boundary₁ := squareBoundary₁
  boundary₂ := squareBoundary₂
  boundary_squared := square_boundary_squared
  interiorChain := 1
  surface := ![1, 1, -1, -1]

/-- [definition] The tube membrane: the lateral sides `e₀ − e₂` of a strip whose longitudinal
ends `e₁`, `e₃` are open. -/
def tubeMembrane : Membrane ℚ (Fin 4 → ℚ) (Fin 4 → ℚ) ℚ where
  boundary₁ := squareBoundary₁
  boundary₂ := squareBoundary₂
  boundary_squared := square_boundary_squared
  interiorChain := 1
  surface := ![1, 0, -1, 0]

/-- [definition] The hollow membrane: the same edge loop on the complex with no face. -/
def hollowMembrane : Membrane ℚ (Fin 4 → ℚ) (Fin 4 → ℚ) ℚ where
  boundary₁ := squareBoundary₁
  boundary₂ := 0
  boundary_squared := by simp
  interiorChain := 0
  surface := ![1, 1, -1, -1]

/-- [established-bounded; formal-checked] The globe membrane bounds its interior chain. -/
theorem globeMembrane_boundsInterior : globeMembrane.BoundsInterior := by
  funext i; fin_cases i <;> simp [globeMembrane, squareBoundary₂]

/-- [counterexample; formal-checked] **The tube fails (3)**: the potential of vertex `v₁` has
nonzero exact flux through the lateral membrane, so it is not closed and bounds nothing. -/
theorem tubeMembrane_escapes :
    tubeMembrane.boundary₁.dualMap (LinearMap.proj 1) tubeMembrane.surface = 1 ∧
      ¬ tubeMembrane.Bounds := by
  have h : tubeMembrane.boundary₁.dualMap (LinearMap.proj 1) tubeMembrane.surface = 1 := by
    simp [tubeMembrane, squareBoundary₁]
  refine ⟨h, fun hbounds => ?_⟩
  have := (tubeMembrane.closed_iff_no_exact_flux.mp hbounds.closed) (LinearMap.proj 1)
  rw [h] at this
  norm_num at this

/-- [counterexample; formal-checked] **A hollow cycle fails (3)**: the edge loop is closed but, on
the complex without its face, it bounds nothing. -/
theorem hollowMembrane_closed_not_bounds : hollowMembrane.Closed ∧ ¬ hollowMembrane.Bounds := by
  constructor
  · funext i
    fin_cases i <;>
      simp [hollowMembrane, squareBoundary₁, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four]
  · rintro ⟨region, hregion⟩
    have := congrFun hregion 0
    simp [hollowMembrane] at this

/-- [established-bounded; formal-checked] **The linear globe is relatively complete**: coupled
through the conserved mass, with the interior pair turning persistently in the fibre. -/
theorem linearGlobe_relativelyComplete : RelativelyComplete linearGlobe globeMembrane := by
  refine ⟨?_, ?_, globeMembrane_boundsInterior⟩
  · rw [linearGlobe, block_coupled_iff]; exact massC_ne_zero
  · rw [linearGlobe, block_notDetermined_iff]
    refine ⟨(1, 0, 0), (mass_observabilityKernel_iff _).mpr rfl, ?_, 4, by norm_num,
      quarter_pow_four _⟩
    simp [quarterA]

/-- [counterexample; formal-checked] **A cold lattice (`A = 0`) fails (2)** although it is
coupled: nothing moves in its fibre. -/
theorem coldLattice_fails :
    (blockRegion (0 : Interior3 →ₗ[ℚ] Interior3) 0 massC 0).Coupled ∧
      ¬ (blockRegion (0 : Interior3 →ₗ[ℚ] Interior3) 0 massC 0).NotDetermined := by
  refine ⟨(block_coupled_iff _ _ _ _).mpr massC_ne_zero, ?_⟩
  rw [block_notDetermined_iff]
  rintro ⟨u, _, hA, _⟩
  exact hA rfl

/-- [counterexample; formal-checked] **A quench (`A = −1`) fails (2)** although it is coupled and
`A` moves every nonzero fibre vector: the unit-clock step sends the interior to zero, so no fibre
difference recurs. -/
theorem quench_fails :
    (blockRegion (-LinearMap.id : Interior3 →ₗ[ℚ] Interior3) 0 massC 0).Coupled ∧
      ((1, 0, 0) : Interior3) ∈ observabilityKernel (-LinearMap.id) massC ∧
      ¬ (blockRegion (-LinearMap.id : Interior3 →ₗ[ℚ] Interior3) 0 massC 0).NotDetermined := by
  have hzero : (1 + -LinearMap.id : Module.End ℚ Interior3) = 0 := by
    apply LinearMap.ext; intro v; simp
  refine ⟨(block_coupled_iff _ _ _ _).mpr massC_ne_zero, ?_, ?_⟩
  · rw [mem_observabilityKernel_iff]
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      simp only [LinearMap.neg_apply, LinearMap.id_apply, map_neg, ih, neg_zero]
  · rw [block_notDetermined_iff]
    rintro ⟨u, _, hA, n, hn, hper⟩
    rw [hzero, zero_pow hn.ne', LinearMap.zero_apply] at hper
    exact hA (by rw [← hper, map_zero])

section Ricci

open Holonics.Millennium.Ricci

/-- [definition] The generator whose unit-clock step is `Ricci.flow (1/6)`. -/
def ricciA : Tri →ₗ[ℚ] Tri where
  toFun ℓ := flow (1 / 6) ℓ - ℓ
  map_add' a b := by
    ext <;> simp only [flow, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  map_smul' c a := by
    ext <;> simp only [flow, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
      smul_eq_mul, RingHom.id_apply] <;> ring

/-- [definition] The receiver of the conserved total. -/
def totalC : Tri →ₗ[ℚ] ℚ where
  toFun := total
  map_add' a b := by simp only [total, Prod.fst_add, Prod.snd_add]; ring
  map_smul' c a := by simp only [total, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    RingHom.id_apply]; ring

theorem totalC_ricciA (ℓ : Tri) : totalC (ricciA ℓ) = 0 := by
  change total (flow (1 / 6) ℓ - ℓ) = 0
  have h := theFlowConservesTheTotal (1 / 6) ℓ
  simp only [total, Prod.fst_sub, Prod.snd_sub] at h ⊢
  linarith

/-- On a total-free difference the step halves: `Ricci.theDeviationContractsAtTheWindingRate`
at `τ = 1/6`, with the total conserved by `Ricci.theFlowConservesTheTotal`. -/
theorem ricci_step_halves (u : Tri) (hu : total u = 0) : (1 + ricciA) u = (1 / 2 : ℚ) • u := by
  have hflow : (1 + ricciA) u = flow (1 / 6) u := by
    rw [one_add_apply]; change u + (flow (1 / 6) u - u) = _; abel
  obtain ⟨h1, h2, h3⟩ := theDeviationContractsAtTheWindingRate (1 / 6) u
  have hm : mean u = 0 := by simp [mean, hu]
  have hmf : mean (flow (1 / 6) u) = 0 := by simp [mean, theFlowConservesTheTotal, hu]
  rw [hm, hmf] at h1 h2 h3
  rw [hflow]
  ext <;> simp <;> linarith

theorem ricci_kernel_total {u : Tri} (hu : u ∈ observabilityKernel ricciA totalC) :
    total u = 0 := by
  simpa [totalC] using (mem_observabilityKernel_iff _ _ u).mp hu 0

/-- [counterexample; formal-checked] **The Ricci-type decaying fibre fails (2).** The triangle flow
read by its conserved total is coupled, and its fibre holds a nonzero difference that the step
moves, `(1, −1, 0)`. That difference contracts by `1/2` each tick, so no fibre difference recurs. -/
theorem ricci_fails :
    (blockRegion ricciA 0 totalC 0).Coupled ∧
      ((1, -1, 0) : Tri) ∈ observabilityKernel ricciA totalC ∧
      ricciA ((1, -1, 0) : Tri) ≠ 0 ∧
      ¬ (blockRegion ricciA 0 totalC 0).NotDetermined := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [block_coupled_iff]
    intro h
    have := LinearMap.congr_fun h ((1, 0, 0) : Tri)
    simp [totalC, total] at this
  · rw [mem_observabilityKernel_iff]
    intro k
    cases k with
    | zero => simp [totalC, total]
    | succ k => rw [pow_succ', Module.End.mul_apply]; exact totalC_ricciA _
  · intro h
    have := congrArg Prod.fst h
    simp [ricciA, flow] at this
    norm_num at this
  · rw [block_notDetermined_iff]
    rintro ⟨u, hu, hA, n, hn, hper⟩
    have hpow : ∀ k : ℕ, ((1 + ricciA) ^ k) u = ((1 / 2 : ℚ) ^ k) • u := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, ricci_step_halves u
          (ricci_kernel_total hu), smul_smul, pow_succ]
    rw [hpow] at hper
    have hlt : (1 / 2 : ℚ) ^ n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hn.ne'
    have hsmul : ((1 / 2 : ℚ) ^ n - 1) • u = 0 := by rw [sub_smul, one_smul, hper, sub_self]
    rcases smul_eq_zero.mp hsmul with hc | hu0
    · linarith
    · exact hA (by rw [hu0, map_zero])

end Ricci

/-- [definition] A reading of the first coordinate plus the mass. -/
def firstPlusMass : Interior3 →ₗ[ℚ] ℚ where
  toFun v := v.1 + v.2.2
  map_add' a b := by simp; ring
  map_smul' c a := by simp; ring

/-- [counterexample; formal-checked] **A fully observable interior fails (2)**: its unobservable
subspace is zero, so the boundary history determines the interior. -/
theorem fullyObservable_fails :
    (blockRegion quarterA 0 firstPlusMass 0).Coupled ∧
      ¬ (blockRegion quarterA 0 firstPlusMass 0).NotDetermined := by
  constructor
  · rw [block_coupled_iff]
    intro h
    have := LinearMap.congr_fun h ((1, 0, 0) : Interior3)
    simp [firstPlusMass] at this
  · rw [block_notDetermined_iff]
    rintro ⟨v, hv, hA, _⟩
    rw [mem_observabilityKernel_iff] at hv
    have h0 := hv 0
    have h1 := hv 1
    have h2 := hv 2
    simp [firstPlusMass, quarterA, pow_two] at h0 h1 h2
    obtain ⟨x, y, m⟩ := v
    simp only at h0 h1 h2
    apply hA
    have hy : y = 0 := by linarith
    have hx : x = 0 := by linarith
    simp [quarterA, hx, hy]

/-- [counterexample; formal-checked] A sealed interior (`C = 0`) fails (1). -/
theorem sealedInterior_not_coupled :
    ¬ (blockRegion quarterA 0 (0 : Interior3 →ₗ[ℚ] ℚ) 0).Coupled := by
  rw [block_coupled_iff]; simp

/-! ### The nonlinear Birkhoff globe on `Standing`'s plane energy -/

section Birkhoff

open Holonics.Foundation.Standing

/-- [definition] The quarter turn of the rational plane. -/
def quarter (p : Plane) : Plane := (-p.2, p.1)

theorem quarter_energy (p : Plane) : planeEnergy (quarter p) = planeEnergy p := by
  simp [quarter, planeEnergy]; ring

theorem quarter_sub (a b : Plane) : quarter a - quarter b = quarter (a - b) := by
  ext <;> simp [quarter]; ring

theorem iterate_quarter_sub (k : ℕ) (a b : Plane) :
    quarter^[k] a - quarter^[k] b = quarter^[k] (a - b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', quarter_sub, ih]

theorem iterate_quarter_energy (k : ℕ) (p : Plane) : planeEnergy (quarter^[k] p) = planeEnergy p := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', quarter_energy, ih]

theorem quarter_four (p : Plane) : quarter^[4] p = p := by
  obtain ⟨a, b⟩ := p
  simp [quarter]

theorem planeEnergy_eq_zero {p : Plane} (h : planeEnergy p = 0) : p = 0 := by
  obtain ⟨a, b⟩ := p
  simp only [planeEnergy] at h
  have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  simp [ha, hb]

theorem quarter_eq_self_iff (d : Plane) : quarter d = d ↔ d = 0 := by
  constructor
  · intro h
    obtain ⟨a, b⟩ := d
    simp only [quarter, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    ext <;> simp <;> linarith
  · rintro rfl; simp [quarter]

/-- [definition] Interior: the quarter turn. Boundary: the conserved energy of the interior, read
at each tick. Admitted: the nonvacuum states. -/
def birkhoffGlobe : Region Unit Unit Plane ℚ ℚ where
  step _ state := (quarter state.1, planeEnergy state.1)
  exterior _ boundary := boundary
  admitted := {state | planeEnergy state.1 ≠ 0}

theorem birkhoffGlobe_interior_word (word : List Unit) (state : Plane × ℚ) :
    (transportWord birkhoffGlobe.step word state).1 = quarter^[word.length] state.1 := by
  induction word with
  | nil => rfl
  | cons g word ih =>
    rw [transportWord_cons, List.length_cons, Function.iterate_succ_apply', ← ih]
    rfl

/-- The fibre difference of `state` and its quarter-turned partner, along every word. -/
theorem birkhoffGlobe_diff (word : List Unit) (state : Plane × ℚ) :
    transportWord birkhoffGlobe.step word (quarter state.1, state.2) -
        transportWord birkhoffGlobe.step word state =
      (quarter^[word.length] (quarter state.1 - state.1), 0) := by
  cases word with
  | nil => ext <;> simp
  | cons g word =>
    rw [transportWord_cons, transportWord_cons]
    change (quarter (transportWord birkhoffGlobe.step word (quarter state.1, state.2)).1,
        planeEnergy (transportWord birkhoffGlobe.step word (quarter state.1, state.2)).1) -
      (quarter (transportWord birkhoffGlobe.step word state).1,
        planeEnergy (transportWord birkhoffGlobe.step word state).1) = _
    rw [birkhoffGlobe_interior_word, birkhoffGlobe_interior_word, List.length_cons,
      Function.iterate_succ_apply', ← iterate_quarter_sub]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sub]; rw [quarter_sub]
    · simp only [Prod.snd_sub, iterate_quarter_energy, quarter_energy, sub_self]

/-- [established-bounded; formal-checked] **The nonlinear Birkhoff globe is relatively complete.**
The exterior reads only the conserved energy, which separates two admitted interiors of energies
`1` and `4`. Every nonvacuum interior has a partner in its fibre whose difference turns
persistently, returning after four ticks. -/
theorem birkhoffGlobe_relativelyComplete : RelativelyComplete birkhoffGlobe globeMembrane := by
  refine ⟨?_, ?_, globeMembrane_boundsInterior⟩
  · refine ⟨(1, 0), (2, 0), 0, by simp [birkhoffGlobe, planeEnergy],
      by simp [birkhoffGlobe, planeEnergy], fun h => ?_⟩
    have := h () [()]
    simp [Region.observe, birkhoffGlobe, planeEnergy] at this
    norm_num at this
  · intro state hstate
    have hp : state.1 ≠ 0 := by
      intro h; apply hstate; rw [h]; simp [planeEnergy]
    have hd : quarter state.1 - state.1 ≠ 0 := by
      rw [sub_ne_zero]; intro h; exact hp ((quarter_eq_self_iff _).mp h)
    refine ⟨(quarter state.1, state.2), ?_, ?_, ?_⟩
    · intro _ word
      have := congrArg Prod.snd (birkhoffGlobe_diff word state)
      simp only [Prod.snd_sub] at this
      exact (sub_eq_zero.mp this).symm
    · intro word
      refine ⟨(), ?_⟩
      have h1 := birkhoffGlobe_diff (() :: word) state
      rw [transportWord_cons, transportWord_cons] at h1
      rw [h1, birkhoffGlobe_diff, List.length_cons, Function.iterate_succ_apply']
      intro h
      have h' := congrArg Prod.fst h
      simp only at h'
      rw [quarter_eq_self_iff] at h'
      apply hd
      apply planeEnergy_eq_zero
      rw [← iterate_quarter_energy word.length, h']
      simp [planeEnergy]
    · intro word
      refine ⟨[(), (), (), ()], by simp, ?_⟩
      rw [birkhoffGlobe_diff, birkhoffGlobe_diff, List.length_append]
      rw [Function.iterate_add_apply]
      simp only [List.length_cons, List.length_nil]
      rw [show 0 + 1 + 1 + 1 + 1 = 4 from rfl, quarter_four]

end Birkhoff

/-! ### Receiver relativity: one system, two receiver families -/

/-- [definition] Two boundary channels `(w₁, w₂)`: `w₁' = m` and `w₂' = x`. -/
def twoChannelC : Interior3 →ₗ[ℚ] ℚ × ℚ := massC.prod (LinearMap.fst ℚ ℚ (ℚ × ℚ))

/-- [definition] The finer family reads both boundary channels. -/
def fineRegion : Region PUnit PUnit Interior3 (ℚ × ℚ) (ℚ × ℚ) :=
  blockRegion quarterA 0 twoChannelC 0

/-- [definition] The coarser family reads only the mass channel `w₁`. -/
def coarseRegion : Region PUnit PUnit Interior3 (ℚ × ℚ) ℚ :=
  Region.ofAdditive (fun _ => blockStep quarterA 0 twoChannelC 0)
    (fun _ => (AddMonoidHom.fst ℚ ℚ)) Set.univ

theorem fine_refines_coarse : fineRegion.Refines coarseRegion :=
  ⟨rfl, rfl, fun _ => ⟨PUnit.unit, Prod.fst, fun _ => rfl⟩⟩

/-- [established-bounded; formal-checked] for the coarse family and [counterexample;
formal-checked] for the fine one. **Relativity:** the same dynamics and membrane are relatively
complete for the receiver of the mass channel alone, and not relatively complete once the
receiver that also reads the channel `w₂' = x` is added: that channel determines the fibre. -/
theorem relativity_witness :
    RelativelyComplete coarseRegion globeMembrane ∧
      ¬ RelativelyComplete fineRegion globeMembrane := by
  have hF : ∀ z : Interior3 × (ℚ × ℚ), z.1.2.2 = 0 → z.2.1 = 0 →
      z ∈ futureCollapsed (outwardRead (I := Interior3) (fun _ : PUnit => AddMonoidHom.fst ℚ ℚ))
        (fun _ : PUnit => blockStep quarterA 0 twoChannelC 0) := by
    intro z hm hw
    rw [mem_futureCollapsed_iff]
    intro _ word
    have carried : ∀ word : List PUnit,
        (transportWord (fun g s => (fun _ : PUnit => blockStep quarterA 0 twoChannelC 0) g s)
          word z).1.2.2 = 0 ∧
        (transportWord (fun g s => (fun _ : PUnit => blockStep quarterA 0 twoChannelC 0) g s)
          word z).2.1 = 0 := by
      intro word
      induction word with
      | nil => exact ⟨hm, hw⟩
      | cons g word ih =>
        rw [transportWord_cons]
        generalize transportWord _ word z = s at ih ⊢
        obtain ⟨h1, h2⟩ := ih
        rw [blockStep_apply, blockVelocity_apply]
        simp [quarterA, twoChannelC, massC, h1, h2]
    simpa [outwardRead] using (carried word).2
  refine ⟨⟨?_, ?_, globeMembrane_boundsInterior⟩, fun h => ?_⟩
  · refine ⟨0, (0, 0, 1), 0, trivial, trivial, fun h => ?_⟩
    have := h PUnit.unit [PUnit.unit]
    simp [Region.observe, coarseRegion, Region.ofAdditive, blockStep_apply, twoChannelC,
      massC] at this
  · intro state _
    refine ⟨state + ((1, 0, 0), (0, 0)), ?_, ?_⟩
    · rw [coarseRegion, ofAdditive_agree_iff, add_sub_cancel_left]
      exact hF _ rfl rfl
    · rw [coarseRegion, ofAdditive_persistent_iff, add_sub_cancel_left]
      refine ⟨4, by norm_num, ?_, ?_⟩
      · rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, Function.iterate_add_apply,
          Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one]
        simp [blockStep_apply, quarterA, twoChannelC, massC]
      · intro h
        have := congrArg (fun z : Interior3 × (ℚ × ℚ) => z.1.2.1) h
        simp [blockStep_apply, quarterA, twoChannelC, massC] at this
  · have h2 := h.notDetermined
    rw [fineRegion, block_notDetermined_iff] at h2
    obtain ⟨v, hv, hA, _⟩ := h2
    rw [mem_observabilityKernel_iff] at hv
    have h0 := hv 0
    have h1 := hv 1
    obtain ⟨x, y, m⟩ := v
    simp [twoChannelC, massC, quarterA] at h0 h1
    apply hA
    have hy : y = 0 := by linarith [h0.2, h1]
    simp [quarterA, h0.2, hy]

end Witnesses

end Holonics.Objects.RelativeCompleteness
