import Holonics.HNN.MediumStanding

/-!
# HNN.FactoredMedium: the Rust's deposit laws keep the medium admissible by construction

[definition] #62 (owed by `HNN/MediumStanding`, whose deposit laws `Φe`, `Φc` are hypotheses
that each keep its locus admissible). The Rust does not move a learned carrier: it moves the
carrier's factors and re-forms the carrier from them (`hnn::constitution`, "Loci"):

```text
element g      W_s = −f fᵀ ,   A_ρ = u_ρ v_ρᵀ − v_ρ u_ρᵀ ,   W_c a linear locus
channel a      C = c cᵀ ,   K = b bᵀ ,   D = F Fᵀ
deposit        x ← x + η_x G_x / h_x′  per factor family,  W_c by its normal law
```

so every learned carrier is admissible whatever the step moves the factors to (the factor
carriers stay PSD with no clamp, `HNN/Normal.factorCarrier_psd`). This file states the medium with
the factors as its state and proves the standing law there with no hypothesis on the deposit.

* **The state** (`Factored`) carries the declared operands of `Word.Medium` (the channel
  embeddings, `Y`, `G`, `h`, the sheet classes `σ`), each element's factors `f`, `u_ρ`, `v_ρ` and
  its contrast port `W_c`, and each channel's factors `c`, `b`, `F`, on factor spaces `FE r`, `FC a`
  of any finite dimension. The carriers are re-formed by the adjoint (`toMedium`): `sq c = c c*`,
  `skew u v = u v* − v u*`.
* **The constitution** is a state whose declared operands are admissible (`Declared`) at the
  declared tick length (`FactoredAt`).
* **The deposit** (`fdeposited`) moves each locus's factors by its own law `Ψe`, `Ψc` from the data
  on the edges that read it (`MediumStanding.locusOf`). The laws are any functions of the locus's
  factors and its data. The Rust's certified step reads more than that ([open] below).
* **The release** (`frelease`) zeroes a released locus's factors, which zeroes its carriers: it is
  `LocusMap.release` on the carriers (`toMedium_release`).

[proved-derived; formal-checked] What is proved.

1. **Every factored medium is admissible** (`toMedium_admissible`), from its declared operands only:
   `⟨v, −f f* v⟩ = −‖f* v‖²`, `⟨v, (u v* − v u*) v⟩ = ⟨u* v, v* v⟩ − ⟨v* v, u* v⟩ = 0`,
   `⟨v, c c* v⟩ = ‖c* v‖²` and `⟨c c* x, y⟩ = ⟨c* x, c* y⟩ = ⟨x, c c* y⟩` (`sq_psd`, `sq_symm`,
   `skew_no_work`).
2. **The locus map's laws hold** (`factoredLaw_lawful`) for every pair of factor laws, and **the
   quiet laws** (`factoredLaw_quiet`) for factor laws that keep a locus on empty data. The agreement
   on a locus is the agreement of its factors and declared operands (`FAgreeOn`), which gives the
   carriers' agreement (`agreeOn_toMedium`), so the operator's and references' laws follow from
   `LocusMap.blockOp_agree` as in `MediumStanding`.
3. **The standing on the factored medium** (`factoredStanding`), with released loci staying released
   (`factored_released_stays_released`).
4. **The Rust's collapse is sufficient for every per-locus factor law**
   (`factored_rust_collapse_sufficient`):
   with the factor laws as the only deposit, `MediumStanding.rust_collapse_sufficient`'s hypotheses
   `hΦe`, `hΦc` are gone. Its remaining hypotheses are the Rust's declarations: the seeded contact
   blocks come with their end rings and no receiver is a contact block.
5. **The Rust's step is quiet on empty data** (`certifiedStep_quiet`). The certified step moves the
   factors by `η` times a sum over the data that reached the locus (`certifiedStep`), which is zero
   on empty data whatever `η`. So under it released loci stay released with no hypothesis
   (`certified_released_stays_released`), and `MediumStanding`'s `hΦe0`, `hΦc0` are gone too.

[open] What it does not cover: the step's certified descent (`Holon/Deposition`, outside the
standing law). The loci with no `Word.Medium` operand (`SourcePort(g)`, `Standing(g)`,
`ReceivingMap(g)`) are `HNN/RingLoci`, and the loaded ring block joined to the medium is
`HNN/LoadedMedium`.

[open; source-inspected at `37e24ef3`] **The Rust's step is not yet a per-locus factor law.** Its
moves are sums over the data that reached the locus, so they are zero on empty data, which is all
`certifiedStep_quiet` uses. But each move is read through state this file's locus omits (a factor
family's carried statistic `h_x′`, a linear locus's successor Gram and chart), and its scalar is the
deposit's joint certified step, whose gains read the medium's reach: `1 + ω` over every ring's
contrast port and the span factor `F(s)` over every resonator not certified passive
(`hnn::constitution::Constitution::{contrast_amplitude, ring_reaches}`, read in `deposited`). An
off-walk contrast port is never reached, so it stays at its zero founding and `ω` is unchanged by
the collapse. An off-walk resonator is declared material, and the collapse releases it
(`Constitution::release`, `Locus::Resonator`). Where it is pumped, `F(s)` drops after the collapse,
and a later deposit's step at a retained locus could differ from the uncollapsed run's. Record B
§8 has the Rust read the reach over the word's diamond only (`Reach::loci`; the release-law fix,
not yet on main at this writing), and the joint step whose reads are the diamond's and whose budget
is the retained set's is `HNN/JointStep` (`certified_budgeted_rust_unchanged`): the collapse
changes no step and no refusal.
Owed (#62): the carried statistics in the locus's state.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.FactoredMedium

open Holonics.HNN.Propagation Holonics.HNN.Retention Holonics.HNN.CarriedStanding
open Holonics.HNN.TickFamily Holonics.HNN.TickStanding
open Holonics.HNN.Word Holonics.HNN.TickBlocks Holonics.HNN.LocusMap
open Holonics.HNN.MediumStanding

universe u

/-! ## 1. The factor forms are admissible -/

section Forms

variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- [definition] **The square of a factor**, `c c*`. -/
def sq (c : E →L[ℝ] F) : F →L[ℝ] F := c ∘L ContinuousLinearMap.adjoint c

/-- [definition] **The skew form of two factors**, `u v* − v u*`. -/
def skew (u v : E →L[ℝ] F) : F →L[ℝ] F :=
  u ∘L ContinuousLinearMap.adjoint v - v ∘L ContinuousLinearMap.adjoint u

theorem sq_inner (c : E →L[ℝ] F) (x y : F) :
    inner ℝ x (sq c y) =
      inner ℝ (ContinuousLinearMap.adjoint c x) (ContinuousLinearMap.adjoint c y) :=
  (ContinuousLinearMap.adjoint_inner_left c _ x).symm

/-- [proved-derived; formal-checked] A square is positive: `⟨v, c c* v⟩ = ‖c* v‖²`. -/
theorem sq_psd (c : E →L[ℝ] F) (v : F) : 0 ≤ inner ℝ v (sq c v) := by
  rw [sq_inner]; exact real_inner_self_nonneg

/-- [proved-derived; formal-checked] A square is symmetric. -/
theorem sq_symm (c : E →L[ℝ] F) (x y : F) : inner ℝ (sq c x) y = inner ℝ x (sq c y) := by
  rw [real_inner_comm, sq_inner, sq_inner, real_inner_comm]

/-- [proved-derived; formal-checked] A negated square is passive. -/
theorem neg_sq_passive (c : E →L[ℝ] F) (v : F) : inner ℝ v ((-sq c) v) ≤ 0 := by
  rw [show (-sq c) v = -(sq c v) from rfl, inner_neg_right]
  exact neg_nonpos.mpr (sq_psd c v)

/-- [proved-derived; formal-checked] A skew form does no work: `⟨v, (u v* − v u*) v⟩ = 0`. -/
theorem skew_no_work (u w : E →L[ℝ] F) (v : F) : inner ℝ v (skew u w v) = 0 := by
  simp only [skew, sub_apply, ContinuousLinearMap.comp_apply, inner_sub_right]
  rw [← ContinuousLinearMap.adjoint_inner_left u, ← ContinuousLinearMap.adjoint_inner_left w,
    real_inner_comm]
  exact sub_self _

theorem sq_zero : sq (0 : E →L[ℝ] F) = 0 := by simp [sq]

end Forms

/-! ## 2. The factored medium -/

section Medium

variable {Ring Contact ρ : Type u}
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ r, FiniteDimensional ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)] [∀ a, FiniteDimensional ℝ (Ch a)]
variable {FE : Ring → Type u} [∀ r, NormedAddCommGroup (FE r)] [∀ r, InnerProductSpace ℝ (FE r)]
  [∀ r, FiniteDimensional ℝ (FE r)]
variable {FC : Contact → Type u} [∀ a, NormedAddCommGroup (FC a)]
  [∀ a, InnerProductSpace ℝ (FC a)] [∀ a, FiniteDimensional ℝ (FC a)]
variable {endRing : Contact × Bool → Ring}

variable (endRing V Ch ρ FE FC) in
/-- [definition] **The factored medium** (`hnn::constitution`, "Loci"): the declared operands of
`Word.Medium`, each element's passive factor `f`, slice factors `u_ρ`, `v_ρ` and contrast port
`W_c`, and each channel's square factors `c`, `b`, `F`. -/
structure Factored where
  channel : (e : Contact × Bool) → Ch e.1 →L[ℝ] V (endRing e)
  Y : Ring → ℝ
  G : Contact → ℝ
  h : ℝ
  σ : Ring → ρ → ℝ
  f : (r : Ring) → FE r →L[ℝ] V r
  u : (r : Ring) → ρ → FE r →L[ℝ] V r
  v : (r : Ring) → ρ → FE r →L[ℝ] V r
  Wc : (r : Ring) → V r →L[ℝ] V r
  c : (a : Contact) → FC a →L[ℝ] Ch a
  b : (a : Contact) → FC a →L[ℝ] Ch a
  F : (a : Contact) → FC a →L[ℝ] Ch a

/-- [definition] **The carriers re-formed from the factors**: `W_s = −f f*`,
`A_ρ = u_ρ v_ρ* − v_ρ u_ρ*`, `C = c c*`, `K = b b*`, `D = F F*`. -/
def toMedium (φ : Factored ρ V Ch FE FC endRing) : Medium endRing V Ch ρ where
  channel := φ.channel
  Y := φ.Y
  G := φ.G
  h := φ.h
  Ws r := -sq (φ.f r)
  A r i := skew (φ.u r i) (φ.v r i)
  σ := φ.σ
  Wc := φ.Wc
  C a := sq (φ.c a)
  D a := sq (φ.F a)
  K a := sq (φ.b a)

/-- [definition] **The declared operands are admissible**: positive admittances, conductances and
tick length, and channel embeddings. -/
structure Declared (φ : Factored ρ V Ch FE FC endRing) : Prop where
  Y_pos : ∀ r, 0 < φ.Y r
  G_pos : ∀ a, 0 < φ.G a
  h_pos : 0 < φ.h
  channel : ∀ e, IsChannelEmbedding (φ.channel e)

/-- [proved-derived; formal-checked] **Every factored medium with admissible declared operands is
admissible**, whatever its factors. -/
theorem toMedium_admissible {φ : Factored ρ V Ch FE FC endRing} (hφ : Declared φ) :
    (toMedium φ).Admissible where
  Ws_passive r v := neg_sq_passive (φ.f r) v
  A_skew r i v := skew_no_work (φ.u r i) (φ.v r i) v
  C_psd a v := sq_psd (φ.c a) v
  D_psd a v := sq_psd (φ.F a) v
  K_psd a v := sq_psd (φ.b a) v
  C_symm a x y := sq_symm (φ.c a) x y
  K_symm a x y := sq_symm (φ.b a) x y
  Y_pos := hφ.Y_pos
  G_pos := hφ.G_pos
  h_pos := hφ.h_pos
  channel := hφ.channel

/-- [definition] **Two factored media agree on a locus**: on ring `r`'s element its factors, its
sheet classes and `W_c`; on its junction `Y_r`; on contact `a`'s channel its factors and its two
embeddings; on its conductance `G_a`. -/
def FAgreeOn (φ φ' : Factored ρ V Ch FE FC endRing) : Locus Ring Contact → Prop
  | .element r => φ.f r = φ'.f r ∧ φ.u r = φ'.u r ∧ φ.v r = φ'.v r ∧ φ.σ r = φ'.σ r ∧
      φ.Wc r = φ'.Wc r
  | .junction r => φ.Y r = φ'.Y r
  | .channel a => φ.c a = φ'.c a ∧ φ.b a = φ'.b a ∧ φ.F a = φ'.F a ∧
      ∀ s, φ.channel (a, s) = φ'.channel (a, s)
  | .conductance a => φ.G a = φ'.G a

/-- [proved-derived; formal-checked] Agreeing factors give agreeing carriers. -/
theorem agreeOn_toMedium {φ φ' : Factored ρ V Ch FE FC endRing} {ℓ : Locus Ring Contact}
    (h : FAgreeOn φ φ' ℓ) : AgreeOn (toMedium φ) (toMedium φ') ℓ := by
  cases ℓ with
  | element r =>
    obtain ⟨hf, hu, hv, hσ, hc⟩ := h
    refine ⟨?_, ?_, hσ, hc⟩
    · show -sq (φ.f r) = -sq (φ'.f r)
      rw [hf]
    · show (fun i => skew (φ.u r i) (φ.v r i)) = fun i => skew (φ'.u r i) (φ'.v r i)
      rw [hu, hv]
  | junction r => exact h
  | channel a =>
    obtain ⟨hc, hb, hF, he⟩ := h
    refine ⟨?_, ?_, ?_, he⟩
    · show sq (φ.c a) = sq (φ'.c a)
      rw [hc]
    · show sq (φ.F a) = sq (φ'.F a)
      rw [hF]
    · show sq (φ.b a) = sq (φ'.b a)
      rw [hb]
  | conductance a => exact h

omit [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)]
  [∀ r, FiniteDimensional ℝ (FE r)] [∀ a, FiniteDimensional ℝ (FC a)] in
theorem fagreeOn_refl (φ : Factored ρ V Ch FE FC endRing) (ℓ : Locus Ring Contact) :
    FAgreeOn φ φ ℓ := by
  cases ℓ with
  | element r => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | junction r => exact rfl
  | channel a => exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  | conductance a => exact rfl

omit [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)]
  [∀ r, FiniteDimensional ℝ (FE r)] [∀ a, FiniteDimensional ℝ (FC a)] in
theorem fagreeOn_trans {φ₁ φ₂ φ₃ : Factored ρ V Ch FE FC endRing} {ℓ : Locus Ring Contact}
    (h₁ : FAgreeOn φ₁ φ₂ ℓ) (h₂ : FAgreeOn φ₂ φ₃ ℓ) : FAgreeOn φ₁ φ₃ ℓ := by
  cases ℓ with
  | element r =>
    exact ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
      h₁.2.2.2.1.trans h₂.2.2.2.1, h₁.2.2.2.2.trans h₂.2.2.2.2⟩
  | junction r => exact Eq.trans h₁ h₂
  | channel a =>
    exact ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
      fun s => (h₁.2.2.2 s).trans (h₂.2.2.2 s)⟩
  | conductance a => exact Eq.trans h₁ h₂

/-- The element's factors and contrast port. -/
abbrev ElementFactors (r : Ring) : Type u :=
  (FE r →L[ℝ] V r) × (ρ → FE r →L[ℝ] V r) × (ρ → FE r →L[ℝ] V r) × (V r →L[ℝ] V r)

/-- The channel's factors. -/
abbrev ChannelFactors (a : Contact) : Type u :=
  (FC a →L[ℝ] Ch a) × (FC a →L[ℝ] Ch a) × (FC a →L[ℝ] Ch a)

/-- [definition] **The deposit on the factors** (`Constitution::deposited`): each element's
`(f, u, v, W_c)` and each channel's `(c, b, F)` move by its own law from the data that reached it;
the declared operands stay. -/
def fdeposited
    (Ψe : (r : Ring) → ElementFactors (V := V) (FE := FE) (ρ := ρ) r → EdgeData endRing V Ch →
      ElementFactors (V := V) (FE := FE) (ρ := ρ) r)
    (Ψc : (a : Contact) → ChannelFactors (Ch := Ch) (FC := FC) a → EdgeData endRing V Ch →
      ChannelFactors (Ch := Ch) (FC := FC) a)
    (dat : Locus Ring Contact → EdgeData endRing V Ch) (φ : Factored ρ V Ch FE FC endRing) :
    Factored ρ V Ch FE FC endRing where
  channel := φ.channel
  Y := φ.Y
  G := φ.G
  h := φ.h
  σ := φ.σ
  f r := (Ψe r (φ.f r, φ.u r, φ.v r, φ.Wc r) (dat (.element r))).1
  u r := (Ψe r (φ.f r, φ.u r, φ.v r, φ.Wc r) (dat (.element r))).2.1
  v r := (Ψe r (φ.f r, φ.u r, φ.v r, φ.Wc r) (dat (.element r))).2.2.1
  Wc r := (Ψe r (φ.f r, φ.u r, φ.v r, φ.Wc r) (dat (.element r))).2.2.2
  c a := (Ψc a (φ.c a, φ.b a, φ.F a) (dat (.channel a))).1
  b a := (Ψc a (φ.c a, φ.b a, φ.F a) (dat (.channel a))).2.1
  F a := (Ψc a (φ.c a, φ.b a, φ.F a) (dat (.channel a))).2.2

open Classical in
/-- [definition] **The release of the factors** (`Constitution::release`): a released element's
factors and `W_c` and a released channel's factors become zero; the declared operands stay. -/
def frelease (keep : Locus Ring Contact → Prop) (φ : Factored ρ V Ch FE FC endRing) :
    Factored ρ V Ch FE FC endRing where
  channel := φ.channel
  Y := φ.Y
  G := φ.G
  h := φ.h
  σ := φ.σ
  f r := if keep (.element r) then φ.f r else 0
  u r := if keep (.element r) then φ.u r else 0
  v r := if keep (.element r) then φ.v r else 0
  Wc r := if keep (.element r) then φ.Wc r else 0
  c a := if keep (.channel a) then φ.c a else 0
  b a := if keep (.channel a) then φ.b a else 0
  F a := if keep (.channel a) then φ.F a else 0

/-- [proved-derived; formal-checked] **The factors' release is the carriers' release**:
`toMedium (frelease keep φ) = LocusMap.release keep (toMedium φ)`. -/
theorem toMedium_release (keep : Locus Ring Contact → Prop) (φ : Factored ρ V Ch FE FC endRing) :
    toMedium (frelease keep φ) = release keep (toMedium φ) := by
  classical
  simp only [toMedium, frelease, release, Medium.mk.injEq, true_and]
  split_ands <;> funext x <;> split_ifs <;>
    first | rfl | (funext i; simp [skew]) | simp [sq_zero]

omit [∀ r, FiniteDimensional ℝ (FE r)] [∀ a, FiniteDimensional ℝ (FC a)] in
theorem declared_fdeposited {Ψe Ψc} {dat : Locus Ring Contact → EdgeData endRing V Ch}
    {φ : Factored ρ V Ch FE FC endRing} (hφ : Declared φ) :
    Declared (fdeposited Ψe Ψc dat φ) :=
  ⟨hφ.Y_pos, hφ.G_pos, hφ.h_pos, hφ.channel⟩

omit [∀ r, FiniteDimensional ℝ (FE r)] [∀ a, FiniteDimensional ℝ (FC a)] in
theorem declared_frelease {keep : Locus Ring Contact → Prop} {φ : Factored ρ V Ch FE FC endRing}
    (hφ : Declared φ) : Declared (frelease keep φ) :=
  ⟨hφ.Y_pos, hφ.G_pos, hφ.h_pos, hφ.channel⟩

end Medium

/-! ## 3. The law on the factored medium -/

section Law

variable {Ring Contact ρ : Type u} [Fintype Ring] [DecidableEq Ring] [Fintype Contact]
  [DecidableEq Contact] [Fintype ρ]
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ r, FiniteDimensional ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)] [∀ a, FiniteDimensional ℝ (Ch a)]
variable {FE : Ring → Type u} [∀ r, NormedAddCommGroup (FE r)] [∀ r, InnerProductSpace ℝ (FE r)]
  [∀ r, FiniteDimensional ℝ (FE r)]
variable {FC : Contact → Type u} [∀ a, NormedAddCommGroup (FC a)]
  [∀ a, InnerProductSpace ℝ (FC a)] [∀ a, FiniteDimensional ℝ (FC a)]
variable {endRing : Contact × Bool → Ring}

variable (endRing V Ch ρ FE FC) in
/-- [definition] **The constitution**: a factored medium with admissible declared operands at the
declared tick length `h₀`. -/
def FactoredAt (h₀ : ℝ) : Type u := {φ : Factored ρ V Ch FE FC endRing // Declared φ ∧ φ.h = h₀}

variable {Λ Mo Cell Crib : Type*}

/-- [definition] **The law on the factored medium**: `MediumStanding.mediumLaw` with the factors as
the state, the carriers re-formed from them, and any per-locus factor laws as the deposit. -/
def factoredLaw (h₀ : ℝ) (cls : Λ → ℕ → Ring → ρ → ℝ)
    (openState : Λ → Mo → (b : Ring ⊕ Contact) → BlockM endRing V Ch b) (ticks : Λ → Mo → ℕ)
    (cross : Λ → Λ → (b : Ring ⊕ Contact) → MediumRef Ring Ch b → MediumRef Ring Ch b →
      (BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b))
    (absorb : (b : Ring ⊕ Contact) → BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b)
    (ingestStep : Cell → Λ × Mo → Λ × Mo) (rekey : Crib → Λ → Λ)
    (Ψe : (r : Ring) → ElementFactors (V := V) (FE := FE) (ρ := ρ) r → EdgeData endRing V Ch →
      ElementFactors (V := V) (FE := FE) (ρ := ρ) r)
    (Ψc : (a : Contact) → ChannelFactors (Ch := Ch) (FC := FC) a → EdgeData endRing V Ch →
      ChannelFactors (Ch := Ch) (FC := FC) a) :
    TickLaw ℝ (BlockM endRing V Ch) (FactoredAt ρ V Ch FE FC endRing h₀) (Locus Ring Contact)
      (MediumRef Ring Ch) (Ring → ρ → ℝ) Λ Mo Cell Crib where
  op c φ := blockOp (withSheets_admissible (toMedium_admissible φ.2.1) c)
  reads := Reads endRing
  refReads := RefReads
  openReads _ _ := False
  recvReads _ _ := False
  agreeOn ℓ φ φ' := FAgreeOn φ.1 φ'.1 ℓ
  ref φ := mediumRef (toMedium φ.1)
  recv _ _ := LinearMap.id
  cls := cls
  openState _ := openState
  ticks := ticks
  cross := cross
  absorb := absorb
  ingestStep := ingestStep
  rekey := rekey
  apply φ d := ⟨fdeposited Ψe Ψc (locusOf d) φ.1, declared_fdeposited φ.2.1, φ.2.2⟩
  release keep φ := ⟨frelease keep φ.1, declared_frelease φ.2.1, φ.2.2⟩

variable {h₀ : ℝ} {cls : Λ → ℕ → Ring → ρ → ℝ}
  {openState : Λ → Mo → (b : Ring ⊕ Contact) → BlockM endRing V Ch b} {ticks : Λ → Mo → ℕ}
  {cross : Λ → Λ → (b : Ring ⊕ Contact) → MediumRef Ring Ch b → MediumRef Ring Ch b →
    (BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b)}
  {absorb : (b : Ring ⊕ Contact) → BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b}
  {ingestStep : Cell → Λ × Mo → Λ × Mo} {rekey : Crib → Λ → Λ}
  {Ψe : (r : Ring) → ElementFactors (V := V) (FE := FE) (ρ := ρ) r → EdgeData endRing V Ch →
    ElementFactors (V := V) (FE := FE) (ρ := ρ) r}
  {Ψc : (a : Contact) → ChannelFactors (Ch := Ch) (FC := FC) a → EdgeData endRing V Ch →
    ChannelFactors (Ch := Ch) (FC := FC) a}

/-- The factored medium's law at the section's operands. -/
local notation "FL" => factoredLaw (Cell := Cell) (Crib := Crib) h₀ cls openState ticks cross
  absorb ingestStep rekey Ψe Ψc

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] [Fintype ρ]
  [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)]
  [∀ r, FiniteDimensional ℝ (FE r)] [∀ a, FiniteDimensional ℝ (FC a)] in
/-- [proved-derived; formal-checked] **The deposit on the factors is local per locus.** -/
theorem fdeposited_local {φ φ' : Factored ρ V Ch FE FC endRing} {d d' : EdgeData endRing V Ch}
    {ℓ : Locus Ring Contact} (hφ : FAgreeOn φ φ' ℓ)
    (hd : ∀ y z, Reads endRing ℓ z y → d y z = d' y z) :
    FAgreeOn (fdeposited Ψe Ψc (locusOf d) φ) (fdeposited Ψe Ψc (locusOf d') φ') ℓ := by
  have hdat := locusOf_congr (ℓ := ℓ) hd
  cases ℓ with
  | element r =>
    obtain ⟨hf, hu, hv, hσ, hc⟩ := hφ
    have key : Ψe r (φ.f r, φ.u r, φ.v r, φ.Wc r) (locusOf d (.element r)) =
        Ψe r (φ'.f r, φ'.u r, φ'.v r, φ'.Wc r) (locusOf d' (.element r)) := by
      rw [hf, hu, hv, hc, hdat]
    exact ⟨congrArg Prod.fst key, congrArg (fun p => p.2.1) key, congrArg (fun p => p.2.2.1) key,
      hσ, congrArg (fun p => p.2.2.2) key⟩
  | junction r => exact hφ
  | channel a =>
    obtain ⟨hc, hb, hF, he⟩ := hφ
    have key : Ψc a (φ.c a, φ.b a, φ.F a) (locusOf d (.channel a)) =
        Ψc a (φ'.c a, φ'.b a, φ'.F a) (locusOf d' (.channel a)) := by rw [hc, hb, hF, hdat]
    exact ⟨congrArg Prod.fst key, congrArg (fun p => p.2.1) key, congrArg (fun p => p.2.2) key, he⟩
  | conductance a => exact hφ

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] [Fintype ρ]
  [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)]
  [∀ r, FiniteDimensional ℝ (FE r)] [∀ a, FiniteDimensional ℝ (FC a)] in
/-- [proved-derived; formal-checked] **A deposit keeps a locus no datum reaches**, for factor laws
that keep a locus on empty data. -/
theorem fdeposited_quiet
    (hΨe0 : ∀ r p, Ψe r p (fun _ _ => []) = p) (hΨc0 : ∀ a p, Ψc a p (fun _ _ => []) = p)
    (φ : Factored ρ V Ch FE FC endRing) {d : EdgeData endRing V Ch} {ℓ : Locus Ring Contact}
    (h : ∀ y z, Reads endRing ℓ z y → d y z = []) :
    FAgreeOn φ (fdeposited Ψe Ψc (locusOf d) φ) ℓ := by
  have hdat := locusOf_quiet (ℓ := ℓ) h
  cases ℓ with
  | element r =>
    have key : Ψe r (φ.f r, φ.u r, φ.v r, φ.Wc r) (locusOf d (.element r)) =
        (φ.f r, φ.u r, φ.v r, φ.Wc r) := by rw [hdat, hΨe0]
    exact ⟨(congrArg Prod.fst key).symm, (congrArg (fun p => p.2.1) key).symm,
      (congrArg (fun p => p.2.2.1) key).symm, rfl, (congrArg (fun p => p.2.2.2) key).symm⟩
  | junction r => exact rfl
  | channel a =>
    have key : Ψc a (φ.c a, φ.b a, φ.F a) (locusOf d (.channel a)) = (φ.c a, φ.b a, φ.F a) := by
      rw [hdat, hΨc0]
    exact ⟨(congrArg Prod.fst key).symm, (congrArg (fun p => p.2.1) key).symm,
      (congrArg (fun p => p.2.2) key).symm, fun _ => rfl⟩
  | conductance a => exact rfl

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] [Fintype ρ]
  [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)]
  [∀ r, FiniteDimensional ℝ (FE r)] [∀ a, FiniteDimensional ℝ (FC a)] in
/-- [proved-derived; formal-checked] The release keeps every locus it keeps. -/
theorem fagreeOn_frelease {keep : Locus Ring Contact → Prop} (φ : Factored ρ V Ch FE FC endRing)
    {ℓ : Locus Ring Contact} (hk : keep ℓ) : FAgreeOn φ (frelease keep φ) ℓ := by
  classical
  cases ℓ with
  | element r => exact ⟨(if_pos hk).symm, (if_pos hk).symm, (if_pos hk).symm, rfl, (if_pos hk).symm⟩
  | junction r => exact rfl
  | channel a => exact ⟨(if_pos hk).symm, (if_pos hk).symm, (if_pos hk).symm, fun _ => rfl⟩
  | conductance a => exact rfl

/-- [proved-derived; formal-checked] **The locus map's laws hold on the factored medium**, for every
pair of factor laws. -/
theorem factoredLaw_lawful : (FL).Lawful (blockAdj endRing) where
  sparse c φ := blockOp_sparse _
  reads_adj ℓ z y h := LocusMap.reads_adj h
  op_reads c φ φ' y z h :=
    blockOp_agree (withSheets_admissible (toMedium_admissible φ.2.1) c)
      (withSheets_admissible (toMedium_admissible φ'.2.1) c) (φ.2.2.trans φ'.2.2.symm)
      fun ℓ hr => agreeOn_withSheets (agreeOn_toMedium (h ℓ hr)) c
  ref_reads φ φ' b h := by
    cases b with
    | inl r => rfl
    | inr a =>
      have hG : φ.1.G a = φ'.1.G a := h (.conductance a) rfl
      have hc : φ.1.c a = φ'.1.c a := (h (.channel a) rfl).1
      show (ULift.up (φ.1.G a), sq (φ.1.c a)) = (ULift.up (φ'.1.G a), sq (φ'.1.c a))
      rw [hG, hc]
  open_reads _ _ _ _ _ _ := rfl
  recv_reads _ _ _ _ := rfl
  apply_local φ φ' d d' ℓ hφ hd := fdeposited_local hφ hd
  release_keeps keep φ ℓ hk := fagreeOn_frelease φ.1 hk

omit [Fintype Ring] in
/-- [proved-derived; formal-checked] **The quiet laws hold on the factored medium** for factor laws
that keep a locus on empty data. -/
theorem factoredLaw_quiet
    (hΨe0 : ∀ r p, Ψe r p (fun _ _ => []) = p) (hΨc0 : ∀ a p, Ψc a p (fun _ _ => []) = p) :
    (FL).Quiet where
  refl ℓ φ := fagreeOn_refl φ.1 ℓ
  trans _ _ _ _ h₁ h₂ := fagreeOn_trans h₁ h₂
  apply_quiet φ _ _ h := fdeposited_quiet hΨe0 hΨc0 φ.1 h

omit [Fintype Ring] in
/-- [proved-derived; formal-checked] The law's release is `LocusMap.release` on the carriers. -/
theorem factoredLaw_release (keep : Locus Ring Contact → Prop)
    (φ : FactoredAt ρ V Ch FE FC endRing h₀) :
    toMedium ((FL).release keep φ).1 = release keep (toMedium φ.1) :=
  toMedium_release keep φ.1

/-! ## 4. The standing on the factored medium, and the Rust's rule -/

/-- [proved-derived; formal-checked] **The standing on the factored medium** (#62): the tick-indexed
standing law of `HNN/TickStanding` at the factored medium's law, for any factor laws. -/
def factoredStanding {S R : Set (Ring ⊕ Contact)} (hopen : ∀ l m, SupportedIn (openState l m) S) :
    Holonics.Foundation.Standing.StandingLaw
      (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R))
      (Option ℕ × ReceiverReading ℝ (BlockM endRing V Ch) R) (ValidResident (blockAdj endRing) FL S)
      (ValidResident (blockAdj endRing) FL S) ℝ :=
  tickStanding (L := FL) (adj := blockAdj endRing) (S := S) (R := R) factoredLaw_lawful
    (fun _ => hopen)

/-- [proved-derived; formal-checked] **On the factored medium a deposit between words never
reopens a released locus**, for factor laws that keep a locus on empty data. -/
theorem factored_released_stays_released
    (hΨe0 : ∀ r p, Ψe r p (fun _ _ => []) = p) (hΨc0 : ∀ a p, Ψc a p (fun _ _ => []) = p)
    {S R : Set (Ring ⊕ Contact)} (hopen : ∀ l m, SupportedIn (openState l m) S)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing) FL S)
    (h : StagedOff (blockAdj endRing) S R s.1) {ℓ : Locus Ring Contact}
    (hℓ : ¬ TickStanding.Retained (blockAdj endRing) FL S R ℓ) :
    FAgreeOn (frelease (TickStanding.Retained (blockAdj endRing) FL S R) s.1.loci.1)
      (Holonics.Foundation.Chronology.transportWord
        (transport (blockAdj endRing) FL factoredLaw_lawful (fun _ => hopen)) w
        ⟨retain (blockAdj endRing) FL S R s.1, retain_valid s.2⟩).1.loci.1 ℓ :=
  released_stays_released factoredLaw_lawful (factoredLaw_quiet hΨe0 hΨc0) (fun _ => hopen) w s h hℓ

/-- [proved-derived; formal-checked] **The Rust's rule keeps the retained loci** on the factored
medium, as on the medium (`MediumStanding.retained_rust`): the two laws read the same loci. -/
theorem retained_rust_factored {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) {ℓ : Locus Ring Contact}
    (h : TickStanding.Retained (blockAdj endRing) FL S R ℓ) :
    LocusMap.Retained endRing S R (2 * Fintype.card (Ring ⊕ Contact)) ℓ := by
  rcases h with ⟨z, y, hr, hw⟩ | ⟨b, hrb, hreach, hobs⟩ | ⟨b, hrb, -⟩ | ⟨b, hrb, -⟩
  · exact retained_of_reads hS hR hr ((inDiamond_continuing_iff S R z y).mpr hw)
  · have hd := (inDiamond_continuing_iff (adj := blockAdj endRing) S R b b).mpr ⟨hreach, hobs⟩
    cases ℓ with
    | element r => exact absurd hrb id
    | junction r => exact absurd hrb id
    | channel a =>
      obtain rfl : b = .inr a := hrb
      exact channel_of_edge hS hR (Or.inl rfl) (Or.inl rfl) hd
    | conductance a =>
      obtain rfl : b = .inr a := hrb
      exact Or.inl (channel_of_edge hS hR (Or.inl rfl) (Or.inl rfl) hd)
  · exact absurd hrb id
  · exact absurd hrb id

/-- [proved-derived; formal-checked] **The collapse the Rust runs is sufficient, for every
per-locus factor law** (`hnn::retention::collapse` under `Diamond::continuing`; the Rust's own
deposit is not yet such a law, module header [open]).
Releasing every locus the Rust's per-locus rule does not retain at `e_last = 2 |B|` (the factors'
release, which is `LocusMap.release` on the carriers, `factoredLaw_release`) changes no admitted
face of the current word or of any pending word, after any word of the generators. No hypothesis
on the factor laws remains. -/
theorem factored_rust_collapse_sufficient {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) (hopen : ∀ l m, SupportedIn (openState l m) S)
    (q : Option ℕ × ReceiverReading ℝ (BlockM endRing V Ch) R)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing) FL S) :
    observe FL q (Holonics.Foundation.Chronology.transportWord
        (transport (blockAdj endRing) FL factoredLaw_lawful (fun _ => hopen)) w
        ⟨{ s.1 with loci := (FL).release (LocusMap.Retained endRing S R
            (2 * Fintype.card (Ring ⊕ Contact))) s.1.loci }, s.2⟩).1 =
      observe FL q (Holonics.Foundation.Chronology.transportWord
        (transport (blockAdj endRing) FL factoredLaw_lawful (fun _ => hopen)) w s).1 :=
  keeps_sufficient factoredLaw_lawful (fun _ => hopen)
    (fun _ hℓ => retained_rust_factored hS hR hℓ) q w s

/-! ## 5. The Rust's step is quiet on empty data -/

/-- [definition] **The certified step on a locus's factors** (`Constitution::deposited`, "The
certified step"): the factors move by a step `η` times the sum, over the edges that read the
locus and the data on each, of each datum's move `g` (the unit step `D = Σ_t w g_t (X̂ f_t)ᵀ` of a
normal law, `Δx = G_x / h_x′` of a factor family). The step `η` and the moves `g` are any functions
of the factors and the data. The Rust's `η` is the certified `2^k`, which also reads other loci, and
its moves read the locus's statistic or successor chart (module header [open]); the sum over no data
is zero whatever they read. -/
def certifiedStep {P : Type*} [AddCommGroup P] [Module ℝ P]
    (η : P → EdgeData endRing V Ch → ℝ)
    (g : P → (y z : Ring ⊕ Contact) →
      BlockM endRing V Ch z × Module.Dual ℝ (BlockM endRing V Ch y) → P)
    (p : P) (dat : EdgeData endRing V Ch) : P :=
  p + η p dat • ∑ y, ∑ z, ((dat y z).map (g p y z)).sum

omit [DecidableEq Ring] [DecidableEq Contact] [Fintype ρ] [∀ r, FiniteDimensional ℝ (V r)]
  [∀ a, FiniteDimensional ℝ (Ch a)] in
/-- [proved-derived; formal-checked] **The certified step keeps a locus no datum reaches**: on
empty data the sum is zero, whatever `η`. -/
theorem certifiedStep_quiet {P : Type*} [AddCommGroup P] [Module ℝ P]
    (η : P → EdgeData endRing V Ch → ℝ)
    (g : P → (y z : Ring ⊕ Contact) →
      BlockM endRing V Ch z × Module.Dual ℝ (BlockM endRing V Ch y) → P) (p : P) :
    certifiedStep η g p (fun _ _ => []) = p := by
  simp [certifiedStep]

variable
    {ηe : (r : Ring) → ElementFactors (V := V) (FE := FE) (ρ := ρ) r → EdgeData endRing V Ch → ℝ}
    {ge : (r : Ring) → ElementFactors (V := V) (FE := FE) (ρ := ρ) r → (y z : Ring ⊕ Contact) →
      BlockM endRing V Ch z × Module.Dual ℝ (BlockM endRing V Ch y) →
      ElementFactors (V := V) (FE := FE) (ρ := ρ) r}
    {ηc : (a : Contact) → ChannelFactors (Ch := Ch) (FC := FC) a → EdgeData endRing V Ch → ℝ}
    {gc : (a : Contact) → ChannelFactors (Ch := Ch) (FC := FC) a → (y z : Ring ⊕ Contact) →
      BlockM endRing V Ch z × Module.Dual ℝ (BlockM endRing V Ch y) →
      ChannelFactors (Ch := Ch) (FC := FC) a}

/-- The factored medium's law under the certified step. -/
local notation "CL" => factoredLaw (Cell := Cell) (Crib := Crib) h₀ cls openState ticks cross
  absorb ingestStep rekey (fun r => certifiedStep (ηe r) (ge r))
  (fun a => certifiedStep (ηc a) (gc a))

/-- [proved-derived; formal-checked] **On the factored medium under the certified step, a deposit
between words never reopens a released locus**, with no hypothesis on the steps or the moves. -/
theorem certified_released_stays_released
    {S R : Set (Ring ⊕ Contact)} (hopen : ∀ l m, SupportedIn (openState l m) S)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing) CL S)
    (h : StagedOff (blockAdj endRing) S R s.1) {ℓ : Locus Ring Contact}
    (hℓ : ¬ TickStanding.Retained (blockAdj endRing) CL S R ℓ) :
    FAgreeOn (frelease (TickStanding.Retained (blockAdj endRing) CL S R) s.1.loci.1)
      (Holonics.Foundation.Chronology.transportWord
        (transport (blockAdj endRing) CL factoredLaw_lawful (fun _ => hopen)) w
        ⟨retain (blockAdj endRing) CL S R s.1, retain_valid s.2⟩).1.loci.1 ℓ :=
  factored_released_stays_released (fun r p => certifiedStep_quiet (ηe r) (ge r) p)
    (fun a p => certifiedStep_quiet (ηc a) (gc a) p) hopen w s h hℓ

end Law

end Holonics.HNN.FactoredMedium

#print axioms Holonics.HNN.FactoredMedium.toMedium_admissible
#print axioms Holonics.HNN.FactoredMedium.toMedium_release
#print axioms Holonics.HNN.FactoredMedium.factoredLaw_lawful
#print axioms Holonics.HNN.FactoredMedium.factoredLaw_quiet
#print axioms Holonics.HNN.FactoredMedium.factoredStanding
#print axioms Holonics.HNN.FactoredMedium.factored_released_stays_released
#print axioms Holonics.HNN.FactoredMedium.retained_rust_factored
#print axioms Holonics.HNN.FactoredMedium.factored_rust_collapse_sufficient
#print axioms Holonics.HNN.FactoredMedium.certifiedStep_quiet
#print axioms Holonics.HNN.FactoredMedium.certified_released_stays_released
