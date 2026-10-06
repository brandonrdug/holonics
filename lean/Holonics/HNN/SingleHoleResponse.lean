import Holonics.HNN.LoadedMedium
import Holonics.HNN.TickFamily
import Holonics.Foundation.ReceiverRelease
import Mathlib.Tactic.Abel

/-!
# HNN.SingleHoleResponse: one shared source label through an absolute loaded word

[definition; bounded consumer of the accepted 6f536ac3 certificate] This file makes the exact
single-hole affine section explicit. The first-source terms keep the full first population
normalization; pair terms keep the full offset population normalization on each edge. The label
at the hole is the same `c` in every first term, pair endpoint, source port and offset. Each ordered
pair edge carries its own bilinear kernel `F e` and phase/lift placement `Q e`, so different source
rings and offsets retain their distinct `PairPort E_g^(δ)`. A pair edge has distinct endpoints, so
at most one endpoint is the hole. Consequently its one-hole term is linear in that shared label;
no independent endpoint labels and no quadratic hole term are introduced.

The source-side operands recover through `HNN.Moment.encoderMoment_add`,
`encoderMoment_contract`, `exteriorOffset_independent_of_E`, `Objects/SourcePorts.port_eq_symbol_sum`,
and `Objects/SourceHolon.offsetMomentAt`: first and ordered-pair source counts are already owned.
The expansion below specializes those terms to one missing station and explicit complete-population
normalizers. The physical consumer uses `HNN.LoadedMedium.loadedOp` at `openedAt + t`, over the full
loaded state. Only the actual source-to-state opening/injection and receiver chart are boundary
hypotheses: the current owners do not yet prove that Rust's `station_section`,
`PairPort::apply_table`, `PopulationChart::value`, and its rational carriers instantiate those
Lean operands. This file does not claim an exact rational-Rust to real-Lean embedding or a Lean
GrainCell implementation; those concrete joins remain open.

Computational object: the helical pair interaction. Winding objects touched: helix, pair,
navigator faces and placement, and tube. Cell holonomy and the tower thread remain attached.
Recorded failures this consumer is structured to avoid: dropping the shared-parameter cross terms
or using independently varied endpoints; using a static tick across a pump; releasing from a
coordinate enclosure that loses correlation; and treating model constancy as recovery of the
removed truth. The law here is exact linear/unit transport only, with no chart/lattice residual or
saturation premise hidden in the consumer.

No axiom, sorry or native_decide.
-/

noncomputable section

namespace Holonics.HNN.SingleHoleResponse

open scoped BigOperators

/-! ## 1. Constructive source expansion at one missing station -/

section Source

variable {K Station Label X W : Type*} [Field K]
  [Fintype Station] [DecidableEq Station]
  [Fintype Label] [DecidableEq Label]
  [AddCommGroup X] [Module K X]
  [AddCommGroup W] [Module K W]

/-- The completed station chart: every intact station keeps its declared class, and the one hole
is filled by the same admitted label `c`. -/
def completedCell (hole : Station) (known : Station → Label) (basis : Label → X)
    (c : Label) (s : Station) : X :=
  if s = hole then basis c else basis (known s)

/-- A first-port term after the source's carried phase/lift transport. `weight` includes the
normalization at the full first population, which is independent of `c`. -/
def firstCompleteTerm (hole : Station) (known : Station → Label) (basis : Label → X)
    (c : Label) (weight : K) (P : Station → X →ₗ[K] W) (s : Station) : W :=
  weight • P s (completedCell hole known basis c s)

/-- Known first-port contribution. The missing station contributes zero here. -/
def firstFixedTerm (hole : Station) (known : Station → Label) (basis : Label → X)
    (weight : K) (P : Station → X →ₗ[K] W) (s : Station) : W :=
  if s = hole then 0 else weight • P s (basis (known s))

/-- First-port response column. It is zero off the missing station. -/
def firstResponseTerm (hole : Station) (basis : Label → X) (c : Label)
    (weight : K) (P : Station → X →ₗ[K] W) (s : Station) : W :=
  if s = hole then weight • P s (basis c) else 0

/-- One complete first-source population, using its full class-independent normalization. -/
def firstComplete (hole : Station) (known : Station → Label) (basis : Label → X)
    (c : Label) (weight : K) (P : Station → X →ₗ[K] W) : W :=
  ∑ s, firstCompleteTerm hole known basis c weight P s

/-- The fixed first-source population. -/
def firstFixed (hole : Station) (known : Station → Label) (basis : Label → X)
    (weight : K) (P : Station → X →ₗ[K] W) : W :=
  ∑ s, firstFixedTerm hole known basis weight P s

/-- The first-source response at the shared label. -/
def firstResponse (hole : Station) (basis : Label → X) (c : Label)
    (weight : K) (P : Station → X →ₗ[K] W) : W :=
  ∑ s, firstResponseTerm hole basis c weight P s

/-- The pair-port term for one ordered offset edge. `F e` is that edge's existing bilinear pair
relation (which may differ at every ring/offset); `Q e` carries its output through the edge's
phase/lift placement. The edge is ordered as current endpoint, earlier endpoint. -/
def pairCompleteTerm (hole : Station) (known : Station → Label) (basis : Label → X)
    (c : Label) (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (weight : Station × Station → K) (e : Station × Station) : W :=
  weight e • Q e (F e (completedCell hole known basis c e.1)
    (completedCell hole known basis c e.2))

/-- Pair-port terms with both endpoints intact. -/
def pairFixedTerm (hole : Station) (known : Station → Label) (basis : Label → X)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (weight : Station × Station → K) (e : Station × Station) : W :=
  if e.1 = hole ∨ e.2 = hole then 0 else
    weight e • Q e (F e (basis (known e.1)) (basis (known e.2)))

/-- The correlated pair response: the same label supplies the unique missing endpoint, while the
other endpoint retains its known class. -/
def pairResponseTerm (hole : Station) (known : Station → Label) (basis : Label → X)
    (c : Label) (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (weight : Station × Station → K) (e : Station × Station) : W :=
  if e.1 = hole then
    weight e • Q e (F e (basis c) (basis (known e.2)) )
  else if e.2 = hole then
    weight e • Q e (F e (basis (known e.1)) (basis c))
  else 0

/-- All normalized pair-port terms for a completed source. -/
def pairComplete (edges : Finset (Station × Station)) (hole : Station)
    (known : Station → Label) (basis : Label → X) (c : Label)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (weight : Station × Station → K) : W :=
  ∑ e ∈ edges, pairCompleteTerm hole known basis c F Q weight e

/-- The normalized pair-port contribution whose endpoints are both intact. -/
def pairFixed (edges : Finset (Station × Station)) (hole : Station)
    (known : Station → Label) (basis : Label → X)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (weight : Station × Station → K) : W :=
  ∑ e ∈ edges, pairFixedTerm hole known basis F Q weight e

/-- The sum of the pair-port columns at the same missing label used by the first population. -/
def pairResponse (edges : Finset (Station × Station)) (hole : Station)
    (known : Station → Label) (basis : Label → X) (c : Label)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (weight : Station × Station → K) : W :=
  ∑ e ∈ edges, pairResponseTerm hole known basis c F Q weight e

/-- The complete source vector, with the class-independent first and offset normalizations
already included in `weight` and `weight e`. -/
def completeSource (edges : Finset (Station × Station)) (hole : Station)
    (known : Station → Label) (basis : Label → X) (c : Label) (firstWeight : K)
    (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W) (pairWeight : Station × Station → K) : W :=
  firstComplete hole known basis c firstWeight P +
    pairComplete edges hole known basis c F Q pairWeight

/-- The fixed source vector, including the intact first and offset populations. -/
def fixedSource (edges : Finset (Station × Station)) (hole : Station)
    (known : Station → Label) (basis : Label → X) (firstWeight : K)
    (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W) (pairWeight : Station × Station → K) : W :=
  firstFixed hole known basis firstWeight P +
    pairFixed edges hole known basis F Q pairWeight

/-- The full signed response column of one shared source label across first and pair ports. -/
def responseSource (edges : Finset (Station × Station)) (hole : Station)
    (known : Station → Label) (basis : Label → X) (c : Label) (firstWeight : K)
    (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W) (pairWeight : Station × Station → K) : W :=
  firstResponse hole basis c firstWeight P +
    pairResponse edges hole known basis c F Q pairWeight

/-- The full first population is exactly its intact population plus the one missing class term.
This is a termwise source identity, not a hypothesis that the desired completed-source equality
already holds. -/
theorem firstComplete_eq_fixed_add_response (hole : Station) (known : Station → Label)
    (basis : Label → X) (c : Label) (weight : K) (P : Station → X →ₗ[K] W) :
    firstComplete hole known basis c weight P =
      firstFixed hole known basis weight P + firstResponse hole basis c weight P := by
  change (∑ s, firstCompleteTerm hole known basis c weight P s) =
    (∑ s, firstFixedTerm hole known basis weight P s) +
      ∑ s, firstResponseTerm hole basis c weight P s
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : s = hole <;>
    simp [firstCompleteTerm, firstFixedTerm, firstResponseTerm, completedCell, h]

/-- A pair edge with distinct endpoints has exactly one of three cases: both known, hole at its
current endpoint, or hole at its earlier endpoint. The two one-hole cases use the same label `c`.
The existing bilinear pair port is consumed before any receiver projection. -/
theorem pairComplete_eq_fixed_add_response (edges : Finset (Station × Station))
    (hole : Station) (known : Station → Label) (basis : Label → X) (c : Label)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (weight : Station × Station → K)
    (hedges : ∀ e ∈ edges, e.1 ≠ e.2) :
    pairComplete edges hole known basis c F Q weight =
      pairFixed edges hole known basis F Q weight +
        pairResponse edges hole known basis c F Q weight := by
  change (∑ e ∈ edges, pairCompleteTerm hole known basis c F Q weight e) =
    (∑ e ∈ edges, pairFixedTerm hole known basis F Q weight e) +
      ∑ e ∈ edges, pairResponseTerm hole known basis c F Q weight e
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have hd := hedges e he
  by_cases hs : e.1 = hole
  · have ht : e.2 ≠ hole := by
      intro ht
      exact hd (hs.trans ht.symm)
    simp [pairCompleteTerm, pairFixedTerm, pairResponseTerm, completedCell, hs, ht]
  · by_cases ht : e.2 = hole
    · simp [pairCompleteTerm, pairFixedTerm, pairResponseTerm, completedCell, hs, ht]
    · simp [pairCompleteTerm, pairFixedTerm, pairResponseTerm, completedCell, hs, ht]

/-- **Constructive one-hole source expansion** consumed by the physical consumer. The known
first/offset populations and the shared signed response are separated by expansion of the actual
first terms and bilinear pair-port terms. -/
theorem oneHoleSourceExpansion (edges : Finset (Station × Station))
    (hole : Station) (known : Station → Label) (basis : Label → X) (c : Label)
    (firstWeight : K) (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (pairWeight : Station × Station → K)
    (hedges : ∀ e ∈ edges, e.1 ≠ e.2) :
    completeSource edges hole known basis c firstWeight P F Q pairWeight =
      fixedSource edges hole known basis firstWeight P F Q pairWeight +
        responseSource edges hole known basis c firstWeight P F Q pairWeight := by
  unfold completeSource fixedSource responseSource
  rw [firstComplete_eq_fixed_add_response hole known basis c firstWeight P,
    pairComplete_eq_fixed_add_response edges hole known basis c F Q pairWeight hedges]
  abel

/-- Population-normalized single-hole form. The first population keeps `ν(N)` for every completion,
and an ordered edge at offset `δ` keeps `ν(max(N−δ,0))`; natural subtraction is saturating, exactly
as in the accepted source law. Neither normalization is recomputed from the observed sparse counts. -/
theorem populationNormalizedOneHoleSourceExpansion
    (edges : Finset (Station × Station)) (hole : Station) (known : Station → Label)
    (basis : Label → X) (c : Label) (N : ℕ)
    (offset : Station × Station → ℕ) (ν : ℕ → K)
    (hN : N = Fintype.card Station)
    (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (hedges : ∀ e ∈ edges, e.1 ≠ e.2) :
    completeSource edges hole known basis c (ν (Fintype.card Station)) P F Q
        (fun e => ν (Fintype.card Station - offset e)) =
      fixedSource edges hole known basis (ν (Fintype.card Station)) P F Q
          (fun e => ν (Fintype.card Station - offset e)) +
        responseSource edges hole known basis c (ν (Fintype.card Station)) P F Q
          (fun e => ν (Fintype.card Station - offset e)) := by
  simpa [hN] using
    (oneHoleSourceExpansion edges hole known basis c (ν N) P F Q
      (fun e => ν (N - offset e)) hedges)

end Source

/-! ## 2. The same response through the actual absolute loaded tick family -/

section LoadedConsumer

open Holonics.HNN.LoadedMedium
open Holonics.HNN.TickFamily
open Holonics.HNN.Propagation

variable {Ring Contact : Type*} [Fintype Ring] [Fintype Contact]
  [DecidableEq Ring] [DecidableEq Contact]
variable {endRing : Contact × Bool → Ring}
variable {V : Ring → Type*} [∀ r, NormedAddCommGroup (V r)]
  [∀ r, InnerProductSpace ℝ (V r)]
variable {Ch : Contact → Type*} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)]
variable {adj : Ring ⊕ Contact → Ring ⊕ Contact → Prop}

abbrev LoadedState := (b : Ring ⊕ Contact) → LoadedM endRing V Ch b

/-- Source responses change ring storage only. Their arriving waves, contact displacement/rate and
resonator positions/rates are zero; the fixed entered state supplies all such interior operands. -/
def SourceResponseShape (x : LoadedState (endRing := endRing) (V := V) (Ch := Ch)) : Prop :=
  (∀ g, (x (.inl g)).1.2 = 0 ∧ (x (.inl g)).2 = (0, 0)) ∧
    ∀ a, (x (.inr a)).1 = 0

/-- The actual loaded full-block operator at the word's absolute opened tick. Each step therefore
uses the resonator pump phase at `openedAt + t`, as owned by `LoadedMedium.loadedOp`. -/
def absoluteLoadedFamily (T : BlockOp ℝ (BlockM endRing V Ch))
    (res : (g : Ring) → ResOp (V g)) (h : ℝ) (openedAt : ℕ) :
    ℕ → BlockOp ℝ (LoadedM endRing V Ch) :=
  fun t => loadedOp T res h (openedAt + t)

private theorem tick_add_loaded (T : BlockOp ℝ (LoadedM endRing V Ch))
    (x y : LoadedState (endRing := endRing) (V := V) (Ch := Ch)) :
    tick T (x + y) = tick T x + tick T y := by
  funext b
  simp only [tick, Pi.add_apply, map_add, Finset.sum_add_distrib]

/-- A tick-indexed block word is additive in its full opening state. -/
theorem trajectoryAt_add_loaded (T : ℕ → BlockOp ℝ (LoadedM endRing V Ch))
    (x y : LoadedState (endRing := endRing) (V := V) (Ch := Ch)) (t : ℕ) :
    trajectoryAt T (x + y) t = trajectoryAt T x t + trajectoryAt T y t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [trajectoryAt, ih]
      exact tick_add_loaded (T t) _ _

/-- The loaded response identity at its concrete owner: `loadedOp` is evaluated at each actual
absolute tick `openedAt + k`, over storage, arrivals, contact states and resonator `(u,w)` alike. -/
theorem absoluteLoaded_response_add (T : BlockOp ℝ (BlockM endRing V Ch))
    (res : (g : Ring) → ResOp (V g)) (h : ℝ) (openedAt t : ℕ)
    (anchor response : LoadedState (endRing := endRing) (V := V) (Ch := Ch)) :
    trajectoryAt (absoluteLoadedFamily T res h openedAt) (anchor + response) t =
      trajectoryAt (absoluteLoadedFamily T res h openedAt) anchor t +
        trajectoryAt (absoluteLoadedFamily T res h openedAt) response t :=
  trajectoryAt_add_loaded (absoluteLoadedFamily T res h openedAt) anchor response t

/-- Full-state normalized source-opening bridge. `N` is certified as the station population;
each response is injected into storage only, with zero arrivals, contacts and resonator state. -/
theorem openedState_from_normalized_source
    {K Station Label X W : Type*} [Field K] [Fintype Station] [DecidableEq Station]
    [Fintype Label] [DecidableEq Label] [AddCommGroup X] [Module K X]
    [AddCommGroup W] [Module K W] [Module ℝ W]
    (edges : Finset (Station × Station)) (hole : Station) (known : Station → Label)
    (basis : Label → X) (N : ℕ) (offset : Station × Station → ℕ) (ν : ℕ → K)
    (hN : N = Fintype.card Station) (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (hedges : ∀ e ∈ edges, e.1 ≠ e.2)
    (sourceInjection : W →ₗ[ℝ] LoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (enteredInterior : LoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (openComplete : Label → LoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (hresponseShape : ∀ c, SourceResponseShape
      (sourceInjection (responseSource edges hole known basis c (ν N) P F Q
        (fun e => ν (N - offset e)))))
    (hopen : ∀ c, openComplete c = enteredInterior +
      sourceInjection (completeSource edges hole known basis c (ν N) P F Q
        (fun e => ν (N - offset e)))) :
    (∀ c, openComplete c =
      (enteredInterior + sourceInjection
        (fixedSource edges hole known basis (ν (Fintype.card Station)) P F Q
          (fun e => ν (Fintype.card Station - offset e)))) +
      sourceInjection (responseSource edges hole known basis c (ν (Fintype.card Station)) P F Q
        (fun e => ν (Fintype.card Station - offset e)))) ∧
    (∀ c, SourceResponseShape
      (sourceInjection (responseSource edges hole known basis c (ν (Fintype.card Station)) P F Q
        (fun e => ν (Fintype.card Station - offset e)))) := by
  have hsplit (c : Label) := populationNormalizedOneHoleSourceExpansion edges hole known basis c
    (Fintype.card Station) offset ν rfl P F Q hedges
  have hopen' (c : Label) : openComplete c = enteredInterior +
      sourceInjection (completeSource edges hole known basis c (ν (Fintype.card Station)) P F Q
        (fun e => ν (Fintype.card Station - offset e))) := by
    simpa [hN] using hopen c
  constructor
  · intro c
    rw [hopen' c, hsplit c]
    simp only [map_add, add_assoc]
  · intro c
    simpa [hN] using hresponseShape c

/-- The receiver reads the fixed-plus-same-label response after the tick-indexed loaded physical
word. The only caller bridge is `hopen`, which relates the native source opening to the constructive
first/offset expansion above. -/
theorem loadedReceiving_response
    {Label Y : Type*} [Fintype Label] [DecidableEq Label]
    [AddCommGroup Y] [Module ℝ Y]
    (T : BlockOp ℝ (BlockM endRing V Ch)) (res : (g : Ring) → ResOp (V g))
    (h : ℝ) (openedAt t : ℕ)
    (openedState : Label → LoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (anchor : LoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (response : Label → LoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (hopen : ∀ c, openedState c = anchor + response c)
    (receiver : LoadedState (endRing := endRing) (V := V) (Ch := Ch) →ₗ[ℝ] Y) :
    ∀ c, receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt) (openedState c) t) =
      receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt) anchor t) +
        receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt) (response c) t) := by
  intro c
  rw [hopen c, absoluteLoaded_response_add]
  exact map_add receiver _ _

end LoadedConsumer

/-! ## 3. Exact finite leader union and receiver-relative constant release -/

section GrainAndRelease

variable {Completion Class : Type*} [Fintype Completion] [DecidableEq Completion]
  [Fintype Class] [DecidableEq Class]

/-- A completion's exact greatest face, supplied with its exact maximum value. This leaves the
receiving GrainCell chart explicit: callers must identify this rational ordered face with their
actual chart before using the theorem. -/
def exactLeaders (reading : Class → ℚ) (greatest : ℚ) : Finset Class :=
  Finset.univ.filter fun c => reading c = greatest

/-- The compatible completed-model leaders are the union of the exact leader faces of each
completion. -/
def exactLeaderUnion (reading : Completion → Class → ℚ) (greatest : Completion → ℚ)
    (compatible : Finset Completion) : Finset Class :=
  compatible.biUnion fun x => exactLeaders (reading x) (greatest x)

/-- Exact finite leader-union soundness: every published class is a greatest class for an admitted
completion, and every such greatest class is published. Ties are retained as a set. -/
theorem exactLeaderUnion_mem_iff (reading : Completion → Class → ℚ)
    (greatest : Completion → ℚ) (compatible : Finset Completion) (c : Class) :
    c ∈ exactLeaderUnion reading greatest compatible ↔
      ∃ x ∈ compatible, reading x c = greatest x := by
  simp [exactLeaderUnion, exactLeaders]

/-- With a certified exact maximum for each completed reading, the union contains precisely the
greatest classes for admitted completions. The certificate preserves tied leaders. -/
theorem exactLeaderUnion_sound (reading : Completion → Class → ℚ)
    (greatest : Completion → ℚ) (compatible : Finset Completion)
    (hmaximum : ∀ x ∈ compatible,
      (∀ c, reading x c ≤ greatest x) ∧ ∃ c, reading x c = greatest x) :
    ∀ c, c ∈ exactLeaderUnion reading greatest compatible ↔
      ∃ x ∈ compatible, (∀ j, reading x j ≤ greatest x) ∧ reading x c = greatest x := by
  intro c
  rw [exactLeaderUnion_mem_iff]
  constructor
  · rintro ⟨x, hx, hread⟩
    exact ⟨x, hx, (hmaximum x hx).1, hread⟩
  · rintro ⟨x, hx, _, hread⟩
    exact ⟨x, hx, hread⟩

/-- A constant exact scalar receiving face has zero width over its compatible finite family and is
releasable at tolerance zero under the existing receiver law. -/
theorem constant_face_released_at_zero
    (compatible : Finset Completion) (hcompat : compatible.Nonempty)
    (reading : Completion → ℚ)
    (hconstant : ∀ x ∈ compatible, ∀ y ∈ compatible, reading x = reading y) :
    Holonics.Foundation.ReceiverRelease.Releasable compatible hcompat reading 0 := by
  change Holonics.Foundation.ReceiverRelease.width compatible hcompat reading ≤ 0
  have hz : Holonics.Foundation.ReceiverRelease.width compatible hcompat reading = 0 :=
    (Holonics.Foundation.ReceiverRelease.width_eq_zero_iff compatible hcompat reading).2 hconstant
  rw [hz]
  exact le_rfl

/-- The declared holding law actually releases this constant receiver face at tolerance zero. -/
theorem holdingLaw_releases_constant_face_at_zero
    (compatible : Finset Completion) (hcompat : compatible.Nonempty)
    (reading : Completion → ℚ)
    (hconstant : ∀ x ∈ compatible, ∀ y ∈ compatible, reading x = reading y) :
    (Holonics.Foundation.ReceiverRelease.holdingLaw Completion Unit Unit 0).decide
      compatible hcompat reading =
        Holonics.Foundation.ReceiverRelease.ReleaseReturn.released := by
  have hz : Holonics.Foundation.ReceiverRelease.width compatible hcompat reading = 0 :=
    (Holonics.Foundation.ReceiverRelease.width_eq_zero_iff compatible hcompat reading).2 hconstant
  simp [Holonics.Foundation.ReceiverRelease.holdingLaw, hz]

/-- If the union of exact completed-model leader faces is the singleton `{winner}`, every emitted
leader agrees with that same class. Its exact class reading is therefore released at tolerance
zero by the existing holding law. -/
theorem singletonLeader_holdingLaw_release
    (compatible : Finset Completion) (hcompat : compatible.Nonempty)
    (reading : Completion → Class → ℚ) (greatest : Completion → ℚ)
    (winner : Class) (hunionsingle : exactLeaderUnion reading greatest compatible = {winner})
    (emit : Completion → Class)
    (hemits : ∀ x ∈ compatible, emit x ∈ exactLeaders (reading x) (greatest x))
    (classReading : Class → ℚ) :
    (Holonics.Foundation.ReceiverRelease.holdingLaw Completion Unit Unit 0).decide
      compatible hcompat (fun x => classReading (emit x)) =
        Holonics.Foundation.ReceiverRelease.ReleaseReturn.released := by
  apply holdingLaw_releases_constant_face_at_zero
  intro x hx y hy
  have hxUnion : emit x ∈ exactLeaderUnion reading greatest compatible := by
    rw [exactLeaderUnion_mem_iff]
    exact ⟨x, hx, (Finset.mem_filter.mp (hemits x hx)).2⟩
  have hyUnion : emit y ∈ exactLeaderUnion reading greatest compatible := by
    rw [exactLeaderUnion_mem_iff]
    exact ⟨y, hy, (Finset.mem_filter.mp (hemits y hy)).2⟩
  have hxWinner : emit x = winner := by
    rw [hunionsingle] at hxUnion
    simpa using hxUnion
  have hyWinner : emit y = winner := by
    rw [hunionsingle] at hyUnion
    simpa using hyUnion
  rw [hxWinner, hyWinner]

end GrainAndRelease

/-! ## 4. Composed normalized source, opening, absolute word, receiver and grain face -/

section EndToEnd

open Holonics.HNN.LoadedMedium
open Holonics.HNN.TickFamily
open Holonics.HNN.Propagation

variable {Ring Contact : Type*} [Fintype Ring] [Fintype Contact]
  [DecidableEq Ring] [DecidableEq Contact]
variable {endRing : Contact × Bool → Ring}
variable {V : Ring → Type*} [∀ r, NormedAddCommGroup (V r)]
  [∀ r, InnerProductSpace ℝ (V r)]
variable {Ch : Contact → Type*} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)]

abbrev EndToEndLoadedState := (b : Ring ⊕ Contact) → LoadedM endRing V Ch b

/-- The fixed, fully normalized source after the retained interior has been entered. -/
def normalizedSourceAnchor
    {K Station Label X W : Type*} [Field K] [Fintype Station] [DecidableEq Station]
    [Fintype Label] [DecidableEq Label] [AddCommGroup X] [Module K X]
    [AddCommGroup W] [Module K W] [Module ℝ W]
    (edges : Finset (Station × Station)) (hole : Station) (known : Station → Label)
    (basis : Label → X) (offset : Station × Station → ℕ) (ν : ℕ → K)
    (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (entered : EndToEndLoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (inject : W →ₗ[ℝ] EndToEndLoadedState (endRing := endRing) (V := V) (Ch := Ch)) :=
  entered + inject (fixedSource edges hole known basis (ν (Fintype.card Station)) P F Q
    (fun e => ν (Fintype.card Station - offset e)))

/-- The common-label source response injected at a selected missing station. -/
def normalizedSourceResponse
    {K Station Label X W : Type*} [Field K] [Fintype Station] [DecidableEq Station]
    [Fintype Label] [DecidableEq Label] [AddCommGroup X] [Module K X]
    [AddCommGroup W] [Module K W] [Module ℝ W]
    (edges : Finset (Station × Station)) (hole : Station) (known : Station → Label)
    (basis : Label → X) (offset : Station × Station → ℕ) (ν : ℕ → K) (c : Label)
    (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (inject : W →ₗ[ℝ] EndToEndLoadedState (endRing := endRing) (V := V) (Ch := Ch)) :=
  inject (responseSource edges hole known basis c (ν (Fintype.card Station)) P F Q
    (fun e => ν (Fintype.card Station - offset e)))

/-- End-to-end theorem for the accepted exact one-hole domain. It derives the anchor and shared
label response from the normalized source expansion and the retained full-state opening, advances
both through `LoadedMedium.loadedOp` at `openedAt + k`, reads the linear receiver, transports the
result through an explicit GrainCell face map, and releases a singleton exact leader union at zero
tolerance. `score ∘ grainCell` is supplied by the receiver chart; it is never identified with raw
coordinates of the linear receiver. -/
theorem normalizedSource_loadedWord_grain_singleton_release
    {K Station Label X W Y Grain Class : Type*} [Field K]
    [Fintype Station] [DecidableEq Station] [Fintype Label] [DecidableEq Label]
    [Fintype Class] [DecidableEq Class] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module ℝ Y]
    [AddCommGroup W] [Module K W] [Module ℝ W]
    (edges : Finset (Station × Station)) (hole : Station) (known : Station → Label)
    (basis : Label → X) (N : ℕ) (offset : Station × Station → ℕ) (ν : ℕ → K)
    (hN : N = Fintype.card Station) (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W) (hedges : ∀ e ∈ edges, e.1 ≠ e.2)
    (sourceInjection : W →ₗ[ℝ] EndToEndLoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (enteredInterior : EndToEndLoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (openComplete : Label → EndToEndLoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (hresponseShape : ∀ c, SourceResponseShape
      (sourceInjection (responseSource edges hole known basis c (ν N) P F Q
        (fun e => ν (N - offset e)))))
    (hopen : ∀ c, openComplete c = enteredInterior +
      sourceInjection (completeSource edges hole known basis c (ν N) P F Q
        (fun e => ν (N - offset e))))
    (T : BlockOp ℝ (BlockM endRing V Ch)) (res : (g : Ring) → ResOp (V g))
    (h : ℝ) (openedAt ticks : ℕ)
    (receiver : EndToEndLoadedState (endRing := endRing) (V := V) (Ch := Ch) →ₗ[ℝ] Y)
    (grainCell : Y → Grain) (score : Grain → Class → ℚ)
    (reading : Label → Class → ℚ)
    (hreading : reading = fun c j => score (grainCell (receiver (trajectoryAt
      (absoluteLoadedFamily T res h openedAt)
      (normalizedSourceAnchor edges hole known basis offset ν P F Q enteredInterior sourceInjection +
        normalizedSourceResponse edges hole known basis offset ν c P F Q sourceInjection) ticks))) j)
    (greatest : Label → ℚ) (compatible : Finset Label) (hcompatible : compatible.Nonempty)
    (winner : Class)
    (hunion : exactLeaderUnion reading greatest compatible = {winner})
    (hmaximum : ∀ c ∈ compatible,
      (∀ j, reading c j ≤ greatest c) ∧ ∃ j, reading c j = greatest c)
    (emit : Label → Class)
    (hemits : ∀ c ∈ compatible, emit c ∈ exactLeaders (reading c) (greatest c))
    (classReading : Class → ℚ) :
    (∀ c, SourceResponseShape
      (sourceInjection (responseSource edges hole known basis c
        (ν (Fintype.card Station)) P F Q
        (fun e => ν (Fintype.card Station - offset e))))) ∧
    (∀ c, receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
        (openComplete c) ticks) =
      receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
        (enteredInterior + sourceInjection
          (fixedSource edges hole known basis (ν (Fintype.card Station)) P F Q
            (fun e => ν (Fintype.card Station - offset e)))) ticks) +
        receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
          (sourceInjection (responseSource edges hole known basis c
            (ν (Fintype.card Station)) P F Q
            (fun e => ν (Fintype.card Station - offset e)))) ticks)) ∧
    (∀ c, grainCell (receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
        (openComplete c) ticks)) =
      grainCell (receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
        (enteredInterior + sourceInjection
          (fixedSource edges hole known basis (ν (Fintype.card Station)) P F Q
            (fun e => ν (Fintype.card Station - offset e)))) ticks) +
        receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
          (sourceInjection (responseSource edges hole known basis c
            (ν (Fintype.card Station)) P F Q
            (fun e => ν (Fintype.card Station - offset e)))) ticks)) ∧
    (Holonics.Foundation.ReceiverRelease.holdingLaw Label Unit Unit 0).decide
      compatible hcompatible (fun c => classReading (emit c)) =
        Holonics.Foundation.ReceiverRelease.ReleaseReturn.released := by
  have hopened := openedState_from_normalized_source edges hole known basis N offset ν hN P F Q
    hedges sourceInjection enteredInterior openComplete hresponseShape hopen
  let anchor := enteredInterior + sourceInjection
    (fixedSource edges hole known basis (ν (Fintype.card Station)) P F Q
      (fun e => ν (Fintype.card Station - offset e)))
  let response : Label → EndToEndLoadedState (endRing := endRing) (V := V) (Ch := Ch) :=
    fun c => sourceInjection (responseSource edges hole known basis c
      (ν (Fintype.card Station)) P F Q (fun e => ν (Fintype.card Station - offset e)))
  have hread := loadedReceiving_response T res h openedAt ticks openComplete anchor response
    hopened.1 receiver
  have hcomputed (c : Label) :
      receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
        (openComplete c) ticks) =
      receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
        (anchor + response c) ticks) := by
    calc
      receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
          (openComplete c) ticks) =
        receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt) anchor ticks) +
          receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt) (response c) ticks) :=
            hread c
      _ = receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
          (anchor + response c) ticks) := by
        rw [absoluteLoaded_response_add, map_add]
  have hfaceAdd (c : Label) := congrArg grainCell (hread c)
  have hreadingFull : (fun c j => score (grainCell (receiver (trajectoryAt
      (absoluteLoadedFamily T res h openedAt) (openComplete c) ticks)) j)) = reading := by
    rw [hreading]
    funext c j
    exact congrArg (fun z => score (grainCell z) j) (hcomputed c)
  have hunionFull : exactLeaderUnion
      (fun c => score (grainCell (receiver (trajectoryAt
        (absoluteLoadedFamily T res h openedAt) (openComplete c) ticks)))) greatest compatible =
      {winner} := by
    rw [hreadingFull]
    exact hunion
  have hmaximumFull : ∀ c ∈ compatible,
      (∀ j, score (grainCell (receiver (trajectoryAt
        (absoluteLoadedFamily T res h openedAt) (openComplete c) ticks)) j) ≤ greatest c) ∧
      ∃ j, score (grainCell (receiver (trajectoryAt
        (absoluteLoadedFamily T res h openedAt) (openComplete c) ticks)) j) = greatest c := by
    intro c hc
    have hrc : (fun j => score (grainCell (receiver (trajectoryAt
        (absoluteLoadedFamily T res h openedAt) (openComplete c) ticks)) j)) = reading c :=
      congrFun hreadingFull c
    rcases hmaximum c hc with ⟨hle, hex⟩
    constructor
    · intro j
      rw [congrFun hrc j]
      exact hle j
    · obtain ⟨j, hj⟩ := hex
      exact ⟨j, by rw [congrFun hrc j]; exact hj⟩
  have hemitsFull : ∀ c ∈ compatible, emit c ∈ exactLeaders
      (fun j => score (grainCell (receiver (trajectoryAt
        (absoluteLoadedFamily T res h openedAt) (openComplete c) ticks)) j)) (greatest c) := by
    intro c hc
    have hrc : (fun j => score (grainCell (receiver (trajectoryAt
        (absoluteLoadedFamily T res h openedAt) (openComplete c) ticks)) j)) = reading c :=
      congrFun hreadingFull c
    change emit c ∈ Finset.univ.filter
      (fun j => score (grainCell (receiver (trajectoryAt
        (absoluteLoadedFamily T res h openedAt) (openComplete c) ticks)) j) = greatest c)
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_univ _
    · rw [congrFun hrc (emit c)]
      exact (Finset.mem_filter.mp (hemits c hc)).2
  have hsound := exactLeaderUnion_sound
    (fun c => score (grainCell (receiver (trajectoryAt
      (absoluteLoadedFamily T res h openedAt) (openComplete c) ticks)))) greatest compatible
    hmaximumFull
  have hfromSound (c : Label) (hc : c ∈ compatible) :
      emit c ∈ exactLeaderUnion
        (fun x => score (grainCell (receiver (trajectoryAt
          (absoluteLoadedFamily T res h openedAt) (openComplete x) ticks)))) greatest compatible := by
    apply (hsound (emit c)).2
    refine ⟨c, hc, (hmaximumFull c hc).1, ?_⟩
    exact (Finset.mem_filter.mp (hemitsFull c hc)).2
  have hconstant : ∀ c ∈ compatible, ∀ d ∈ compatible,
      classReading (emit c) = classReading (emit d) := by
    intro c hc d hd
    have hcWinner : emit c = winner := by
      have hx := hfromSound c hc
      rw [hunionFull] at hx
      simpa using hx
    have hdWinner : emit d = winner := by
      have hy := hfromSound d hd
      rw [hunionFull] at hy
      simpa using hy
    rw [hcWinner, hdWinner]
  refine ⟨hopened.2, ?_, ?_, ?_⟩
  · intro c
    exact hread c
  · intro c
    exact hfaceAdd c
  · exact holdingLaw_releases_constant_face_at_zero compatible hcompatible
      (fun c => classReading (emit c)) hconstant

end EndToEnd

end Holonics.HNN.SingleHoleResponse

#print axioms Holonics.HNN.SingleHoleResponse.firstComplete_eq_fixed_add_response
#print axioms Holonics.HNN.SingleHoleResponse.pairComplete_eq_fixed_add_response
#print axioms Holonics.HNN.SingleHoleResponse.oneHoleSourceExpansion
#print axioms Holonics.HNN.SingleHoleResponse.populationNormalizedOneHoleSourceExpansion
#print axioms Holonics.HNN.SingleHoleResponse.absoluteLoaded_response_add
#print axioms Holonics.HNN.SingleHoleResponse.openedState_from_normalized_source
#print axioms Holonics.HNN.SingleHoleResponse.loadedReceiving_response
#print axioms Holonics.HNN.SingleHoleResponse.exactLeaderUnion_mem_iff
#print axioms Holonics.HNN.SingleHoleResponse.exactLeaderUnion_sound
#print axioms Holonics.HNN.SingleHoleResponse.constant_face_released_at_zero
#print axioms Holonics.HNN.SingleHoleResponse.holdingLaw_releases_constant_face_at_zero
#print axioms Holonics.HNN.SingleHoleResponse.singletonLeader_holdingLaw_release
#print axioms Holonics.HNN.SingleHoleResponse.normalizedSource_loadedWord_grain_singleton_release
