import Holonics.Transport.SourceMoment
import Holonics.Foundation.Standing
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Source ports: phase-weighted edge ports, their symbols, and anchor separability

[definition] Objects 3 and 8 of `docs/ELEMENTARY_OBJECTS.md`, the formal side of the native
source-port laws (`incident/machine_source_contacts.rs`, reviewer defect A3). Over a commutative
ring `R`: modules `V`, `W`, a linear phase `L : V → V`, an injection `I : W → V`, a word
`u : ℕ → A` of length `N` over a finite alphabet and an encoder `E : A → W`. Position `t` carries
the phase weight `L^(N−1−t)`. [agent-inferred] The word is indexed by `ℕ` with a declared length
`N` rather than `Fin N`, so that offset edge sets are `Finset (ℕ × ℕ)` images of `range`; entries
at positions `≥ N` are never read.

[proved-derived; formal-checked] What is proved.

(a) **Port = symbol sum.** For an edge set `p` of pairs `(f, t)`,
    `Σ_(f,t)∈p L^(N−1−t) I (E(u_t) − E(u_f)) = Σ_a D_(p,a) I E(a)` with
    `D_(p,a) = Σ_(u_t=a) L^(N−1−t) − Σ_(u_f=a) L^(N−1−t)` (`port_eq_symbol_sum`). The offset port
    is `offsetEdges N δ = {(k, k+δ)}` (`port_offsetEdges`, `portSymbol_offsetEdges`). At `L = 1`
    it telescopes to its ends, `I(Σ_(k≥N−δ) E(u_k) − Σ_(k<δ) E(u_k))`
    (`offset_port_identity_telescopes`) — the A3 collision. Witness: under the quarter turn
    with `a ↦ 0`, `b ↦ (1,0)`, `c ↦ (0,1)`, the offset-1 ports of `abca` and `acba` are
    `(−2,−2)` and `0`, while at `L = 1` both are the endpoint term `0`
    (`quarter_turn_port_witness`): the phase separates what the identity merges, and the
    port is not its endpoints.
(b) **Transpose and standing.** `m = Σ_a C_a I E(a)` with `C_a = Σ_(u_k=a) L^(N−1−k)`
    (`moment_eq_symbol_sum`); for every covector `g`, `g(Σ_a D_a I E(a)) = Σ_a (I* D_a* g)(E a)`
    and likewise for `C` (`port_transpose`, `moment_transpose`, via `dualMap`). The symbols
    `(C, D)` — `2|A|` endomorphisms, fixed in `N` and intrinsic to the word — together with the
    anchor reading `L^N q₀` are a `Standing.StandingLaw` whose sources are passages (word,
    contemporary anchor `q₀`), whose generator re-anchors the passage at a new contemporary
    standing, and whose receivers are every encoder `E` with covectors on the state
    `L^N q₀ + m` and on the port (`symbolStanding`; sufficiency uses (a)/(b)). This matches the
    native law: the contemporary standing enters only through the anchor, never by advancing `C`.
    Witnesses: `abca ≠ acba` have equal symbols at identity phase
    (`identity_phase_equal_symbols`); under the quarter turn a reading with encoder `abc`
    separates them, so their symbols differ (`quarter_turn_symbols_separate`).
(c) **Anchor separability.** For `U q = L q + τ` and `q_(k+1) = U q_k + I E(u_k)`,
    `q_N = U^N q₀ + Σ_k L^(N−1−k) I E(u_k)` (`stepped_eq_anchor_add_moment`); the moment does
    not depend on `q₀`; `U^N q₀ − U^N q₀' = L^N (q₀ − q₀')` (`iterate_affine_sub`); and for a
    linear reading `F`, `F(q_N) − F(q_N') = (L^N)* F (q₀ − q₀')` (`anchor_covector`).

[open] The same statements for a nonlinear reading via `fderiv`, and ports between distinct rings
with distinct clocks.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Objects.SourcePorts

open Holonics
open Holonics.Foundation.Chronology
open Holonics.Foundation.Standing
open Holonics.Transport.SourceMoment

variable {R : Type*} [CommRing R]
variable {V W A : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [Fintype A] [DecidableEq A]

/-! ## (a) The phase-weighted port and its symbol sums -/

section Port

variable (L : V →ₗ[R] V) (I : W →ₗ[R] V) (N : ℕ) (u : ℕ → A) (E : A → W)

/-- [definition] The phase weight of position `t`: `L^(N−1−t)`. -/
def weight (t : ℕ) : Module.End R V := L ^ (N - 1 - t)

/-- [definition] **The phase-weighted port** of an edge set `p` of position pairs `(f, t)`:
`Σ_(f,t)∈p L^(N−1−t) I (E(u_t) − E(u_f))`. -/
def port (p : Finset (ℕ × ℕ)) : V :=
  ∑ e ∈ p, weight L N e.2 (I (E (u e.2) - E (u e.1)))

/-- [definition] The port symbol `D_(p,a) = Σ_(u_t = a) L^(N−1−t) − Σ_(u_f = a) L^(N−1−t)`. -/
def portSymbol (p : Finset (ℕ × ℕ)) (a : A) : Module.End R V :=
  (∑ e ∈ p with u e.2 = a, weight L N e.2) - ∑ e ∈ p with u e.1 = a, weight L N e.2

/-- [definition] The moment `m = Σ_(k<N) L^(N−1−k) I E(u_k)`. -/
def moment : V := ∑ k ∈ Finset.range N, weight L N k (I (E (u k)))

/-- [definition] The moment symbol `C_a = Σ_(k<N, u_k = a) L^(N−1−k)`. -/
def momentSymbol (a : A) : Module.End R V :=
  ∑ k ∈ Finset.range N with u k = a, weight L N k

theorem sum_by_symbol {ι : Type*} (s : Finset ι) (sel : ι → ℕ) (w : ι → Module.End R V) :
    ∑ i ∈ s, w i (I (E (u (sel i)))) =
      ∑ a, (∑ i ∈ s with u (sel i) = a, w i) (I (E a)) := by
  rw [← Finset.sum_fiberwise s (fun i => u (sel i))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

/-- [proved-derived; formal-checked] **The port is a symbol sum**:
`port p = Σ_a D_(p,a) I E(a)`. -/
theorem port_eq_symbol_sum (p : Finset (ℕ × ℕ)) :
    port L I N u E p = ∑ a, portSymbol L N u p a (I (E a)) := by
  have h1 := sum_by_symbol I u E p Prod.snd (fun e => weight L N e.2)
  have h2 := sum_by_symbol I u E p Prod.fst (fun e => weight L N e.2)
  simp only [port, portSymbol, map_sub, Finset.sum_sub_distrib, LinearMap.sub_apply, h1, h2]

/-- [proved-derived; formal-checked] **The moment is a symbol sum**: `m = Σ_a C_a I E(a)`. -/
theorem moment_eq_symbol_sum :
    moment L I N u E = ∑ a, momentSymbol L N u a (I (E a)) :=
  sum_by_symbol I u E (Finset.range N) id (weight L N)

/-- [definition] The offset edge set `{(k, k+δ) | k + δ < N}`. -/
def offsetEdges (δ : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N - δ)).image fun k => (k, k + δ)

omit [Fintype A] [DecidableEq A] in
theorem port_offsetEdges (δ : ℕ) :
    port L I N u E (offsetEdges N δ) =
      ∑ k ∈ Finset.range (N - δ), weight L N (k + δ) (I (E (u (k + δ)) - E (u k))) := by
  rw [port, offsetEdges, Finset.sum_image]
  intro x _ y _ h
  exact (Prod.ext_iff.mp h).1

omit [Fintype A] [DecidableEq A] in
/-- [proved-derived; formal-checked] **At identity phase the offset port telescopes to its ends**:
`Σ_(k≥N−δ) E(u_k) − Σ_(k<δ) E(u_k)`, for `δ ≤ N`. -/
theorem offset_port_identity_telescopes (δ : ℕ) (hδ : δ ≤ N) :
    port 1 I N u E (offsetEdges N δ) =
      I ((∑ k ∈ Finset.Ico (N - δ) N, E (u k)) - ∑ k ∈ Finset.range δ, E (u k)) := by
  rw [port_offsetEdges]
  simp only [weight, one_pow, Module.End.one_apply, ← map_sum, Finset.sum_sub_distrib]
  congr 1
  have hshift : ∑ k ∈ Finset.range (N - δ), E (u (k + δ)) = ∑ k ∈ Finset.Ico δ N, E (u k) := by
    rw [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl fun k _ => by rw [add_comm]
  have hsplit1 := Finset.sum_range_add_sum_Ico (fun k => E (u k)) hδ
  have hsplit2 := Finset.sum_range_add_sum_Ico (fun k => E (u k)) (Nat.sub_le N δ)
  rw [hshift, sub_eq_sub_iff_add_eq_add, add_comm, hsplit1, add_comm, hsplit2]

omit [Fintype A] in
/-- [proved-derived; formal-checked] The offset port symbol, position by position. -/
theorem portSymbol_offsetEdges (δ : ℕ) (a : A) :
    portSymbol L N u (offsetEdges N δ) a =
      ∑ k ∈ Finset.range (N - δ),
        ((if u (k + δ) = a then weight L N (k + δ) else 0) -
          if u k = a then weight L N (k + δ) else 0) := by
  have hinj : Set.InjOn (fun k => (k, k + δ)) (Finset.range (N - δ) : Set ℕ) :=
    fun x _ y _ h => (Prod.ext_iff.mp h).1
  rw [portSymbol, offsetEdges, Finset.sum_filter, Finset.sum_filter, Finset.sum_image hinj,
    Finset.sum_image hinj, ← Finset.sum_sub_distrib]

/-! ## (b) The transpose: every covector reads the symbols through `I*` and `D*` -/

/-- [proved-derived; formal-checked] **Port transpose.** For every covector `g`,
`⟨g, Σ_a D_(p,a) I E(a)⟩ = Σ_a ⟨I* D_(p,a)* g, E(a)⟩`. -/
theorem port_transpose (p : Finset (ℕ × ℕ)) (g : Module.Dual R V) :
    g (port L I N u E p) = ∑ a, I.dualMap ((portSymbol L N u p a).dualMap g) (E a) := by
  rw [port_eq_symbol_sum, map_sum]
  rfl

/-- [proved-derived; formal-checked] **Moment transpose.** `⟨g, m⟩ = Σ_a ⟨I* C_a* g, E(a)⟩`. -/
theorem moment_transpose (g : Module.Dual R V) :
    g (moment L I N u E) = ∑ a, I.dualMap ((momentSymbol L N u a).dualMap g) (E a) := by
  rw [moment_eq_symbol_sum, map_sum]
  rfl

end Port

/-! ## The symbols are the future-sufficient data of the passage -/

section Standing

variable (L : V →ₗ[R] V) (I : W →ₗ[R] V) (N : ℕ) (p : Finset (ℕ × ℕ))

/-- [definition] A receiver: an encoder and two covectors, one on the moment and one on the port. -/
abbrev PortReceiver (R V W A : Type*) [CommRing R] [AddCommGroup V] [Module R V] := 
  (A → W) × Module.Dual R V × Module.Dual R V

/-- [definition] A present passage: the word and the contemporary anchor `q₀` (the standing the
passage is read against). -/
abbrev Passage (A V : Type*) := (ℕ → A) × V

/-- [definition] Re-anchoring: the contemporary standing is replaced; the word is not. -/
def reanchor (q : V) (x : Passage A V) : Passage A V := (x.1, q)

omit [AddCommGroup V] [Module R V] [Fintype A] [DecidableEq A] in
theorem transportWord_reanchor_fst (word : List V) (x : Passage A V) :
    (transportWord reanchor word x).1 = x.1 := by
  induction word with
  | nil => rfl
  | cons q word ih => simpa [reanchor] using ih

omit [AddCommGroup V] [Module R V] [Fintype A] [DecidableEq A] in
/-- The last re-anchoring (the head of the word, applied last) is the contemporary anchor. -/
theorem transportWord_reanchor (q : V) (word : List V) (x : Passage A V) :
    transportWord reanchor (q :: word) x = (x.1, q) := by
  rw [transportWord_cons]
  simp only [reanchor, transportWord_reanchor_fst]

/-- [definition] The reading of a passage: `g(L^N q₀ + m) + h(port)` for encoder `E`. -/
def readPassage (r : PortReceiver R V W A) (x : Passage A V) : R :=
  r.2.1 ((L ^ N) x.2 + moment L I N x.1 r.1) + r.2.2 (port L I N x.1 r.1 p)

/-- [definition] The retained object: the word-intrinsic symbols `(C, D)` and the anchor reading
`L^N q₀`. -/
def retainSymbols (x : Passage A V) :
    (A → Module.End R V) × (A → Module.End R V) × V :=
  (momentSymbol L N x.1, portSymbol L N x.1 p, (L ^ N) x.2)

/-- [definition] Reopen from the retained object after a re-anchoring word: the anchor term is the
last re-anchor's `L^N q`, or the retained anchor if none. -/
def reopenSymbols (r : PortReceiver R V W A) (word : List V)
    (CDa : (A → Module.End R V) × (A → Module.End R V) × V) : R :=
  r.2.1 ((match word with
      | [] => CDa.2.2
      | q :: _ => (L ^ N) q) + ∑ a, CDa.1 a (I (r.1 a))) +
    r.2.2 (∑ a, CDa.2.1 a (I (r.1 a)))

/-- [proved-derived; formal-checked] **The native standing.** `(C, D)` are word-intrinsic and fixed
in `N`; the contemporary standing enters only through the anchor `L^N q₀`. For every encoder and
every covector pair, the reading after every re-anchoring word is reopened from `(C, D, L^N q₀)`;
sufficiency is `moment_eq_symbol_sum` and `port_eq_symbol_sum`. -/
def symbolStanding : StandingLaw V (PortReceiver R V W A) (Passage A V)
    ((A → Module.End R V) × (A → Module.End R V) × V) R where
  transport := reanchor
  observe := readPassage L I N p
  retain := retainSymbols L N p
  reopen := reopenSymbols L I N
  sufficient r word x := by
    cases word with
    | nil =>
        simp only [reopenSymbols, retainSymbols, transportWord_nil, readPassage,
          moment_eq_symbol_sum, port_eq_symbol_sum]
    | cons q word =>
        rw [transportWord_reanchor]
        simp only [reopenSymbols, retainSymbols, readPassage, moment_eq_symbol_sum,
          port_eq_symbol_sum]

end Standing

/-! ## Witnesses: `abca` and `acba` -/

/-- [definition] The encoder `a ↦ 0`, `b ↦ (1,0)`, `c ↦ (0,1)`. -/
def abc : Fin 3 → ℚ × ℚ := ![(0, 0), (1, 0), (0, 1)]

/-- [definition] The words `abca` and `acba`. -/
def abca : ℕ → Fin 3 := fun k => ([0, 1, 2, 0] : List (Fin 3)).getD k 0
def acba : ℕ → Fin 3 := fun k => ([0, 2, 1, 0] : List (Fin 3)).getD k 0

/-- [proved-derived; formal-checked] **Identity phase merges, the quarter turn separates, and the
port is not its endpoints.** At `L = 1` both offset-1 ports are the endpoint term `E(a) − E(a) = 0`;
under the quarter turn the port of `abca` is `(−2, −2)` and that of `acba` is `0`. -/
theorem quarter_turn_port_witness :
    port (1 : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ)) LinearMap.id 4 abca abc (offsetEdges 4 1) = 0 ∧
      port (1 : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ)) LinearMap.id 4 acba abc (offsetEdges 4 1) = 0 ∧
      port MomentMachine.quarterTurn LinearMap.id 4 abca abc (offsetEdges 4 1) = (-2, -2) ∧
      port MomentMachine.quarterTurn LinearMap.id 4 acba abc (offsetEdges 4 1) = (0, 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [port_offsetEdges, weight, Finset.sum_range_succ, abca, acba, abc, pow_succ,
      MomentMachine.quarterTurn] <;> norm_num
  rfl

/-- [proved-derived; formal-checked] **Different words, equal symbols.** At identity phase `abca`
and `acba` have equal moment and offset-1 port symbols (both words carry the same letter counts
and the same end/start counts), so they are one standing. -/
theorem identity_phase_equal_symbols :
    abca ≠ acba ∧
      retainSymbols (1 : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ)) 4 (offsetEdges 4 1) (abca, (0 : ℚ × ℚ)) =
        retainSymbols 1 4 (offsetEdges 4 1) (acba, (0 : ℚ × ℚ)) := by
  refine ⟨fun h => by simpa [abca, acba] using congrFun h 1, ?_⟩
  simp only [retainSymbols, Prod.mk.injEq, and_true]
  constructor <;> funext a <;> fin_cases a <;>
    simp only [momentSymbol, portSymbol_offsetEdges, Finset.sum_range_succ,
      Finset.sum_range_zero, abca, acba, weight, one_pow, List.getD_cons_succ,
      List.getD_cons_zero] <;> simp <;> abel

/-- [proved-derived; formal-checked] **Different symbols, separated by an encoder.** Under the
quarter turn, the reading `fst` of the offset-1 port with encoder `abc` separates `abca` from
`acba`, so their retained symbols differ (`separating_future_refutes_the_standing`). -/
theorem quarter_turn_symbols_separate :
    readPassage MomentMachine.quarterTurn LinearMap.id 4 (offsetEdges 4 1)
        (abc, 0, LinearMap.fst ℚ ℚ ℚ) (abca, (0 : ℚ × ℚ)) ≠
      readPassage MomentMachine.quarterTurn LinearMap.id 4 (offsetEdges 4 1)
        (abc, 0, LinearMap.fst ℚ ℚ ℚ) (acba, (0 : ℚ × ℚ)) ∧
    retainSymbols MomentMachine.quarterTurn 4 (offsetEdges 4 1) (abca, (0 : ℚ × ℚ)) ≠
      retainSymbols MomentMachine.quarterTurn 4 (offsetEdges 4 1) (acba, (0 : ℚ × ℚ)) := by
  have hsep : readPassage MomentMachine.quarterTurn LinearMap.id 4 (offsetEdges 4 1)
        (abc, 0, LinearMap.fst ℚ ℚ ℚ) (abca, (0 : ℚ × ℚ)) ≠
      readPassage MomentMachine.quarterTurn LinearMap.id 4 (offsetEdges 4 1)
        (abc, 0, LinearMap.fst ℚ ℚ ℚ) (acba, (0 : ℚ × ℚ)) := by
    simp only [readPassage, map_zero, LinearMap.zero_apply, zero_add]
    rw [quarter_turn_port_witness.2.2.1, quarter_turn_port_witness.2.2.2]
    norm_num
  refine ⟨hsep, ?_⟩
  exact (symbolStanding MomentMachine.quarterTurn LinearMap.id 4 (offsetEdges 4 1)).separating_future_refutes_the_standing
    (abc, 0, LinearMap.fst ℚ ℚ ℚ) [] hsep

/-! ## (c) Anchor separability -/

section Anchor

variable (L : V →ₗ[R] V) (τ : V) (I : W →ₗ[R] V) (u : ℕ → A) (E : A → W)

/-- [definition] The affine advance `U q = L q + τ`. -/
def affineAdvance (q : V) : V := L q + τ

/-- [definition] The stepped state `q_(k+1) = U q_k + I E(u_k)`. -/
def stepped (q₀ : V) : ℕ → V
  | 0 => q₀
  | k + 1 => affineAdvance L τ (stepped q₀ k) + I (E (u k))

omit [Fintype A] [DecidableEq A] in
theorem moment_succ (N : ℕ) :
    moment L I (N + 1) u E = L (moment L I N u E) + I (E (u N)) := by
  rw [moment, Finset.sum_range_succ, moment, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < N := Finset.mem_range.mp hk
    rw [weight, weight, show N + 1 - 1 - k = (N - 1 - k) + 1 by omega, pow_succ',
      Module.End.mul_apply]
  · simp [weight]

omit [Fintype A] [DecidableEq A] in
/-- [proved-derived; formal-checked] **The anchor separates from the moment.**
`q_N = U^N q₀ + Σ_k L^(N−1−k) I E(u_k)`: the moment term does not depend on `q₀`. -/
theorem stepped_eq_anchor_add_moment (q₀ : V) (N : ℕ) :
    stepped L τ I u E q₀ N = (affineAdvance L τ)^[N] q₀ + moment L I N u E := by
  induction N with
  | zero => simp [stepped, moment]
  | succ N ih =>
      rw [stepped, ih, moment_succ, Function.iterate_succ_apply', affineAdvance, affineAdvance,
        map_add]
      abel

omit [Fintype A] [DecidableEq A] in
/-- [proved-derived; formal-checked] The anchor moves linearly: `U^N q₀ − U^N q₀' = L^N (q₀ − q₀')`. -/
theorem iterate_affine_sub (q₀ q₀' : V) (N : ℕ) :
    (affineAdvance L τ)^[N] q₀ - (affineAdvance L τ)^[N] q₀' = (L ^ N) (q₀ - q₀') := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', affineAdvance,
        affineAdvance, add_sub_add_right_eq_sub, ← map_sub, ih, pow_succ', Module.End.mul_apply]

omit [Fintype A] [DecidableEq A] in
/-- [proved-derived; formal-checked] **The anchor's covector is `(L^N)* ∇F`.** For a linear
reading `F`, the change of `F(q_N)` with the anchor is `(L^N)* F` applied to the anchor change;
the moment does not enter. -/
theorem anchor_covector (F : Module.Dual R V) (q₀ q₀' : V) (N : ℕ) :
    F (stepped L τ I u E q₀ N) - F (stepped L τ I u E q₀' N) =
      (L ^ N).dualMap F (q₀ - q₀') := by
  rw [stepped_eq_anchor_add_moment, stepped_eq_anchor_add_moment, ← map_sub,
    add_sub_add_right_eq_sub, iterate_affine_sub]
  rfl

end Anchor

section Audit
#print axioms port_eq_symbol_sum
#print axioms moment_eq_symbol_sum
#print axioms offset_port_identity_telescopes
#print axioms port_transpose
#print axioms moment_transpose
#print axioms symbolStanding
#print axioms quarter_turn_port_witness
#print axioms identity_phase_equal_symbols
#print axioms quarter_turn_symbols_separate
#print axioms stepped_eq_anchor_add_moment
#print axioms anchor_covector
end Audit

end Holonics.Objects.SourcePorts
