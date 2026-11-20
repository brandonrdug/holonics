# Hodge asks that the face functor be full, a colourless class offers its reader magnitudes alone, the product formula is a tower's exchange law, and a crossed pair is a commutator no uncoupled bank reads (in Lean)

November 20, 2026, 20:02 to 20:34 UTC. One bounded pass on a lens, made the hour after the gauge of three outside
claims ([the zeta record](2026-11-20_A_PUBLISHED_LEAN_ARCHIVE_CLAIMS_THE_RIEMANN_HYPOTHESIS_FOR_ZETA_AND_EVERY_DIRICHLET_CHARACTER_ITS_STATEMENT_IS_MATHLIBS_ITS_TEXT_ADDS_NO_AXIOM_AND_ITS_KEY_IS_MULTIPLICITY_AS_A_CARRY_COUNT_WON_BY_A_CHAIN_OF_THETA_LIFTS.md),
[the fluid record](2026-11-20_UNFORCED_BLOW_UP_IS_CLAIMED_FOR_EULER_WITH_A_WHOLE_LEAN_PROOF_AND_FOR_NAVIER_STOKES_AS_AN_IMPLICATION_FROM_UNPOSTED_DATA_THE_NAVIER_STOKES_PROFILE_IS_A_CYCLE_OF_THE_SCALE_FLOW_CLOSED_BY_A_SCREW_AND_A_DYAD.md)).
Refs #410, #404. Nothing ran on a learner or on the card. One Lean module enters with three finite statements (§7).
Each paragraph carries its grade: `tree` (read in this repository), `from training` (a result of the literature,
named, not looked up that day), `source-inspected` (read in the outside archive) or `agent-inferred` (this record's
join). Every statement of §6 is `agent-inferred`: a host read on saved states with its guess to fix, and no build.

## 1. The lens

Brandon, November 20, 20:02 UTC (a paraphrase; his words stay out of the repository). With the Riemann hypothesis and
Navier–Stokes claimed in one day by automated work, nothing was shown for Hodge, and he asks why. His impression is
that Hodge would be the most powerful of the three for a computing system, because it states how things connect,
and that it ties to P versus NP. He names four flags to be organized: a spectrum is a colour (Galois, gaps and
differences, and a nullity of the null as the sign of a difference); what lacks colour is carried by magnitude
(loudness, energy and action, norms, geometry alone and perhaps discrete, the constants of a medium); the fluid
paper's tower of parametric amplifiers brings Iwasawa's theory to mind; and the conservation of faces has to be an
exchange law here. He asks for the takeaways that bear on the engineering of Athena.

## 2. What the tree held

`tree`. Most of the four flags stand in the atlas already, each under its own date. The search was `rg -i` over
`docs/atlas/` for hodge, colour, palette, iwasawa, lefschetz, galois, frobenius, polariz, NP, permanent and
"conservation of faces".

| Flag | Owner | What it states |
|---|---|---|
| a Hodge class has no colour | `hodge.colourless-classes-weil` (October 26) | Hodge classes are the rational classes the turn `U(1)` fixes, Tate classes the ones Frobenius fixes after a twist; the polarization's positivity puts Frobenius's colours on the circle of radius `√q` |
| count or turn | `hodge.count-or-turn-two-halves` (November 15) | under a change of scale a mode is a count or a turn; RH is the stretch's half and Hodge the quotient's |
| a colour has no reading of its own | `colour.scope-reading`, `colour.trace-compression`, `colour.colour-tower` | a scope reads a colour as its relative trace; the trace to the layer below keeps the old colours and erases the new |
| loudness and colour as charges | `frame.moment-map-loudness-colour` (November 16) | a place's power and a region's colour are the moment maps of the phase rotations and of the frame's turns |
| the half from a form | `key.scaled-form-places-modes` | the half is forced by a reversal and a positive pairing; Hodge supplies the pairing on the classes closed routes span |
| the tower | `tower.iwasawa-growth-law`, `tower.main-conjecture-not-identity`, `tower.characteristic-face-blind`, `tower.control-kernel-cokernel` (`Foundation/IwasawaTower`) | `\|M/ω_n M\| = p^(μpⁿ + λn + ν)`; the main conjecture is an equality of two faces; the characteristic face does not determine the module |
| conservation of faces | `face.conserved-is-congruence` (`Compression/OneFaceLaw`) | a face is conserved by an operation exactly when its kernel is a congruence |
| the cost of finding | `key.slow-modes-landmarks`, `coupling.border-degeneration`, `coupling.pvsnp-official` | location is exponential only in the slow modes; counting on a surface of genus `g` takes `4^g` Pfaffians; the border of the determinant reaches the padded permanent at `n = 3, m = 2` |
| a signature as a gap | `hodge.lorentzian-reverse-inequality` | the Hodge index signature is the reverse Cauchy–Schwarz inequality |
| what a bank holds | `parametron.carry-bank-group-ceiling` (November 19), `parametron.no-linear-relative-phase` | uncoupled circles read a group through `Γ/Γ′` or `Γ/Γ″`; no linear threshold reads a relative phase |
| a card's joins | `holarchy.harmonic-class-join` (November 11) | a local step relaxes the exact and coexact parts and fixes the harmonic part; each global class is a join |
| the tick | `tower.field-tick-contraction` (November 20, 19:52 UTC) | a series is released at a tolerance where its tick contracts under a certified metric |
| a power of one torus | `hodge.torus-power-narayana` (November 18) | on `Eⁿ` the Hodge classes number Catalan(n+1) and intersections of divisors span them |

So this record does not introduce the flags. It states each as one sentence with its hypotheses, says which part
is a theorem and which a figure of speech, and draws what follows for the machine.

## 3. Why the day's automated work brought no claim on Hodge

Corrected November 20, 21:20 UTC. This section was headed "Why no finite object settles Hodge" and its first
paragraph closed on the sentence that no single finite object settles it either way. That gave one receiver's view,
the proof-checker's, as the only one, and on the refuting side it contradicted a theorem the tree holds
(`Foundation/FiniteKey.refuted_by_one_reading`). The paragraph now says what one object does and what a cause does;
[the record of the correction](2026-11-20_HODGE_ASKS_THAT_EACH_VARIETYS_FAILURE_GROUP_BE_FINITE_A_CLASS_OF_GRAIN_K_CLOSES_AFTER_K_TURNS_ONE_OBJECT_REFUTES_WHERE_A_CAUSE_COMPLETES_AND_A_CHART_OF_ONE_PERIOD_REACHES_NO_DECAYING_FUNCTION_IN_LEAN.md)
holds the reasons, the finite object variety by variety, and what follows.

`agent-inferred`, on facts `from training`. The reason is mostly in the statement's shape, and it is the lens's own
second flag.

- **The shape.** The Riemann hypothesis is a statement over an unending family that one computation refutes (a zero
  off the line), and the day's proof is a chain of positive counts. The fluid proofs are one constructed object and a
  theorem that the object is stable. The Hodge conjecture says: for every smooth projective variety and every
  rational class of type `(p,p)`, a cycle exists. One object would refute it: a variety with a class the turn keeps
  that no multiple of any cycle carries, shown by an invariant every cycle obeys and the class does not. Both
  neighbours of the statement fell to one object each (integer coefficients: Atiyah and Hirzebruch 1962, Kollár
  1992; no polarization: Voisin 2002), and neither invariant reaches the rational, polarized statement. Variety by
  variety the question is one finitely generated group, the integer classes the turn keeps modulo the carried ones,
  and the conjecture says that group is finite. What completes the statement over every variety is a cause, a
  construction from class to carrier, and no count of instances stands in for it. So an automated result on Hodge
  is either that group computed for a named variety, a finite answer, or the construction, and the day showed
  neither.
- **The hypothesis is an equality.** That a class is of type `(p,p)` is the vanishing of period integrals,
  transcendental numbers. An enclosure by intervals certifies an inequality, as it does for a zero's sign change or a
  fluid profile's coercive bound, and it never certifies an equality. The class has no spectrum for a computation to
  bracket: it is the part the turn does not move.
- **One machine, in one codimension.** The only general passage from a class to a cycle is Lefschetz's for divisors:
  a class of type `(1,1)` is the Chern class of a line bundle, by the exponential sequence, and a section's zeros are
  the divisor (`hodge.lefschetz-one-one-passage`). In codimension two and above the same integration lands in a
  complex torus that is not algebraic in general (Griffiths 1969), and every known case is a construction by hand in
  a special family (`hodge.torus-power-narayana` is one).
- **The library.** Mathlib has no statement of the conjecture, so a claimed formal proof has nothing to be checked
  against, where the zeta archive's theorem is `RiemannHypothesis` as Mathlib defines it. `source-inspected`: 99,187
  of that archive's 175,187 files are abelian-variety theory, with directories of heights and theta functions, period
  integrals and p-adic Hodge theory, so if the archive stands the gap in the library narrowed that day.

A guess, to be scored by events: the first automated results of this family are statements of Tate's kind over
finite fields, where Frobenius gives a spectrum that a computation can bracket, before any statement of Hodge's kind
over the complex numbers.

On the objects: a statement over an unending family is completed by a finite word every reader runs
(`key.derivation-finite-word-every-reader`). For Hodge the word to write is a construction, a passage from a
class to a cycle that works in every codimension as the exponential sequence works in the first, and what it would
carry to other charts is §5.4's sentence: every relation the faces admit, made by a part.

## 4. Hodge and the cost of finding

`from training` for the theorems; the sorting into theorem and figure of speech `agent-inferred`. No theorem takes
the Hodge conjecture to P versus NP or back (`coupling.pvsnp-official` states the latter and leaves it as it is).
Four links are theorems or published programmes.

1. **A count is one determinant where a sign class vanishes.** The perfect matchings of a planar graph are counted
   by one Pfaffian (Kasteleyn 1961), and on a surface of genus `g` by `4^g = |H¹(Σ; ℤ₂)|` of them (Galluccio and
   Loebl 1999; `key.slow-modes-landmarks`). The unsigned count is the permanent's kind and the signed count the
   determinant's, and the cost of passing from one to the other is exponential only in the rank of a cohomology
   group: in what cannot be untwisted.
2. **A Hodge signature is a spectral gap.** The package of Poincaré duality, hard Lefschetz and the Hodge–Riemann
   relations holds on the Chow ring of every matroid, with no variety behind it, and gives the log-concavity of its
   characteristic polynomial (Adiprasito, Huh and Katz 2018). The same signature, one positive direction and a
   negative definite complement (`hodge.lorentzian-reverse-inequality`), gives the fast mixing of the walk that
   exchanges one element of a basis, and with it an approximate count of a matroid's bases in polynomial time
   (Anari, Liu, Oveis Gharan and Vinzant 2019; Brändén and Huh 2020).
3. **Permanent against determinant runs through this positivity.** Mulmuley and Sohoni's programme reads the
   question as a containment of orbit closures and asks for obstructions among representation-theoretic
   multiplicities; by Mulmuley's account the positivity it needs is of the kind whose known proofs use Deligne's
   purity. Its simplest form was closed in 2016 (Bürgisser, Ikenmeyer and Panova: no occurrence obstructions).
   `coupling.border-degeneration` is its border at the smallest size.
4. **Hodge makes a search halt.** Cycles enumerate the classes that are algebraic, and periods computed to rising
   precision refute a class that is not of type `(p,p)`. The conjecture says the two lists are complements, so it
   implies that algebraicity is decidable (Simpson 2008); with Tate's conjecture in place of Hodge's the
   Néron–Severi group is computable (Poonen, Testa and van Luijk 2015). This is the shape of a good
   characterization in Edmonds's sense, a witness exists if and only if no obstruction does, which is the class
   where fast algorithms were later found for matching, linear programmes and primality.
   `hodge.polarized-receiver-detection` is this shape in the tree: no nonzero class orthogonal to every
   algebraic class.

The figure of speech is the rest. The conjecture gives existence over the rationals, with no bound on the degree of
the cycle and no procedure of bounded cost, and its integral form is false. So it stands with the expected answer to
the other question and not against it: witnesses exist, and finding them can be hard.

## 5. The four flags as statements

### 5.1 A spectrum is a colour, and a nullity of the null is a difference

`from training`; the join `agent-inferred`. The turn `U(1)` acts on a class of type `(p,q)` by `z^(p−q)`. The
smallest rational group that contains this action is the Mumford–Tate group, and the Hodge classes in every tensor
construction are exactly its invariants. The Tate classes are the invariants of the image of the Galois group, whose
elements at the primes are the Frobenius colours (`prime.frobenius-colour-chebotarev`). The Mumford–Tate conjecture
says the two groups are one. The conjectures of Hodge and of Tate say its invariants are the classes of cycles.

The lens's phrase is then the double annihilator. A reductive group is recovered from its invariants in all tensor
constructions, and it is as large as they are few (`coupling.galois-receiver-duality`: every relation induces an
antitone connection, and the closed sets are the ones equal to their double annihilator). If cycles made fewer
classes than the turn fixes, the group that fixes every cycle would be larger than the group the turn generates:
there would be a symmetry that no turn shows, and its nonzero difference from the turn's group would be the class
with no cycle. Hodge says that no such difference exists.

### 5.2 What has no colour is carried by magnitude

`from training`; the reading `agent-inferred`. A class of type `(p,p)` is a product of `p` turns and `p` mirror
turns, so every phase cancels: the simplest is `(i/2)·dz ∧ dz̄`, the area form, which is at once the positive form
of the polarization and the form whose integral over a disc is the action. What a reader can take from such a
class is magnitude alone, in three kinds, and they are the lens's list.

- Integers: the intersection numbers of cycles, which is geometry with nothing continuous in it.
- Sizes under the positive form: the volume of a cycle is its class paired with a power of the form (Wirtinger), so
  an algebraic cycle is the least-volume member of its class; over a number field the size is a height, and the
  covolume of the lattice of cycles under the height pairing is a regulator.
- The medium's constants: the periods, the entries of the matrix that compares the rational classes with the
  differential forms, with `2πi` the period of the unit turn.

Conjecturally the count and the sizes are one account: the count of colourless classes in a degree is the order of a pole of the
L-function there (Tate), and their covolume is its leading coefficient, with the periods and the orders of finite
groups (Birch and Swinnerton-Dyer, Beilinson, Bloch and Kato; `bsd.universal-ledger-clause`). On the machine the
same split is built: a place's loudness `‖f_j‖²` is the charge of its phase rotation
(`frame.moment-map-loudness-colour`), the one quantity of a place that no turn moves.

The lens's flag on norms and compactness has a theorem too. A polarization gives a positive definite form that the turn
keeps, `Q(x, C·x̄)` with `C` the action of the quarter turn, so every part that the turn keeps has a complement the
turn keeps: the category is semisimple, the group is reductive, and its real form twisted by `C` is compact.
`receipt.conserving-receiver-iff-semisimple` (`Coupling/MovingMetricSpectral`, November 18: a kept positive form
exists exactly where the motion is semisimple with its modes on the locus) is this on a finite space. A part splits
off cleanly only where a positive form is kept.

### 5.3 A tower of amplifiers and Iwasawa's tower

`source-inspected` for the first paragraph, `from training` for the second, `agent-inferred` for the third.

The association is in the zeta archive's own definitions. Its criterion is stated on a level `j` whose aggregate
runs over the even characters of conductor `2^(j+2)`, the characters of the `j`-th layer of the cyclotomic tower over
the prime two (the zeta record, §11), and the remark names the tower as its stand-in for the extensions of the
constant field.

In Iwasawa's theory the generator of the tower's group stands where Frobenius stands over a curve, the
characteristic polynomial of its action on the tower's module stands where the numerator of the zeta function
stands, and the sizes at the finite layers grow as `p^(μpⁿ + λn + ν)` (`tower.iwasawa-growth-law`): `λ` is the degree
of that polynomial, the count of modes each layer multiplies, and `μ` is a growth in proportion to the layer's whole
size, which is zero for the cyclotomic tower of an abelian field (Ferrero and Washington 1979).

The exchange law between the two towers is the product formula (`trace.place-ledger`, `prime.register-two-places`):
for a nonzero rational the sizes at all places multiply to one, so what a tower gains at the real place it loses at
`p`. The fluid paper's cascade is a tower read at the real place, each stage pumped by the one before and gaining
`exp(ε^(−1/2))` (`fluid.craik-criminale-tower`); Iwasawa's is a tower read at `p`, where the same climb is a
contraction (`T = γ − 1` is topologically nilpotent). The zeta remark's count is the exchange itself: orders of
vanishing won at the primes against a size at the real place (`rh.multiplicity-route-no-ground`). What does not
transfer: no parametric resonance is in Iwasawa's theory, and the two towers are not one piece of mathematics. What
they share is a group of scale steps, a generator whose action has a characteristic polynomial, and one law both
state in their own terms: a stage hands on a frame, and size alone is blind. In the fluid paper the size of a wave
does not determine its successor. In the tree, `Λ/(T²)` and `Λ/(T) ⊕ Λ/(T)` have one characteristic ideal and are
different modules (`tower.characteristic-face-blind`).

### 5.4 Conservation of faces, and what Hodge adds to it

`tree` for the first sentence, `from training` for the second paragraph, `agent-inferred` for the join.
`face.conserved-is-congruence`: a face is conserved by an operation exactly when the face of a result is a function
of the faces of the operands. Cohomology is a conserved face for every operation of geometry: a map of varieties
acts on it, a product's classes are the tensor of the factors' (Künneth), a class pairs with its complement to a
number (Poincaré duality, the port's pairing of flow and effort), the mirror exchanges `(p,q)` with `(q,p)`, and
raising and lowering by the positive form satisfy `[L, Λ] = H`, with `H` the count of the degree from the middle
(hard Lefschetz; the tree's positive commutator of November 18). The trace formulas are the same law for counts:
the fixed points of a map are the alternating sum of its traces on the faces (Lefschetz), and the explicit formula,
Selberg's and the relative trace formula of the zeta remark are its forms on other terrains. Each is one
distribution read in two bases, a sum over cycles and a sum over colours.

Conservation says the faces form a functor. Hodge says the functor is full. By Künneth and duality a rational map
between the classes of `X` and of `Y` that commutes with the turn is a Hodge class on `X × Y`, and the conjecture
there says it is the class of a correspondence, an actual cycle on the product. On the objects: every map of faces
that commutes with the turn and is rational is the face of an actual contact between the two Holons. That is the
lens's impression that Hodge states how things connect, written as a statement, and it is why
Grothendieck's motives need it: with it the things themselves, taken up to the relations cycles make, form one semisimple category through which every reading
factors.

The three statements of the day then sit on one trace formula. RH: the turning terms have the half as their size.
Hodge and Tate: the terms with no turn are counts of actual cycles, one by one and not only in sum. Birch and
Swinnerton-Dyer: those terms' leading constants are the cycles' volumes.

## 6. What follows for the machine

`agent-inferred` throughout. Four reads, each on saved states by a host ruler, each with the recorded failure it
resembles and what differs, and each with a guess to fix before the read. None is a build and none is a gate. They
are written beside what the hardware record of the same day leaves to be found: the premise of the tick's
contraction and the ruler that sizes a register (its §8 and §9).

**6.1 Type the tension before a part is founded.** The founding read takes the covector's tension at a locus
(`contact.tension-founds-face`, `tools/tension_ruler.py`). Split it over a lap's saved states into its mean,
`‖E c‖²`, and its power with no mean, `tr Cov c`, with the rank of the covariance above the deposit's standing
spread. A mean is a count: a lane, a face linear in the state, can take it. Power with no mean is of the type of
§5.2, a product of a turn and a mirror turn, and §7's third statement says what that costs: over a cycle of the
turn every reading that is real-linear in two strands has mean zero whatever phase stands between them, and the
pairing of one strand with the mirror of the other has that phase as its mean. So a tension of this type is removed
by a pair contact or a pump (`parametron.no-linear-relative-phase`) and by no lane at any width. The guess to fix:
at the places where the line binds (a role to its filler, an opener to its closer) the tension has power well over
its mean, and at the places inside a word the reverse. If so it is the reason the face's growth from 128 to 224
bought words and not composition. Resembles: the tension read made a gate on November 16 and retired on November 18.
Differs: it adds one split to that read and gates nothing.

**6.2 One read sizes the tick's release and names what the tick cannot settle.** The hardware record asks for the
largest gain of the trained tick by power iteration. Keep the top of the spectrum and not only its largest value. A
tick has modes of gain one wherever it has a symmetry or a kept class: the scale of a ray that every reader divides
out, the phases whose charges are the loudness and the colour (`frame.moment-map-loudness-colour`), and on a complex
the harmonic part, which friction keeps while it relaxes the exact and coexact parts
(`holarchy.harmonic-class-join`; the heat flow of `hodge.count-or-turn-two-halves`). A contraction with `ρ < 1` on
the whole space has none of these, so a tick that has them is not certified on the whole space. The certificate is
asked on the quotient by those modes (`hodge.hilbert-quotient-energy-gns`: the energy form's radical is the
harmonic population and the quotient is definite), where the next gain `ρ₂` gives the count of ticks,
`K = ln(τ/r₀)/ln ρ₂`. The modes of gain one are what the tick leaves for a store to hold, and their count at a
locus, above the census's spread, is the size of the register that locus needs. Where the spectrum has no gap below
one, no tolerance releases it. The built tick reads that way already: a mode of gain one under a held source grows
by one step a tick, and read through its own power its changes fall as `(k − 1)/(k + 1)`
(`tower.field-tick-running-mean`). Resembles: the held tick of November 15, withdrawn because it assumed a
relaxation the built tick does not have. Differs: this is a read of the trained tick's own gains, and it is the read
that would have shown that.

**6.3 Nesting is the invariant of a coupled pair of circles.** A carry reads a word of openers and closers as a
product in a group. Two pairs nested return the carry in every group, and two pairs crossed return it exactly where
the elements commute (§7, first statement). So a bank of circles that are not coupled reads `([)]` as it reads
`([])` at any width, which is `parametron.carry-bank-group-ceiling` on the one word that matters for typed
brackets. The count: of the `C(2n, n)` words with as many openers as closers, `catalan n` are nested, one in
`n + 1` (§7, second statement), and the invariants of `SU(2)` in the `2n`-th tensor power of its plane are spanned
by the pairings that do not cross, `catalan n` of them (Rumer, Teller and Weyl 1932, `from training`): the classes a
coupled pair of circles leaves fixed are the nested structures, and the classes an uncoupled bank leaves fixed are
all the balanced ones. `hodge.torus-power-narayana` holds the same two kinds of count on a power of a torus:
with the extra commuting symmetry `Eⁿ` has `C(2n, n)` Hodge classes, and without it a Catalan number (there
Catalan(n+1), the classes being counted in every degree at once). The read:
in the ruler of margins an outside reader proposed that day, set crossed against nested continuations with equal
counts of every bracket. The guess to fix: the line as it stands gives the two the same margin, to the panel's
spread, at every width it has had. Resembles: a bracket probe read as a campaign, and a grammar handed to the
machine. Differs: it is one probe in a ruler, and nothing is authored into the engine; the coupled carry the lead is
building is the part, and this names the reading that tells whether it took.

**6.4 A register's width from its growth, with the cache test as a growth law.** For a part that is refined level
by level (the carry circles' tower, `Declaration::carry`), count the states it occupies at each grain `bⁿ` over a
lap's saved states and fit `log_b N_n = μ·bⁿ + λ·n + ν`. `λ` is the count of digits a level adds, the width the
part's information needs (the dimension a box count reads). `μ > 0` is growth in proportion to the grain's own
size, which is growth with the items seen: the guide's test for a cache, stated as a number. The guess to fix: of
the lanes added from 128 to 224, most blocks show `λ` near zero and a few carry it, which would say which parts
need the width. Resembles: a width tuned to a reading (the method rule "width is never a dial"). Differs: the
count is of the part's own occupied states, a partition of its information, and sets no width by a code.

One sentence for the scan the hardware side is restructuring: an associative chain is free to regroup, and what a
regrouping cannot make local are the classes of §6.2, one join each, so a region's count of gain-one modes is also
a floor on its joins.

## 7. Lean

`formal-checked`. `HolonicsResearch/HNN/NestedPairs.lean`, imported by the research root, with no `sorry` and no
axiom added.

```lean
def nested [Group Γ] (a b : Γ) : Γ := a * b * b⁻¹ * a⁻¹
def crossed [Group Γ] (a b : Γ) : Γ := a * b * a⁻¹ * b⁻¹

theorem nested_eq_one [Group Γ] (a b : Γ) : nested a b = 1
theorem crossed_eq_one_iff [Group Γ] (a b : Γ) : crossed a b = 1 ↔ a * b = b * a
theorem crossed_swaps_ne_one :
    crossed (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) ≠ 1
theorem affineTracks_crossed [Group Γ] (htor : ∀ g : Γ, IsOfFinOrder g) {f : Γ → ι → ℂ}
    (hf : AffineTracks f) (γ a b : Γ) : f (γ * crossed a b) = f (γ * nested a b)

theorem nested_share (n : ℕ) :
    (n + 1) * Fintype.card { p : DyckWord // p.semilength = n }
      = (powersetCard n (univ : Finset (Fin (2 * n)))).card

theorem no_linear_reading (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n) (u c d c' d' : ℂ) :
    ∑ k ∈ range n,
      (c * ζ ^ k + d * conj (ζ ^ k) + (c' * (u * ζ ^ k) + d' * conj (u * ζ ^ k))) = 0
theorem pair_reads_relative_phase (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n) (u : ℂ) :
    (∑ k ∈ range n, ζ ^ k = 0) ∧ (∑ k ∈ range n, u * ζ ^ k = 0) ∧
      ∑ k ∈ range n, u * ζ ^ k * conj (ζ ^ k) = n * u
```

What the three add to their neighbours. `affineTracks_crossed` is `CarryGroupTracking.affineTracks_comm` on the
word of two crossed pairs, with the swaps of three things as the carry that tells it from the nested one.
`nested_share` joins Mathlib's count of Dyck words to the count of words with equal counts.
`no_linear_reading` stands beside `HNN/Floquet`'s `no_linear_threshold_reads_relative_phase`: there no linear
threshold agrees with the sign of a relative phase at an instant, by parity under the half-turn; here no
real-linear reading holds the phase in its mean over a cycle, and the pairing's mean is the phase itself.

Not in Lean, and named as constructions: the invariants of `SU(2)` in an even tensor power as the span of the
pairings that do not cross; the certificate of §6.2 on a quotient by the modes of gain one (the hardware record's
statements for #410 are its first half); and the functor of §5.4 on a finite model, where a map of faces that
commutes with a turn is shown to be the face of a contact.

## 8. Atlas

Nine rows enter with this record or its module as owner.

- `hodge.face-functor-full`, `hodge.one-object-refutes-a-cause-completes` (entered as `hodge.no-finite-witness`,
  corrected and renamed that evening), `hodge.mumford-tate-one-group` (`interpretation`): §5.4,
  §3 and §5.1.
- `tower.product-formula-exchange` (`interpretation`): §5.3.
- `parametron.crossed-pair-is-a-commutator`, `code.nested-share-of-balanced`,
  `receiver.pair-reads-relative-phase` (`formal-checked`): §7, with the readings of §6.1 and §6.3 in their scope as
  `agent-inferred`.
- `tower.tick-gap-sizes-registers`, `radix.growth-law-sizes-a-register` (`interpretation`): §6.2 and §6.4, not read
  and not built.

Notes enter the scope of `hodge.colourless-classes-weil` (the three kinds of magnitude),
`parametron.carry-bank-group-ceiling` (the crossed word) and `tower.field-tick-contraction` (the quotient by the
modes of gain one). No grade changes.

## 9. Receipts

Read and written in a cloud container (4 cores, 15 GB), on Lean 4.33.0 with the package's pinned Mathlib.

- The module: `lake build HolonicsResearch.HNN.NestedPairs` read `Build completed successfully (3516 jobs)` in
  7 min 5 s of wall time, with no warning from the module. `#print axioms` on its fourteen statements reads
  `propext`, `Classical.choice` and `Quot.sound` alone.
- The library: `bash tools/lean_check.sh HolonicsResearch` was launched under a deadline of 25 minutes that no
  measured read had fixed, and it was stopped at 20:33 UTC on its own rate: 142 research modules in seven and a half
  minutes, which puts the 1,172 still to build at about an hour. It is incomplete evidence. 321 of the library's
  1,493 modules were built and its root was not reached; the projection's error is that there was none. What stands
  in its place is `agent-inferred`: the module's names live in a namespace no other file opens, it declares no
  instance, notation or attribute, and nothing imports it but the root.
- Text: `tools/link_check.py atlas` and `links`, `tools/test_records_index.py`, `tools/lean_census.py`.
- The second reader's note on the zeta archive was read in the repository's mailbox on the PC and its two pointers
  in this container's copy of the archive.

## 10. Sources

`from training`, none looked up on the day: Hodge 1950; Lefschetz 1924; Atiyah and Hirzebruch 1962; Griffiths 1969;
Kollár 1992; Deligne 1982 (Hodge cycles on abelian varieties); Mumford 1966; Tate 1965; Kasteleyn 1961; Galluccio
and Loebl 1999; Adiprasito, Huh and Katz 2018; Brändén and Huh 2020; Anari, Liu, Oveis Gharan and Vinzant 2019;
Mulmuley and Sohoni 2001 and Mulmuley 2011; Bürgisser, Ikenmeyer and Panova 2016; Simpson 2008; Poonen, Testa and
van Luijk 2015; Edmonds 1965; Iwasawa 1959; Ferrero and Washington 1979; Mazur and Wiles 1984; Rumer, Teller and
Weyl 1932; Bertrand 1887 and André 1887. A date or an attribution here is a reader's memory and is checked at its
source before it is leaned on.
