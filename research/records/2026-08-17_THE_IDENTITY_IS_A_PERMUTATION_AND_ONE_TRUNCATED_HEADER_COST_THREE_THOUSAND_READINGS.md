# The identity is a permutation, and one truncated header cost three thousand readings

**Date:** 2026-08-17
**Truth status:** `established-bounded` for every measured return below, each carrying its command;
`proved-derived` for the identification of a same-head identity with a permutation and of its
generated closure with a subgroup of the symmetric group; `interpretation` for the reading of a
conflicted head as a junction.
**Evidence:** `measured` — `cargo test --workspace --lib` **2,329 passed, 0 failed, 19 ignored**;
`cargo run --release -p holonic-engine --example the_material_founds_the_identity_atlas`, over four
declared subtrees — `Geometry`, `Analysis/SpecialFunctions`,
`Analysis/SpecialFunctions/Trigonometric`, `NumberTheory` — on this machine today.
**Provenance:** Brandon, 2026-08-16, on the machine reasoning about mathematics through token
manipulation: *"We want a machine that can be prompted to reason about and manipulate patterns in
text about mathematics… geometric proofs and math analysis proof methods through token manipulation
(discrete mathematics, antecedents and consequents that are implicit in code and semantics about
mathematics or code, or anything ordered which all things are)"*; and *"I want Eros to be able to
authoritatively output an atlas of common mathematics identities… prominent dynamic transport
mechanisms and tools for mathematics."*
**Plan:** [`blueprint/THE_STATEMENT_IS_A_CROSSING_WORD_AND_THE_SEPARATOR_IS_ORIENTED.md`](../../blueprint/THE_STATEMENT_IS_A_CROSSING_WORD_AND_THE_SEPARATOR_IS_ORIENTED.md),
**all five stations executed**; what remains open at the end of them is stated below. It sits under
[`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) at the station *MATHEMATICS INTO THE
INFORMATION CENTRIFUGE*.

---

## 1. The finding that dominates the rest, and it is one line of the reader

`lean_development::header_terminator` cut a declaration's header at **the first `:=` anywhere**.
Mathlib writes named arguments as `(R := R)`, so

```text
    z ∈ maxTensorProduct (R := R) C₁ C₂ ↔ …          was read as
    z ∈ maxTensorProduct (R                          an opener that never closes
```

**Forty-five of 3,383 theorem headers in `Mathlib/Geometry` came back with an unclosed bracket, and
that was enough to destroy the reading of the other three thousand.** `statement_grammar::recover`
founds a bracket species by a property that holds over the **whole** population — deliberately, and
its own documentation says so — so a single truncated member removed the parenthesis species for
everyone. With no parenthesis species the depth profile flattened, and with a flat depth the split
could not be founded either.

> **One refusal cascaded into three, and none of the three named the first.** The family came back
> without `()` and `{}`, the suppositions came back as 40,778 bare tokens, and nothing in that
> reading pointed at a terminator.

The repair is the same law the module applies everywhere else: **the terminator is the first one at
depth zero**. Measured after it, on the identical material:

```text
                                  before        after
    headers not nesting             45            3
    bracket species founded          6            8   () and {} rejoin
    suppositions read as bare    40,778          149
    statements whose split moved  3,256           18   between the two orientations
```

The three that still do not nest are exhibited by name in the run — two `by`-blocks written inside a
statement, one structure instance — and are **excluded from the founding population rather than
allowed to decide it**, which is the reader auditing its own return through the new
`lean_development::header_nests`.

**The instrument that found it is worth more than the repair.** A *near-miss census* — per candidate
species, how many statements refuse it and which — turns an invisible cascade into a measurement.
Without it the missing species is a fact with no cause attached.

## 2. Three foundings that were properties of a three-statement fixture

`statement_grammar` had been run on **three** statements of this repository's own proof plumbing.
Pointing it at mathematics falsified three of its rules, and each correction is a weakening of an
authored condition rather than an addition.

**The charset.** `StatementIsNotAscii` refused any statement outside ASCII. Measured over 18,666
`theorem`-opening lines in `Mathlib/Geometry` and `Mathlib/Algebra`: **14,150 carry a non-ASCII
character and 4,516 do not**, so the gate refused **75.8%** of the material and what it refused was
precisely the notation — `ℝ ℕ ∠ ≅ ¬ ₁ ᵥ ⟪⟫`. The rule is now `char::is_alphanumeric`, which
**coincides** with the ASCII form on every ASCII character, so admitted populations read
bit-identically. `ℝ` and `ℕ` are letters and `₁` is a digit in the material's own script, so `h₁` is
one token; `∠`, `≠`, `∈`, `↔` are symbols and remain punctuation. The grain is read off the
material's character properties rather than off a byte range the module chose.

**And the excision exposed a latent defect that only fires on notation.** `depths` pushed one entry
per **character** while every caller indexes it by **byte**. On ASCII the two coincide; `ℝ` is three
bytes, so a per-character profile drifts behind the offsets used to read it and mis-founds groups
silently. Both arms are asserted in the module.

**The separator.** The rule was *the character occurring exactly once at depth zero in every
statement*. It is the fixture's shape, not a property of a separator, and it fails structurally: a
separator marks each supposition **and** the conclusion. The founding is now split in two —
occurrence founds the separator, and among its depth-zero occurrences the admissible splits are
those leaving **a leading region of bracket groups and whitespace**, which is the property the
binder reading was already founded on, asked before the split instead of discovered afterwards as
residue.

Measured over 387 whole statements from `Mathlib/Geometry/Euclidean` under the recovered family: the
depth-zero count is **1 in 373 and plural in 13**, and in every one of the 13 the plurality is a
supposition written *inside the conclusion* with no brackets — `∃! cs : Sphere P, …`. **Both
directions are wrong there and the founding property is right**, which is why `SeparatorOrientation`
is a tiebreak and not the rule. On the full subtree it decides only **18 statements of 3,692**, each
a theorem with no suppositions at all.

**The bracket pair.** Mathematics groups in several species at once — `()`, `{}`, `[]`, `⟨⟩`, `⦃⦄`,
`⟮⟯`, `⁅⁆`, `⟪⟫` all balance over `Mathlib/Geometry` — so the *unique pair* rule founds nothing.
The object is the **family**, generating one depth together, and it is not a weakening: which species
opened a group is now recovered and carried on the group, a classification the single-pair reading
could not express. Measured on `Geometry`: **659 suppositions opened by `()` and 1,091 by `{}`**,
recovered, with nobody naming either.

## 3. The atlas: an identity is a permutation, and the heads found groups

The organ is applied **twice, to itself**. A conclusion is a statement at a smaller scale, so the
identical recovery runs over the conclusion population and founds the relation it asserts — `'='`,
carried by 1,706 of 3,364 conclusions in `Geometry` — and the two sides it relates. Nothing is told
that `=` relates two sides.

For a conclusion relating two applications of **one head**, the rearrangement of the arguments is a
permutation, and the permutations one head exhibits **generate a subgroup of the symmetric group**,
computed by exact closure.

**`Mathlib/Geometry`, 119 files, 46,752 lines, 3,692 statements:**

```text
    head                   degree  order  abelian  generators
    angle                       2      2     true  [2 1]
    perpBisector                2      2     true  [2 1]
    riemannianEDist             3      2     true  [1 3 2]
    s.mongePlane                2      2     true  [2 1]

    angle x y = angle y x
    perpBisector p₁ p₂ = perpBisector p₂ p₁
    riemannianEDist I x y = riemannianEDist I y x
    s.mongePlane i₁ i₂ = s.mongePlane i₂ i₁
```

**`riemannianEDist` is the one to read.** Its permutation is `[1 3 2]` — the first argument is
**fixed** and only the last two exchange. The machine separated a parameter from an operand, on a
head it was never told the arity of, from argument tokens alone.

**`Mathlib/Analysis/SpecialFunctions`, 95 files, 30,795 lines, 3,738 statements** — a material this
reading was not built against, and its headers all nest:

```text
    betaIntegral                    2      2     true  [2 1]
    ordinaryHypergeometricSeries    4      2     true  [1 3 2 4]

    betaIntegral v u = betaIntegral u v
    ordinaryHypergeometricSeries 𝔸 a b c = ordinaryHypergeometricSeries 𝔸 b a c
```

The second is `₂F₁(a,b;c;z) = ₂F₁(b,a;c;z)` — **the upper-parameter symmetry of the hypergeometric
series** — with the algebra `𝔸` and the lower parameter `c` held fixed and only the upper pair
exchanged. Recovered from spelling.

**The falsifier fires and is retained.** Rearrangements that are not permutations of one multiset are
returned by name as *transports that are not symmetries* — 75 in `Geometry` — each carrying which
argument on the right stands nowhere on the left. The classification can fail and is observed
failing, which is what separates it from a partition the driver authored.

## 4. The compression, and the atlas it produces

Replacing each argument by the position of its first occurrence is a **rebase**: a relabelling with
zero remainder. Two identities sharing a rebased form are one identity in two alphabets.

```text
    relations both sides read     385
    rebased forms                 287
    forms carrying more than one   50        singletons 237
```

The collapsed families are the atlas, and they are what a reference page for an operation carries:

```text
    angle x0 x1 = Real.arccos x2   <- angle x (x + y) = Real.arccos (‖x‖ / ‖x + y‖)
                                   <- angle x (x - y) = Real.arccos (‖x‖ / ‖x - y‖)
    angle x0 x1 = Real.arctan x2   <- angle x (x + y) = Real.arctan (‖y‖ / ‖x‖)
                                   <- angle x (x - y) = Real.arctan (‖y‖ / ‖x‖)
    angle x0 x1 = angle x2 x3      <- angle (-x) (-y)     = angle x y
                                   <- angle (c • x) (c • y) = angle x y
                                   <- angle (f u) (f v)   = angle u v
    angle x0 x1 = π                <- angle (-x) x = π
                                   <- angle x (-x) = π
```

**The third family is `angle`'s invariance group acting on both arguments at once** — negation,
scaling by a unit, and any admitted map — assembled from three separately written theorems by the
rebase and by nothing else. The remainder of the compression is the 237 singletons, exhibited rather
than discarded.

**And on `Mathlib/Analysis/SpecialFunctions/Trigonometric` the families are the reference page**, 61
rebased forms over 113 relations:

```text
    cos x0 = cos x1   <- cos (-θ) = cos θ
                      <- cos (2 * π - x) = cos x
                      <- cos (n * (2 * π) - x) = cos x        ... 4 more
    cos x0 = sin x1   <- cos (x - π / 2) = sin x
                      <- cos (θ - ↑(π / 2)) = sin θ
    cos x0 = 1        <- cos (0 : Angle) = 1
                      <- cos (2 * π) = 1
                      <- cos (n * (2 * π)) = 1
    arcsin x0 = x     <- arcsin (sin x) = x
    arctan x0 = x     <- arctan (tan x) = x
    Set.range x0 = Set.univ   <- Set.range cos = Set.univ
                              <- Set.range sin = Set.univ
```

**`cos x0 = cos x1` is cosine's invariance family** — evenness and `2π`-periodicity in one row,
assembled by the rebase from theorems written separately and apart. And the falsifier is doing its
job in the same run: `cos (-θ) = cos θ` is refused **as a symmetry** and kept as a substitution,
because the argument changed rather than moved.

## 5. The transport atlas, with three founded species and a two-sided verdict

A same-head relation is one of three species, founded from the two argument lists: a **symmetry** (a
permutation), a **substitution** (same arity, one position carrying a different construction), or an
**arity move**. The verdict is on the symmetry question, two-sided and decided by zero-ness rather
than by how often a form occurs.

```text
    angle    9 transports   symmetry 1 substitution 12 arity 0   CONFLICTED -- a junction
    dist    10 transports   symmetry 0 substitution  9 arity 0   NO SYMMETRY STATED IN THIS MATERIAL
    map      8 transports   symmetry 0 substitution  0 arity 0   OPEN -- no same-head relation here
```

**`angle` is `CONFLICTED` and that is the informative verdict**: it carries `angle x y = angle y x`
*and* `angle x (r • y) = angle x y`, so its two positions are neither simply symmetric nor simply
substitutable — the behaviour depends on something the head's name does not carry, which is
`H.0362`'s atlas edge with its recognition condition still missing.

**`dist`'s row is an aperture statement, not a claim.** `dist` is symmetric and mathlib says so in
`Topology`, which this subtree does not contain. The run says this in its own output.

## 5b. The transport graph, and the atlas emitted as data

A relation between **two** heads is an edge: this operation may be re-presented as that one, with the
rebased form as the edge's label. Composing two edges is composing two transports.

**Bound names are held out, and the reader founds which they are.** `lean_development` already
returns `local_bindings` per declaration, so a head its own statement binds is a variable standing
where an operation would. Without that separation the graph's most connected nodes were `f`, `p`,
`x` and `0` — the graph reading its material's alphabet. Measured on `Geometry`: **84 relations held
out**, and the graph falls from 234 heads and 224 edges to **176 heads and 151 edges**.

```text
    two-step routes with NO direct edge   44
      I.target  ->  range  ->  closure
      hf.mfderivToContinuousLinearEquiv  ->  mfderiv  ->  ContinuousLinearMap.id
      Finset.univ.affineCombination  ->  s.touchpoint  ->  s.points
```

Those are compositions the corpus licenses and never states in one theorem.

**The atlas is emitted**, `meta/IDENTITY_ATLAS_<material>.tsv`, 843 rows for `Geometry`, in four
kinds — `symmetry`, `transport`, `edge`, `identity` — each `identity` row carrying the corpus
statement **verbatim** in its witness column. An atlas whose rows cannot be taken back to the
material they were read off is a summary, and a summary is not a deposit.

## 5c. The proof is a word, and the algebra says what cancelled

**Station three.** A proof is a sequence of moves; each move is a crossing whose state is binary —
in the word or not — so a proof is a subset and two proofs compose by symmetric difference. That is
the grading group of `multiquadratic` exactly. Each distinct move is given a distinct **prime**, so
the generators are independent by construction, and a move used twice contributes `√p·√p = p` and
leaves the grading: **it cancels**. The word splits two ways and only two:

```text
    the GRADE        the moves used an ODD number of times   -- what survives
    the COEFFICIENT  the primes used an EVEN number of times -- what cancelled
```

**The identification is verified, not asserted.** On `Geometry`: 266 distinct moves, 1,974 proofs
read, and **1,930 words were rebuilt by actually multiplying `√p` in `multiquadratic`**, with both
the grade *and* the cancelled rational asserted equal to the parity reading; 44 refused past a
declared eight-generator aperture.

Put to the pairs the compression already supplies — two theorems reaching one rebased identity —

```text
    same grade      15   the two proofs differ only by moves that cancelled
    grade differs   46   the symmetric difference IS the remainder

    SignType.sign x0 = 1
      … SignType.sign (s.excenterWeights {i} j) = 1
      … SignType.sign (s.excenterWeights ∅ i) = 1
      REMAINDER   only the first: [convert simp simp_rw]   only the second: []
```

**One bound, stated in the run because it is real:** this algebra is **commutative**, so the word
forgets the order of the moves and keeps their parity. It records what survived cancellation, never
the sequence. A carrier keeping the order must be non-commutative, and that is
`structure_group::curvature_commutator`'s subject rather than this one's.

## 5d. The identity meets arithmetic, and the test can refute

**Station four**, and it is what turns everything above from a report about a corpus into a claim
about mathematics. A **resolver** is an organ returning an exact rational from exact rational
arguments. Its own symmetry group is recovered the same way the corpus's was — every permutation of
its arguments tested, admitted only if it holds on **every** probe — and the admitted set is
asserted closed under composition, which catches a defect in the test rather than proving a theorem.

**The driver never pairs a resolver with an identity.** Matching is by arity, every same-arity pair
is tested, and the arithmetic decides.

```text
    resolver                     arity  order  separates  group
    additive-composition             2      2       true  [2 1]
    oriented-difference              2      1       true  identity only      <- the control
    squared-separation               2      2       true  [2 1]
    beta-on-integers                 2      2       true  [2 1]
    corner-cosine                    3      2       true  [2 1 3]
    cross-ratio                      4      4       true  [2 1 4 3] [3 4 1 2] [4 3 2 1]
    hypergeometric-partial-sum       4      2       true  [1 3 2 4]
```

`cross-ratio` is the **standing organ** `relational_geometry::receiver_atlas::cross_ratio`, called
rather than rewritten — its own documentation refuses a second carrier by name — and its group of
order four is the classical invariance, **recovered by arithmetic rather than quoted**.

**And the join separates in both directions, which is the whole evidence:**

```text
    ordinaryHypergeometricSeries   corpus states [1 3 2 4]
        refuted   by cross-ratio                  arithmetic breaks [1 3 2 4]
        CONFIRMED by hypergeometric-partial-sum

    Nonnegg                        corpus states [2 1 4 3]        (Mathlib/NumberTheory)
        CONFIRMED by cross-ratio                  its own group has order 4
        refuted   by hypergeometric-partial-sum   arithmetic breaks [2 1 4 3]
```

Two arity-four heads, two arity-four resolvers, each head matching exactly one and refuted by the
other. Also confirmed: `betaIntegral` against `beta-on-integers` — `B(m,n) = B(n,m)` computed
exactly on rationals — and `jacobiSum`, `legendreSym`, `qrSign` at arity two.

**The run states its own discrimination and it is small at low arity.** A confirmation at arity 2
distinguishes one of 2 permutations and at arity 4 one of 24, so **four confirmations of a
two-letter symmetry are not four independent facts**: every symmetric binary operation confirms
every stated exchange, and only the control can fail there. The separation in this run is at
arity four.

## 5e. The codec's surface was read as a limit, and the join was not shut

**Brandon, on being told the closure organ was unreachable because mathlib states its parameters as
variables:** *"Why are we constrained by mathlib? its just a codec."*

He is right and the sentence is withdrawn. **A universally quantified statement is a claim about
every instance, so it licenses instantiation rather than forbidding it.** What the corpus supplies is
the *permutation*; the parameter family and the organ that classifies it are this body's, and the
question is whether the two commute. Nothing was ever needed from mathlib but the permutation.

And the reachable form is **stronger** than the resolver test, because it is structural rather than
about values: not *does an organ return the same number under a permutation*, but **does the
permutation preserve the classification the organ computes.**

`hypergeometric_closure` decides whether a three-site turning equation's solution closes — whether
its return group is finite — by sorting integers on a circle. Swept over the machine's own exact
family, `a, b, c` each ranging over the eleven rationals with denominator at most five in `[0,1]`:

```text
    dial values swept   11        triples 1,331
    classification      closes 12   does-not-close 726   splits 593
    the sweep separates true   -- all three species present, so a permutation CAN break it
```

**The closure locus's own symmetry group, computed by the organ:**

```text
    [1 2 3]   PRESERVES the classification everywhere
    [2 1 3]   PRESERVES the classification everywhere
    [1 3 2]   breaks it at (1/5, 1/5, 0)
    [2 3 1]   breaks it at (1/5, 1/5, 0)
    [3 1 2]   breaks it at (1/5, 1/5, 0)
    [3 2 1]   breaks it at (1/5, 1/5, 0)
    order 2, and closure under composition is asserted
```

**And the corpus's permutation lands in it.** Every three-subset of positions that the corpus's
permutation maps to itself is tested — nothing is chosen, and a subset it does not preserve is not a
restriction at all:

```text
    ordinaryHypergeometricSeries  [1 3 2 4]  on positions (2 3 4)  restricts to [2 1 3]
                                                              IN the closure locus's group
    ordinaryHypergeometricSeries  [1 3 2 4]  on positions (1 2 3)  restricts to [1 3 2]
                                                              NOT in it
```

Positions `(2 3 4)` are `(a, b, c)` — the dials — and that restriction is exactly the group the organ
computed. Positions `(1 2 3)` include the algebra token, for which the organ has no dial, and that
restriction fails as it should. **Both are reported; the driver picks neither.**

> **A symmetry written in tokens by one body, and a classification computed exactly by another over a
> family the first never mentioned, agree.** That is the joint the centrifuge record named on
> 2026-08-14 and it is closed — not by carrying a mathlib statement into a symbolic object, which is
> still not done, but by noticing that the two bodies only ever needed to exchange a permutation.

## 5f. The statement is carried, and the joint named 2026-08-14 is closed

The closure organ was reached by exchanging a permutation, which translated no statement. **This
carries the statement.** Driver:
`crates/holonic-engine/examples/the_integrand_is_read_and_the_organ_names_its_transcendental.rs`,
over `Mathlib/Analysis/SpecialFunctions/Integrals` — 3 files, 76 whole theorem statements, of which
**37 carry a conclusion, an equality and a depth-zero comma**, which is the integral shape founded by
the same oriented-separator law one scale further down.

**What the organ is asked.** `hermite_reduction` splits `f = h' + g` and returns the **residue
polynomial** with no root extracted. That polynomial decides the transcendental: no residues ⟹ the
antiderivative is rational; all residues rational ⟹ logarithms; some residue not rational ⟹ an
arctangent. **The corpus's own right-hand side says which one it used, and the organ never sees it.**

```text
    the organ predicts arctan
      integral_inv_sq_add_sq    (c ^ 2 + x ^ 2)⁻¹   corpus: c⁻¹ * (arctan (b/c) − arctan (a/c))
      integral_div_sq_add_sq    c / (c ^ 2 + x ^ 2) corpus: arctan (b/c) − arctan (a/c)
    the organ predicts log        (6 statements)
      integral_inv              x⁻¹                 corpus: log (b / a)
      integral_one_div          1 / x               corpus: log (b / a)
    the organ predicts rational   (2 statements)
      integral_id               x                   corpus: (b ^ 2 − a ^ 2) / 2

    DISAGREEMENTS  0        parameter sweep moved a class  0        schedules disagreed  0
```

Three distinct classes, ten statements, **zero disagreements**. Both declared reduction schedules were
run on every integrand and the residue class did not move — the module's own gauge, measured rather
than assumed — and every bound parameter was instantiated at 1, 2 and 3 with the class fixed.

**And the second organ takes what the first refuses.** `elementary_chart` decides `∫ R·e^g` by the
consistency of one exact rational linear system:

```text
    integral_exp   exp x   ELEMENTARY -- realizer [1], differentiated back
                           corpus: exp b − exp a
```

`∫e^x = 1·e^x`, and the table writes the same antiderivative at two ends. The organ and the table
agree on the indefinite object; the table adds the boundary the organ does not carry.

**The reader's precedence is declared, not founded, and the run says so.** A corpus that brackets
whenever it matters never exhibits the precedence it relies on. The declaration is safe **because the
answer key is external**: a wrong precedence gives a wrong integrand, a wrong integrand gives a wrong
class, and a wrong class disagrees with the corpus's own closed form. The disagreement column is that
falsifier and it is printed first. Twenty-seven integrands are refused by name and retained —
`sin x`, `log s`, `√(1 − x²)`, `x ^ r` with a variable exponent — because they are not rational
functions and this is not their organ.

**And the fourth transport is not driven, which is a return rather than a gap.**
`exponentiated_ratio`'s law is `exp(a+b) = exp(a)·exp(b)`, and the corpus states it as
`Real.exp_add`. Putting one to the other would return agreement carrying **no evidence**:
`exponentiate` is `2^{Σ q_k log₂ p_k} = Π p_k^{q_k}`, so the homomorphism holds by construction and no
material could make it fail — a check whose material cannot vary the property under test. What is
real is one-sided: the organ **refuses a fractional coefficient**, because a fractional exponent
leaves `ℚ` for the finer chart, while the corpus states the law over `ℝ` where that boundary does not
exist. They do not disagree; the organ's aperture is a distinction its chart can see and the corpus's
cannot.

## 6. What is open, stated as such

**Stations three and four were built the same day and are reported above.** What remains open at
the end of them:

**The crossing word is commutative and therefore order-blind.** Keeping the sequence needs a
non-commutative carrier; `structure_group::curvature_commutator` is where that lives and nothing
joins it to a proof body.

**The centrifuge record's sentence is discharged.** All four transports it named are accounted for:
`hypergeometric_closure` by exchanging a permutation, `hermite_reduction` and `elementary_chart` by
carrying the statement into an exact symbolic object, and `exponentiated_ratio` by the measured
finding that driving it would be a tautology. What remains is coverage rather than a joint: the
expression reader's alphabet is rational functions and one exponential shape, and everything outside
it is refused by name.

**The resolver population is written in the driver, and only two of seven are standing organs.**
`cross-ratio` is called from `relational_geometry`; `corner-cosine` states `contact_gluing`'s law
because that organ returns a corner only inside a `ContactTriangle` this probe has no material for;
the other five are arithmetic written here. The pairing is not authored and the control refutes, but
a resolver population drawn entirely from standing organs would be stronger and is owed.

## 7. What this record does not claim

Nothing was elaborated, type-checked, or submitted to a kernel; Lean is text throughout. A group
returned here is the group **the writing exhibits**, which is a claim about the corpus rather than
about the mathematics behind it — the two agree exactly when the corpus states its heads'
symmetries, and that is a property of the corpus.

The atlas covers two subtrees of one library, each named in the run. A head absent from the group
table generated nothing on this material; that is not a claim that it has no symmetry. Coverage is
bounded by a stated refusal: a side carrying punctuation at its own depth is not one application and
is declined, which is why 385 of 1,706 equational conclusions read both sides. No Millennium result
moved.
