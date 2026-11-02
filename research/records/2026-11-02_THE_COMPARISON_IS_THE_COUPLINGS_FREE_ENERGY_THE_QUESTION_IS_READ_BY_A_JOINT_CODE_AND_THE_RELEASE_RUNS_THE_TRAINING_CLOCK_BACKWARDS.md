# The comparison is the coupling's free energy, the question is read by a joint code, and the release runs the training clock backwards

**Status: design, November 2 (Claude), for Athena alpha (#404), with its issues #601, #602 and #603.**
The findings of §2 are measured: exterior readings of the public GSM8K training split and of the
source (receipts in §9), or read from the field's own records. The design of §3 is agent-inferred
from the laws named at each item. The acceptance of §5 is fixed before anything in §3 is built or
run.

## 0. Why this record

On November 2 Brandon asked Claude to bring the day's unification (the blanket, the keys as its
slopes, the lock as its dual) to Athena's implementation and to take authority over the repository's
architecture for it, because the field's measurements and gradients seemed to him the wrong ones.
He asked for designs, a plan, issues, and the places to clean up or concentrate, critically and
abstractly. The design thread's pending step was PR #600 (a site opens on its whole moment) and a
90-minute card run whose mark is a question effect of at least 0.1 bits a byte at the context read.

This record reads the field against the governing laws (CLAUDE.md: loss is the logarithm of a ratio
of Holons, with its phase part; the comparison is mutual; a code is a code; the anti-reduction law),
names what it measures and how its gradient is formed, gives one design, fixes its acceptance, and
lists the issues and the cleanup. Its lessons check is §7.

## 1. The field as it stands, in the elementary objects

`hnn::tower::field` (3,804 lines; card realization `crates/holonics-cuda/src/hnn/field.rs`) runs one
GSM8K problem as one region. Read in the elementary objects:

| Part of the field | Object | Where |
|---|---|---|
| a region: question sites resolved, answer sites and voids open | a passage of one Holon over a complex whose cells are the region's sites; the question is one port, the answer another | `Region` |
| the opening `x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1))` (+ `C s_t` with #600) | the helical code's encoding `E` and its phase-carried moment | module law table |
| the charts `k, p, v` at still and turned mode sets | the constitution's faces | `FieldDeclaration` |
| ring phasors on the dyadic and triadic towers, skin `e^(−2πd/n)` | parametron rings on navigator towers; the skin is the ring's dissipation | `ring_periods` |
| the contact `z_ij = 2^(−β) Σ_m [D_m Re(conj p̃ k̃) − D_m² |k̃|²/2] − ⌊log₂|i−j|⌋` | a pair contact: the receiver's lock against the source as it arrives, paying the source's address | `lock` |
| the current `y_i = conj(U_i) Σ e_ij D ṽ_j / Σ e_ij` | the interconnection: the phase-carried moment gathered at a site | module law table |
| the face `p̂_t = 2^(z_t)/Σ 2^z`, `z_t = R r̂(x^K_t) + c` | the receiver's face, read through its own readout `R` | module law table |
| the code `Σ −log₂ p̂_t(u_t)` over the unresolved sites, covector `p̂ − q`, the certified held step | the comparison and its deposition (`hnn.certified-normal-step`) | `FieldLearner` |
| the release: momentum `μ = ½`, a pump doubling `β` over its levels, a lock at majority, the extent where the void locks | a receiver's reception at the request boundary, with an authored schedule | `Field::release` |
| the reads: bits a byte at the opening, at the context (one answer site in four open), beside a foil question; the question effect = foil − context | readings | `field_train.rs` |

## 2. What the field measures and how its gradient is formed

### 2.1 The comparison counts a lock only at the same place

[measured; the law from CLAUDE.md and the October 19 micro-control design §7] The loss law compares
the produced `|H⟩` with the target `|T⟩`, both encoded through the same `E` and phase transport, as
the ratio `R = Ĝ_(T←H)`, whose logarithm has a magnitude part and a phase part (the winding branch).
The October 19 design states the lock as zero slip between two clocks: the release and the target
are strands on their own clocks, `λ` is the longest order-keeping coupling of equal classes,
`F* = |H| + |T| − 2λ`, and the plateaus carry lags. That is the project's success test of record
(stated in the repository by [the October 24 tower record](2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT_AND_EVERY_LOOK_IS_READ_BY_ITS_LOCK.md)),
and its owner is `receiver::coupling` (atlas `code.lock-friction-alignment-code`, Lean
`HNN/EffectiveTension:alignment_code`).

The field's code compares `p̂_t` with the target's class at the same place `t`. Of all the
order-keeping couplings between the release's places and the target's cells it keeps one, the
diagonal. Three consequences follow.
- **No phase part.** A release that is right but one place late is charged at every later byte, and
  the lag that would say so is never formed.
- **One strand.** The target enters as a class label read through the face's own readout `R`, not
  encoded through `E`. The comparison's covector never reaches the target's encoding, so only one of
  the two participants moves.
- **The place-wise marginal.** Where content does not sit at fixed places, the best face under a
  place-wise target is the average over phrasings at that place. In the 7,473 GSM8K training answers
  the commonest byte at places 0 to 63 spells `The t` and then a space at 60 of the 64 places
  (receipt `place_mode_output.txt`). The field20 run's releases locked only spaces and a starting
  `T`/`Th` (#404, the dispersing record §16.20). The pump raises `β` until a face's top class holds a
  majority, so what it can lock is the place-wise top class: the space (agent-inferred, from the two
  readings).

This is the multimodality failure of non-autoregressive generation, where the per-place target
averages over phrasings (Gu et al. 2018; Ghazvininejad et al. 2019), and the literature's cure is
the one the lock test of record already names: compare through a monotone coupling
(Ghazvininejad et al. 2020, aligned cross-entropy; Graves et al. 2006 and Saharia et al. 2020, the
CTC family). It is also recorded failure 4 recurring (the native readout sat at the byte marginal), one
level up: at the place-wise marginal. No change to the opening removes it while the comparison
stays at the place. #600 changes the opening only.

### 2.2 The question is read where the answer cannot restate itself

[measured] The context read opens the answer sites at `t ≡ r (mod 4)` with every other site
resolved, and the question effect is the foil's code less the own code. By the chain rule,

```text
I(Q; A) = I(Q; A_res) + I(Q; A_open | A_res),
```

so the read measures only what the question adds after three quarters of the answer has been given.
The field's own record says why it added the foil: a neighbour inside the answer carries much of a
digit, since the result after `>>` repeats the one before it. Measured over every answer byte of the
training split, each read once across the four parts (receipt `screen_output.txt`):

| An open byte is | Share of answer bytes | Of which digits | Of which letters |
|---|---|---|---|
| glue (spaces, punctuation, operators, annotation marks) | 31.1% | | |
| restated elsewhere in the answer with that byte resolved | 45.6% | 14.9% | 30.7% |
| restated only in the question | 12.4% | 0.62% | 11.75% |
| restated nowhere | 10.9% | 0.80% | 10.1% |

The answer restates 91% of its own digit bytes. For the 0.62% of answer bytes that are digits of a
number the answer does not restate, the question is the only other place the number stands.

**The ceiling.** In this read the three bytes on each side of an open byte are resolved, so

```text
I(Q; A_open | A_res) ≤ H(A_open | A_res) ≤ Σ_i H(a_i | A_res) ≤ Σ_i H(a_i | l₃(i), r₃(i)),
```

and a held-out model's cross-entropy bounds the last term from above. A Witten–Bell interpolated
neighbour model on the contexts `(l₃,r₃)`, `(l₂,r₂)`, `(l₁,r₁)`, fit on the problems whose index is not
divisible by five and read on the rest (1,495 problems, 432,270 answer bytes; receipt
`bound_output.txt`), codes the answer at 0.904 bits a byte. Its series by class:

| Class | Bits a byte in the class | Contribution to the 0.904 |
|---|---|---|
| restated digits | 2.424 | 0.359 |
| restated letters | 0.716 | 0.221 |
| glue | 0.448 | 0.140 |
| question-only letters | 0.854 | 0.099 |
| letters restated nowhere | 0.492 | 0.050 |
| digits restated nowhere | 2.506 | 0.020 |
| question-only digits | 2.530 | 0.015 |

A restated byte is fixed by its other occurrence in the resolved answer, which any reader of the
whole answer recovers without the question. The bytes the answer does not restate contribute 0.184
bits a byte, digits 0.035 of it. So a reader of the question, however perfect, shows at most about
0.18 bits a byte at this read, plus what it adds at glue and restated bytes beyond what the rest of
the answer already fixes there, and nearly all of it is letters of names and nouns.

The ceiling bounds the information. A field's measured effect (its code beside the foil less its
code beside its own question) can exceed it only by being misled by the foil, and a field that takes
names from whatever question stands beside it is misled exactly so. The pending run's mark (0.1 bits a
byte) asks for more than half of the ceiling, and what reaches it is spelling names out of the
question, rewarded once by the own question and again by the foil: the channel of the copier retired
on November 2 (the antipattern record's instance 4). The plan of a solution (which numbers, which
operations, in which order) is restated inside the answer, so this read cannot see it. A pass would read that channel, not
composition; a fail cannot be told from the read's own ceiling.

### 2.3 The codes it reports are not codes

[measured from the source] Training draws each site unresolved with probability `τ`, `τ` uniform on
`(0, 1]`, and codes `Σ −log₂ p̂` over the unresolved sites, unweighted (`field_train.rs`, `shape`).
With `τ` uniform the number of open sites among `m` is uniform on `{0, …, m}`
(`∫₀¹ C(m,k) τᵏ(1−τ)^(m−k) dτ = 1/(m+1)`) and the open set is uniform given its size, so the masks
already draw the states of a random reading order. The weight is what is missing. The random-order
chain code is

```text
E_σ L_σ(A) = m · E_(K ~ U{1..m}) E_(|open| = K) [ (1/K) Σ_(i open) −log₂ p̂_i(a_i | resolved) ],
```

(Hoogeboom et al. 2022, the order-agnostic bound; Sahoo et al. 2024 and Shi et al. 2024 write it as
the `1/τ` weight), and `E_σ L_σ(A) ≥ −log₂ E_σ P_σ(A)`, the code of the order mixture (Jensen). The
unweighted sum is a pseudo-likelihood: its minimum is no description length of the answer and its
gradient is not the joint code's.

The held reads inherit this. The opening read (every answer site open at once) is a product of
per-site faces, which is why its floor sits at the byte table (5.34 bits a byte against the table's
5.05, `field_train.rs`, `context_regions`). The context read is a pseudo-likelihood of a quarter
given three quarters. Neither is `−log₂ P(A | Q)` for any distribution over answers, so "bits a byte" names a
different quantity at each read (recorded failures 7, a code length read as progress, and 18, a sum
replaced its series).

### 2.4 The release is an authored schedule the training never meets

[read from the source] The release carries momentum `μ = ½`, a pump doubling `β` over its levels to
`PUMP_TOP`, a lock where the top class holds a majority, and the extent where the void locks. The lock
at majority is derived: it is the only threshold at which the top class is unique. The doubling and
the level count are not derived from the field. Training reads uniform masks and front regions
(§14.6, built to bring training to the release's own states); the release's states at high `β` are
met by no comparison.

### 2.5 The library and the learner do not meet

[measured from the source; receipt `closure_output.txt`] `field.rs` imports 27 items from the
October tower (`hnn::tower`: affine, covector, deposit step, exp series, face code, ratio adjoint,
release and others) and two items from `hnn::keyed_modes`. `field_train.rs` imports the field,
`TowerFace` and `Units`. Counting every module-level `crate::`, `super::` and `self::` reference as a
use, transitively, from `hnn::tower::field`, `hnn::tower` and `hnn::units`:
- 120 of the 355 modules of `crates/holonics/src` (155,269 lines) are reached, and 235 modules
  (156,119 lines; 119,213 outside `hnn::tests`) are reached by no path.
- Reached by no path at all: `physics` (10,343 lines), `hnn::section_lock` (1,248), `hnn::overture`
  (826, the overture route unparked on October 29, #146), `hnn::wave` (518), and `receiver::coupling`
  (1,013), the owner of the success test of record.
- Mostly unreached: `holarchy` (9,416 of 10,202 lines), `receiver` (12,634 of 19,740),
  `compression` (12,579 of 24,785), `hnn::reference` (17,360 of 26,533), `hnn::constitution`
  (15,483 of 35,467).

Module-level reach overstates use, so these are lower bounds on what the learner does not run.
`field_train.rs` reimplements the coupling's recurrence as a private read ("nothing of it enters the
field"). The atlas already joins the three laws the comparison needs, and the learner consumes none of
them:
- `code.lock-friction-alignment-code`: the lock's friction is the conditional code of in-order copying
  with the coupling given;
- `receiver.deletion-trace-likelihood`: on a soft key the coupling's covector is the surviving
  posterior mass less the predicted mass (Lean `Transport/DeletionReceiver:covector_column`);
- `radix.held-face-reading-order`: the chain rule holds in every reading order, and a held face gains
  the same information in every order, paid where the order leaves places free.

The anti-reduction law (every operator has a caller in the live learner and an acceptance that
vanishes when it is removed) fails on both sides: the learner's comparison has no owner in the
library, and half the library has no caller in the learner. Two modules are named `field`:
`hnn::field` (the HNN's complex of closing rotor rings and pair contacts) and `hnn::tower::field`.

### 2.6 Data

GSM8K alone is 7,473 training problems with 2,150,033 answer bytes, a small budget for a learner
(recorded failure 10, too little data, names the risk). GSM8K-only to start stands (Brandon, October 31); the lawful lever beside it is the overture
route of #146 (inherited coefficients seed native navigators' initial configuration and constitution,
converted exactly at the boundary), whose owner `hnn::overture` the learner does not reach.

## 3. The design

### 3.0 One object at three temperatures

[agent-inferred] The comparison, the measurement and the release are one object: the coupling
between the produced strand `H` and the target strand `T`. At `β → ∞` it is the lock test of record
(`λ`, `F*`, the plateaus and their lags). At `β = 1` it is the learning comparison, a conditional code
of `T` given `H` whose covector is the posterior contact. Along the release, `β` is the clock and the
clicks are its phase transitions. This is the afternoon's blanket at one more place: the coupling's
free energy is a sum over couplings that dequantizes to the max over couplings as `β → ∞`, the way the
Ronkin function's limit is the tropical patchwork (Kenyon, Okounkov and Sheffield 2006 for dimers);
the slopes are the keys, the Fenchel gap `N(x) + σ(k) − ⟨k, x⟩` is a relative entropy, and its
gradient is `p − q`. Here the valve is the contact `(i, j)` and the network is the coupling lattice.
The atlas already states the general law (`navigation.path-loop-tropical`, the October 28 free-energy
record): a free energy over the walks of a graph whose low-temperature face is the least action cost.
The couplings are the monotone walks of the lattice of places against cells, so the comparison is one
case of it, and the lock test is its low-temperature face.

### 3.1 The comparison is the coupling's free energy (#601)

[agent-inferred; the owners named are existing] **Objects.** Two strands: the release's faces
`p̂_1, …, p̂_n` at the answer port on the release's clock, and the target `t_1, …, t_m` on its own. A
pair contact joins a place `i` to a cell `j`; its slip is the friction. The receipt is the posterior
contact field and its lags.

**Equations at the consumer.** A coupling `c` is an order-keeping injection of `T`'s cells into `H`'s
places; a place not coupled writes the void `∅`.

```text
Z(T | H) = Σ_c Π_((i,j)∈c) p̂_i(t_j) · Π_(i∉c) p̂_i(∅),        L(T | H) = −log₂ Z
P(i, j) = P(i−1, j) p̂_i(∅) + P(i−1, j−1) p̂_i(t_j),   P(0, 0) = 1        (prefix sweep)
S(i, j) = S(i+1, j) p̂_(i+1)(∅) + S(i+1, j+1) p̂_(i+1)(t_(j+1)),   S(n, m) = 1   (suffix sweep)
Z = P(n, m) = S(0, 0),   γ_ij = P(i−1, j−1) p̂_i(t_j) S(i, j) / Z     (posterior contact)
r_i = Σ_j γ_ij e_(t_j) + (1 − Σ_j γ_ij) e_∅       (the target the coupling places at i)
∂L/∂(logits at i) = p̂_i − r_i                   (the learning covector)
```

- **A code.** Distinct couplings are distinct writings of the `n` places, and dropping the voids sends
  each writing to exactly one strand, so `Σ_T 2^(−L(T|H)) = 1`. (The sweeps are the October 19 `P` and
  `S` in sums instead of maxima.)
- **Never worse than the place.** The diagonal coupling is one term of `Z`, so
  `L(T | H) ≤ L_place(T | H) = Σ_j −log₂ p̂_j(t_j) + Σ_(i>m) −log₂ p̂_i(∅)`, with equality only when every
  other coupling has weight zero.
- **The covector is the atlas's.** `p̂_i − r_i` is `receiver.deletion-trace-likelihood`'s surviving
  posterior mass less the predicted mass, now at the field's answer port.
- **The success test is its zero-temperature face.** At temperature,
  `L_β(T|H) = −β⁻¹ log₂ Σ_c 2^(−β L_c) → min_c L_c` as `β → ∞`. Add the second slip (a target cell the
  release omits: a move `P(i, j−1)·2^(−ℓ_T(j))` in the prefix sweep and its mirror in the suffix sweep,
  `ℓ_T(j)` the omitted cell's code); with equality faces and unit charges for both slips the limit is
  `|H| + |T| − 2λ = F*`, `code.lock-friction-alignment-code`'s value, which `receiver::coupling`
  computes today. One owner carries both temperatures. At temperature one each cell is charged its
  code, not a unit, which removes the first of the three differences that row names between the
  friction and the information distance.
- **The phase part.** On a ring of modulus `D` the contact `(i, j)` carries the lag `d = i − j` as its
  winding `⌊d/D⌋` and residue `d mod D`. The receipt's phase is the `γ`-weighted lag field per ring,
  the October 19 plateaus at temperature: `ℓ = log R` has the coupling code as its magnitude and the lag
  field as its turn. A release one place late couples at nearly zero friction and reads lag `+1`
  everywhere after the slip, where the place-wise code calls almost every byte wrong. The consumer is
  `ratio.phase-alignment-descent`: the turned modes descend the lag by alignment.
- **Both strands move.** The face reads a class through the same `E` that encodes the target (the loss
  law's "encoded through the same `E` and phase transport"), for example `z_i(a) = Re⟨R r̂_i, E(a)⟩` in
  place of a separate readout, so the comparison's covector reaches the target's encoding at its end of
  each contact. The symmetric pair `L(T|H) + L(H|T)` is the information-distance form already in
  `code.lock-friction-alignment-code`: the release must cover the target and must not write what the
  target lacks.

**Exact arithmetic and the card.** The sweeps are sums of products of the field's exact faces, carried
in the exponent chart on the logits' grain with the field's own exponential series at each sum, as its
face already is (a normalization as a systolic reduction over carried exponentials). Each anti-diagonal
`i + j = s` depends only on the two before it, so its cells are co-present with shared immutable input
and disjoint staged output (the hardware law). Each cell's two or three products are summed in one
place, and the sums across cells and problems (the code, the covectors) add exact dyadic values,
which is associative, so any partition gives the same bits. A problem's lattice has
`(m + 1)(n − m + 1)` cells (the lag runs from `0` to `n − m`), or `(n + 1)(m + 1)` with the second
slip: at a few hundred places, at most about `10⁵` cell updates a problem. The card realization is part of the build (GPU first), with host
parity.

**The void.** A void place now writes nothing wherever it stands, so a release is its non-void places
in order, and its extent is no longer read at the first void.

**What it changes.** The face is no longer pulled to the place-wise marginal: it is credited for
content in order wherever it stands, the turned modes are told the lag, and the target's encoding takes
part. The release is compared as it is written, at its own length, and the success test becomes the
learning comparison's own limit rather than an exterior read.

### 3.2 The question is read by a joint code (#602)

[agent-inferred] **The reading.** For a declared reading order `σ` of the answer's sites,

```text
L_σ(A | Q) = Σ_k −log₂ p̂(a_σ(k) | Q, a_σ(<k)),        I_σ(Q; A) = L_σ(A | Q′) − L_σ(A | Q),
```

with `Q′` a foil question. The chain rule's gain is the same in every order
(`radix.held-face-reading-order`), so the reading does not depend on where `σ` puts the question's
share; `σ` moves only where the share is paid, and that is the series to report (glue, letters, digits;
first occurrences and restatements). Unlike the context read it is not screened: it contains the
question's information about the plan of the solution as well as about its names.

**From the existing masks.** With `k` of the `m` answer sites resolved (the masks already draw `k` and
the resolved set uniformly), the weighted sum `(m/(m − k)) Σ_(open) −log₂ p̂` is an unbiased estimate of
`E_σ L_σ`, an upper bound on the order mixture's code (§2.3). The same weight in training makes every
training and held "bits a byte" one quantity: the order-averaged joint code. For the reading of
`I(Q; A)` the masks cover the answer only, with the question resolved.

**With §3.1.** The joint code at fixed places still pays the place-wise price at its first factors,
which is an honest number: it says what the field can do. The coupling is the comparison of releases.
The joint code is the measurement of the question; the coupling is how the field learns to answer it.

### 3.3 The release runs the training clock backwards; its clicks are phase transitions (#601)

[agent-inferred, joining Brandon's lens of November 2, which reads the click as a phase transition and
the staircase as a compressed lattice of the configurations in flux and their transformations, as in
chemistry and thermodynamics]
- **The clock.** Training masks each site with probability `τ`; its reverse starts with every answer
  site open and resolves them as `τ` falls. The weighted joint code (§3.2) trains every state that
  reverse can visit (Austin et al. 2021; Sahoo et al. 2024); a release that resolves sites only at its
  clicks weights those states differently, which the front regions already address. The release's
  schedule is the training clock run backwards, not an authored pump.
- **The schedule.** Within a state, `β` is the anneal's inverse temperature, and the lawful schedule
  keeps the thermodynamic speed constant: successive sweeps move `β` by `Δβ` with
  `Δβ² Var_β(E)` the same at every sweep, where `E` is the code of the field's current configuration and
  `β² Var_β(E)` its heat capacity (Salamon and Berry 1983; Crooks 2007). At a click, where a group of
  sites locks together, the heat capacity peaks and the schedule slows there by itself. The doubling
  pump spends the same sweeps on every octave of `β` whether or not anything is happening. The sweep
  count stays the workload's.
- **The staircase.** Locks are born together at the clicks, never one most-settled site at a time,
  and the order of the births is a chain in the lattice of configurations under local flips. In the afternoon's honeycomb valve network that lattice is exact: the dimer
  configurations of a plane bipartite graph under face flips form a distributive lattice (Propp 2002;
  Lam and Zhang 2003), the resonance lattice of a benzenoid's Kekulé structures in chemistry. A release
  is read as its staircase: which sites lock at each click, with each click's cost in bits; in the
  release's own order the joint code is the sum of its clicks' costs.
- **The lock** at majority stays (§2.4: it is derived).

### 3.4 Readings are fields, not scalars (#602)

[agent-inferred]
- **Susceptibility** `χ(a, q) = ∂L_a / ∂x⁰_q`: the answer site `a`'s code against the question site
  `q`'s opening, from the reverse the field already runs (it returns covectors to every opening). It is
  the participation of the question's sites in each answer site through the field's own transport (the
  October 28 record: attention is the field's participation, never a store), reported as a field over
  (answer site, question site).
- **Its falloff** with distance reads the field's phase: frozen (a site hears only its near field),
  liquid (a power law) or gaseous (flat), which measures the dispersing field's own law (its §2).
- **The lock field**: `λ`, `F*` and the plateaus' lags for each held problem, against its own target and
  against a foil target.
- Every reading is reported as its series (lesson 19).

### 3.5 A witness before any run (#601)

[agent-inferred] Hand-set strands at terrain size: a release equal to its target one place late (a
leading void), one with a byte inserted, one with a byte deleted. The place-wise code charges every
byte after the slip; the coupling's code charges the slip alone, and its phase part reads lag `+1`
(the first two) or `−1` (the third) after it. One certified step on each covector: the coupling's moves
the faces toward the target's content, the place-wise one toward the place-wise top class. Host and
card bit-equal. The witness is evidence of the comparison's law, never the goal (lesson 12).

## 4. PR #600 and the pending run

[agent-inferred]
- **Merge #600.** It repairs a located cause (§16.21: every chart read a trigram), its gate and tests are
  clean, and its sampled card parity holds (every read, face, covector and release equal). It changes the opening, not the comparison.
- **Do not launch the 90-minute run with its present mark and stop rule** (question effect at least 0.1
  bits a byte at the context read; stop when the held effect is at or below the foil's). By §2.2 the
  mark reads the copier's channel and has a ceiling near 0.18; by §2.1 the release stays at the
  place-wise top class whatever the opening carries. The card's next learner run carries §3.1 and §3.2
  with their card realizations and parity, after §3.5's witness, read by §5.

## 5. Acceptance, fixed now

- **A1, the lock test of record.** On held problems that no run has read, the releases' `λ` against
  their own targets rises and `F*` falls across laps, and `λ` against the own target exceeds `λ` against
  a foil target (another held problem's answer), summed over the held problems. The lags are reported
  as their series.
- **A2, the question's information.** `I_σ(Q; A)` for each held answer, in the declared order and the
  weighted joint code, rises across laps, reported as its series over the answer's sites.
- **A3, the output.** Every held release is shown whole beside its foil's release, as it came out, with
  no grading by numerals or delimiters.
- **Retired as an acceptance:** the context read's question effect and its stop rule. The context read
  stays as a reading of completion.

A release that recites the question's names raises A1 and A2 without solving anything (recorded failure 2,
the copier's recurrences). A3 is where that is seen, so A3 is part of every report.

## 6. Plan and issues

The order (sequential where a step consumes another's return):
1. **#602 first, in the masks** (small): the weight `m/(m − k)` in training and in the held reads; the
   joint code's question information and its series in every receipt; the context mark retired as an
   acceptance.
2. **#601, the comparison** (the main build): `receiver::coupling`'s temperature-one passage
   (sums, posterior, lag field) with the place-wise code as its diagonal; the face read through `E`;
   `FieldLearner` consuming the posterior's covector at the answer port and the lag field at the turned
   modes; the card realization with parity; §3.5's witness; then the run under §5. The release's
   schedule from the heat capacity follows once the joint code reads each click's cost.
3. **#603, consolidation**, beside the two on disjoint owners: each unreached module gets its consumer
   in the live learner or is retired after its law moves to Lean or a guide; one name per `field`; the
   field's module doc states the current law only; `field_train`'s private coupling retired onto
   `receiver::coupling`; CONSTRUCTION_STATE, THE_REBUILD and the issue lists in CLAUDE.md and AGENTS.md
   brought to November; the status lines of #405 to #407; the working machine's worktrees.

**Where to concentrate.** The comparison and the reading (#601, #602) decide whether anything the
field learns can be seen; the opening and the charts are downstream of them. **Where to clean.** The
half of the library that the learner does not reach, the duplicate coupling, the two `field` modules,
and the patch history inside the field's module doc and its 2,123-line record (#603).

## 7. The recorded failures each choice could repeat

| Choice | Failure it could repeat | Why it does not, or what holds it |
|---|---|---|
| the coupling comparison (§3.1) | an authored routine standing in for learning (1); catered machinery | the coupling computes no answer: it is the comparison of record at temperature, and the release still comes from the field |
| the coupling comparison | recitation counted as generation (2); the copier's recurrences | reciting the question's names raises A1 and A2; A3 reads the output whole in every report |
| the coupling comparison | text run on its codec's grain as the exception (3) | strands of classes on clocks: text, raster strands of images, acoustic frames and motor screw words alike (`receiver::coupling` already states its equality face codec-neutral) |
| the joint code (§3.2) | a code length read as progress (7); a sum replaced its series (18) | a reading beside the output, never the success; reported as its series over sites |
| the heat-capacity schedule (§3.3) | an authored routine; a limit without its workload (15) | the schedule reads the field's own fluctuation; the sweep count stays the workload's |
| the witness (§3.5) | a known-truth fixture became the goal (11) | evidence of the comparison's law only; the run's acceptance is §5 |
| the recommendation (§4) | the latest phrasing narrowed the work (14) | the design keeps the whole lens: mutual comparison, the lock test, the phase part, the blanket |
| every build here | a design thought in the programming language (19) | stated as contacts, slips, lags on rings, clocks and couplings; the sweeps are their recurrence |

## 8. Lean obligations (#410)

- (a) The coupling's code is a code and never worse than the place-wise code:
  `Σ_T 2^(−L(T|H)) = 1` and `L(T|H) ≤ L_place(T|H)`.
- (b) Its tropical limit: `lim_(β→∞) L_β = min_c L_c`, equal to `alignment_code`'s `F*` at unit slips
  (joins `HNN/EffectiveTension`).
- (c) The covector identity `∂L/∂(logits at i) = p̂_i − r_i` with `r_i` the posterior (joins
  `Transport/DeletionReceiver:covector_column`).
- (d) The order-agnostic bound: the weighted masked sum's expectation is `E_σ L_σ`, and
  `E_σ L_σ(A) ≥ −log₂ E_σ P_σ(A)` (joins `radix.held-face-reading-order`'s owed chain-rule gain).
- (e) The screening identity `I(Q; A) = I(Q; A_res) + I(Q; A_open | A_res)` and the neighbour bound of
  §2.2.

## 9. Receipts

In [this record's receipts directory](2026-11-02_THE_COMPARISON_IS_THE_COUPLINGS_FREE_ENERGY_THE_QUESTION_IS_READ_BY_A_JOINT_CODE_AND_THE_RELEASE_RUNS_THE_TRAINING_CLOCK_BACKWARDS_receipts/).
Each is an exterior reading of public data or of the source: none is a learner input, an acceptance or
a mechanism, and none reads a generation. They ran on the four-core cloud container in this thread,
outside the project's build and tests, each well under its 120 s or 300 s outer timeout.
- `screen.py`, `screen_output.txt`: the restating classes of §2.2 (2.8 s).
- `bound.py`, `bound_output.txt`: the neighbour-model ceiling of §2.2 (27.8 s).
- `place_mode.py`, `place_mode_output.txt`: the place-wise commonest bytes of §2.1.
- `closure.py`, `closure_output.txt`: the module-level reach of §2.5, read at `f0e57b4b`.
- Data: the GSM8K training split, `train.jsonl`, 4,166,206 bytes, sha256
  `17f347dc51477c50d4efb83959dbb7c56297aba886e5544ee2aaed3024813465`, from the dataset's public
  repository; not committed. The standard test split was not read.
