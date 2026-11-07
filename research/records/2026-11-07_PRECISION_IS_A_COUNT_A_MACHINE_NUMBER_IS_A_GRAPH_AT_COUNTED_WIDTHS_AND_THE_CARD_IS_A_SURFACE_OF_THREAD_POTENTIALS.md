# Precision is a count: a machine number is a graph at counted widths, and the card is a surface of thread potentials

Status (2026-11-07): derived from Brandon's November 7 lens and reconciled with his earlier
statements on precision. The guides' precision law (CLAUDE.md, AGENTS.md: "Precision is the bit
widths of graphs; no floats as storage") was rewritten the same morning on the design branch
(`claude/project-thread-nclk1x`), with that day's code documentation, records and atlas rows; this
record is the law's derivation, and §6 lists every other use of the retired word and what it
becomes. Refs #76, #73.

## 1. The lens

Brandon, November 7, paraphrased (his words stay out of the repository):

- Calling the machine's arithmetic "exact", and setting it against "floating point", built an
  abstract wall into the semantics. The numbers are bit widths of graphs. Nothing involving π can be
  exact, and he never claimed it could. This is computational theory.
- The word is a bad convention, poison in the well, which the theory is above. Reconcile it with his
  earlier messages and integrate the result everywhere.
- It is parallelization theory in general: information dispersed through many cores, each with a
  lower clock than a CPU core. The GPU is a surface with many thread potentials.
- If organizations of quantum states hold distributions of information and propagate them (phonons,
  Doppler curves, formations such as rotons), and those states and their distributions are in turn
  countable subjects, then no precision is given in advance: it is whatever the organization counts.
  Physics, thermodynamics and radix say it, and transistors and parametrons are the same case:
  signalling, absorption, scattering.

## 2. What it reconciles

His earlier statements on the subject, paraphrased:

| Date | Statement |
|---|---|
| July 12 | `1.0` and `1.00` are different constructions; π is a series, not 3.14 or 3.14159. |
| July 21 | Floats are compressed glyphs; the information is in the series that composes a float. |
| September 22 | Transcendentals are their constraint identities; a float's error enters only in how its face is attained. |
| September 25 | A decimal is a collapse. |
| September 29 | The machine stores series expansions; it is active navigation. |
| October 14 | Refusing floats avoids the error of naively authored dimensions of bit precision; floats and maxes have the same problem. |
| October 15 | Bit purity is about how information lives in the dynamics of the geometry, not only in the symbols. |
| October 17 | Computation is information diffusion; transistors are elements that propagate state cycles; parametrons. |
| October 18 | The law is for dynamic precision and against arbitrary precision, an efficiency law about bit purity and not about how numbers are written; a float store kills the series whose terms group by shared denominators and numerators, where the codas cancel in the flux. |
| October 22 | Information dissolves into a receiver's kernel and is never annihilated (carried release). |
| October 31, November 1 | Hardware is a traffic system; a width is never a dial. |
| November 3 | A number is a word in a basis; compression costs navigation, a conserved exchange. |
| November 3 to 5 | Widths are branch partitions and dynamic bit registers, each only as wide as its information and chained by carries; a width is its need kept as its own binary expansion, never doubled. Floating-point numbers are themselves radix-based counts. |

The one apparent conflict: October 18 is "against arbitrary precision", while November 7 says the
precision is arbitrary. They are one law read from two sides. October's arbitrary precision is a
width that nothing counts: a hand-picked width, a format, or a width that grows because nothing
cancels or releases. November's is that no width is given in advance: a width is what the
organization holding a distribution counts for its receiver, and the counting has no top. Both
refuse a width that is not counted. "Exact" fails both: it claims a count with no bound and no
receiver.

## 3. The law

**A machine number is a graph whose terms are carried at counted bit widths.**

1. **Graph.** A value is the terms of a navigator's expansion, numerators grouped over the
   denominators they share (inversion, charts, basis, gcd, softmax and sigmoid), so terms cancel
   where the mathematics cancels them. Ratios keep their remainder; integers keep their
   factorization.
2. **Count.** A term's width is the log₂ of the number of states its organization distinguishes for
   its receiver.
   - A mode of a medium distinguishes the levels its signal separates above its noise floor: a
     channel of signal-to-noise `S/N` separates about `√(1+S/N)` levels a sample, `½ log₂(1+S/N)`
     bits (Hartley, Shannon).
   - A parametron pumped at a subharmonic of order `n` locks `n` phases, one digit of radix `n`;
     period doubling gives the binary digit.
   - A transistor separates the levels its swing spans above its thermal scale `kT/q`.
   - A register of digits of radices `r_k` distinguishes `∏ r_k` states; its width is `Σ log₂ r_k`.
   - In the machine, a term's need is read from the operation that made it (a product: the
     factors' widths added; a sum of `n` terms: the widest plus `⌈log₂ n⌉`) and kept as its own
     binary expansion, registers at its set bits merged by carries; never doubled, never set by a
     word or a format.
3. **Recursion.** Distributions of counts are countable subjects in turn: occupation patterns (`N`
   quanta over `M` modes make `C(N+M−1, N)` patterns), their populations, and formations of them
   (phonons out of a lattice's motion, rotons on the same branch further out). Each level's width is
   finite; the tower has no top. That is why no number is exact and no width is final.
4. **Release.** A term leaves its carrier only by release at a declared tolerance. What its
   receiver no longer distinguishes is scattered into other modes or absorbed by another receiver,
   that is, dissolved into the receiver's kernel, and the remainder is carried
   (`lean/HolonicsResearch/Foundation/CarriedRelease.lean`). Nothing is annihilated and nothing is
   rounded silently.
5. **Counts add in any order.** Integer and rational terms at their counted widths, summed on any
   partition of the card, give the same bits; float addition is not associative. The bit-identity of
   a whole lap across the host, the RTX 4080 SUPER and an A100 (November 7) is this conservation of
   counts, not exactness.
6. **Identity.** A relation the mathematics proves (`x² = 2`, a Cayley turn `t² = h²K/(4C)`,
   Kraft's equality, a Jacobian at a rest) is carried as the relation; every reading of it is a face
   at a counted width. π and `e` are navigators: a spigot is a counting organization that releases
   their digits to the width it counts.
7. **Floats.** A float is a graph whose widths a format fixes: one mantissa width for every term, so
   the grouping where codas cancel is lost. Floats are fine in discussion and reports; as storage
   they are a format standing in for a count. Foreign floats are converted where they arrive.

The retired word named none of these. Each former use says one of four things: a counted width, an
order-free reduction, an identity, or a carried remainder. §6 maps them.

## 4. Parallel dispersal: the card is a surface of thread potentials

A core with a `W`-bit word carries a term of need `w` as `⌈w/W⌉` serial word steps. One fast core
holding a wide value is one mode carrying a large count in sequence. The same graph split at its set
bits disperses: narrow limbs over many slower potentials, partial counts meeting in accumulators
sized by their own count.

- With `ℓ`-bit limbs, a product of terms of widths `a` and `b` is `⌈a/ℓ⌉⌈b/ℓ⌉` limb products of
  `2ℓ` bits. A sum of `n` of them needs `2ℓ + ⌈log₂ n⌉` bits, so an accumulator of width `A` holds
  `2^(A−2ℓ)` limb products before its carry passes to the next limb: unsigned 8-bit limbs in a 32-bit
  accumulator hold `2^16` products (`2^15` under a sign bit). The carries merge registers as a count's
  increment does.
- A lap's time is the graph's bits moved and terms executed over the surface's potentials, never one
  core's clock.

Reading [agent-inferred]: the A100 replay of lap 4 matched the 4080 bit for bit and ran 1.37 times
slower because the kernels hold every term in fixed 64- and 128-bit scalar words on the ordinary
cores, a format's count instead of the graph's, not because the arithmetic is integer. The same
counts dispersed as the graph's own limbs over either card's tensor surfaces keep the bits (item 5)
and engage far more potentials. Design's plan of November 7 (profile the dominant products, rewrite
the largest as limb-sliced tensor work with the same results, measure both cards) is this section's
first build.

## 5. The learner's step is a number too

The kernel deposit's step is a reading, and its width is the count of its evidence. Lap 6 measured
this the hard way.

- Along the moments' direction `d` a section of `N` states gives per-state slopes
  `f_s = min(1,A_s)(D_s·d)/T`, their sum `s`, its sampling variance
  `v = (N/(N−1)) Σ (f_s − f̄)²`, and the curvature `c = (ln 2/2T²) Σ min(1,A_s)(D_s·d)²`.
  At the rest, `(ln 2/2T²) E[min(1,A) D Dᵀ]` is the Jacobian of the expected deposit: the flow
  `min(Pq, P′q′)` is symmetric and `D` antisymmetric, so the proposal's terms and the second
  derivatives cancel.
- The slope reading distinguishes about `|s|/√v` levels (signal over noise, §3 item 2), so a length
  read from it means something to about `½ log₂(s²/v)` bits.
- The law of November 7, 05:55, read the length from one section: `α = −(s/c)(1 − v/s²)`, nothing
  when the shrink `1 − v/s²` is not positive. For a step `k·(−s/c)` from a slope whose signal is
  `σ_s²` and noise `σ²`, the expected change of the deposit's quadratic model,
  `−k σ_s²/c + k²(σ_s² + σ²)/(2c)`, is least at `k = σ_s²/(σ_s² + σ²)` (complete the square), and the
  shrink estimates that share. The identity holds; the reading failed. In lap 6's first 140
  sections the steps fitted their own section and cost the next (transfers +44k to +504k µbits a
  state): the 16 states of one section undercount the noise a fresh section sees. After them, as
  the field flattened, `c` fell a thousandfold, the length grew as `1/c`, acceptance reached 1, and
  at section 202 a released value outgrew its 64-bit carrier (no state written).
- The reading that settles it was already in laps 4 and 5. At rate 12 the transfer (the next
  section's covector priced on the step) was about +2k µbits a state, against −35k on the step's own
  section. The transfer is the derivative of the step's length on fresh states, so near zero means
  rate 12 already sat a little past the line minimum along the moments' direction. The step was
  never length-bound; it is evidence-bound, and a section's covector is mostly its own states'
  noise.
- The width as a count [agent-inferred]: the moments normalize each coordinate by its spread, so a
  step's relative noise falls as the square root of the states it averages, and four times the
  states buy one bit of width at the same noise, the `½ log₂(1+S/N)` of §3 item 2. Lap 7's law
  reads `n` states a section at once across the card's potentials (§4), with rate
  `12 − ½ log₂(n/16)` and the moments' rates counting states, not sections
  (`FIRST_RATE 2^−3·n/16`, `SECOND_RATE 2^−8·n/16`). Laps 4 and 5 moved the held enumerated code
  6.639 → 6.526 → 6.503 bits a place, against 4.93 for the letters' own frequencies.
- The code is a count as well: `2^6.503 ≈ 91` letters are still equally live at each place, against
  `2^4.93 ≈ 30` under the letters' frequencies.

## 6. What each use of the retired word becomes

Counts are at origin/main `de446804`, case-insensitive.

| Where | Uses | Senses | Becomes |
|---|---|---|---|
| `CLAUDE.md`, `AGENTS.md` | 12 each | the precision law; identity adverbs; plain English | the law rewritten on the design branch ("Precision is the bit widths of graphs"; "Integer series" for the parallel-determinism item; representation "at declared widths"); cohomology's "exact ⊕ coexact" kept |
| `docs/ELEMENTARY_OBJECTS.md` | 65 | mostly identity adverbs ("exactly when"); cohomology ("exact ⊕ coexact"); some precision ("exact realization grains", "exactness is the default", "exact enclosure") | precision → counted width; adverbs → "when", "only"; cohomology kept |
| `docs/THE_MACHINE.md` | 25 | precision ("exact chart values", "exact bit lengths", "exact amplitude") and identity | the same rules |
| `docs/plans/THE_REBUILD.md`, `CONSTRUCTION_STATE.md`, helical, winding and constraint-mode guides | 105, 51, 21, 29, 12 | the same mixture | the same rules |
| `docs/canon/EPISTEMIC_GRADES.md` | the grade `implemented-exact`; "exact scope", "exact revision" | a grade for returned equality or invariant receipts; plain English | grade → `implemented-invariant`; plain English → "named" |
| `docs/atlas/` | 1,114 | rows stating identities, bounds and counts | adverbs dropped; precision rows → counted width |
| `crates/` identifiers | `ExactRatMatrix` 1,907; `ExactInterval` 819; `ExactLinearError` 164; `ExactPolynomialError` 115; `ExactWork` 102; `HnnExactConst` 71; `ExactValueError` 71; `ExactOrdering` 50; `exact_bits` 45; `HnnExactMut` 35; `ExactFace` 33; `ExactInverseOperator` 22; `ExactPairContraction` 13; `ExactWordMatrix` 11; others | names claiming precision | drop the prefix where the type already names its carrier (`RatMatrix`, `WordMatrix`, `LinearError`, `PolynomialError`, `Work`); `ExactInterval` → `Enclosure` (an interval at a counted width around a navigator's value); `exact_bits` → `need_bits`; one rename per owner family at its next touch, with gate 1 on the card host; Rust's `chunks_exact` stays |
| `crates/` comments | about 3,200 "exact", 1,300 "exactly" | mixed | with each owner's rename |
| `lean/` | about 30,000 | almost all the `exact` tactic; cohomology names | untouched: a keyword of the proof language, and cohomology's word |
| `research/records/` | about 43,000 in 3,811 files | history | unchanged; this record supersedes the word, and the guides govern |
| the line's vocabulary | threads and receipts | | the design branch's names govern: the "exact read" is the **enumerated read** (`ENUMERATED.tsv`, `FIELD_ENUMERATED_READ`: each place's conditional read through every letter's energy), so "held exact code" → **held enumerated code**, beside the **face code** (the first-order force); "exact kernel" → **invariant kernel** (its rest is the true distribution); "exactly J" → J; "exact conditional" → the enumerated conditional; "exact integers" → integer counts at their widths; "bit-identical" stays |

Order and owners: the guides' law, that day's code documentation (`field.rs`, `energy.rs`, the
card's `energy.rs`), records and atlas rows on the design branch; this record and its route, the
objects guide and THE_MACHINE, and the remaining atlas rows' precision senses from the theory
thread; THE_REBUILD, CONSTRUCTION_STATE, the geometry guides and the grades canon after them in one
documentation change; code identifiers per owner family at their next touch with the gate; records
stay as written.

## 7. Formal statements owed (#410)

- Stars and bars: the occupation patterns of `N` quanta over `M` modes number `C(M+N−1, N)`.
- The recursion has no top: with `T₀ = M` and `T_(j+1) = C(T_j+N−1, N)`, the counts grow without
  bound for `M, N ≥ 2`, and every level is finite.
- The shrink: for `c > 0` and `σ_s² + σ² > 0`, the model change at `k` minus its value at
  `k* = σ_s²/(σ_s² + σ²)` equals `((σ_s² + σ²)/(2c))(k − k*)²`.
- The accumulator: `n` products of `ℓ`-bit limbs sum within `2ℓ + ⌈log₂ n⌉` bits.

They join `lean/HolonicsResearch/Foundation/CarriedRelease.lean` and
`lean/Holonics/Aeon/Clock/CarryWord.lean`.
