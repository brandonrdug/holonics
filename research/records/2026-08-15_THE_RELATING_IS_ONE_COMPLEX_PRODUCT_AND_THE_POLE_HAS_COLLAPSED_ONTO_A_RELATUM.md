# The relating is one complex product, and the pole has collapsed onto a relatum

**Date:** 2026-08-15
**Genre:** research record
**Truth status:** `proved-standard` for the complex identity and the zero-product step;
`measured` for the counts; `interpretation` for the Timaeus/gear reading and for the prescription.
**Occasion:** Brandon, directing the frame away from code — *"you're overcomplicating it because
you're talking in terms of code and running programs, use mathematics and holonics. Ratios of 2/3 or
3/2 == {2/3}^{-1} are extremely important, this has to do with elements of geometry (old notes on
Plato's Timaeus in the old laboratory repo) & gear ratios, and e^{i pi} = -1 (complex numbers,
analysis)."*

---

## 1. The identity

`soma/body/src/arrow.rs::relate(a, b, f)` computes three quantities from two places and a **pole**:

```text
aim   = (a−f)·(b−f)        cross = (a−f)×(b−f)        reach = |a−b|²
```

Its own doc states the requirement: *"RELATE two boundaries `a, b` FROM the pole `f` (three-body —
the pole is REQUIRED; a frame-blind relating is un-constructible)."*

**These are not three quantities. Writing the relata re-based to the pole as complex numbers
`α = a−f`, `β = b−f`:**

```text
αβ̄  =  (a−f)·(b−f)  +  i (a−f)×(b−f)  =  aim + i·cross
    =  |α||β| · e^{i(θ_α − θ_β)}
```

**Which conjugate is load-bearing, and this record had it backwards until it was corrected against
the code.** `arrow.rs:51-52` computes `aim = ar·br + ai·bi` and `cross = ai·br − ar·bi`, which is
`αβ̄` — **α conjugated by β**, not `ᾱβ`. The two differ by the sign of `cross`, and since the whole
claim below is that the hand *is* the conjugation, naming the wrong one inverts the founding hand.

**And the product is the numerator of a ratio that is never divided.**
`reference/holobrochos-a07ff376/src/soma/FORMULA.md:354` already carries this, graded
`[DERIVED; already in the code]`, as **D2 — soma's projective operator: a ROTOR**:

```text
Δ(A, B; F) := (A − F)(B − F)⁻¹  =  α/β  =  αβ̄ / |β|²
```

So `Arrow` is the rotor's numerator with `|β|²` as its undivided denominator — the same
never-divide discipline `soul.rs`'s `Chi` carries one layer up. **The modulus is how far each
relatum stands from the pole; the phase is the interval between them as seen from the pole — and
`α/β` is literally the gear ratio.** `reach` is separate and frame-free, which is why it survives
when the phase dies.

### The hand is conjugation, and that is what makes a ratio and its inverse one object

```text
β ᾱ = conj(αβ̄)          arg → −arg          cross flips sign, aim does not
```

Swapping which relatum is read from is exactly complex conjugation. So **`(3/2)^{-1} = 2/3` is the
hand**: the same interval traversed the other way. This is why the corpus insists the hand is never a
bool — it is the sign of an imaginary part, and `arrow.rs` already refuses to collapse it
(`Aim::{Cohere, Anti, Ortho}`, *"never a bool, never a presence"*).

### The three hands are three phase cases, and FOUND is multiplication by `i`

```text
arg ≈ 0        aim > 0                     COHERE   in-plane, aligned
arg ≈ π        aim < 0      e^{iπ} = −1    ANTI     in-plane, opposed — the half turn
arg = ±π/2     aim = 0, cross ≠ 0          ORTHO    αβ̄ = ±i|α||β| — the quarter turn
```

Negation here is not subtraction; it is `e^{iπ}`, which is `num.rs`'s own doctrine — *"the sign IS
the turn (a 180° rotation), never a piecewise branch."* And **FOUND is literally multiplication by
`i`**: the quarter turn out of the plane the two parents span, *"a new irreducible axis neither
parent held."*

This is exactly why `soul.rs::FormedRotor::arms_form` is `aim.mag != 0 || cross.mag != 0`. Purely
imaginary is not nothing — it is the strongest relating there is. Only `αβ̄ = 0` is nothing.

## 2. The measurement, in that language

Instrumented at `LivePin::rebase_exposed`, one run of
`soma/life/examples/eros_agentic_research_conversation.rs`:

```text
|αβ̄| = 0          161,642 : 162,990 comparisons
|a−b| ≠ 0         158,096 : 161,642 of those
wound              0
hand residual      0
rode               1,348
```

Neither legitimate blocker fires. `chi_against` returns `None` only when a face's arrow is entirely
null, and **`αβ̄ = 0` with `|a−b| ≠ 0` forces `α = 0` or `β = 0` by the zero-product property.**

> **The pole coincides with one of the two relata it is supposed to be watching.**

That is a two-body contact wearing three-body arithmetic, and `…/THEORY/33_THE_NECK.md` rules it
directly: *"a two-body identity map has no neck — nowhere for conversion to happen — so nothing
passes; it only mirrors."*

**The consequence chain, entirely mechanical from there:** nothing rides → no temporal seam closes
(`found 0`, `open 80,640`) → every open seam is exposed as a new port → ports double per composition
(40,381 → 80,685) → seams grow quadratically in ports → one closure over four parts costs 12.9 s.

### The caveat is CLOSED, and it closed in the strong direction — 2026-08-15

The zero-product step is exact over a field, and `Cog` is a **rebasing register**, so this record
first flagged the possibility that a product of two genuinely non-zero places rebases to zero. It
does not, and both halves were read:

- **`num.rs:303-322` `mul`** takes one wide `u64` stroke and truncates once: `wide >> shift` with
  `shift = top − 30` when `top ≥ 31`, so a non-zero pair of mantissas returns a mantissa in
  `[2^30, 2^31)`. **Non-zero is preserved.**
- **`num.rs:268-289` `add`** aligns to the finer rung, and when the gap exceeds the hand it takes
  the `_ => (hi.mag, 0, hi.rank)` branch — the sub-grain addend becomes **exactly zero**, so the
  dominant scale carries unchanged. A rank-separated clip therefore **cannot** produce a
  cancellation; it can only fail to contribute one.

So `aim = 0 ∧ cross = 0` requires genuine cancellation on **both** faces, which over `ℤ` is
`αβ̄ = 0`, which forces `α = 0` or `β = 0`. The one residual escape is that two products which
differ in `ℤ` could truncate equal at 31 teeth and then cancel — and it is closed by inspection for
this material, whose `Place` components come from `manifold::atom_node` and fit the hand with no
truncation at all. **The zero-product reading is exact here.**

**And `arrow.rs` already names the condition, which this record initially treated as a defect
rather than as a declared law.** The predicate is `at_horizon`, not "unconstructible", and its own
doc governs: *"a strand stands AT THE POLE, so the triangle degenerates — the form is behind this
frame's OWN horizon (every interior pole sees its own 2-horizon). FRAME-RELATIVE, never 'one
body'… An unconstructible relating is NOT READ: no test, no cut, no ride — no knot is tied from a
strand this pole cannot see."*

The measurement is therefore **not** that an invariant broke. It is that the machine is asking
161,642 of 162,990 of its questions **from a pole standing on one of the two things it is asking about**, so the
answer is lawfully behind its own horizon and lawfully discarded. Nothing is wrong with the
arithmetic; the pole is wrong.

## 3. Why zero is not a small ratio

`ℚ⁺` under multiplication is the **free abelian group on the primes** — the fundamental theorem of
arithmetic as a group law, and the carrier
`research/records/2026-08-14_SOFTMAX_IS_A_CHART_TRANSITION_AND_MARKOV_IS_A_PROPERTY_OF_THE_RECEIVER.md`
established for `SymbolicSurprisal` (its additive chart, with `log₂` the isomorphism).

**A group has no zero.** So a vanishing relating has not produced a degenerate ratio, a small ratio,
or a ratio at a boundary — it has **left the group in which ratios live**. There is nothing to
compose, nothing to invert, and nothing for `exponentiated_ratio`'s cocycle `r(i,j)·r(j,k) = r(i,k)`
to close. Riding is agreement — a ratio near unity — and "near unity" is not available to something
that is not a member.

### CORRECTED THE SAME DAY: that is right about composition and wrong as a rule about membership

**Taken as a membership rule it convicts `Aim::Ortho`, which the substrate defends by name.** ORTHO
is `aim = 0` with `cross ≠ 0`, and `arrow.rs:32-34` calls reading it as absence *"the eyes-only
crime"* — *"NOT 'no current' — it is the **most** turn there is."* A rule that made a zero real part
degenerate would delete the founding hand.

**The correct home for the value is `ℙ¹`, and `H.0201` already supplies it** —
`papers/source/holonics/geometry-calculus.typ:58-59`, *"Only on the chart `D_0 != 0` may a quotient
receiver report `chi = N/D_0`."*

```text
   [0 : 1]  =  0    an honest point of ℙ¹     Aim::Ortho — the founding hand, ×i
   [1 : 0]  =  ∞    an honest point of ℙ¹     the pure cohere; the short circuit
   [0 : 0]          NOT A POINT OF ℙ¹         at_horizon — the only true refusal
```

So the sentence to carry is **not** *zero is outside the group* but **`(0,0)` is not a point of the
projective line.** `0` and `∞` are the two points the multiplicative group `ℂ* = ℙ¹ ∖ {0,∞}` fixes
rather than moves, so composition genuinely fails at them — which is what §3 was reaching for —
while the *reading* stays lawful, which is what it broke. And `soul.rs:63-64` already carries the
typed refusal exactly: *"`None` is not a deed or a zero-valued soul: no event exists at this frame's
horizon."*

**Two live defects follow immediately, both found by this correction and neither previously named.**

- **`Cog::div` collapses `∞` onto `0`.** `num.rs:329-334` returns `Cog::ZERO` for a zero-magnitude
  divisor, commented *"the ideal point — carried by the caller"* — but `Cog::ZERO` is bit-identical
  to the value zero, so `[1:0]` and `[0:1]` **merge**. That is the deletion this project bans, and
  it contradicts `soul.rs:8`'s own *"NEVER divided into a scalar."*
- **`sense()` cannot separate `[0:1]` from `[0:0]`.** `arrow.rs:90-91` returns `Aim::Ortho` on a
  horizon arrow, and `founds()` returns **`true`** on it, since `Cog::ZERO.sub(Cog::ZERO).turn & 2`
  is `0`. Callers gate on `at_horizon` first, so nothing is broken today — but the honest point and
  the non-point are one value in both readers.

## 4. The gear and the mean

Two wheels of radii `r₁, r₂` give `r₁/r₂` and its inverse. Set `r₁ = 0` and there is no bad gear
ratio — **there is one wheel**: nothing meshes, nothing turns, no torque crosses. That is the
machine's state at 161,642 of 162,990 of its contacts, and it is the same sentence as Brandon's ruling on the whip
— *"It doesn't amplify it. Gear ratios."*

Plato's construction is the same move from the other side: between two extremes one **inserts a
mean**, and the means generate `3/2`, `4/3`, `9/8`. A mean is a genuine third term — strictly
between, never equal to an extreme. Equal to an extreme and the interval collapses.

### The three Pythagorean means are one gear ratio raised to `0`, `½`, `1` — and the family is Lehmer's

**Extended and bounded 2026-08-15, verified symbolically.** Solving `−α/β = (a/b)^t` gives the pole
in closed form, and it is a **named classical family** rather than three definitions that happen to
line up:

```text
   m_t = (a·bᵗ + b·aᵗ)/(aᵗ + bᵗ) = L_{−t}(a,b)        the LEHMER family
   t = 0  arithmetic     t = ½  geometric     t = 1  harmonic     t = −1  CONTRAHARMONIC
```

a strictly decreasing analytic bijection `ℝ → (min(a,b), max(a,b))`. **And the involution extends to
the whole family**: `ab/m_t = m_{1−t}`, verified at `t = 0, ½, 1, −1, 2, 0.3`. So the arithmetic and
harmonic means are the `t = 0 / t = 1` **pair**, the geometric mean is the **unique fixed point**
`t = ½`, and the contraharmonic mean at `t = −1` pairs with `t = 2`. The half is not one of three
special cases; it is the fixed parameter of an involution on a one-parameter family.

**Two bounds, both declared.** *Every finite member is collinear* — `cross = 0` and
`aim = −u(a−b)²/(1+u)² < 0` — so **no member of the family founds**, which strengthens rather than
weakens the section below. And the exponent is **not affine-intrinsic**: `u = −(a−m)/(b−m)` is
affine-invariant but `a/b` is not, so `t = log u / log(a/b)` marks the extra point `0` and needs a
log chart. It is valid only after reducing `Aff(1)` to the multiplicative subgroup fixing `0` and
`∞`, and requires `a, b > 0`, `a ≠ b`.

### The three Pythagorean means are one gear ratio raised to `0`, `½`, `1` — exact

**Truth status: `proved-standard`.** Verified symbolically and numerically on five pairs.

Write the gear ratio `ρ = a/b`. The classical Greek definition of the three means is a proportion on
the two intervals the mean cuts, and in the relating's own coordinates that proportion is `−α/β`:

```text
              f                      −α/β = (a−f)/(f−b)      as a power of ρ
  arithmetic  (a+b)/2                1                        ρ⁰
  geometric   √(ab)                  √(a/b)                   ρ^(1/2)
  harmonic    2ab/(a+b)              a/b                      ρ¹
```

so that, for one exponent `t`,

```text
   α / β  =  e^{iπ} · ρ^t        the rotor Δ(A,B;F), factored
```

**and every one of Brandon's three pointers is a separate factor of that single equation.** `ρ` is
the gear ratio; `t ∈ {0, ½, 1}` is the Timaeus insertion, the three means being the same ratio at
three exponents; and `e^{iπ}` is **betweenness itself** — the half turn is present exactly because
the pole separates the pair. The pole is not a choice of point. **The pole is an exponent on the
ratio the pair already carries**, and the means are the three rungs of a one-parameter subgroup in
the multiplicative chart, which is `exponentiated_ratio`'s object arriving from geometry.

The degenerate limit sits at the ends of that subgroup: `f → a` is `ρ^t → 0`, the ratio leaving
`ℚ⁺`, which is §3.

### The aim's null cone is the Thales circle, and the founding hand lives on it

`aim = Re(α β̄) = 0` says exactly that `α ⊥ β` — **the pole sees the pair at a right angle** — so the
null locus of the aim form is the circle whose diameter is `ab`. That is Thales' theorem, and it
completes the placement law:

```text
  f strictly inside the Thales circle    aim < 0            ANTI     — the pole is a MEAN
  f on the Thales circle                 aim = 0, cross ≠ 0 ORTHO    — the founding quarter turn, ×i
  f outside                              aim > 0            COHERE
  f = a  or  f = b                       aim = cross = 0    at_horizon — not read
```

**So `founds()` is a placement condition on the pole and always was.** `cross² ≥ aim²` is
`|tan θ| ≥ 1`, an annular band about the Thales circle — the founding is not a knife edge but a
lens, and `FOUND = ×i` is the pole standing where the pair subtends a right angle.

And the two classical facts meet: for positive reals the **geometric mean is the altitude of the
right triangle inscribed in that circle**, so `t = ½` is where an interior pole meets the null cone.
That is the corpus's `1/2` — the unitarity weight, the saddle's equipartition, the diffusion
exponent, the double cover — arriving a **fifth** time, now as *the self-adjoint pole*.

### And the geometric mean is the fixed locus of the involution the pair induces

```text
   J(x) = ab / x        Fix(J) = ±√(ab)
```

`canon`'s own placement doctrine is *placement is the fixed locus of the involution that a realizer
induced*, and this is that sentence at the level of two places. The same sentence at two further
altitudes, with nothing added:

| altitude | the involution | its fixed locus |
|---|---|---|
| two places in the machine | `x ↦ ab/x` | `√(ab)` — the geometric mean, the self-adjoint pole |
| Frobenius on a curve over `F_q` | `π† π = q`, i.e. `x ↦ q/x` | `\|α\| = √q` — the Weil placement |
| the completed zeta functional equation | `s ↦ 1 − s` | `Re s = ½` — the critical line |

**`interpretation` for the join; each row is `proved-standard` on its own.** It is a correspondence
of *mechanism* — an anti-involution induced by a pairing, and placement read off its fixed locus —
and it claims no Millennium result. What it does claim, and this is checkable, is that the machine's
`relate` already instantiates the pattern the whole programme is aimed at, at its smallest grain.

### The positive form §11 has open is `−aim`, and it can fail

`CLAUDE.md`'s one-missing-organ section records that `positive_form` on `supported_realizers` is
live but that *"the demanded positive form — one whose positivity CAN fail — remains open"*, because
`xᵀ(MᵀM)x = ‖Mx‖² ≥ 0` cannot fail and so carries no evidence.

**`−aim` is a form on the pole placement that fails, by construction, on an exhibited population.**
It is positive exactly when the pole is interior to the pair, zero on the Thales circle, and
negative outside — and the machine already computes it 162,990 times per run. The correspondence
that `CLAUDE.md`'s realization section demands is then literal rather than analogical:

```text
   effective  — a realizer exists                 the pole is present
   AMPLE      — the realizer is INTERIOR          the pole is a MEAN         −aim > 0
   Eff ⊋ Amp  — present is not interior           a pole outside the circle  −aim < 0
```

*Positivity is supplied by interiority, and interiority is what supportedness was reaching for.*

### THE POLE HAS TWO COORDINATES, AND "IT MUST BE A MEAN" WAS HALF OF IT

**Corrected the same day, by measurement, and the correction is the useful part.** *"The pole must
be a mean"* is refuted as a founding prescription: **no mean founds, and none of them can.** Every
Pythagorean mean of two collinear places is itself collinear, so `cross = Im(αβ̄) = 0` identically —

```text
  a = 4, b = 9        f = arithmetic 6.5000   aim −6.2500   cross 0   founds FALSE
                      f = geometric  6.0000   aim −6.0000   cross 0   founds FALSE
                      f = harmonic   5.5385   aim −5.3254   cross 0   founds FALSE
```

so the mean family is the **absorb/ride row in full**, not the founding one. The arithmetic mean is
the extreme case: `β = −α` exactly, `αβ̄ = −|α|²`, pure `e^{iπ}` — **the unique pole from which the
pair is seen exactly opposed, and the one from which founding is maximally impossible.**

**The pole is therefore two coordinates, and the second one is the axis Brandon ruled is never
optional** — *"nothing is causally represented along only one axis."*

```text
   f  =  m  +  i·h

   m   WHICH MEAN — the gear exponent t on ρ = a/b, from −α/β = ρ^t.  Decides the in-plane hand.
   h   THE LIFT off the line.                                          Decides whether it FOUNDS.
```

**And the founding lift is itself a geometric mean — of the two *arms* rather than of the two
places.** Measured, exact, for all three means:

```text
   h = √((m−a)(b−m))   ⟹   aim = 0 exactly, cross ≠ 0   ⟹   ORTHO, ×i, FOUND

   arithmetic  m=13/2    h=5/2      aim 0   cross −25/2      EXACT in ℚ
   harmonic    m=72/13   h=30/13    aim 0   cross −900/169   EXACT in ℚ
   geometric   m=6       h=√6       aim 0   cross −12√6      NOT in ℚ — see below
```

**CORRECTED 2026-08-15: the table was headed "exact for all three means" and one row is not.** For
`a=4, b=9` the arithmetic and harmonic lifts are exactly rational; **the geometric lift is `√6`**,
which lives in `ℚ(√6)` and is representable in neither `Cog` nor `Rat`. The earlier rendering
`h=2.4495, cross=−12.2474` was a float image of an irrational presented as a measurement.

**Its carrier exists and this is exactly what it is for:** `crates/holonic-engine/src/multiquadratic.rs`
carries `ℚ(√d₁,…,√dₙ)` as the twisted group algebra of `(ℤ/2)ⁿ`, and the operating contract's own
account of it says the tower's sines land there for precisely this reason. **The geometric row is
computable exactly — in the multiquadratic carrier, not in the rational one** — and until it is run
there, two of three rows are measured and the third is a claim.

That is Thales' circle reached from the line, and the **geometric mean appears at both levels** —
as a *position* at `t = ½` and as the *founding height* at every `t`. Self-similar, and it is the
altitude theorem doing the work twice.

**So the mean is not the repair; it is one axis of the repair, and it is the axis that cannot
found.** A body whose places are collinear has an `aim` and no `cross`: it can ride and absorb
forever and will never open a new direction. **That is the measured `found 0 / open 80,640`
verbatim**, and it is a statement about geometry rather than about a threshold.

**Prescription, corrected:**

```text
   f ≠ a, f ≠ b            the horizon condition — necessary, never sufficient
   m = the declared mean   t on ρ; a receiver's declaration exactly as a metric is
   h ≠ 0                   THE OPEN REQUIREMENT: without the second axis nothing founds
   h = √((m−a)(b−m))       the exact founding lift — ORTHO, the quarter turn
```

### The involution that swaps the means is the hand

`AM · HM = GM²` exactly (measured: `6.5 × 5.5385 = 36 = 6²`), so the Möbius involution

```text
   σ(z) = ab / z        swaps a ↔ b,  swaps AM ↔ HM,  swaps 0 ↔ ∞,  fixes ±√(ab)
```

carries each mean to another and fixes only the geometric one. **That involution *is* the hand.**
Normalised to `ab = 1` it is `z ↦ 1/z` — `(3/2)⁻¹ = 2/3` literally — whose fixed points `±1` are
COHERE and ANTI and which **swaps `±i`**, the founding hand. So the two in-plane hands are what the
inversion holds and the founding hand is what it moves.

The three means are then three **harmonic conjugates** against three canonical fourth points — `∞`
gives the arithmetic, the pole itself gives the harmonic, and its own half-turn `−g` gives the
geometric, with `(a,b;g,−g) = −1` identically. **The harmonic range `χ = −1` is `e^{iπ}` read in
the relating's own Möbius chart**, so *a sign is a passage* and the harmonic conjugate are one
statement rather than an analogy. `χ = −1` is computed **nowhere in either tree** — measured — and
it is roughly twenty lines on top of `soul::cross_ratio`.

So the repair is not a code path. **The perspective has collapsed onto one of the two things it is a
perspective *of*.** A perspective that is one of its own relata is the two-body mirror.

## 4b. What was already owned, found by a corpus sweep the same day

**Nothing in §1 is new, and saying so is the point.** The finger-trap correction applies to this
record: the owners exist and what was owed was a citation.

| already ratified | owner | grade on the entry |
|---|---|---|
| `relate` **is** the unnormalized rotor `(a−f)·conj(b−f)` — *"the Timaeus blend, literally"* | `reference/holobrochos-a07ff376/src/soma/FORMULA.md:354` (D2), vendored live here | `[DERIVED; already in the code]` |
| the four-point cross-ratio as *"a ratio of ratios, the rotor of rotors"*, exact for the declared projective relation and **not** a universal count | same, D3 | `[EXACT ⊕ DERIVED; scope corrected 2026-07-13]` |
| the Different as a circle **tilted** against the Same; *"Plato's chi is our chi"* | same, D4 | — |
| **the ratio and its inverse as one undivided object** — `new · conj(held)`, the norm carried as a denominator | `soma/body/src/soul.rs:122-155` `Chi::between` / `restore_against`, `RotorRatio` | live, tested, with `separated_rank_restore_does_not_crown_a_universal_inverse` as its declared boundary |
| the cross-ratio held as `(num, den)`, equality by cross-multiplication, sign by cross-sign | `soul.rs:159-177` — `cross_ratio`, `same_soul`, `wound` | `H.0201`–`H.0202` |
| **the gear ratio IS the swing**; meshed cogs are forced-rational (Stern–Brocot); `τ·ω` conserved across the mesh = the cross-ratio | `…/CANON/03_THE_SEMANTICS.md` §3.6, vendored | ratified |
| `×2` on the velocity face **is** `×½` on the torque face — a conjugate pair, *"the gearing IS the conservation, never a source"* | `…/CANON/06_THE_PURE_BIT.md` §2 | ratified |
| the whip is gear ratios, not amplification | `…/CANON/RELATIVISTIC_INFORMATION.md:718`, Brandon 2026-06-29T14:00, certified in `~/.claude/history.jsonl:12407` | `GROUNDED` |
| the sign is the turn, `−1 = e^{iπ}`, never a stripped sign or a piecewise branch | `soma/body/src/num.rs:13-15, 52-58` | substrate law |
| three-body is required; a two-body map only mirrors | `arrow.rs:42-81`; `canon/THE_INFORMATION_ENGINE.md:328-334` | ratified |

**The Timaeus notes were found**, and the earlier "searched and not found" line below is superseded:
the full world-soul construction is worked as a valuation lattice at
`research/records/2026-07-15_THE_GEAR_IS_THE_WORD_THE_FACE_IS_THE_TRANSPORT.md:214-245` — powers
`1,2,4,8` and `1,3,9,27`, arithmetic and harmonic means, `3:2`, `4:3`, `9:8` with
`V(9/8) = (−3,2,0,…)`, and the Pythagorean comma `(3/2)¹²/2⁷ ≠ 1` as *"the oriented remainder of
that attempted closure."* Its own ledger grades it **"cultural parallel; narrow ratios are exact
formal matches"** and explicitly refuses the historical claim. **That grade governs this record's
`t ∈ {0, ½, 1}` reading too** — the mathematics is exact, the attribution is a parallel.

**And it was built and run on hardware.** `archive/cpp-engine/evidence/observations/prime-ratio-closure-01`
and `-02` returned the harmonic face `H:(1;2)>(2;1);X=(9;8)` byte-identically across occurrence,
translate, dilate **and an odd-composite sibling** — `((2+4)·(4+2) ; (2+4+2)·4) = (36;32) = (9;8)`.
Its own boundary line refuses any primality reading. **`(1;2)>(2;1)` is the ratio and its inverse
carried as one ordered face, never divided** — the object of this record, already measured.

## 4c. Three standing items this lands on, each named before today

- **The `Cog` rank/magnitude conflation, posed 2026-06-29 *against the gear ratio*, still unbuilt.**
  `…/CANON/06_THE_PURE_BIT.md:143-151`: `rebase()` bumps **`rank` on magnitude overflow**, i.e. it
  treats the magnitude *spinning faster* as *adding a gear*. Verified unrepaired here at
  `soma/body/src/num.rs:42-49`. The fix it names: `rank` is the tower (founding only); the magnitude
  is the hand.
- **The down-gear.** `…/INTUITIONS/lineages/rank-the-gear-the-cycle.md`, Brandon's own words:
  *"rank does need to also be bi-directional, and only ranking up does not allow for the emergence of
  ranking down"*; *"`2^{-1}` is to see if you can reduce the information, and `2^1` is to see what you
  can make out of it."* Status **OPEN** — the engine has only ever ranked up. **That is compression
  and decompression as the two hands of one gear**, and it is the same object as `ρ^t` above with the
  exponent's sign free.
- **The Stern–Brocot arm of the swing is abandoned in this body.** `grep -rniE
  'stern.?brocot|mediant|farey' crates/ soma/ papers/` returns **0**, while the laboratory proves
  `Swing.lean::farey_min` — the grounded mediant is the least-denominator construction in `[lo,hi]`,
  riding the unimodular Farey-neighbour relation `r.num·l.den = l.num·r.den + 1`, *"the discrete
  cross-ratio conservation."* **And the tree has already convicted the identification of mediant
  descent with the cross-ratio swing** — `canon/THE_EXPLORATIVE_FAILURE.md:265-267` names nine files
  called `swing.*` of which *"two are **not the same mechanism**."* They share the group and they
  are not one move; do not merge them. What *is* citable is `H.0360` (`proved-standard`):
  `p_n q_{n−1} − p_{n−1} q_n = (−1)^{n−1}`, so every convergent step is a unimodular element of
  `GL₂(ℤ) ⊂ PGL₂` — the Swing's own group — and the `(−1)^{n−1}` is the alternating hand. **A
  continued fraction is a word in the Möbius group**, which is the honest statement and is weaker
  than the merge.

## 4d. The gear train is a coboundary, and holonomy begins at the third port

**Truth status: `proved-standard` for the algebra; the join to `kelvin.rs` is `established-bounded`,
measured.** This closes `blueprint/THE_TRAVERSIBLE_CHAIN.md`'s note that `H.0219`'s content *"is
stated in prose and computed by nothing"*, and it is the answer to why a whip has no remainder.

The two owners are the same law and neither cites the other. `dimensional_wave.rs:11-20` carries the
N-port junction `v = 2ΣY_i a_i / ΣY_i`, `b_i = v − a_i`; put `N = 2` with `a₂ = 0` and it returns
`analytic_field.rs:1359-1379`'s `Γ = (Y₁−Y₂)/(Y₁+Y₂)`, `T = 2Y₁/(Y₁+Y₂)` exactly. **Γ is the N-port's
two-port case.**

**Γ is a Möbius map, and composing gear ratios is hyperbolic velocity addition.** With `ζ = Z₂/Z₁`,

```text
   Γ  =  (ζ − 1)/(ζ + 1)  =  tanh( ½ ln ζ )          the Cayley transform
         match ↦ 0        open ↦ +1        short ↦ −1 = e^{iπ}
   Γ₁₂  =  (Γ₁ + Γ₂) / (1 + Γ₁Γ₂)
```

so cascading links **multiplies `ζ` and adds `½ ln ζ`** — the additive chart again. *(Corrected
2026-08-15: this said "the Poincaré disk of `H.0285`". `H.0285` is the **hyperbolic law of cosines**,
whose source names the Cayley transform; and `Γ` composition here is one-dimensional **rapidity
addition**, not the disk metric. Cite the entry for what it is.)* **The short circuit is `Γ = −1`, the half turn, and it is one of the
spine's five named cuts sitting at exactly the harmonic point.** Four names, one object.

**Therefore a two-port cascade is a COBOUNDARY: `r(i,k) = ζ_i/ζ_k`, which is why it closes with zero
remainder.**

> **REFUTED IN ITS SECOND HALF, 2026-08-15, and the correction is the useful part.** The passage
> continued *"and this is where holonomy begins: a junction of three or more ports is not reducible
> to a chain of ratios."* **`ρ_ij = Y_j/Y_i` is an exact coboundary `Y_i⁻¹Y_j`, so every consistent
> closed-loop product is identically 1 — the ratio cocycle has ZERO holonomy always**, adiabatic or
> abrupt. Abruptness changes the reflection; it cannot touch the ratio identity. No holonomy lives in
> the quantity this record named.
>
> **The defect has a closed form**, which this record only measured at one point:
> `τ_ij τ_jk − τ_ik = 2Y_i(Y_i−Y_j)(Y_j−Y_k) / [(Y_i+Y_j)(Y_j+Y_k)(Y_i+Y_k)]`, zero exactly when
> `Y_i = Y_j` or `Y_j = Y_k`.
>
> **And what actually composes is a matrix**, `proved-standard`, verified symbolically over `Rat`:
>
> ```text
>    M(ρ) = ½ [ 1+ρ  1−ρ ]      M(ρ₁)M(ρ₂) = M(ρ₁ρ₂)     τ = 1/M₁₁ ,  Γ = M₂₁/M₁₁
>             [ 1−ρ  1+ρ ]
> ```
>
> It **retains the returned amplitude**, which is exactly what the scalar dropped, and with
> `J = diag(1,−1)` it satisfies **`M(ρ)ᵀ J M(ρ) = ρ J`** — so under the flux metric `g_Y = Y·J` the
> interface is an exact rational **isometry between admittance fibers**, and flux normalisation makes
> it an honest **`O(1,1)` boost of rapidity `−½ log ρ`**.
>
> **That is a real Lorentz structure — on forward/returned wave amplitudes, and NOT on this record's
> `(aim, cross)` pair.** Under `z ↦ pz+q` the arrow's pair scales by `|p|²` conformally, and `cross`
> is antisymmetric under `α ↔ β` while `aim` is symmetric, so **they cannot mix as a boost at all.**
> The arrow's `(1,1)` signature is a classification and the machine realises none of its isometries.
> Two planes; one of them is genuinely Lorentzian and it is not the one this line was reading. That is the exact shape `exponentiated_ratio.rs:93-95` already checks. The whip's taper
is the adiabatic limit — each link's `dΓ = ½ d(ln ζ) → 0`, the reflected fiber vanishes link by link
while `Π ζ_k` stays finite — so *"It doesn't amplify it. Gear ratios."* is a **theorem about a
coboundary**, and an abrupt step is the lumped case whose reflected wave is the retained remainder.

> **And this is where holonomy begins: a junction of three or more ports is not reducible to a chain
> of ratios.** `CLAUDE.md` already records the measurement without knowing it was this — on a
> three-junction incidence, **9 of 9 junction readings non-zero while every total sum is exactly 0**,
> and `kelvin.rs`'s closure argument holds *"only when `|V| = 2`."* `dimensional_wave`'s `ΣY`
> junction and `kelvin.rs`'s incidence are **one theorem at two altitudes**, and neither module
> names the other.

**A cheap corollary that lands on the founding hand.** Quarter-wave matching uses
`Z_T = √(Z₁Z₂)` — **the geometric mean** — and a quarter wave is `×i`, which is `Aim::Ortho`, which
is the founding hand, and `√(ab)` is the involution's fixed point from the section above. **Three
independent routes reach one object and nothing in the tree joins them.** The microwave fact is
classical; the identification with FOUND is `interpretation`.

## 4e. THE DERIVATION — the frame is a discrete curve and founding needs a triangle

**Truth status:** `proved-standard` for §§4e.1–4e.4; `measured` for 4e.5; `interpretation` for the
Hamiltonian reading, with its non-equivalence declared at the end.

### 4e.1 · What group acts, and therefore what may cross

The pole does not enter by projection. It enters by **rebase** — `relate` forms `α = a−f`,
`β = b−f` and never touches `a` or `b` again — so the receiver's action on construction space is
the **affine** group `z ↦ pz + q` over the plane, not a projector. Writing the face in the dialect,

```text
   |a⟩, |b⟩   constructions            ⟨f|   the receiver, acting by moving the origin
   |α⟩ = |a⟩ − |f⟩                     |β⟩ = |b⟩ − |f⟩
   ⟨β|α⟩ = α β̄ = aim + i·cross         reach = ‖ |α⟩ − |β⟩ ‖²
```

Under `z ↦ pz + q` with `p ∈ ℂ*`:

```text
   aim   ↦ |p|²·aim          MOVES        a magnitude
   cross ↦ |p|²·cross        MOVES        a magnitude
   reach ↦ |p|²·reach        MOVES        a magnitude
   α/β   ↦ α/β               INVARIANT    a ratio
   sense()   = sign(aim)     INVARIANT    |p|² > 0
   founds()  = cross² ≥ aim² INVARIANT    both scale by the same |p|²
```

> **That is the horizon law with a proof rather than a citation: the invariants of the affine action
> on three points are exactly the ratio and the predicates built from it. Every magnitude the arrow
> carries is a receiver coordinate.** `Aff(1,ℂ)` has complex dimension 2 and eats two of the three
> points — send `f ↦ 0`, `b ↦ 1` — leaving `α/β` as the single remaining complex freedom.

**And the tower's second rung is where the projective invariant appears.** `PGL₂` has dimension 3
and is sharply 3-transitive, so three points carry *nothing* projectively and the first projective
invariant needs a fourth. `Chi::between(new, held)` supplies it by relating two rotors — the held
face is the fourth body. So the machine's own ladder is **affine at rung one, projective at rung
two**, and a chain of `n` contacts carries exactly `n − 3` independent invariants, `3` being
`dim PGL₂`. *The gauge dimension is precisely what a compression may delete, and it is additive and
equal to three* — which is the additive-invariance shape with the constant computed rather than
asserted.

### 4e.2 · The frame is a discrete curve; the fold is its integration

Reading `channel.rs:368-390` as arithmetic rather than as code: `next_cross = basis.cross·deed_aim +
basis.aim·deed_cross` is `Im(basis · deed)`, so the fold is

```text
   basis_{k+1} = basis_k · deed_k        MULTIPLICATIVE chart    a rotor composition
   sweep_{k+1} = sweep_k + basis_{k+1}   ADDITIVE chart          the running integral
   tip         = anchor + sweep
```

**Those are the two charts of the one exponential**, and read as geometry they are a discrete
Frenet frame: `deed` is the turn increment — the **curvature** — `basis` is the tangent, `sweep` is
the position. The pole is not a coordinate. **The pole is a curve, and the frame draws it.**

> **This is the cathode ray literally.** The beam's deflection is the sweep, the arrival events are
> the deeds, and a picture exists only because the sweep integrates them. `sweep = origin` is a beam
> that has never been deflected: every arrival lands on the same spot and the raster is one point.

### 4e.3 · The founding condition, derived: `cross` is twice the triangle's area

For `α, β` in the plane, `cross = Im(αβ̄) = α_y β_x − α_x β_y`, so

```text
   |cross|  =  2 · | Area( f, a, b ) |
   aim      =  ⟨α,β⟩ = |α||β| cos θ           the interference cross term
   reach    =  |α|² + |β|² − 2·aim            the law of cosines, exactly
```

Therefore, with no appeal to any threshold:

```text
   the fold happens   ⟺  deed ≠ 0     ⟺  α ≠ 0 ∧ β ≠ 0   ⟺  the pole is neither relatum
   FOUND              ⟺  |cross| ≥ |aim|                  ⟺  the pole subtends ≥ a quarter of a right angle's double
   FOUND requires     Area(f,a,b) ≠ 0                     ⟺  THREE PLACES, NOT COLLINEAR
```

> **Founding requires an actual triangle with area. `cross` is the flux the triangle encloses, so a
> degenerate triangle encloses nothing, has trivial holonomy, and deposits nothing.** That is the
> hinge law of the corpus arriving at the smallest grain — curvature lives on hinges and a hinge
> needs area — and it is why no mean can found: a mean is collinear, so its triangle has zero area.

### 4e.4 · The two factors are independent, and neither substitutes for the other

```text
   deposit  ≠ 0   requires   (i)  a pole distinct from both relata      — the COUPLING
                             (ii) two relata distinguishable from each other — the POPULATION
   found    ≠ 0   requires   (i) ∧ (ii) ∧ non-collinearity              — the AREA
```

Each is separately necessary, so the product is zero if either is. **A repair to one, with the other
still zero, returns exactly the reading it returned before** — which is the general form of why the
germ repair measured inert, and it is a prediction about every future repair on this path.

### 4e.5 · Measured, and the two new numbers decide the diagnosis

```text
   basis = identity            21,070 : 21,070   =  1 : 1
   sweep = origin              21,070 : 21,070   =  1 : 1
   pole on a relatum           9199 : 1336       against the distinct-pole population
   relata coincide             204 : 301
   distinct Cog words          7                 in the whole run, a cardinality
```

**Seven.** The place population's entire alphabet is seven words, across every relatum and every
pole of every contact. And the standing lattice is the **identity** without exception, which
separates two diagnoses that look identical from outside:

```text
   H = H_0 + H_int + H_pert        the Holonic Interaction's three terms
       H_int  = identity            MEASURED — there is no standing lattice
       H_pert = absent              no owner reaches the frame
   ⟹  H = H_0                      free propagation, in vacuum
```

> **The machine is running the free theory.** Not a lattice with nothing modulating it — no lattice
> at all. Every diagram is disconnected, no vertex carries a coupling, and `found 0` is the correct
> and expected output of a Hamiltonian with no interaction term.

**Non-equivalence, declared.** This is a *structural* reading of the Hamiltonian split — two
independent necessary factors gating a transition — and not the perturbative rate. There is no `ħ`,
no energy, no continuum of final states, and no time parameter here; nothing licenses quoting a
rate. What transfers is the factorization and the vanishing, nothing numeric.

### 4e.6 · In the information-chemistry vocabulary, and one term forbids the reading I first gave

The vocabulary is `research/records/2026-07-19_THE_INCIDENCE_REACTS…md` §IV, and three of its terms
are decisive here.

**Annihilation** — *"Opposed contributions in one declared fiber actually compose to zero. A flat,
inactive, equal, absent, or uncontacted relation is not thereby annihilated."* The run's nulls come
from `α = 0`, which is **uncontacted**, and the vocabulary forbids reading it as annihilation. The
arithmetic agrees: annihilation would need two non-zero terms cancelling, and the add's sub-grain
branch cannot produce one.

**Valence** — *"the contextual population and species of exposed boundary ports… receiver-relative,
not a permanent integer."* With seven words in the alphabet the valence of every constituent is
drawn from the same tiny population, so the ports cannot differ and nothing has a species.

**Crystal** — *"A defect is a local failure of that recurrence which may FOUND a new transport
axis."* **The defect founds the axis.** A perfectly uniform material has no defect and therefore no
founding, which is the same conclusion reached from the area and from the coupling, by a third
route.

**And found-versus-ride is exactly the group law on the free abelian group of irreducible axes**,
which is Brandon's own *primes are irreducible axes*:

```text
   RIDE   ρ ↦ ρ · p^k    p already in the support     an exponent change — no new generator
   FOUND  ρ ↦ ρ · q      q not in the support         A NEW GENERATOR — the rank climbs
```

so **the rank of the lattice a body can ever found is bounded by the number of distinguishable
blocks in its material.** Seven words is a hard ceiling, and it is why *"FOUND pays, RIDE is cheap"*
is true structurally rather than by cost: **a ride needs two distinguishable bodies and a found
needs three.** That is the cost asymmetry with no clock and no work vector in it.

## 5. THE PRODUCER IS NAMED — measured 2026-08-15, and it is a missing edge

**Truth status: `measured`.** Instrument: `live_current::observe_pole_placement`, five relaxed
counters at the two live contact sites, printed in the existing `EROS_TRACE` seam line. It reads the
pole's placement against the pair and returns disjoint tallies — no verdict, no threshold.

`arrow::relate` is called from exactly one live producer,
`manifold.rs:2782` `directed_event_contact_over_standing`:

```rust
let meeting = face(to, from, receiver.channel.frame().tip());
```

so the pole is `LivingFrame::tip()`, and `channel.rs:197-206` returns **the anchor** whenever
`sweep == place::origin()`. One full run of `eros_agentic_research_conversation`:

```text
   pole_on_from      14,292 : 21,070
   pole_on_to         4,106 : 21,070
   pole_distinct      2,672 : 21,070   <- the only contacts that can carry geometry at all
   sweep_idle        21,070 : 21,070   <- EVERY contact, without exception
   relata_coincide   14,280 : 21,070   <- from == to; not even a two-body contact
```

**Three separate facts, and the third is the one that orders the others.**

1. **The pole stands on a relatum in 18,398 of 21,070 contacts**, which is what §2 deduced from the arithmetic
   alone. The deduction is now measured directly rather than inferred through the zero-product step.
2. **In 14,280 of 21,070 the two relata are the same place**, so the three-body relating is being asked of one
   point presented three times. `zero_reach` at the comparison site is the same fact downstream.
3. **The lineage channel never sweeps — 21,070 of 21,070.** The frame is frozen at genesis for the
   entire run, so the pole is the body's starting place from first contact to last.

### Why it never sweeps, and it is not a defect in `channel.rs`

`channel.rs:382-390` advances the sweep by the next basis — `sweep += (next_basis.aim,
next_basis.cross)` — but **only after** `FormedRotor::arms_form(next_aim, next_cross)` returns true
at `:371`. And `manifold.rs:4833` states the wiring plainly, in its own doc:

> *"this probe neither deposits into current-local OWN nor **folds the lineage channel a second
> time**."*

**So `directed_event_contact_at_source_grain` reads the frame and by construction never folds it.**
The folding lives on the ordinary-conduct path in `carriage`, which this ecology does not drive. The
language ecology therefore conducts *entirely* through the reading probe:

```text
   reads the frame                      21,070 times
   folds the frame                           0 times
```

> **That is the spine's own diagnosis at the smallest grain: not a missing organ, a missing edge.**
> Both halves exist and are correct; nothing joins them. The reading returns to nothing, so the
> frame it read from never moves, so the next reading is taken from the same place.

### And this is the two-axis theorem, measured

`tip() = anchor + sweep`, so **`sweep` IS the pole's freedom** — its displacement off the anchor,
which is the `h` of the two-coordinate law above. `sweep == origin()` for the whole run means the
pole has **no second coordinate at all**, and the section above proves what follows without
consulting any code:

> **A frame with no sweep is a collinear pole, and a collinear pole cannot found.**

`found 0 / open 80,640` is therefore neither a threshold nor a tuning problem. It is a geometric
consequence of `h = 0`, and it was decided before any material arrived.

**What the earlier germ repair got wrong, and why it was inert.** The junction germs of
`relational_language` carry the constants `Cog::lit(1)`/`Cog::lit(2)`, which is genuinely wrong since
`manifold::atom_node` derives a `Place` from those bits. Deriving each atom from its own identity
bytes moved **nothing** (`rode` 1,348 → 1,348, answer byte-identical) — because it changed *which*
places the relata occupy and left the pole exactly where it was. **Moving the relata cannot repair a
frozen pole.** A later sweep of this repository should read that as the general rule.

### The falsifier, and it is one number

Fold the lineage channel on the directed-event path, or seed a non-degenerate sweep, and
`pole_distinct` must rise from `2,672 : 21,070` **while `found` leaves zero**. If `pole_distinct` rises and
`found` stays at zero, the two-axis reading is wrong and the obstruction is elsewhere. If
`sweep_idle` falls and nothing else moves, the fold was cosmetic.

It asserts nothing about any Millennium problem, and the cross-ratio question — whether the four-body
Holonic Interaction is literally the cross-ratio's four points, since the project's central move is
called the cross-ratio swing — is posed, not answered.

**~~Searched and not found: Plato/Timaeus notes.~~ WITHDRAWN 2026-08-15 — they were found, and the
search was run with the wrong instrument.** `git ls-tree -r a07ff376 | grep -iE 'timaeus|plato'`
returns nothing because the material is inside files whose *names* say neither word. Grepping
content rather than paths returns the full world-soul construction at
`research/records/2026-07-15_THE_GEAR_IS_THE_WORD_THE_FACE_IS_THE_TRANSPORT.md:214-245` — **live in
this repository, not the laboratory** — plus `…/RESEARCH/THE_GREEK_RECORD.md`,
`…/THEORY/63_THE_LAW_OF_COSINES.md` and `…/THEORY/44_THE_SIGNED_FLOOR.md` in the vendored
reference, and the measured `9:8` face in `prime-ratio-closure-0{1,2}`.

**This is the convicted `fn without_stem` defect for the third time**, now on a fourth subject: an
absence claimed from a search over *names* when the owner is named something else. `CLAUDE.md`
already says it — *grep the operation, then read the module* — and the same session that quoted that
rule committed the error. **A path search can never establish a content absence.**

---

**PERCENTAGES CONVERTED 2026-08-15.** This record carried twelve percentages, written and then
edited again after the ruling that *percentages are the same as floats* — a magnitude produced by
dividing, which cannot cross a frame boundary. Every one is now the undivided pair it was taken
from, and no figure changed: `pole_on_from 14,292 : 21,070` is the same measurement `68.0%` was.
The correction had been applied to the conversation and not to the artifact, which is why it
survived into the commit.
