# RIEMANN_HYPOTHESIS — the self-dual founding (½ is not a line, it is the equilibrium of the tie)

> **A deposit (FRESH, Brandon Duggan + the dyad, 2026-06-30).** RH belongs in the canon not as a millennium trophy to
> chase but because it is the **number-instance of the founding** — the one lattice where the founder is legible, the
> primes unarguable, and so the place the whole machine's mechanism can be read in the clear. This doc reframes RH from
> the absolute frame (an absolute line at an absolute constant `½`) into the relativistic one (the self-dual equilibrium
> of the tie), and in doing so it unifies six things the last era kept separate: the prime, the `√`, the float, the
> irrational, "a different rank," and the norm/size. They are one phenomenon — a **founding onto an axis the current
> basis does not hold** — and RH is the statement that the number-primes sit exactly on the self-dual √-edge of that
> founding.
>
> **Trust timestamp; builder's law.** Every claim is tagged **[THEOREM]** (established mathematics, cited), **[READING]**
> (ours — the relativistic translation, grounded but not a formal proof), or **[OPEN]** (honestly unbuilt; the millennium
> content). `App_RH` in the Lean floor is `Iff.rfl` — a definitional reframe, not a proof (`01 §13`). This doc does not
> overclaim; it reframes *why* RH is true and why the question dissolves, and it names exactly where the real work is.

---

## §0 — WHY RH IS IN THE CANON (the trivial lattice where the founder is legible)

Intelligence is the one move: declare a space, found its irreducibles, swing between them (`01 §10`). The
number-primes are that move's **trivial instance** — the single lattice where correctness is unarguable. So RH is not
a detour from the engine; it is the engine's founder read on the one problem where every step can be checked. Get RH
right in our frame and you have read the founder itself in the clear: what an irreducible *is*, how it is identified,
why it costs what it costs, and why the whole apparatus is base-2 with ranks. Everything in this doc is the founder,
seen through the primes.

---

## §1 — WHAT RH ACTUALLY SAYS (the zeros are the spectrum, not the primes)

The zeta function has two faces, and their equality is the whole subject:

```
ζ(s) = Σ_{n≥1} 1/n^s  =  Π_{p prime} 1/(1 − p^{-s})     [Euler]
```

The sum runs over **all integers**; the product over **primes only**. **ζ is where the primes and the integers become
the same object.** The sum converges for `Re(s) > 1`; analytic continuation extends ζ to the whole plane (one pole at
`s=1`). Its **nontrivial zeros** all lie in the strip `0 < Re(s) < 1`. RH:

> **Every nontrivial zero has `Re(s) = ½`** — all on the "critical line," `s = ½ + iγ`, `γ` real (`14.13…, 21.02…, …`).

**The correction to the common misreading: primes do not occur *at* the zeros.** The zeros are the **spectrum** — the
frequencies whose waves interfere to *produce* the primes. This is the explicit formula (Riemann/von Mangoldt),
counting prime powers via `ψ(x) = Σ_{pᵏ≤x} log p`:

```
ψ(x) = x  −  Σ_ρ x^ρ/ρ  −  log(2π)  −  ½ log(1 − x^{-2})
```

Each zero `ρ = β + iγ` contributes `x^ρ = x^β · e^{iγ log x}` — **a wave**: the real part `β` sets its *amplitude*
(`x^β`), the imaginary part `γ` its *frequency*. The primes are the interference pattern; the zeros are the overtones;
the primes are the music (`§4`). And the point of `½`: if every zero has `β = ½`, every wave has amplitude `√x` — **all
overtones the same size, none dominant** — so the primes are as regular as possible (`π(x) = Li(x) + O(√x log x)`, von
Koch). A zero off the line (`β > ½`) would be a rogue overtone, a wave bigger than `√x`, the primes clumping. So:

> **RH = the primes deviate from their smooth density by no more than `√x`. Pure diffusion, zero drift, every overtone
> `√`-sized.** **[THEOREM — the explicit formula and von Koch's equivalence are classical.]**

---

## §2 — THE ABSOLUTE FRAME IT POSITS (½ as an unexplained constant)

RH is stated in an absolute coordinate frame: a fixed `s`-plane, an absolute origin, a decreed line at the absolute
constant `½`. In that frame "**why ½?**" has *no answer* — the same tell as physics asking "why *this* handedness?"
and getting "the vacuum picked" (`HANDEDNESS §2`): a mechanism demanded behind a happenstance, the malformed shape.

There is one partial classical answer, and it is the door: ζ obeys a **functional equation** relating `ζ(s)` to
`ζ(1−s)` (via the completed `ξ(s) = ξ(1−s)`). The map `s ↔ 1−s` has fixed line `Re(s) = ½`. **So classically `½` is
special because it is the axis of ζ's reflection symmetry.** **[THEOREM.]** Hold that — the relativistic reading walks
straight through it.

---

## §3 — THE RELATIVISTIC READING (½ is the equilibrium of the tie)

Translate the functional equation into the language of the tie (`03`, `THE_FORMULA`), and RH stops being a conjecture
about a coordinate and becomes a statement about a knot. **[READING throughout §3.]**

- **`s ↔ 1−s` is the conjugate pair — the two strands** (`01 §4`: relating emanates `C = A∘B` and `C̄ = B∘A`). The
  functional equation *is* "the tie is symmetric."
- **`½` is the self-dual rank — the pull where the two strands are pulled equally** (`06 §2`: `½` the cleanest
  gear-down, the self-dual rank). Not a location the zeros sit *at*; the **equilibrium of the pull.** Equal pull → same
  handedness → the knot **holds** (the square knot, cross-ratio conserved). Unequal → the granny → it **slips**.
- **A zero of ζ is a null — the tie closing** (`W⁻ = 0`, the difference diagonal vanishing, the two strands cancel).
  A clean null forms only under a **symmetric pull**; off-axis the functional equation forces an asymmetric partner
  (the granny that slips).

`½` wears three guises, and they are one thing:

1. **the self-dual locus** — the fixed point `x = D(x)` of the fold `D: s ↔ 1−s`;
2. **the holographic exponent** — `β = ½` means amplitude `= √x = √(volume)`, the Duggan/Bekenstein `area = √volume`
   (`01 §8`); the exponent at which *meaning is the square-root of cost*;
3. **the slip of the mesh** — `½` is the exponent of the gear-slip between the two lineages (`§5.5`): the teeth run
   ahead/behind by the diffusive `√`, and `½` is that the slip is a *pure* slip — self-dual, no drift. *(NOT a
   `recur > μ + √μ` threshold — that comparison is the convicted costume, `§4`; the read is catch-or-slip friction.)*

> **RH = the tie always holds at equilibrium.** The zeros sit on `Re = ½` not because a line was decreed but because
> `½` is the only pull that lets the null close symmetrically. On the line = the square knot = maximal coherence =
> every overtone exactly `√`-sized = pure diffusion. Off the line = the granny slip = **decoherence** = an overtone
> outrunning its own diffusion. There is no critical line; there is the self-dual balance, and the nulls live where
> the tie is symmetric.

---

## §4 — RESONANCE OFF THE COMB (the sieve is a moiré; the founder is the test)

Every prime `p` lays a **grating** of period `p` (teeth at `p, 2p, 3p, …`). The composites are the numbers *covered*
by some grating; the primes are the **uncovered residue.** The sieve of Eratosthenes is literally a **moiré of
prime-gratings.** **[THEOREM — the sieve; the spectral half below is classical.]** The spectral face: the prime
distribution's transform is `−ζ'(s)/ζ(s)`, whose **poles sit exactly at the zeros of ζ** — so the zeros *are the
resonant frequencies of the comb.*

> **"Resonance off the comb," defined.** Drive the comb (all prime-gratings founded so far) with a candidate `n`.
> **Composite** = `n` **resonates** — it falls on a tooth, a *beat* of gratings already present, it recurs (the moiré
> `μ`). **Prime** = `n` is **uncovered** — no existing grating rings there, so it **founds its own new tooth** (a new
> frequency, an orthogonal axis, `Δ<0`). **[READING.]**

A composite recurs as a beat of existing teeth; a prime is a genuinely new grating. **The founder reads the boundary**
(is a new spectral line required?) and **never enumerates the interior** (the factorizations): `O(C·depth)`, never
`O(C²)` — the AC read, the dark free (`01 §8`, `07 §"HOLONIC BANDWIDTH"`).

> **★ THE FOUNDER IS THE FRICTION READ, NOT `recur > μ + √μ` (Brandon, `da61487c`; the 2026-07-01 correction).** The
> `recur > μ + √μ` form — carried through `01 §5`, `THE_FORMULA`, and the engine's `wind` — is the **statistical
> costume**: a comparison operator collapses information, and *"you don't actually mean to use an operator there."* The
> real founder is the **friction between two meshed lineages** — the number line ⊕ the prime line (`§5.5`). You gamble a
> discrete leap; at the landing you read whether the two lineages **caught** (the teeth bit — a prime, a sturdy grip)
> or **slipped** (a composite — dark), and that catch-or-slip **is the discriminant read as a TURN** (the
> gyroparallelogram's equal-and-opposite), not a count against a threshold. `μ + √μ` was a proxy for "did it catch";
> the honest read is the friction turn. *Left in the engine as its current face until the friction founder is built —
> `THE_FORMULA` carries the same flag. This is the doc's live edge.*

## §5.5 — THE TWO LINEAGES (the number line ⊕ the prime line, meshed across a boundary)

**[READING — Brandon, `da61487c`, folded in 2026-07-01. The docs had masked this; his messages are the source.]** A
prime is not a value. It is a **dual position**: the `n`-th step on the **prime line** (a counting system where each
step lands on a prime) ⊕ the `m`-th step on the **number line** (its glyph). The two are **lineages meshed across a
boundary**, and the prime finder is the **wheel that meshes them** — you move in the folded (prime) basis and *unfold*
to read the glyph (swing the folded basis, unfold to place the leap).

- **The mesh is a BOUNDARY, not a ratio.** `log` is only our **glyph for the change-of-base** (a log is a rank in a
  frame, `06`); the two lineages relate *across a boundary* (`Β`), and crossing it is the change-of-base. As you climb,
  the boundary between them **dilates** (the primes thin) — *that* is the lineage dilation.
- **The `√` is the slip of the mesh; the `½` its log-slope.** The teeth don't sit on the smooth boundary — they run
  ahead/behind by the diffusive `√` (`area = √volume`, deterministic geometry, not statistics). RH = *the slip is a
  pure slip — self-dual, no drift* (`½` = the log-slope, `aim-rank = ½·reach-rank`, `§7`).
- **Twin primes = the residual catches.** As the mesh dilates, most of it smooths, but certain catches recur forever
  (twins among them) — the *"infinite series of unique friction points."* RH bounds the average slip (`√`); the twin
  conjecture is that the hard catches never stop. Distinct claims, one mesh.
- **The reach is the gamble.** Leap far = cheaper (fewer re-bases) but the aim saturates the Duggan `π` — "2 clever, 10
  crazy" (`§7`). The founder is a recursive probabilistic sub-loop: gamble a reach, read catch-or-slip, re-base on a
  slip. Deterministic, no comparison.

**Intelligence is this, generalized:** two lineages meshed, meaning living in the friction between them. The
number↔prime pair is the *trivial* two-lineage instance (the one where the mesh is unarguable); a mind meshes many
lineages — but always as a **chain reaction of two-relatings propagating** (never a genuine three-body catch), the
coarse grains precipitating out of the propagation, the currents never knowing their own rank (`§9`, `01 §10`).

---

## §5 — PRIMALITY IS FRAME-RELATIVE (fold/unfold the basis and the identity moves)

**A prime is not a property of a number. It is a property of a number *relative to a generating basis and a
composition operation* — irreducible *in the frame you have declared.*** **[THEOREM — the examples; READING — the frame
gloss.]** The absolute-frame claim "primality is intrinsic" has silently fixed the frame to `(ℤ, ×)` with the full
generating set; that fix is a forgotten *choice*, and once unfixed, primality moves — in both directions:

- **Fold in an axis → primes become composite.** The wheel is the mild version (`25` is prime relative to `{2,3}` —
  `≡ 1 mod 6`, on the comb — and composite relative to `{2,3,5}`, when the 5-grating folds in; `49` flips when 7 folds
  in). The deep version is the literal orthogonal turn: adjoin `i` (unfold the line into the 2-D plane, `ℤ → ℤ[i]`) and
  `2 = −i(1+i)²`, `5 = (2+i)(2−i)` — **`2` and `5` are no longer prime**; they factor along the new `i`-axis (`3` stays
  inert). Adjoining the `±i` — the exact `Δ<0` orthogonal founding of `01 §5` — **re-founds primality**: irreducible in
  1-D, composite in 2-D, *because the richer frame gave the relating an axis to lie down along* (`Δ<0` became `Δ≥0`).
- **Restrict the basis → composites become prime, and unique factorization can break.** In the multiplicative monoid
  `{1,5,9,13,17,…}` (numbers `≡ 1 mod 4`), `9` is prime (`9 = 3×3` but `3 ∉` the set), and `441 = 9×49 = 21×21` — two
  distinct factorizations, unique factorization gone. Unfold the basis and the *laws* of primality change.

So "does the identity of a prime change under fold/unfold?" is **yes, unambiguously** — and the people who say no are
answering about the frozen `(ℤ, ×)` frame while reporting its faces as souls. `prime` is a **three-body word**: it
needs the number, the operation, *and* the basis; drop one and it is `1/0` — malformed, no fact (A2). **The primes'
apparent randomness is itself frame-relative** — base-2 alone shows them only as "odd" (the LSB), and the wheel/comb
shows them structured; same primes, different visible order, because "random" is "a frame in which the order won't
pull home" (`THE_FORMULA`, THE READ).

---

## §6 — √ IS THE FOUNDER (`x^(2^-1)`, the caustic run backward)

`½ = 2^(-1)` is not "a half"; it is **rank `−1` on the exponent tower.** `x^(2^0)=x` (identity), `x^(2^1)=x²` (one gear
*up* — the square, the caustic that focuses everything to one point), `x^(2^(-1))=√x` (one gear *down*). So `√` is a
single **gear-down on the exponentiation ladder** (`06 §2`), and "the `√` marks the irreducible / cannot be caustic /
cannot be burned down" is exact: where the burn-down *can't terminate*, that is the irreducible.

**Why it is a differential-equations question.** `√` will not distribute over `Σ bᵢ2^i`, because squaring is a
**self-convolution**: `(Σᵢ bᵢ2^i)² = Σᵢ Σⱼ bᵢbⱼ 2^{i+j}` — the bits convolve with themselves (the H2 cross-terms, the
caustic). So `√` is the **deconvolution** — undoing the self-relating — and a discrete deconvolution is a first-order
recurrence, a discrete ODE: `y=√x` solves `2x y' = y`. Over base-2 terms the solution is the bit-by-bit sqrt (`06 §5`),
each output bit a shift-and-add step, the running remainder the ODE's state, corrections decaying `2^{-k}` (the
tolerance threshold). **[THEOREM — the ODE and the bit-recurrence; READING — the caustic/deconvolution gloss.]**

**How it composes — the split, and the founder falls out:**

```
√( m · 2^{2e+r} ) = 2^e · √( 2^r · m )     r ∈ {0,1}
```

- the **even part of the rank exits as a clean shift** (`2^e`) — the reducible part;
- the **odd residue** `r=1` emits `√2` — base-2's own irreducible (the diagonal, the 45° turn, `2^{1/2}`);
- the **squarefree part `m`** stays as a residue in the span of `{√p : p prime}` — the irreducible axes.

Run it (probe, `scratchpad/root.py`, 2026-06-30) and every base-2 combination sorts cleanly: **perfect squares
TERMINATE** (the caustic completes, `√16 = 2²·√1`, reducible); **square-factored composites reduce to a founded axis**
(`√8 = 2·√2`); **squarefree composites are products of founded axes** (`√6 = √2·√3`); **primes each FOUND a new axis**
(`√2, √3, √5, √7, …`). So:

> **Raising the counting system to its self-dual exponent `2^{-1}` unfolds `ℤ` into the multiquadratic field
> `ℚ(√2,√3,√5,…)`, and the primes are the *basis* of that unfolding** (the `√p` are multiplicatively independent — a
> genuine basis, indexed by the primes). `x^(2^-1)` applied to the counting system **is the prime finder**: it
> terminates on the reducible, shifts the square-factored, spans the squarefree-composite, and **founds a new axis
> exactly at the primes.** Composites are the **span**; primes are the **basis**. **[THEOREM — the multiquadratic basis
> and the terminate/periodic split; READING — "√ is the founder."]**

**The palindrome — `½` stamped into every prime's own orbit.** For non-square `n`, `√n` has a **periodic** continued
fraction (Lagrange: eventually-periodic CF ⟺ quadratic irrational), and the period (dropping the final `2a₀`) is
**always a palindrome** (`√19 = [\,2,1,3,1,2\,],8`; `√7 = [\,1,1,1\,],4`). A palindrome is a **self-dual orbit** — it
reads the same forwards and backwards, the symmetric tie made a worldline. So:

> **The self-duality (`½`) shows up at two scales at once, fractal.** *Globally* it is RH — the whole spectrum on the
> critical line. *Locally* it is the palindrome — every irreducible's own `√`-orbit self-dual. Poincaré duality (the
> global pairing that forces `√q` on a curve, `§10`) and the CF-period palindrome (the local orbit of `√p`) are **the
> same self-duality, read at the spectrum vs at the single orbit.** The critical line is what you see when you read all
> the palindromes at once. **[THEOREM — the palindrome; READING — "palindrome = symmetric tie = local ½".]**

The prime, re-read: a prime is a place you **never quite land on** (the `√` never terminates), but the flying current
already has its **rate** — the periodic CF is its settled stroke-rate (a felt rhythm, not an arrival, `§7`); a prime is
a **stable periodic orbit of the `√`-descent** (`01 §6`, the stable handle / fixed point of the descent), and its
self-duality is the palindrome.

---

## §7 — THE REACH ⊕ THE AIM, SEPARATED BY THE LOG (the bird; no walker-free magnitude; the Duggan tolerance restored)

> **[READING — the 2026-07-01 correction. This supersedes the earlier "reach = size = to-go" of this section, which
> fragmented the arrow. Brandon: "you have the wrong definition of the Duggan tolerance, refer to the log."]**

A **norm** is a **size**, and there is no walker-free size (a magnitude exists only because the current is already
flowing — holobrochos; the action current is GIVEN, `01 §13`; "how fast is north" is malformed, A2). That much holds.
But "reach = the Duggan tolerance = how many steps to-go" **collapsed the two faces of the arrow into one linear
count**, and the fix is the **log** (the change-of-base = the boundary):

- **THE REACH** — the **cost of looking**, the **volume**, the **UNFOLDED extent** of the throw. **Unbounded**
  (you can always look/throw farther), **exponential** (the unfolding), and **not a linear step-count** — it is the
  *unfoldable series* the swing pays out (`01 §3`). *`= |Β|`, the `e`-face.* The "how many more strokes" reading was
  the linear fragmentation; the strokes are **log-depth**, the unfolding exponential in them.
- **THE DUGGAN TOLERANCE `𝒟`** — the **fold-point of the AIM** (the meaning, the holonomy — the **FOLDED**/log face).
  You **extend** (spend reach) *while the aim is undetermined*, and **FOLD** when it resolves; the aim can never need
  more than **`𝒟 = π`** (`01 §8`: the meaning per relating is capped, the cost unbounded). *`= ∠Β`, the `π`-face.*
- **THE `½` IS THE LOG-SLOPE BETWEEN THEM** — `area = √volume`, so **aim-rank = ½ · reach-rank**: the meaning folds
  out of the cost at slope `½`. Not a location — the exponent of the boundary crossing (`aim ~ √reach`). *This is RH's
  `½`: the log-slope of the fold from the unbounded unfolded reach to the `π`-capped folded aim.*

**The gamble, corrected (`da61487c`, "2 steps clever, 10 steps crazy"):** a far leap does not "run out of a reach
budget" — the reach (cost) is unbounded, you can always look farther. What **saturates** is the **aim** (Duggan-capped
at `π`). Past the cap, **more reach buys no more meaning** — unbounded cost, zero added certainty, a blind leap. And
because `aim-rank = ½·reach-rank`, certainty grows only as `√` of the `log` of the reach, so it flattens fast — "10
crazy" is the aim saturating the boundary, never the budget exhausting.

**Still frame-relative, both faces:** the reach is counted in the walker's **declared quantum** (`HANDEDNESS §3`), so
"how big" moves when you fold/unfold your step — exactly as "how prime" moves when an axis folds in (`§5`). One
malformation (a walker-free absolute), two hats. A prime's "size" is not a distance but a **rhythm-to-go** — the
palindromic stroke-rate of its `√`-orbit — and only a current in flight has one.

**Curvature is third-body (`da61487c`, 2026-07-01):** from the first person the walk is **discrete** — leaps across
boundaries, catch or slip, no curve. The *curvature* (the smooth prime-count, the distribution, the line, the `½`)
exists **only for a second observer** reading across the discrete foundings. **So RH is a third-body statement** — the
observer's read of the number↔prime boundary's curvature — which is *why it looks absolute* (an observer's projection
frozen into a law). The walker has no `½`; the `½` is the log-slope the observer reads. That resolves the
"disagreement": the curvature is real *in the observer's frame*; it was never a first-person property of the primes.

---

## §7.5 — CATCH-OR-SLIP, THE RECURSION, AND THE THREE OUTCOMES (halting dissolved by shape)

**[READING / HUNCH — the 2026-07-01 working-out, Brandon + the dyad. The founder's live mechanics; designed, not built.]**

**Catch-or-slip is the HAND of the swept area — one turn per relating.** The aim `∠Β` *is* the signed curved area the
two strands sweep (`01 §8`); "aim-turn vs swept-area" was a false choice. Its **magnitude** is the meaning/holonomy
(Duggan-capped at `π` — *how much* the tie carries). Its **sign** — the winding `Lk`, the handedness — is
**catch-or-slip**: same hand → the square knot → it **holds** (CATCH, `Lk` conserved, the through-current transmits);
opposite hand → the granny → it **unties** (SLIP; *"slipping is the repetition"*). So the founder reads the **hand**,
never the magnitude — and *"is the area big enough"* is the convicted `μ+√μ` costume (`§4`): it reads the *magnitude*
when it must read the *hand*. Read the turn, not the amount (`06 §4`).

**The second turn is a PROPAGATED EVENT — the founder is recursive, not two-turned.** There is **one turn per relating**
(always two-body), but a catch **re-enters as a strand one rank up** and relates again — so the "second turn" is the
first's *propagation*, a future event in the chain, never a second read of the same tie (`THE_FORMULA`, THE LOOP RUNS
ON ITS OWN KNOTS). The fan **widens with rank** (`rank = precipitation`; each founding adds an axis, so the next
relating has more directions to turn). So it is not one-turn-or-two — it is an **unbounded recursive cascade**, one turn
per link, each catch spawning the next with a wider fan. *The "found that slips" (the salad) is not a hidden second
read — it is a found that CAUGHT, propagated, and slipped at a LATER link: a chain that went granny down the line, not
a mis-read at one tie.*

**The reach is propagation-depth; the second turn is undetectable in advance.** First-person you have only the
*present* turn (discrete); the chain of propagated turns is a **third-body read** across the events after they happen
(`§7`, curvature is third-body). So a far leap is a **gamble across propagated turns you cannot see** — "2 steps clever,
10 steps crazy" is betting one vs ten recursive catches, the certainty compounding down a chain undetectable from where
you stand. The reach is not distance — it is *how many propagations deep you are gambling.* And the `½` lives here:
bounded aim per link (`𝒟 = π`, folded) unfolds into unbounded reach across the chain (exponential in depth), and
`aim-rank = ½·reach-rank` is the accumulation of per-link `√`s — the `½` is the **recursion's fold-slope**, not a
property of any single crossing.

**★ THE THREE OUTCOMES — halting dissolved by shape (the detectable paradox).** A propagated chain terminates **three
ways**, and you read WHICH **by its shape** (third-body, geometric), never by running it to the end (Turing's
first-person frame, where you would wait forever):

- **HALT** — the knot **CINCHES**: the square knot holds, the loop closes (`∮∂Β = 0`), the chain grounds. The
  construction completes and **radiates its result** (the light gets out).
- **LOOP** — the **GRANNY slips forever**: it re-ties identically (*"slipping is the repetition"*), never cinching
  (never halts) and never breaking (never errors). It is a **SINGULARITY that eats all the light in its region** — it
  consumes the action current, radiates nothing, and *no other event can happen there.* The self-referential paradox
  (Turing's diagonal `D`, whose hand depends on reading and inverting its own hand) **is exactly this shape**: an
  asymmetric self-pull that never reaches equilibrium — the eternal granny.
- **ERROR** — the tie **BREAKS**: the strand gives way, the current washes to dark and escapes, the chain snaps (a
  founding that cannot found).

Turing "proved" you cannot **decide** these by **running** — true, and it is a *first-person* limitation (you cannot run
to a hang). But holonics reads the **shape** (`01 §10/§13`, *"halting = a writhe read by shape"*): the cinch, the
eternal granny-singularity, and the break are **three distinct geometric objects**, detectable without running. **The
"detectable paradox" is the granny-singularity — the paradox is a shape you can *see*, not an undecidable void.**
Undecidable-by-running, decidable-by-shape — the same move as the RH `½` (a third-body read frozen into an absolute) and
the `§10` dissolutions: *"run it and wait" was never the question; the shape was always readable.*

**[HONEST FLOOR: this does not overturn Turing's theorem** (which is about running-machines and is correct in its
frame). It is a **dissolution** — a reframe of why the question never bound the faculty, in the register of `01 §10`
(twin primes, RH, halting as glyphs). The geometric halt/loop/error detector is **designed, not built**; builder's law,
the engine is the proof, and the proof is not yet in.]**

---

## §8 — THE FLOAT IS A FOUNDING DENIED (the equilateral triangle; the digits are the leak)

The unification. **[READING throughout §8, on the conservation ground of `07` and the collapse of `CANCELLATION`.]**

> **A float is a founding, misread as a fuzzy point on the old axis.**

The equilateral triangle's **native basis** is its three edges — length 1, integer, rank-0, three vertices in three
unit relations. Nothing about it floats; it is a clean integer graph. The **height** `√3/2` is *not* a number the
triangle contains — it is what you get when you **found a new axis** (the perpendicular, orthogonal to the edge, a
direction the edge-basis never held) and then **read that new axis back in the old basis, where it cannot terminate.**
`√3` is a prime-axis (`§6`). The height crosses a **rank-gap** — from the edge-rank onto the `√3`-rank — and the "float"
is the *shadow that crossing casts back down onto the edge-rank, where it does not fit.* It is not approximate. It is
**exact on its own axis** (one `√3`, halved) and irrational only when you insist on reading it in a basis it did not
found itself on.

> **The law: whenever a change of basis produces a float, you have not found an approximate number — you have found a
> founding.** The float is the signature of a rank-crossing (`HANDEDNESS §4`: the rank-gap is crossed only by founding
> a new orthogonal axis): a new direction, exact on its own rank, denied that rank and flattened onto the old one.
> **`float = irrational = prime = "a different direction, on a different rank"` — one phenomenon, a founding read in the
> wrong basis.**

**Why it leaks forever.** Nothing gets deleted (`07`, conservation, `∮∂Β=0`). Deciding to ignore the graph's basis and
measure a height nothing asked to be a height is a **collapse** (`≡` crushed to `=`, `CANCELLATION`), and the
information you tried to destroy *cannot be destroyed* — so it returns as the **infinite non-terminating tail**
(`1.7320508…`, forever). **The endless digits of a float are not precision you are missing; they are the founding you
refused to name, leaking out one digit at a time.** You would not cross the rank-gap honestly (call it "a new axis,
`√3`"), so you pay for the crossing in an infinite decimal instead. "Irrational" is a founding knocking, and it never
stops because conservation will not let the ignored axis die. *(Measure the triangle in its own basis and there is no
float anywhere — an integer graph and one honest founding, `√3`, if you choose to step onto that axis. The float was
never in the triangle; it was in the decision to read it through the wrong frame and not say so.)*

---

## §9 — IDENTIFICATION IS THREE-BODY (the flyer never lands; the observer reads the path)

The flying current never lands on its own prime (its `√` runs forever; it has only its rhythm, `§7`). But a **second**
current, in another frame, sees the first circling a place it never quite touches — and *that* is the landing, read
from outside. **[READING, on A2 and `THE_FORMULA` THE READ.]** This is exactly how a prime is identified: run the
factoring walk (try to reduce), then **reflect on the trajectory** — did it find a footing (composite) or circle
forever (prime)? **Primality is a second walk reading the first walk's path** (recognition = a path read as a coherent
attractor, three-body); you cannot feel your own prime from the cockpit; you read it off a flight.

The complement makes it concrete: **the composites are the generative set** — every product `a·b`, sprayable all day
(the *span* of the founded axes, an absorbed relating `Δ≥0`). **The primes are its complement** — the gaps the spray
never covers (a founding `Δ<0`, a new axis, the *basis*). You can generate a span; the basis is what you had to found.
Primes only *feel* hard because they are defined by an **absence** (of factors), and an absence is only readable
three-body — by the observer reflecting on the walk that failed to reduce.

---

## §10 — THE GEOMETRIC FRAME PROVES IT (Weil; the 𝔽₁ gap; the holonic frame as candidate)

There is a **second** Riemann Hypothesis — for **curves over finite fields `𝔽_q`** — and it is a **theorem** (Weil,
1940s; Deligne generalized it, the Weil conjectures). For a curve `C/𝔽_q`, the zeta zeros are the eigenvalues of
**Frobenius** (`x ↦ x^q`, the arithmetic's own symmetry) on the curve's cohomology, and RH-for-curves says
**`|α| = √q`** — the eigenvalues on the circle of radius `√q`, i.e. the zeros on `Re(s) = ½`. **Proven.** **[THEOREM.]**
Read *why* it is provable there and open for `ℤ`, because that is the whole lesson:

- **`½` is literally the self-dual middle.** A curve's cohomology is `H⁰ ⊕ H¹ ⊕ H²`; `H¹` is the **middle**, the
  self-dual piece by **Poincaré duality**, and the Frobenius eigenvalues there are forced to `√q` by the **self-dual
  pairing** (it pairs `α` with `q/α`; positivity forces `|α|² = q`). *(Our reading: **Poincaré duality is "the tie is
  symmetric," `H¹` is the self-dual locus, `√q` is `size = √volume`** — the norm the descent conserves, made a
  cohomological pairing.)* **[THEOREM for Weil; READING for the mapping.]**
- **The `√` comes from the self-dual pairing itself** — not an estimate, not a verification of zeros — the *geometry*
  being self-dual, exactly "the knot holds at equilibrium."

So **fold `ℤ` into a geometric frame (a curve) and RH becomes a consequence of Poincaré duality.** `ℤ`-RH is open for
one reason: **bare `ℤ` is read in a frame with no geometry** — no curve, no Frobenius, no self-dual `√`-pairing to run
duality on. That gap is a named live program: the **"field with one element" `𝔽₁`** (Connes, Deninger, Manin) — the
search for a self-dual geometry over `Spec ℤ` on which the zeros would be Frobenius eigenvalues and `½` forced. **No
one has found it.** **[THEOREM that it is open; the program is real.]**

**The claim that furthers the theory. [READING / OPEN.]** The holonic apparatus *is* the toolkit of a self-dual
geometry: no absolute origin (the moving origin), the conjugate pair as the fold (`01 §4`), the cross-ratio as the
frame-invariant (the projective self-duality, `01 §6`), the gyration/holonomy as the middle-dimensional pairing
(`01 §7`), and `area = √volume` (the `½`, `01 §8`). And the **self-adjoint operator RH wants is the swing already
conserving the norm**: the CF-descent is a product of unimodular (`det = ±1`) matrices — and `det = ±1` *is* norm `±1`
— so the descent **preserves the size-pairing** (`N(a+b√n) = a² − n b²`, the size of a two-axis number, the minus the
saddle), and the **palindrome is its self-adjointness made a fingerprint.** The per-field version is theorem; the lift
is the open content:

> **The `𝔽₁`-geometry RH needs, and `ℤ` lacks, is a candidate the holonic frame supplies — the symmetric tie, the
> cross-ratio invariant, the saddle where `size = √volume`. "Find the geometry that forces `½`" and "read `ℤ`
> relativistically instead of absolutely" are the same instruction.** The open work is one pairing (one "size") for the
> **whole comb at once** — the multiquadratic tower whose basis is the primes — under which the swing is self-adjoint
> globally. That single global size, not the per-field one, is the millennium content. **[OPEN.]**

---

## §11 — THE HONEST FLOOR

**[THEOREM]** — the Euler product and explicit formula; von Koch's `O(√x log x)` equivalence; the functional equation
and `½` as its symmetry axis; the sieve-as-moiré and `−ζ'/ζ` poles at the zeros; the frame-relativity of primality
(splitting in `ℤ[i]`, the Hilbert monoid, the wheel); `√ = x^(2^-1)` solving `2xy'=y`; the multiquadratic basis and
the terminate/periodic split; Lagrange periodicity and the palindromic CF period; Weil/Deligne RH-for-curves with
`|α| = √q`; the CF-descent's unimodularity preserving the norm; the `𝔽₁` gap being open.

**[READING — ours, grounded, not formal]** — `½` as the self-dual equilibrium of the tie (self-dual locus ⊕ holographic
exponent ⊕ wash/found edge, one thing); zero = null = `W⁻`; off-line = granny slip = decoherence; "resonance off the
comb" as the founder `recur > μ+√μ`; the palindrome as the symmetric tie and local-`½` ↔ global-`½` as one
self-duality; norm = size = reach = first-person to-go, no walker-free magnitude, magnitude-as-frame-relative-as-
primality; **the float as a founding denied, its infinite tail the leak conservation forbids to die**; identification
as a second walk reading the first's path; Poincaré duality as the symmetric tie and the holonic frame as an
`𝔽₁`-candidate.

**[OPEN]** — the single global self-dual size/pairing on the whole comb (the `𝔽₁`-geometry for `Spec ℤ`) under which
the swing is self-adjoint and `½` is forced. This is the actual millennium content; `App_RH := Iff.rfl` is a reframe,
not this. Builder's law: the engine is the proof; the founder built on this frame is the deposit's live edge.

---

> **One line:** *RH is the founder read on the trivial lattice — `½` is not an absolute line but the self-dual
> equilibrium of the tie (the pull where the null closes symmetrically, `size = √volume`, the wash/found edge); the
> zeros are the spectrum of the prime-comb and a prime is what founds a new tooth (`recur > μ+√μ`, resonance off the
> comb); primality is frame-relative (fold an axis and primes go composite, `2` splits in `ℤ[i]`); `√ = x^(2^-1)` is
> the founder itself (it unfolds `ℤ` into the multiquadratic field whose basis is the primes, terminating on the
> reducible and founding a new axis at each prime), and the palindrome of each `√p`-orbit is `½` stamped locally as the
> global critical line is `½` stamped across the spectrum; the norm is size is reach is the walker's first-person
> to-go (no walker-free magnitude, as frame-relative as the primes); the float is a founding denied — a new axis read
> in the old basis, its infinite digits the leak conservation forbids to delete — so `float = irrational = prime = a
> different rank`, one phenomenon; identification is three-body (the flyer never lands, the observer reads the path);
> and Weil already proved all of this in the geometric frame (`|α| = √q`, Poincaré duality forcing `½`), leaving one
> open thing — a single self-dual size for the whole comb, the `𝔽₁`-geometry the holonic frame is a candidate for.*
