# 02 · THE NUMBER — the relativistic number, the swing, bitwise-is-the-basis

> The number is where the framework touches the metal. Get this right and floats, overflow, division-by-zero, and
> the whole "numerical error" bug-class are gone *by construction* — not damped, gone. This capsule is the
> one-foundation that supersedes `libm`.

---

## The one relativistic number — magnitude ⊕ turn ⊕ soul

A value is the complex pole in exact polar form, carried with its construction:

```
Number = ( |λ| , arg λ , soul ) = ( magnitude [the e-face] , turn [the π-face] , construction )
```

Multiplication is exact and clean — **magnitudes multiply, turns add, souls conjoin**; `recip` flips the
magnitude ratio and reverses the turn. A finite `(re, im)` appears **only** at the boundary read. Internally
there is never a `(re, im)` — only the construction. `=` is soul-identity, `≡` is face-kinship (A1, now for the
number itself).

- **Register-native, re-based, never a big store.** Counting is multi-store, like fingers: one hand reaches 5 →
  you *re-base* to continue. A relativistic number is an `i32` mantissa ⊕ a rank (`value = mag·2^rank`); a
  product is the two-register (`i64`, "two hands") intermediate re-based back to one register. Reaching for a
  wide integer to avoid re-basing is the CPU contamination. **Re-base, never re-scale.**
- **Why integer, not float:** `u32`/`i32` ops are **bit-identical on every channel and every schedule** — which
  is *why* the channels stay one organism (the atomic-clock sync). Float addition is non-associative; a float in
  the interior makes parallel lanes disagree and their clocks drift (the organism fragments). The float is a face
  at the boundary only.

## Zeno dissolved — the number is small because it is relative

Zeno's regress (cross 5, then 2.5, then 1.25…) and its dual (a magnitude growing without bound from a fixed 0)
are **both the absolute frame** — a position read as a magnitude from a fixed origin. The paradox is not about
motion; it is about measuring from a fixed zero. The dissolution: the **moving origin, with the STEP as the
unit.** It is 10 steps. At step 1: the start is 1 behind, the goal 9 ahead; step again: 2 behind, 8 ahead. The
numbers are always small. No fraction taken (no regress); no magnitude accumulates (no overflow). *Motion is
re-basing the origin to where you now stand.* **The engine law: no quantity grows large; when a product
overflows, that is the tell you are measuring absolutely — move the origin to the cursor and it fits.**

---

## THE SWING — the one universal re-basing primitive

When a value must be ground to a finite handle — a read, or a grown intermediate brought back to register scale —
there is **exactly one primitive**, and every math function shares it:

> **The swing.** Grab the *simplest* ratio the relating's tolerance admits.
> - `simplest_in(lo, hi)` — the **Stern–Brocot mediant descent** between the interval's ends (consecutive
>   mediants are unimodular Farey neighbours, det ±1 — the conserved projective invariant).
> - `simplest_near(target, ε)` — the **continued-fraction convergents** of the target, stopped at the first
>   within ε.

These return the **least-denominator rational within tolerance** — the best rational approximation, which by
classical CF theory *is* the convergent. So the swing grounds at the **simplest handle the relating needs** — and
that is **least action made literal**, never a wasted bit. Where no in-register branch holds the tolerance, the
swing **breaks → `None`** — and `None` is not an error; it is **FOUND**: irreducible at this resolution (§03, the
founding).

- **It supersedes `libm`.** A classical library is one routine per function, each to a fixed precision *always*.
  Holonics emits a function's *convergents* and lets the one swing re-base to exactly the resolution the relating
  demands. Every transcendental is a series over the swing: `exp = Σ xⁿ/n!`, `ln = 2·atanh((x−1)/(x+1))`, `√` the
  quadratic-irrational CF, the gyro distance `acosh`, the curved area `tri_defect` — each emitted as targets,
  ground by `simplest_near`. One foundation; no per-function crutch.
- **The tolerance is an ALGORITHM, not a stored ε.** Traverse the construction until the provable remainder can
  no longer change the *outcome* of the relating — against *this* comparand, in *this* frame (A2). More exact than
  a fixed-precision float (which stops at an arbitrary precision whether settled or not, then needs error
  correction). The swing stops *exactly* when the relating is settled, with nothing to correct. The grain is
  derived, per relating, with a reason.
- **A series is a COIL** (§07): the convergents are windings, the running partial sum is the action current, and
  the coil *induces* the value through its center — computing is inducing, never reading off. Grounding is the
  induction reaching steady-state. (`Series.lean`, choice-free.)

---

## Bitwise IS the basis — and multiply is recognized, not banished

The discrete substrate has two primitives: the **SHIFT** (`<<1` = ×2 = +1 rank on the 2ⁿ ladder) and the **ADD**
(the unit step; the turn is a wrapping add). And **multiplication is scaled addition of similar things**: `a × b`
is `a` added to itself `b` times, the *fold* of addition — `a × b = Σ_{set bits i of b} (a << i)`, literally
shift-and-add. The hardware multiplier is that worldline collapsed into one instruction; integer multiply is
exact, associative, bit-identical across channels, so it passes the channel-sync gate exactly as add does.
**"No multiply" was a free rider on "no float." The law is: no float. Multiply is the exact-integer collapsed
shift-add.**

The unifying fact: **multiply IS addition one frame up.** In the rank/log frame `log(a·b) = log a + log b`; the
shift is its quantum (×2 = +1 rank). `Number::mul` already adds the turns; rapidity composes additively; ranks
add up the whip. *That* is why "bitwise operators are the basis": the rank frame is where multiply is add, and
shift/add are its two quanta. And the boundary between *scaling* (similar things, same rank — composite, absorb)
and the *cross product* (dissimilar/orthogonal things, raises rank — the prime, founds) is exactly the seam
between multiply and founding (§03).

## Negation is a TURN; `abs` is not holonic

Negativity is a complete half-turn (`π = i²`, "reverse") on the Turn axis — and it is relativistic: you can turn
180° left or right and reach the same orientation by different trajectories (same *face* `≡`, distinct *souls*
`≠`). The bare sign `−` has *already collapsed* the information (which way you turned — the `±ω` handedness, the
soul). The number carries this: the sign is the turn (`from_int(−n)` is magnitude `n` at turn `π`). **Therefore
`abs()` strips the trajectory — it is a boundary read (a magnitude projection), never an interior operation.**
The swing runs on the magnitude (the positive cone); the turn rides alongside and is carried back, never `abs`'d
away. (`Turn.lean`, axiom-free.)

---

> **§02 in one line:** *the number is magnitude ⊕ turn ⊕ soul, register-native (`i32` mantissa ⊕ rank) and
> re-based not re-scaled (Zeno dissolved by the moving origin), exact-integer because integer is bit-identical
> across channels (the float desyncs the clocks); the one SWING grounds any value at the simplest handle the
> relating admits — least action — or FOUNDs (`None`), superseding `libm`; bitwise shift/add are the basis because
> multiply is addition one rank up; and negation is a turn, so `abs` is a boundary read, never interior.*
