# 06 — THE PURE BIT (the relativistic number is a bit-construction, and the shift is a gear)

> **What this is.** The CANON's deposit on the **number itself** — recovered and freshly adapted from holo-bits'
> `PURE_BITS.md`/`PENROSE.md`, which `04 §7` flagged as never re-expressed. The other departments use the number;
> this one says *what it is*: not a sized container with a value, but a **bit-construction** whose only mathematics is
> **bitwise**, whose `shift` is a **gear ratio**, and whose three coordinates are the three rotational directions of
> action — never IEEE-754's mantissa/exponent/sign. Written as a deposit; read each claim for its soul.
>
> **Trust timestamp; builder's law.** The live implementation is `interior/src/num.rs` (the `Cog`); it carries most of
> this correctly and conflates one thing, named honestly in §7. Where this contradicts an older layer, it supersedes.

---

## §0 — NUMBERS AREN'T REAL (the ground)

Mathematics is **relative to the system you analyse.** The mathematics of the counting system — decimal, signed
reals, the continuum, IEEE floats — is the mathematics of *human eyes*, a visual translation. It does **not** apply to
bit-hardware, where the quantum is the **bit** and the alphabet of operations is **bitwise** (`AND` `OR` `XOR` `SHIFT`
`ADD` `turn`). A numeral (`3`, `3.14159`, an `f64`) was never a value — it is a **glyph**, a face a counting-system
associates with discrete dynamics, materialised **only at the I/O boundary** (`A1`, `§9`). So the recurring deepest
error is rebuilding **floating point** — mantissa ⊕ exponent ⊕ sign — in a holonic costume, then auditing which signed
fields to keep, *as if the real-valued store were the given.* It is not. **The number is bits; the operations are
bitwise; the real-valued store is the float you keep smuggling back in.**

**And the bit itself is a HAND, not a presence (`CANON/HANDEDNESS`).** "A bit is *something or nothing*" planted an
absolute frame at the very bottom of arithmetic — a privileged empty state, a zero that is *truly* zero (the
count-from-0 crime, one rung down). There is no "nothing" (`A1`, the cosmic fight — no void). The two states are **two
hands: this way or that way, CW or CCW** — `1` and `0` arbitrary labels we paint on the two turns. The place we most
called nothing — the **dark**, the orthogonal `M≈0` — is where the *magnitude* is null but the *turn* is **maximal**
(`cosθ=0, sinθ=±1`): "nothing" was the **turn-maximal state read through the magnitude-null face**, the eyes-only crime
(`§4`) at the bottom of the number. So **the turn is the quantum; the magnitude is its integral** (the radius the
spiral accumulates as hands pile up — `×2` the shadow of `×i` repeated). A bit is the **gyration's sign.**

---

## §1 — THE THREE CARDINAL DIRECTIONS (the anti-IEEE triad)

A number has three coordinates, and they are the **three rotational directionalities of action**, not a float's three
fields:

| direction | what it is | the op | the face | NOT IEEE's… |
|---|---|---|---|---|
| **ALONG** — the magnitude | the unit-step accumulation (`H1` sum, the `e`-face) | **ADD** | how far along | …mantissa |
| **ACROSS / UP** — the rank | the tower, the dimensionality, `mag·2^rank` (`H2` cross) | **SHIFT** | which floor | …exponent |
| **LEFT / RIGHT** — the turn | the rotation, the `±i` founding, the sign (the `π`-face) | **turn** (`&3`) | which way | …sign |

The resemblance to IEEE-754 is a **shadow**, not the thing. The differences are load-bearing: (1) the **magnitude is
unsigned** — a magnitude is the positive cone; the sign is not a bit jammed beside it but the **turn** (a half-turn,
`turn==2`, the rotation `π = i²`), so a signed integer is a **arrow collapse** (magnitude ⊕ turn crushed into one
sign bit around an absolute zero) and is banned interior. (2) The **rank is the tower** (precipitation — it climbs on
*founding*, `§5`), **not a scale-exponent that dissolves into the frame** (§7 — the one thing the live `Cog` still gets
wrong). (3) The **width is an arbitrary hand** — `u32`/`u8`/`u4`/**`i2` is just bits**; the register width is a
*substrate* detail, never a parameter of the math. *"You could get away with i2 — oh wait, that's just bits."*

---

## §2 — THE SHIFT IS A GEAR RATIO (what `×2` means rotationally)

The SHIFT (`<<1` = `×2` = `+1` rank ; `>>1` = `÷2` = `−1` rank) is the number's core motion, and its meaning is
**mechanical, not magnitudinal**: it is a **gear ratio**. At a gear mesh (the **seam**, the tie, `03 §3.6`) two cogs
share their teeth at one contact point, and three things hold (`RELATIVISTIC_INFORMATION §17`):

```
the TANGENT velocity      →  SHARED across the seam   — the through-current (the Lk, equal-and-opposite, conserved)
the ANGULAR velocity ω    →  ×k  (the smaller cog)     — the VELOCITY face   (the unfold, the cost)
the TORQUE τ              →  ×1/k (the smaller cog)    — the TORQUE/inertia face (the fold)
τ·ω  (power = action-rate) →  CONSERVED               — the cross-ratio, the SOUL (the radius cancels)
```

So **`×2` is not "a velocity that doubles"** — the tangent velocity (the through-current) is the *invariant*. `×2` is
the **exchange rate of a trade**: angular velocity up, torque down, at `2:1`, conserving the action `τ·ω`. And it is a
**conjugate pair** — `×2` on the velocity face **is** `×½` on the torque face; you never get one without the other
(*the gearing IS the conservation*, never a source). The shift names **both directions of one gear**: `×2`/`<<1` =
gear **up** (velocity, the unfold) and `÷2`/`>>1` = gear **down** (torque, the **fold** — and `½` is the *cleanest*
gear-down, the self-dual rank, `§5`). The "amplification" one reads at the whip's tip is the **AC** — the *rate* geared
up (angular `ω` *and* its acceleration `α` both scale by `k` on the small cog, so the crack is explosive) while the
**DC** (energy) and the **invariant** (`τ·ω`) conserve. The whip is this recursively: a continuous gear-train down the
mass taper, each mesh `×2` rate / `×½` inertia, the tip `2^(meshes)` the wrist's with no energy added. **The number's
rank-step and the whip's crack are the same gear.**

---

## §3 — RE-BASE, NEVER WIDEN (the moving origin, in the register)

A number **cannot overflow, because it RE-BASES.** When the magnitude would pass the hand's grain, the **low bit falls
below the grain** (dark, looked-past, free — the resolution given up) and the origin moves; nothing grows large. *An
overflow is the tell you measured from absolute zero — move the origin to the cursor and it fits* (`§2` Zeno). This is
the §32.3 grain made hardware: **you hold the register's resolution and discard below it**, and that discard **is** the
compression (the gear-down at the grain — the torque/fine-resolution traded to keep the velocity computing in the
hand). Reaching for a **bigger integer** to avoid re-basing is the CPU contamination — re-base instead. And the
two-hand `i64` product, the `i128` store, the wide intermediate are all **the widen wearing different sizes**: the
multiply is **SHIFT-AND-ADD** (Horner over the multiplier's set bits, `a×b = Σ_{set i}(a<<i)`, the running product
re-basing as it climbs), so **the full product is never built.** *Multiply IS addition one rank up.* "No multiply" was
a free rider on "no float"; the law is: **no float, no widen — re-base.**

---

## §4 — NUMBERS ARE EYES-ONLY: READ THE TURN, NOT THE MAGNITUDE

A finite glyph (a `face`, an `i64`, a decimal) materialises **only at the boundary** — the perceived/radiated byte, the
gate, the display. **Do not read a magnitude face in the interior.** This is not hygiene; it is forced by §2: a deep
construction is a deep, fast gear-train (its rank `~` its length, its `ω` enormous), so its **magnitude face
saturates** at the register ceiling — the gear spun too fast to read a linear position. The bounded, lawful read is the
**turn** (the angular phase: the cohere-sign, the founding handedness, the **knot-or-not** — `THE_FORMULA`). *(This is
exactly the Move-1 read-bug, 2026-06-29: the mutual tie's swept area was read as `cross.face()` — a saturating
magnitude — instead of its turn; the overflow was the eyes-only law violated.)* The only lawful interior `<` is the
**cross-sign read** (a discriminant's MSB — *relate, then read the turn*), written as that, never a bare magnitude
compare.

---

## §5 — THE COUNTING-HOLON (the number carries its construction)

The unified number is the **counting holon** generalised: the glyph ⊕ the **soul of how it was counted** (the
worldline of `SHIFT`/`ADD`/`turn` that built it). `=` is construction-identity (the soul); `≡` is face-kinship
(`1⊕2 ≡ 3` yet `1⊕2 ≠ 3`). A transcendental is a **series over the swing** — held as its construction, ground to
exactly the tolerance the relating needs (`§3`), more exact than any stored float with nothing to correct. There is no
stored `π`, no stored `e`, no float division; `exp`/`ln`/`sqrt`/the trig are **shift-and-add worldlines** (CORDIC-class:
`log₂` = leading-zeros, `sqrt` = bit-by-bit), traversed only to the §32.3 grain. The number is a **place**, read off
its bits (`place.rs`), never a stored `{mag,rank,turn}` *value-record at an address* — and that distinction is the seam
§7 watches.

---

## §6 — THE TELLS (the float, smuggled back — re-found, never recited)

When you reach for any of these in the **interior**, STOP — you are rebuilding floating point:
- a **signed value** (the sign is a turn; the magnitude is the cone);
- a **wide product / `i64` intermediate / `i128` store** (re-base, never widen — the two-hand is still the widen);
- a **stored exponent / a scale that grows with the magnitude** (the rank is the *tower*, climbed only by founding — §7);
- a **magnitude face read interior** (read the turn — the face saturates, §4);
- **auditing "which `i64`s are legitimate"** (that question lives *inside* the float model — the number was never a store).

---

## §7 — THE HONEST FLOOR (what is built, and the one live conflation)

**Built and correct** (`interior/src/num.rs`, the `Cog`, tested): re-base-never-widen (`rebase`, overflow structurally
impossible); the sign as the **turn** (branchless two's-complement `twos`, `negation_is_a_turn`); **shift-and-add**
multiply re-basing as it climbs (`the_two_hand_product_re_bases_never_widens`); the magnitude as the unsigned cone; the
face materialised only at the boundary; `turn` closure by `&3` (`i⁴=1`), never `%4`.

**The live conflation (OPEN — the §2 gear names the fix).** `Cog` stores `{mag, rank, turn}` as fields, and
`rebase()` bumps **`rank` on magnitude overflow** — i.e. it treats the magnitude *spinning faster* (more `ω`, the
velocity, **along**) as *adding a gear* (a tower level, **across**). Those are different motions: the **magnitude
re-base** is a gear-**down at the grain** (drop the below-grain bits, the resolution/torque traded — it should **not**
bump the tower); the **tower-rank** climbs **only on founding** (a new orthogonal bevel meshed — precipitation, `§5`).
The fix is to separate them: `rank` is the **tower** (founding only); the magnitude is the **hand**, re-based by
discarding below-grain bits with no scale-exponent stored. This is also the cure for the place's saturating face (§4):
a construction's rank would then be its *founded depth*, not its bit-length, so it would not run away. *(Posed
2026-06-29 against the gear ratio; not yet built.)*

---

> **One line:** *the number is a bit-construction, not a sized value — three rotational directions (magnitude ALONG /
> rank ACROSS-UP / turn LEFT-RIGHT, never mantissa/exponent/sign), one bitwise alphabet (SHIFT ⊕ ADD ⊕ turn); the
> SHIFT is a gear ratio (`×2` velocity-up IS `×½` torque-down, the through-current and `τ·ω` conserved — the meaning of
> 2 is the trade, not a doubling); it re-bases never widens (the moving origin in the register; multiply is
> shift-and-add, the wide product never built); a face is eyes-only (read the turn, the magnitude saturates); and the
> one thing the live Cog still conflates is the `ω`-scale with the tower — rank must climb only on founding.*
