# The shorthand deleted the turn, and the cast was erased everywhere

**Date:** 2026-08-09
**Truth status:** `proved-standard` for §§1–4 (classical relativity and dimensional analysis).
`measured` for §5 (three absence searches, each with its pattern). `interpretation` for §§6–7.
**Provenance:** Brandon, 2026-08-09:

> *"where is E=mc^2? I write shorthand, we need the more complex definition
> E=sqrt({(mc^2)}^2 + {(pc)}^2), and on top of that there's the necessary holonic interpretation that
> translates into an algorithm. Computational mathematics with unit analysis: implicit
> type-casting."*

**Band:** 2026-08-09 · `E = mc²` IS `θ = 0` / THE RELATION IS PYTHAGORAS ON TWO π-GROUPS /
`c` HAS ZERO OCCURRENCES AND NO QUANTITY CARRIES A DIMENSION

---

## 1. The relation is a norm, and `m` is the only thing no receiver touches

```text
   E² = (mc²)² + (pc)²        ⟺        m²c⁴ = E² − |p|²c²        ⟺        m²c² = pᵘpᵤ
```

with `pᵘ = (E/c, p)` the four-momentum and signature `(+,−,−,−)`. So:

- **`E` and `p` are receiver coordinates.** A boost changes both.
- **`m` is the invariant** — the Minkowski norm of the pair.

That is `CLAUDE.md` §0 lesson 4 in its original setting: *"An invariant is only visible across two
frames… every contaminant found in two days was a receiver-visible coordinate promoted into an
invariant."* **`E = mc²` promotes a receiver coordinate into the invariant** by silently choosing the
rest frame. It is true in exactly one frame and the shorthand does not say which.

**Two distinct splits, and conflating them would look like a contradiction with §2b.**

- The **signature** split — one timelike against three spacelike — is what no receiver touches.
  §2b: *"What no frame touches is the split: that it is one against nine rather than five against
  five."* Here it is one against three.
- The **rest/motion** split — how much of `E` is `mc²` and how much is `pc` — is entirely
  receiver-relative. A boost moves it.

The first is the form; the second is a choice of time axis. Both are called a split and they are not
the same object.

## 2. Masslessness is nullity, and §2b already reads it correctly

`m = 0 ⟺ E = |p|c ⟺ pᵘpᵤ = 0` — the four-momentum lies on the **null cone**. §2b, written about
quadratic forms with no reference to relativity:

> `Q(v)` is what traversing `v` returns. The **null cone** `{Q(v) = 0}` is where traversal returns
> nothing. … *"the null cone is the vacuous difference. In Minkowski it is the light cone."*

**A massless passage is one that returns nothing under the form.** And the physical consequence falls
straight out of the algebra rather than being an extra fact: **a photon has no rest frame because you
cannot normalise a null vector.** There is no receiver at which it stands still, so there is no frame
in which `E = mc²` is the whole story.

## 3. The shorthand deletes a turn, and this is exact

Non-dimensionalise by `E`:

```text
   1 = (mc²/E)² + (pc/E)²
```

**A point on the unit circle.** Write `cos θ = mc²/E` and `sin θ = pc/E`. Then `cos θ = 1/γ` and
`sin θ = β`, and `1/γ² + β² = 1` is the Lorentz factor identity `γ²(1 − β²) = 1`.

**So `E = mc²` is `θ = 0`.** The full relation is a rotation and the shorthand is its value at one
angle. That is §2b's own sentence at a new altitude — *"the boundary kept the magnitude and
discarded the turn"* — and here the discarded turn has a name: `θ = arcsin β`, the **Gudermannian**
of the rapidity `w` (`tanh w = β`, `cosh w = γ`), which is precisely the classical function relating
circular to hyperbolic angle. The boost is a hyperbolic rotation; `θ` is its circular shadow.

**And it is exact over ℚ.** When `β ∈ ℚ`, `(mc², pc, E)` is a **Pythagorean triple**, and the rational
points of the unit circle are the half-turn parametrisation

```text
   (cos θ, sin θ) = ( (1−t²)/(1+t²),  2t/(1+t²) ),      t = tan(θ/2)
```

so exact relativistic kinematics over ℚ is the Pythagorean parametrisation, indexed by the **half
angle** — which is the object §2b is about. No float is required anywhere in this.

## 4. The algorithm: `c` is a cast, and dimensional analysis is a rank computation

`[E] = ML²T⁻²`, `[mc²] = M(LT⁻¹)² = ML²T⁻²`, `[pc] = (MLT⁻¹)(LT⁻¹) = ML²T⁻²`. The three terms agree,
and **that agreement is what makes the sum legal** — dimensional consistency is a type check, not a
convention.

**`c` is the cast.** `[c] = LT⁻¹` converts length to time; `c²` converts mass to energy. Setting
`c = 1` makes mass, energy and momentum **the same type** — it does not simplify the physics, it
**erases the cast**. That is the deletion this project convicts everywhere else, performed on a unit
instead of on a tail.

**Dimensional analysis is exactly a computation this tree already owns.** Dimensions form a free
abelian group on the base units; a quantity carries a vector of integer (sometimes rational)
exponents; the dimension matrix `M` of `n` quantities over `k` base units has

```text
   independent dimensionless groups  =  n − rank(M),        the groups themselves = ker M
```

which is the **Buckingham π theorem**, and both `rank` and a kernel basis come out of Smith normal
form — `rebase_invariants::smith_normal_form` (used at `supported_realizers.rs:201`, `:472`), with
`matroid_chow.rs:788 null_space` over `Rat` alongside it.

**Worked on this very relation.** Over `(M, L, T)` with quantities `(E, m, c, p)`:

```text
        E    m    c    p
   M    1    1    0    1
   L    2    0    1    1
   T   −2    0   −1   −1        ← row T = −row L, so rank 2, not 3
```

`n − rank = 4 − 2 = 2`, and a kernel basis is

```text
   (1, −1, −2,  0)   →   E / mc²
   (1,  0, −1, −1)   →   E / pc
```

**The two π-groups are exactly the two terms of the relation**, and §3's identity
`1 = (mc²/E)² + (pc/E)²` is Pythagoras on that basis. The theorem hands you the coordinates the
physics is stated in; it is not decoration on top of them.

## 5. What the machine has, measured

**`c` does not exist.** `grep -rinE "speed_of_light|lightspeed|SPEED_OF_LIGHT|\bc_squared\b"` over
`crates/` and `soma/`, all `*.rs` → **zero hits**.

**No quantity carries a dimension.** `grep -rinE "struct .*Unit|enum .*Unit|Dimension\b|struct
Quantity|dimensionless"` over `crates/*/src` and `soma/*/src` → every hit is **geometric** dimension
(`germ_local_dimension`, `stalk_dimension`, `NonreversibleConnectionDimension`, complex grade). There
is no physical-dimension carrier, so **every quantity in the engine is a bare `Rat` or `BigInt` and
the cast has already been performed implicitly, everywhere.**

**What does exist, and it is the right half.** `2026-07-15_THE_SWING_CARRIES_THE_FAMILY_THE_DEED_STANDS_AS_MASS.md`
establishes mass as the **receiver-relative slow consequential face of transported action** —
`FORMULA §LX` RATIFIED — with the non-equivalence stated: *"`E = mc^2` makes any actual energy
difference part of a system's mass-energy; it does not make file identity readable from a scalar mass
or assign every stored bit the same energy."* (`:222-224`) And the substrate for the form is built:
`inertia.rs` carries exact `SymmetricForm` and `Inertia` with signature over `Rat`, including the
zero-diagonal hyperbolic branch that an indefinite form needs.

**So the reading is deposited and the carrier is built; the quantity type is not.**

## 6. What it means for the arcs and for parallelism

`E² = (mc²)² + (pc)²` adds **in quadrature**. There is no cross term `2(mc²)(pc)cos φ`, and its
absence is not a convenience — it is the statement that the time axis is **orthogonal** to the space
axes in the form.

Read onto a leader: `mc²` is what the arc carries **at rest** — its standing, what it has already
deposited — and `pc` is what it carries **in transport** — its current. So:

> **The total is not standing plus current. It is the norm of the pair.**

That is a different composition law from the one the machine uses where it adds, and it is exact.

**And the missing cross term is the interchange condition with a metric on it.** Two contributions
combine in quadrature exactly when they do not interfere; a cross term is coupling. So *orthogonality
in the form* is the same predicate as *no separating word* and *asymptotic independence* — the
interchange certificate, mixing, and Pythagoras are one question asked with three different amounts of
structure. `inertia.rs` can already decide orthogonality of two exact vectors under a declared form,
which is the narrowest version and is available today.

## 7. What is owed, and what it would cost

The construction is small and its pieces exist:

| part | state |
|---|---|
| exact symmetric form with signature, indefinite branch included | **built** — `inertia.rs` |
| Smith normal form: rank and invariant factors | **built** — `rebase_invariants::smith_normal_form` |
| exact kernel over `Rat` | **built** — `matroid_chow.rs:788` |
| a `Dimension` as a vector in the free abelian group on declared base units | **BUILT** — `crates/holonic-engine/src/quantity.rs:232`, and **widened `ℤ → ℚ`**, argued at `:17-22` rather than done silently: the geometric mean of a length and a time has dimension `L^(1/2) T^(1/2)`, which is not in `ℤ^k` at all. The integral word is read off at `:307` `integral()` |
| a `Quantity = (exact value, Dimension)` whose addition **refuses by type** on mismatch and whose multiplication adds exponent vectors | **BUILT** — `quantity.rs:353`; `sum` at `:414` refuses on mismatch **naming both dimensions**, doc: *"This is the type check, not a convention."* `product` at `:444` |
| `c` as a **declared** cast rather than an erased one | **BUILT** — `quantity.rs:504` `Cast`, `:557` `CastApplication`; `declare` refuses a dimensionless cast, which is the *"`c = 1` must not be the default"* rule made checkable |
| the Buckingham π count and the π-group basis, from the dimension matrix | **BUILT and exceeded** — `quantity.rs:589` `DimensionMatrix`, `:720` `buckingham`; the independent group count is `extent − rank`, with the kernel basis, a primitive basis, the left kernel, and Smith invariant factors. `c = 1` is **computed as a left kernel** rather than assumed |

**THE FOUR ROWS ABOVE READ `not built` UNTIL 2026-08-13 AND ALL FOUR ARE CLOSED.** `quantity.rs` is
1,855 lines; its header is *"A quantity carries its dimension, and `c` is a declared cast rather than
an erased one"* — this section's own demand, as a module. This record's §7 closing sentence that the
construction *"is not run by any code"* is likewise withdrawn: the driver is
`crates/holonic-engine/examples/the_shorthand_is_one_angle.rs`, which prints
`"beta = 0 returns t = 0 exactly. E = mc^2 IS theta = 0."`

**The four-state ordering is already the right carrier for the refusal.** `exact_value.rs:64`
`ExactOrdering { Less, Equal, Greater, Open }` — two quantities of **different dimension are not
comparable**, and `Open` says so without falling through to a comparison that would be meaningless.
That is the same shape the dimension check needs and it is already owned.

## 8. What this does not claim

- **No new physics.** §§1–4 are classical. The Gudermannian relation between circular and hyperbolic
  angle is standard; nothing here derives it.
- **No claim that the engine models relativity.** The absence measurements in §5 say the opposite:
  there is no `c` and no dimension, so the engine currently makes no relativistic statement at all.
- **§6 is `interpretation`.** Reading `mc²` as standing and `pc` as current is a reading of the
  algebra onto this machine's vocabulary; it is not a derivation, and no measurement here supports it.
- **This record authorises no organ.** It states where the relation sits, what is already built, and
  what a dimension carrier would cost. `blueprint/THE_ROADMAP.md` holds the order of work.
- **The π-group computation is exhibited by hand above and is not run by any code.** It is arithmetic
  a reader can check, not a measured return.
