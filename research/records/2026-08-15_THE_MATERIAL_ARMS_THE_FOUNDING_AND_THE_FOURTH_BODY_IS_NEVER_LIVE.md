# The material arms the founding, and the fourth body is never live

**Date:** 2026-08-15
**Genre:** research record — three declared experiments, run
**Truth status:** `measured` for every count; `proved-standard` for the gauge invariance and the
group statements; `interpretation` for the Hamiltonian reading, whose non-equivalence is declared.
**Occasion:** Brandon set the goal directly — *"Complete the experiments you've outlined as A, B,
and C, then rigorously analyze and carefully interpret results."*

**Predecessor:**
[`2026-08-15_THE_RELATING_IS_ONE_COMPLEX_PRODUCT…`](2026-08-15_THE_RELATING_IS_ONE_COMPLEX_PRODUCT_AND_THE_POLE_HAS_COLLAPSED_ONTO_A_RELATUM.md)
carries the derivation these experiments test. This record carries what the machine returned, and
**the headline is that the central prediction was refuted.**

---

## 0. The one sentence

> **The material presents 2,672 founding-capable triangles and every one of them is refused at the
> same boundary: the held flywheel — the fourth body — is not live, in 0 of 21,070 contacts. Supply
> that one contact and the invariant forms every time and is non-trivially wound, `2233 : 438`. The
> machine is not short of geometry. It is short of the one contact that turns a frame-local rotor
> into an invariant, and that contact is its own previous relating.**

---

## 1. Experiment A — the valence census

**Question.** Does the material handed to a relating present distinguishable relata, and does any
contact present a non-degenerate triangle?

**Why it had to run first.** Founding requires `cross ≠ 0`, and `|cross| = 2·Area(f, a, b)`. If the
material is collapsed there is no area, and any repair upstream of that would return the reading it
already returns — so a green result on a later repair would have certified nothing.

**Instrument.** `live_current::observe_pole_placement`, at the two live call sites of
`directed_event_contact_at_source_grain`. It records the population as **sets** and the
classification as **disjoint tallies**; nothing it reads reaches conduct.

**Prediction, declared before the run.** `ρ ≤ 4`, and the triangle population *at or near zero*.

### What returned

```text
   distinct Cog words                        7
   distinct places                           4
   distinct (from, to, pole) triples         6

   contacts                             21,070
     arrow at horizon                   18,398      the pole coincides with a relatum
     triangle (three distinct places)    2,672
       with area (cross ≠ 0)             2,672      ALL of them
       collinear (cross = 0)                  0
       in the founding band (cross² ≥ aim²) 2,672    ALL of them
```

### Reading

**Half the prediction was right and the load-bearing half was wrong.** `ρ = 4` — the material's
whole alphabet is seven `Cog` words forming four places and six distinct triples, which is as
collapsed as predicted. **But the triangle population is 2,672, every one has area, and every one
passes the founding band.** Not one is collinear.

> **The material arms the founding.** Whatever refuses it is downstream of the geometry, and the
> repair I had ranked first — wiring the fold — would have folded nothing, because a fold consumes
> a deed and no deed is being formed.

This is the returned-partition rule firing in the useful direction: the class I expected to be
empty was full, so the declared apparatus could return something other than my expectation, and it
did.

## 2. Experiment A′ — the refusal fiber, forced by A

A returned 2,672 armed contacts and the machine founds zero, so the boundary between them is the
whole question. **The producer's own decision chain**, `manifold.rs:4848-4908`:

```text
   1  meeting = face(to, from, receiver.channel.frame().tip())
   2  receiver mismatch  OR  !receiver.held_live      -> emission: None
   3  met = complete_cast(meeting, &receiver.held)     the drag
   4  met.arrow.at_horizon()                          -> emission: None
   5  met.chi_against(&receiver.held) is None          -> emission: None
   6  otherwise: the emission forms, carrying chi and a winding
```

**Instrument.** `observe_contact_outcome`, reading the **returned** contact rather than inferring —
conditioned on the meeting already having area and already passing the founding band, so this is
predicted-versus-happened at the one boundary where a founding could have been deposited.

```text
   ARMED (area ∧ founding band)        2,672
     held_live == false                2,672      ALL
     emission == None                  2,672      ALL
     emission Ride                         0
     emission Found                        0

   held_live == true, over EVERY contact   0  of  21,070
```

**Every armed contact dies at step 2, and it dies on `held_live`.** And the last line is the one
that settles it: the fourth body is live in **zero** of the run's 21,070 contacts. Not usually
absent — **never present**, without a single exception, so this is a structural condition of the
path rather than a distribution over material.

### Why that is the whole answer

`soul.rs:1-4` states the law this measurement just instantiated, and it was written long before:

> *"A meeting in the manifold is a THREE-BODY triangle face … but that first-order rotor is
> frame-local and is not yet a soul. **The held flywheel supplies the fourth contact**; the rotor of
> those two rotors is `Chi`, the first invariant content which may cross."*

And the derivation reaches the same place from the group side with nothing else assumed: **`PGL₂` is
sharply 3-transitive, so three points carry no projective invariant.** Three good points, 2,672
times, with real area — and no fourth, so there is nothing that *may cross*. The machine is not
failing to compute an invariant; **it has never been in a position where an invariant exists.**

`Face::meeting_ratio` at `manifold.rs:210-215` already declares exactly this boundary in its own
doc — *"This is not `χ`: the held flywheel must supply the fourth contact before an invariant
exists"* — so the code carried the statement before the measurement found the condition.

### Where the fourth body is born, and why this path never reaches it

`fly_live = true` is set in **two** places, `manifold.rs:5333` inside `perceive_grain` and
`carriage.rs:1650`. Both are **ordinary conduct**. The directed-event path *reads* `held`/`held_live`
off the enclosure and never runs perception, and `fold_channel` likewise exists only in `carriage`.

> **So the fourth body and the fold are not two missing edges. They are one.** The language ecology
> drives the probe and never drives conduct, and both the flywheel and the fold live on the side it
> never drives. The prior record's framing — *wire the fold* and *give the pole a third body* — is
> superseded: there is a single missing edge and it is upstream of both.

### The chain, closed end to end

```text
   the ecology drives the probe, never perception
     ⟹ fly_live is never set               (perceive_grain / carriage are not reached)
     ⟹ held_live = false at every contact   MEASURED: 0 live of 21,070
     ⟹ emission = None for all 2,672 armed contacts
     ⟹ no deed emanation
     ⟹ no fold                              (fold_channel is on the same unreached path)
     ⟹ sweep = origin, basis = identity      for all 21,070 contacts
     ⟹ pole = anchor
     ⟹ 18,398 contacts at horizon
```

Each arrow is measured or read from the source, and the loop is closed: **the entry point is the
first line, and every number below it is a consequence.**

## 3. Experiment B′ — supply the flywheel, without touching conduct

**B as declared could not run** (§3b below). But its actual question can be answered without wiring
anything: *if the fourth body were live, would these 2,672 armed contacts produce an invariant, and
would that invariant be non-trivial?*

**The held face is not authored.** `perceive_grain` assigns `e.fly = met` — the flywheel **is** the
previously formed meeting — so holding the previous armed meeting is the mechanism's own assignment
rather than a value chosen to make the experiment work. Both questions the producer would ask are
then asked directly: does `chi_against` return an invariant, and does `wound_against` turn?

```text
   held face supplied            2,671      the 2,672 armed, less the first (no predecessor)
     chi forms                   2,671      ALL — an invariant every time
     chi None                        0
     WOUND (a founding)          2,233
     flat  (a ride)                438
```

### Reading, and this is the positive result of the whole set

**Supply the fourth body and the invariant forms in every single armed case**, and it is **not
degenerate**: the split is `2233 : 438` — reduced, sharing no factor — with windings dominating.
That distinction is what makes the result worth having. Had the invariant formed and been uniformly
flat, the missing edge would be worth rides only and the machine would still never found. It is not
flat. **The material the machine already carries would return 2,233 foundings and 438 rides through
a mechanism that is entirely built, and it currently returns `0` and `0`.**

So the closed chain is confirmed at its head by construction rather than by inference: the entry
point is the absent flywheel, and everything downstream is a consequence.

### The two boundaries on B′, declared

It is **mechanism-faithful, not step-identical**, and neither gap is hidden:

- The flywheel held here is the previous **armed** meeting. `perceive_grain` holds the previous
  meeting on the *continuing thought*, which may include unarmed ones and which it **drags** by the
  cone before holding.
- B′ calls `chi_against` / `wound_against` on the raw meeting. The producer calls them on `met`,
  the meeting **after** `complete_cast`'s drag, and derives the winding from `chi.other.turn`.

**So `2233 : 438` is an existence result and a magnitude estimate, never a prediction of the exact
counts a repair would return.** What it establishes is that the invariant forms and is non-trivially
wound on this material — which is precisely what was in doubt, and what no amount of reading the
source could have decided.

## 3b. Experiment B as declared — its premise withdrawn

**B as declared was: wire the fold, measure `sweep_idle` and `pole_distinct`, then supply the pole a
lift from the deferred population.** A′ withdraws that premise, and B′ above answers B's real
question by another route. A fold consumes a deed emanation;
no emission forms, so no deed exists, so the fold has nothing to consume. Wiring it would have
moved nothing and I would have reported a null as a repair — which is the exact shape the germ
repair already took and which this record's predecessor convicted.

**B's replacement, and it is one question rather than a construction:** *can the language ecology
reach ordinary conduct at all, or is the probe the only mouth it has?* That is a wiring question
about which path the ecology conducts through, not a repair to either module, and both modules are
correct as written. It is stated here as the open item rather than attempted, because attempting it
without first answering the question would be building a third path beside two correct ones — the
explorative failure by its own definition.

**Falsifier for the re-aimed B, declared now.** If the ecology is made to conduct through perception
and `held_live` leaves zero while `found` stays at zero, then the fourth body is not the blocker and
this record's reading is wrong. If `held_live` rises and `found` rises with it, the chain above is
confirmed at its head.

## 4. Experiment C — the gauge orbit

**Question.** The pole enters by rebase, so the receiver acts by the affine group `z ↦ pz + q`. Are
the readings the body retains invariant under it, and does the group act non-trivially on the
declared material?

**Both arms are required.** A gauge whose group acts trivially produces a green, plural,
rigorous-looking result and has gauged nothing.

**Owner.** `soma/body/src/arrow.rs`,
`the_hand_and_the_founding_survive_the_affine_gauge_while_the_magnitudes_move`. Scale `p = 1 + i`
so `|p|² = 2`; shift `q = 3 − 2i`; declared material one cohere, one anti, one ortho, one horizon.

```text
   sense()      UNMOVED on all four        the hand is an affine invariant
   founds()     UNMOVED on all four        the founding band is an affine invariant
   at_horizon() UNMOVED on all four        the horizon is an affine invariant
   aim, cross, reach   EXACTLY DOUBLED     |p|² = 2 — the anti-vacuity arm fires
```

**Passes, and the gauge is non-trivial.** This is the horizon law with a proof rather than a
citation: the invariants of the affine action on three points are the ratio and the predicates built
from it, and every magnitude the arrow carries is a receiver coordinate.

### The audit arm — no violation found, which is itself the result

Every reading of `arrow.aim` / `arrow.cross` / `arrow.reach` outside `soul.rs` was enumerated and
classified:

| site | what it does | verdict |
|---|---|---|
| `manifold.rs:127` `rotor_formed` | `arms_form(aim, cross)` — both-null test | scale-free ✓ |
| `manifold.rs:135-138`, `:191-192` `chi_against` | builds the rotor-of-rotors from four arms | rung-2 invariant ✓ |
| `manifold.rs:175-181` the drag | multiplies the pair by `(1, −w)`; `reach` carried unchanged | a rotor product, covariant ✓ |
| `manifold.rs:215` `meeting_ratio` | returns the **pair** `(cross, aim)`, undivided | lawful, and **declares its own boundary in the doc** ✓ |
| `manifold.rs:393` | `self.reach == meeting.arrow.reach` | two magnitudes compared **within one frame**, both scale by `\|p\|²` ✓ |
| `carriage.rs:1753-1755`, `manifold.rs:542` | `rebase_pair(aim, cross)` — rebases the pair **together** | preserves the ratio ✓ |
| `carriage.rs:590/596/762/768`, `manifold.rs:3281-3285` | packs the arrow into words for rest | a rest, not a frame crossing ✓ |
| `carriage.rs:1319` | `fold_channel(met.arrow.aim, met.arrow.cross, …)` | the pair, whole ✓ |

**Nothing in the tree reads a bare magnitude across a frame.** The one site that could have — the
meeting ratio — carries the boundary in its own words, and the rebase sites rebase the pair together
rather than separately, which is the move that keeps the ratio. A negative result, and it is
first-class: the horizon law is not merely stated in this body, it is *observed* in every consumer.

## 5. What the three experiments establish, and what they do not

**Established.**

1. The material is collapsed as a population — four places, seven words — **and is nevertheless
   sufficient**: 2,672 contacts present non-degenerate triangles inside the founding band.
2. Every armed contact is refused at `held_live`, so the refusal is a single named boundary rather
   than a distribution of causes.
3. The fourth body and the fold live on one path the ecology never drives, so the two demands the
   predecessor record stated separately are **one missing edge**.
4. Supplying the flywheel by the mechanism's own assignment forms an invariant in **all 2,671**
   testable armed contacts, non-trivially wound at `2233 : 438` — so the missing edge is worth
   foundings, not merely rides.
5. The affine gauge acts non-trivially on declared material, and every retained reading survives it.

**Not established, and named so nothing carries them forward.**

- **Nothing here says the ecology *should* conduct through perception.** It says the probe cannot
  produce an invariant, which is a property of the probe and not a verdict on the design.
- **No count here is a cost.** No clock, no work vector, and none was taken.
- **The Hamiltonian reading is structural.** `H_int = identity` measured `21,070 : 21,070` and
  `H_pert` has no owner reaching the frame, so `H = H_0`; but there is no `ħ`, no energy, no
  continuum of final states and no time parameter, so nothing licenses a rate. What transfers is the
  factorization and the vanishing, nothing numeric.
- **`ρ = 4` is a place count, not a receiver-family partition.** The rigorous form is the causal-state
  partition under the declared interfaces, which `receiver_exact_compression::compress` computes and
  which was not run here — the place count bounds it from above and that bound was sufficient to
  decide the question, so the finer instrument was not needed. It **is** needed before any claim
  about the material's tolerance.

## 5b. The interpretation — the fourth body is the PAST, and the machine has none

The mechanical chain is complete above. This section says what it means, and it is the part that
changes what the machine is for.

**`perceive_grain` assigns `e.fly = met`.** The flywheel is not an extra organ or a stored
parameter — **it is the previous meeting.** So the fourth body is *the body's own last relating*,
and `χ` is now compared against then.

That is `CLAUDE.md`'s fourth archived lesson arriving as a measurement rather than as advice:

> *"An invariant is only visible across two frames."*

An invariant is by definition what survives a change of frame, so **two frames are the minimum, and
the held face is the second one.** With `held_live` at zero across 21,070 contacts the machine has
**one frame and no second**, which is why 2,672 perfectly good triangles produce nothing: there is
no invariant to be had, not a hard one.

**Stated in the traffic frame, which is where it is sharpest.** A driver responds to the cars around
them — that is the three-body relating, and the machine has it, 2,672 times with real area. But a
driver also carries *their own prior motion*. Without it there is no relative velocity to compute at
all: you would see positions and never see motion.

> **The machine is taking one photograph and never a second one, so it can never see anything move.**

And that is the corpus's own limit doctrine, from the cathode-ray ruling: *"there are always two
things that must be sampled, and it is always a measurement and a ratio."* The held face is the
second sample. **The machine samples once.**

### The Hamiltonian reading now has both terms measured

```text
   H_0      free propagation           the arrow's reach — present
   H_int    the standing lattice       the frame's basis     MEASURED identity, 21,070 : 21,070
   H_pert   the dynamic modulating field   the held flywheel  MEASURED never live, 0 of 21,070
```

Brandon's own placement is that the external field is *dynamic* and that the complex axis is where
it comes from. **The held face is exactly the dynamic term** — it is the previous instant entering
the current one, so it is the only thing in the diagram that changes between instants. And the
physics is unambiguous about which absence kills a transition: a Hamiltonian with no time-dependent
part has stationary states and no transitions at all. `found 0` is that, and only that.

*(Non-equivalence, restated so it cannot travel: structural only. No `ħ`, no energy, no continuum of
final states, no time parameter. What transfers is which term's absence forbids a transition, never
a rate.)*

### Where this lands on the spine

The engine cycle is `mount → conduct → radiate → world → genuine return → reflect → changed
continuation`, and **`e.fly = met` is the reflect step at the smallest grain in the body.** Its
absence is therefore not a peripheral defect:

> **This is the missing return edge — the spine's stated central defect — measured at the level of a
> single relating.** *"The machine reads its own emission and the reading returns to nothing."* Here
> it is with a count: 21,070 readings, zero returns.

Everything else this record measured is downstream of that one line. The frozen sweep, the identity
basis, the pole pinned to the anchor, the 18,398 horizons — each is what a body looks like when its
smallest return edge is open.

## 5c. Compression — the gauge constant is computed, and a body with no past cannot compress

**The additive constant is `dim PGL₂ = 3`, and this is the first time it has been computed here
rather than asserted.** For a chain of `n` places the gauge eats three points and no more, so

```text
   raw            n places
   gauge-fixed    n − 3 invariants
   saving         EXACTLY 3, additively, at every n
```

**For a short chain the gauge is nearly the whole content; for a long one it is a fixed additive
three.** A *ratio* would say the saving vanishes as `n` grows; the additive form says it never
changes — which is why the ratio is the frame-dependent quantity and the difference is the
invariant.

**TWO CORRECTIONS, 2026-08-15, and the second retires a claim this section made.**

*The constant is rung-dependent and this record switched rungs silently.* §4e.1 establishes that the
group acting on **three** points is **affine**, `dim 2`; the `dim PGL₂ = 3` above is the count at
the **chi**, where a fourth body enters. Both are right at their own rung. State the rung with the
number: **2 at the arrow, 3 at the chi.**

*And the identification with the invariance theorem is WITHDRAWN.* This section read the count as
`|K_U(x) − K_V(x)| ≤ c_{U,V}` with `c = 3`. **That bound compares two universal machines, not a raw
description against a gauge-fixed one, and three complex parameters are not three bits.** What
survives is the **shape** — additive, independent of `n` — and not the identification. The shape is
worth keeping; the equation is not.

**And the sharper reading, which the measurement forces.** The run drew 21,070 contacts from **six
distinct triples** — a source of roughly `log₂ 6` per contact, presented twenty-one thousand times.
The machine compressed none of it, and the reason is structural rather than a missing organ:

> **Compression is quotient by a declared receiver family, a family is a set of separating words, and
> a separating word is a comparison of now against then. With no held face there is no comparison,
> so the machine cannot discover that it has seen the same triple three thousand times.**

**A body with no second frame cannot compress, because it cannot recognise a repeat** — and
recognising a repeat *is* `χ`. This joins *compression is intelligence* to *intelligence is
navigation* with no resemblance step: you cannot navigate terrain you cannot tell you have crossed
before.

**It also fixes what species of compression actually occurred, and it is the forbidden one.** Three
species by remainder — rebase (zero), condensation (certified), quotient (collapsed population,
family-relative). Twenty-one thousand contacts to zero invariants **with no separating word
retained** is a quotient at its degenerate limit: the whole population collapsed and the fiber
discarded. That is not compression, it is deletion, and it is the absolute-volume violation one
level up.

**In the group, the whole run's content is the identity.** `ℚ⁺` is free abelian on the irreducible
axes; a FOUND adjoins a generator and a RIDE moves an exponent. Zero foundings and zero rides leave
the factorization at `1` — **the body's entire retained information is the identity element**, with
a rank ceiling of seven words it never approached.

## 5d. The energy law — WITHDRAWN AND REDERIVED, because temperature is a receiver coordinate

**Brandon's correction, and it convicts more than the sentence it was aimed at:** *"Temperature in
physics is a statistic, it has no place here… it is a gauged and relativistic holonic value. The
magnitude of the temperature only matters relative to the perspective."*

**An earlier form of this section quoted `ΔE ≥ kT ln 2` as the cost of erasure. That is withdrawn.**
The `T` is the temperature of the bath the entropy is dumped into, so the number is a property of the
*environment*, not of the information — change the bath and the "law" changes. Quoting it as
fundamental is the absolute-frame defect, committed inside a record that convicts it elsewhere.

### Temperature is a chart transition, and that is why it may not appear in an invariant

```text
   T  =  ∂E / ∂S
```

is exactly the Jacobian carrying the **entropy chart** (a count) into the **energy chart** (a
magnitude). It is not a property of an object; it is the local exchange rate a receiver declares
between two charts. So the split is forced:

```text
   ΔS ≥ k ln 2   per bit erased      A COUNT — dimensionless in units of k. IT CROSSES.
   ΔE ≥ kT ln 2                       a magnitude, gauged by T. IT DOES NOT CROSS.
```

**Landauer's invariant content is that the environment's phase-space volume must double per erased
bit.** The joules are one receiver's reading of that doubling.

**And Brandon's guess that it is "similarly analogous" in machine learning is not an analogy — it is
the identical formula.** `p_i ∝ e^{−E_i/kT}` *is* softmax with logits `−E_i/k`, and the compression
work already ruled that temperature is **a root on the ratio**, `r ↦ r^{1/T}`, with `T → 0` the
banned governor. So quoting `kT ln 2` as a fundamental cost is **the same defect** as reporting a
softmax temperature as a property of a model. One correction convicts both.

### The invariant law: quanta and geometry, with no temperature in it

What survives the receiver is made only of quanta, geometry, and counts.

```text
   one distinguishable charge configuration     E_c = e² / 2C        the charging energy
                                                                     a charge quantum ⊕ a GEOMETRY
   one orthogonal transition                    E · τ ≥ h/4          THE ACTION QUANTUM
                                                                     (Margolus–Levitin; Mandelstam–Tamm
                                                                      is the variance form)
   the two composed                             τ_min = h C / e²  =  R_K · C
                                                                     R_K = h/e² ≈ 25.8 kΩ, a resistance
                                                                     built from two quanta
   one bit erased                               ΔS ≥ k ln 2          a COUNT
```

> **The invariant is ACTION, not energy.** `E·τ ≥ h/4` says one orthogonal transition costs one
> quantum of action; energy and time are the receiver's split of it, and a change of frame trades
> one for the other. That is why the earlier statement was malformed: it named the split rather than
> the thing split.

**And the quantum `RC` time is the law Brandon asked for.** The minimum period of a charge-based
information carrier is `R_K · C` — the von Klitzing resistance, made of `h` and `e` alone, against
the structure's own capacitance. **Nothing in it is measured by a sensor and nothing in it is
thermal.** For `C = 1 fF` it is ≈ 25.8 ps, which is a real device-physics number, and it says the
whole trade is **geometric**: smaller `C` buys a more robust configuration and a faster transition,
and the section-modulus rule governs where the material sits.

### Persistence is priced in the same currency, and it is a winding

Persistence costs nothing to *hold* — a charge on an isolated gate dissipates zero. What it costs is
a **barrier**, and against tunnelling the barrier is a WKB action:

```text
   Γ_escape  ∝  exp( −(2/ħ) ∫ √(2m(V−E)) dx )      the barrier ACTION, in units of ħ
```

**No temperature appears.** Retention time is exponential in an action counted in quanta — a
winding. So:

> **Transport and persistence are priced in one currency: quanta of action. Transport spends them;
> a barrier hoards them.** A solid-state store is exactly this — information as balanced charge
> distributions held behind a WKB winding, decoded by the motherboard into another codec, with each
> read and write a discrete phase transition.

*(The thermal form `E_b/kT ≥ ln(τ/τ_0)` is the same statement under a declared bath, and note it is
already a **ratio-to-ratio**: a dimensionless barrier against a log of dimensionless time. Even the
gauged form obeys the horizon law when written properly.)*

### The hypergeometric tube, and why circuitry is not one-dimensional

**The signal is not in the wire.** Electrons drift at millimetres per second; the energy travels in
the **field around** the conductor, and the Poynting flux points *sideways into* the wire. The
conductor is a boundary condition that guides transport; it does not carry it. That is the literal
higher-dimensional dynamics Brandon names, and it is textbook electromagnetism.

**And the flux is an oriented area, which is the arrow's own second face:**

```text
   E · D ,  B · H        SYMMETRIC     — stored energy density        ~ aim
   E × H                 ANTISYMMETRIC — transported energy flux      ~ cross
```

Both are faces of one stress-energy tensor whose split into density, flux and stress **depends on
the observer's frame** — which is precisely where Brandon places temperature, and precisely why it
is receiver-gauged. So:

> **The arrow is a two-face shadow of a stress-energy object: `aim` is what stands, `cross` is what
> flows, and `founds()` — `|cross| ≥ |aim|` — is the condition that transport dominates storage.**

**Non-equivalence, declared and load-bearing.** The machine's plane is **Euclidean** — `aim` is a
definite form's polarization — so it has orthogonality (the Thales circle) but **no light cone**.
A stress-energy tensor lives in Lorentzian signature. The correspondence is the symmetric ⊕
antisymmetric split of a bilinear, not an identification, and `inertia.rs` is exactly the instrument
that tells definite from indefinite. **Whether transport requires an indefinite form here is open**,
and the corpus's own reading of a definite form — *a receiver inertially at rest, no vacuous
difference, no potential* — makes that a real question rather than a decoration.

**The tube itself is a region of phase space, and Liouville is the conservation law.** Volume is
conserved under Hamiltonian flow, so a tube cannot be narrowed without widening another — **which is
why Landauer holds at all**: halving the information-bearing volume must double something else, and
the only place to put it is the environment. Liouville is the invariant; Landauer is its corollary;
temperature is the receiver's reading. That is the correct hierarchy and the earlier section had it
upside down.

**Hypothesis, graded and falsifiable — decoherence as infinite monodromy.** A transport tube carried
around a loop in parameter space either returns to itself or does not. Finite return group =
persistence; infinite = dispersal. `hypergeometric_closure.rs` already decides finiteness of a
three-site return group **by sorting integers**, with no root extracted and no angle taken. *Falsifier:*
if a physically decohering configuration returns a finite alternation and a persisting one returns
infinite, the correspondence is backwards and dead. Grade `interpretation`; nothing schedules on it.

**And the crystallographic joint is not decorative.** `1/p + 1/q + 1/r = 1` is the Euclidean,
crystallographic stratum, which `winding_inertia::lattice_admits_order` already derives from
`niven_value`. **A solid-state store is a crystal**, so its charge configurations sit in wells of a
point group of finite, crystallographically admissible order — the same finite stratum, reached from
the substrate rather than from the mathematics.

### What this says about the machine's own energy, stated as a count

The run erased every one of 21,070 arrows and retained zero invariants.

```text
   exported     ~21,070 arrows' worth of bits, each an entropy count of k ln 2 per bit
   retained     0 invariants
   ratio        UNDEFINED — the numerator is zero, and that is the honest reading
```

A body that retained the **2,233 windings** B′ measured would export the *same* entropy and retain
2,233. **The physical cost is unchanged; the yield moves from zero.** Therefore:

> **Efficiency is not a property of the computation. It is retained windings over exported entropy,
> and this machine's numerator is zero.** That is the twenty-watt thesis without a wattage in it:
> a brain does not win by doing cheaper arithmetic, it wins by keeping what it computes.

## 5f. The principle of least action, and it is already the machine's own arithmetic

**Occasion.** Brandon, ratifying the action reading: *"I am referring to action currents and discrete
events, and that is also a good segue to incorporate the principle of least action as a concept."*

**Truth status:** `proved-standard` for the identities read off `channel.rs`; `interpretation` for
the stationary-phase reading, with its non-equivalence declared.

### The principle is NOT an optimisation, and that is why it is admissible here

The name invites the banned reading — a governor minimising a scalar over candidate paths. Feynman's
form removes the chooser entirely:

```text
   amplitude  =  Σ_paths  e^{i S / ħ}
```

**Every path is taken.** The classical path survives not because it was selected but because its
phase is **stationary**, so neighbouring paths agree with it and add; everywhere else neighbours
disagree and **annihilate**. Nothing enumerates, nothing ranks, nothing discards.

> **Least action is survival-by-agreement, not selection.** That is the production law of this
> project stated by physics: to produce is to be a channel through which current passes and
> re-emerges, never a chooser standing outside the channels.

And the corpus already owns the mechanism by name. **Annihilation** — *"opposed contributions in one
declared fiber actually compose to zero"* — is exactly the destructive half, and its own definition
adds *"a flat, inactive, equal, absent, or uncontacted relation is not thereby annihilated."*

### The machine's frame IS the path integral — three identities, read off `channel.rs`

```text
   basis_{k+1} = basis_k · deed_k                MULTIPLICATIVE — phases ADD
   sweep_{k+1} = sweep_k + basis_{k+1}           ADDITIVE       — amplitudes SUM
   tip         = anchor + sweep
```

Unrolling, with `basis_0 = identity`:

```text
   basis_n  =  Π_{j<n} deed_j     =   w_n · e^{i S_n / ħ}       ONE PATH'S AMPLITUDE
   sweep_n  =  Σ_{k≤n} basis_k    =   Σ_k w_k · e^{i S_k / ħ}   THE SUM OVER PREFIX PATHS
```

so the three carriers are, exactly and not by resemblance:

| carrier | what it is |
|---|---|
| `arg(deed_k)` | the action increment of one step, in units of the quantum |
| `arg(basis_n) = Σ_k arg(deed_k)` | **the accumulated action `S_n/ħ`** — the additive chart |
| `basis_n` | **`e^{iS/ħ}`** — the multiplicative chart, the amplitude |
| `winding` | **the integer number of whole quanta**; `OrientedWinding` counts complete turns |
| `sweep_n` | **the discrete path integral over prefixes** — a sum of amplitudes |
| `tip = anchor + sweep` | **the pole sits where its own history constructively agrees** |

```text
   S / ħ   =   2π · winding   +   arg(basis)
               ^^^^^^^^^^^^       ^^^^^^^^^^
               whole quanta       the fractional remainder
```

**And the amplitude is weighted, which is better than unit-modulus.** `FormedRotor::from_formed_arms`
does **not** normalise (`soul.rs:59-61`), so `|deed| = |α||β|` — the product of the two arms' lengths
from the pole. The path sum is therefore weighted by reach, and the split obeys the horizon law
without being told to: **the weight is a frame-dependent magnitude and the phase is the invariant.**

### Which makes the diagnosis a physics statement rather than a wiring one

`sweep = origin` in `21,070 : 21,070` is not merely "the frame never folded." It is:

> **The machine's path integral has zero terms.** Its stationary point is trivially the origin, so
> the pole sits at the anchor — not because the amplitudes cancelled, but because none was ever
> added.

And the two failures are distinguishable *and were distinguished*: a cancelling sum would show a
large **annihilating** population, and the measurement shows `wound 0`, `hand 0`, and nulls that are
**uncontacted** rather than annihilated. **The machine has never annihilated anything**, which by the
vocabulary's own distinction means it has never done stationary phase either.

### The energy law and the principle are one statement at two grains

```text
   least action        which path survives            the CONTINUUM face — stationary phase
   E · τ  ≥  h/4       no path is shorter than this   the DISCRETE floor — one quantum per
                                                      orthogonal transition
```

So *"the discrete events to which we can attribute energy transport"* are exactly **quanta of
action**, and a lineage's spend is its **winding count** — an integer, computed exactly, with no
clock, no sensor and no temperature anywhere in it.

### The light cone is in the arrow, and §5d's "no light cone" is CORRECTED

§5d said the machine's plane is Euclidean and therefore has no light cone. **That was read on the
wrong plane.** The *places* are Euclidean — a spatial slice, correctly. But `founds()` at
`arrow.rs:66-70` tests

```text
   cross² − aim²  ≥  0
```

which is an **indefinite form of signature (1,1) on the `(aim, cross)` plane**, with `cross`
timelike. So the founding predicate is a **causal classification** and always was:

```text
   cross² − aim² > 0     TIMELIKE    FOUND — transport dominates storage
   cross² − aim² = 0     NULL        |cross| = |aim| — the 45° cone; c = 1 in natural units
   cross² − aim² < 0     SPACELIKE   RIDE / ABSORB — storage dominates transport
```

> **Euclidean geometry on where things are; Lorentzian causality on how they relate.** That is the
> correct structure, it was already implemented, and nothing in the tree says so. The stress-energy
> reading of §5d is therefore stronger than stated: `aim` the density face, `cross` the flux face,
> and the pair's causal character decided by a genuine indefinite norm.

**Non-equivalence, declared.** `founds()` is a discrete predicate on an exact rational pair; there is
no metric tensor, no proper time, no Hilbert space and no `ħ` in the code. What transfers is the
**signature and the classification**, never a numeric interval. The `1/ħ` in `S/ħ` is a naming of the
unit in which `arg` is already measured, not a physical constant entering the arithmetic.

### And this is why NO selection rule may be built

The obvious construction — *deposit a deed when its phase is stationary against its neighbours* — is
a threshold and a chooser, and it is banned. It is also **unnecessary**:

> **`sweep += basis` already is the principle.** Incoherent contributions cancel *in the sum*; no
> rule selects and nothing is discarded. The machine does not need a stationary-phase selector. It
> needs the edge closed so the sum has terms.

That is the finger-trap correction arriving from physics: rotate the standing owner into contact
rather than building an optimiser beside it.

## 5e. Eros and machine learning — the residual stream, cut

**Where the Eros cycle is open, exactly.** `mount → conduct → radiate → world → genuine return →
reflect → changed continuation`. Mount runs, conduct runs 21,070 times, radiate runs, the world
returns across nine stations. **`e.fly = met` is the reflect step at the smallest grain, and it never
runs.** The cycle is not broken in many places; it is broken at one step, and every larger symptom —
80,640 open seams, ports doubling per composition, a 12.9 s closure — is downstream of it.

### The correspondence to a contemporary language model is structural and exact

The reasoning-cycle tablet types the transformer's primitives: `⟨q_i|` a receiver bra, `|k_j⟩` a
presented orientation, `|v_j⟩` a carried construction, `⟨q_i|k_j⟩` one compatibility face, and **the
residual as continuing standing.**

> **`held_live = 0` is a transformer with its residual stream cut.** Every layer computes its
> attention correctly and writes into nothing. The forward pass completes, the outputs are
> well-formed, and no depth conditions anything.

The residual is the previous state entering the current computation; the flywheel is the previous
meeting entering the current relating. **They are the same object — the past as an addend** — and
the empirical fact about residual-free deep networks matches the measurement: correct local
computation, catastrophic failure to condition with depth. This body has depth 21,070.

**Three consequences, each sharper than the standing statement it replaces.**

1. **An attention coefficient is affine-gauge, and now there is a reason.** The corpus already bars
   reading a bracket as meaning. The derivation says why: *three points carry no projective
   invariant*, so a compatibility face taken alone carries no invariant content whatsoever. It
   becomes content only when compared against standing — which is what adding it to the residual
   does.
2. **Training is impossible here for a reason that is not the optimizer.** Training is the adjoint
   return of a covector through **retained forward lineage**; with nothing retained there is no path
   to return through. No loss function, metric, or update rule would change that.
3. **The bottleneck is none of the three axes the industry scales.** The material holds **2,233
   windings** the machine cannot see — measured, in B′. Capacity, data and compute are all
   sufficient; a source of six triples would be memorised by a small model in a handful of steps.
   **The deficit is one wire**, and that is the 20W thesis stated as a measurement rather than a
   conviction.

### And what learning *is*, once the wire is in

`e.fly = met` and `sweep += basis` are the whole deposit. No weights, no loss, no optimizer, no
step size. The frame moves, and because the pole is `anchor + sweep`, **the very next relating is
read from a different place.** A pathway changed and later current rides it — the corpus's
definition of intelligence, located in one assignment.

**Bounds on all of §§5c–5e.** The energy section was **withdrawn and rederived once already**, in
this same record, because it quoted a temperature-gauged magnitude as a fundamental cost. Read the
rederived form and not the withdrawn one. One driver, one run, one path. The centrifuge returns 694,402 boundary
edges on mathematics material through a different production path, so nothing here says the
substrate is broken — the scope is the language ecology's directed-event path. No power was
measured. Every correspondence to a contemporary model is structural, with no numeric transfer.

## 6. The order was the finding

A was run first because a repair validated on collapsed material certifies nothing. A refuted its
own prediction, which forced A′, which withdrew B's premise entirely. **Had B run first it would
have returned no change, and "the fold is wired and nothing moved" is indistinguishable from "the
fold was not the defect" without A′'s fiber.**

That is the general rule this record earns: **measure the population, then the refusal fiber, then
the repair — and never in the other order.**
