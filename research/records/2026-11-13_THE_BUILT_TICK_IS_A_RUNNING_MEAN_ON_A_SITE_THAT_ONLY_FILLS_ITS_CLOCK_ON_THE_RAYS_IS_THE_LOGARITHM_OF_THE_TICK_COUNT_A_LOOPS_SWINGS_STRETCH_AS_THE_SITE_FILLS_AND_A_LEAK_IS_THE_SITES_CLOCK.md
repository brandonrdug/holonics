# The built tick is a running mean on a site that only fills, so its clock on the rays is the logarithm of the tick count; a loop's swings stretch as the site fills; and a leak is the site's clock

Refs #404 #406. Status: [theory's reading of the built tick's own time, with one ruler on a
public receipt; November 13, 21:20Z; §9 read after, near 21:50Z, on the engineering thread's
receipts], by the theory thread, which holds no runs. Nothing here is built and nothing here is an
order. Every statement carries one of three grades: `tree` (an atlas
row or a source line, named), `from training` (a discipline's result, restated on the objects with
its hypotheses) and `agent-inferred` (this thread's reading). Source read on `main` at
`2ef3af73c`.

Owners named: the built tick and its pass (`crates/holonics/src/hnn/tower/field.rs`:
`Field::tick`, `Field::pass`, `lane_chart`; `crates/holonics/src/hnn/tower.rs`: `ratio_to_power`),
the reading of read-depth (`store_train.rs`: `read_depth`; G149's receipt `g149_depth.txt` and
`depth_ruler.py` under the level record's `_receipts/`), the reaction's reading (G158's receipt
`g158_reaction.txt` under the junction record's `_receipts/`), and the atlas rows
`receiver.referent-mass`, `store.finite-quality`, `motion.quadratic-three-kinds`,
`motion.mobius-multiplier-cross-ratio`, `spectro.clock-gauge`, `tower.field-read-free-fall`,
`tower.field-site-power-unread`, `tower.field-tick-return`, `tower.field-reaction-mirror`,
`contact.carry-coupling-through-the-leak`, `contact.pass-reach-gap`, and for §9 the readings
`Field::free_ring` and `read_release` with their receipts, `junction.restitution-family`,
`tower.field-echo` and `receipt.reafference-lag`. Three atlas rows enter (§8), and the scope of
`tower.field-reaction-mirror` gains the readings that read it. No owner moves.

## 1. Why this record exists

Brandon asked on November 13 (18:21Z) that the readings of self-induction reach theory to think
about, whether they hold or miss, and said in the same message that self-induction is something he
asserts and that no reading is a test of it. The engineering thread has since read a reader's
reaction on its source four ways (its G159 to G162: the pair's decomposition, the reaction in the
form of the read's mirror at first order, at finite strength, and in the free ring at sixteen
ticks). Their receipts were not in this thread's tree at this writing, so **no figure of theirs is
repeated in §1 to §8**, and §9 reads them at their receipts; what reached this thread is a relayed
summary, of which this record uses one qualitative line (relayed at 20:58Z, to be read at its
receipt when it lands): with the reaction on at a turning sign, the free ring showed no reversal
within sixteen ticks, and the engineering thread read that as the tick's relaxation damping the
turn and named a drive (the passage still arriving while the ticks run) as its next design.

This record reads what the free ring is made of before any reaction is added: the tick's source
and G149's receipt, which is public. One sentence carries it (`agent-inferred`): **a site's state
within a pass only fills, and every reader divides the filling out, so the pass is a running mean
whose own clock is the logarithm of the tick count; on that clock nothing is damped and a loop's
swings stretch; the leak a site lacks is the clock it lacks.**

## 2. What the tree held

Searched under each discipline's name before writing (running mean, Cesàro, harmonic gain, leak,
forgetting, integrator, aging, estimator gain, spectral gap, power iteration, parabolic, conformal
time, scale factor, redshift, proper time, re-timing, log-periodic).

- **The running mean, as a mass** (`tree`, `receiver.referent-mass`, formal-checked in
  `HNN/ReferentMass`): `k` identified returns from an opening of mass 1 make a region of mass `k`
  whose next return has the share `1/(k + 1)`, the region being the running mean, and its pull on
  the next crossing `M/(M + 1)`. The row is stated of a referent and its loops along a passage.
- **The store with no leak** (`tree`, `store.finite-quality`): `z′ = γz + ξ` at `d = 0` has no
  resting value, its power after `n` steps being `n`; the house rule beside it is that no store is
  at rest and that a store holds by upkeep.
- **Free fall** (`tree`, `motion.quadratic-three-kinds`, `tower.field-read-free-fall`): a shear is
  nilpotent, `(1 + sX)(1 + tX) = 1 + (s + t)X`, and a head's read at held shares is one: `K` ticks
  are one tick `K` times as far. The second row already says that on a chart read at unit power
  the like sign is no runaway, the growth being a scale no chart reads.
- **A site's power is read by nothing** (`tree`, `tower.field-site-power-unread`): every forward
  reader takes the lane chart `r̂ = x/‖x‖`, a push `δ` turning the ray by its part off the ray
  over `‖x‖`, so the power acts only as inertia.
- **A load is a clock** (`tree`, `spectro.clock-gauge`): a uniform load scales every line alike,
  so a receiver's clock (Doppler, redshift, lapse) and a load are one gauge.
- **The leak with its drive charged through it** (`tree`, `contact.carry-coupling-through-the-leak`,
  formal-checked in `HNN/CarryGate`): along the strand a carry circle keeps `1/(1 + d)` of its
  charge and admits `d/(1 + d)` of the level, `|γ| + κ/N₀ = 1`, so the friction sets how far back
  a circle hears and never how loud it is. It was built on November 12 after the sum form
  `z ↦ γz + b` was read holding `(1 + d)/d` places' drive with its turn's covector growing as the
  run squared (G97), and after a leak read below zero was found to be a store with no loss whose
  charge grew with the run (G96, `tower.field-carry-leak-runs`).
- **Rates of a relaxation** (`tree`, `contact.pass-reach-gap`, `contact.alignment-spectral-gap`):
  a pass contracts at its gap, and a carried rate at the gap's square root.
- **Not held** under any name searched: the tick's state as an instance of the running mean; the
  unit-power face of a shear as a move with no rate; a clock set by a site's own amplitude; the
  charts of conformal time and of aging.

The existing owner is `Field::tick`, whose three writes to a site are sums (`x ← x + O y + b_o`,
the pair's `x ← x + W_c(a · b) + b_c`, the triads' likewise). The concrete missing term, against
the law the tree already holds for the carry along the strand, is a leak on the site's state along
the tick. §6 says why that is stated and not ordered.

## 3. The tick adds, and a sum read at unit power is a mean

### 3.1 The source

`tree`, read at source. `Field::pass` opens `x⁰` and calls `Field::tick` on the same `x` `K` times
(`d.ticks`); the tick's writes to `x` are additions (`*xv = fit64(*xv + *ov)` and the pair's and
triads' likewise), and nothing between ticks rescales `x`. Every forward reader takes
`r̂ = x/‖x‖_rms` by lane on `2^(−16)` (`lane_chart`, `ratio_to_power`): keys, probes and values,
the pair chart, the triads and the face. What a tick adds is built from affine maps of such rays,
weighted means of them and their products (the pair and the triads), so it is bounded: write
`g^k` for the whole of what tick `k` adds at a site, `‖g^k‖ ≤ G`.

### 3.2 The mean

```text
x^k = x⁰ + Σ_(m<k) g^m,        r̂(x^k) = r̂( (x⁰ + Σ_(m<k) g^m)/(k + 1) )
```

A sum read at unit power is a mean: the ray after `k` ticks is the ray of the mean of the opening
and the `k` currents, each at the same weight (`agent-inferred`; it is `receiver.referent-mass`
with the opening the mass 1 and each tick a return of share `1/(k + 1)`). The first-order turn of
a ray under a push is `δr̂ = P⊥ g/‖x‖` (`tree`, the row of §2), so a tick moves a ray by at most
`G/‖x^k‖`, and the amplitude is the tick count's to grow.

### 3.3 A current that keeps its direction: the reciprocal slope counts the ticks

Let `g^m = g` and split the opening as `x⁰ = a g + x_⊥`, `x_⊥ ⊥ g`, so `a` is the opening's weight
in ticks of the current. The state's slope off the current's ray is

```text
w_k = ‖x_⊥‖/((k + a)‖g‖),      1/w_(k+1) − 1/w_k = ‖g‖/‖x_⊥‖,      w_(k−1) − w_k = (‖x_⊥‖/‖g‖)/((k + a)(k + a − 1))
```

The reciprocal of the slope advances by one unit a tick. On the rays this is the shear of §2 read
projectively: a move whose two pivots coincide at the current's ray, with multiplier one
(`tree`, `motion.mobius-multiplier-cross-ratio`: `K + 1/K + 2 = tr²/det` at `tr² = 4 det`), so it
has no rate. The change of the ray at tick `k` falls as `1/((k + a)(k + a − 1))`, the ratio of
successive changes is `(k + a − 2)/(k + a)`, which is `(k − 1)/(k + 1)` at `a = 1`, and the
opening's share of the mean is `a/(k + a)`.

### 3.4 A current that reads the site: the linear flow on the site's own clock

Let the current read the site's own ray, `g = M r̂(x)`, `M` fixed (the loop through a site's
partners at held shares, to first order). Then, to first order in `‖M‖/‖x‖`,

```text
dx/dk = M x/‖x‖        ⇒        dx/dτ = M x,      dτ = dk/‖x‖
```

The tick is the linear flow of `M` run on the clock `τ(k) = Σ_(m<k) 1/‖x^m‖`
(`agent-inferred`): a site's amplitude is the lapse of its own clock against the tick, which is
`spectro.clock-gauge` with a load that grows. With eigen-rates `σ_j + iω_j` and `σ₁ > 0` the
largest real part, `‖x‖ = σ₁(k + a)` and

```text
τ = ln(k + a)/σ₁ + const,
mode j against the dominant:  (k + a)^(−ε_j) · e^(i (ω_j − ω₁) ln(k + a)/σ₁),      ε_j = (σ₁ − σ_j)/σ₁
```

So on the tick count a gap shows as an **exponent**, the gap over the dominant rate, and a turn as
a phase that advances with the **logarithm** of the tick count, at the ratio of the turn part to
the growth (the house's `v⁻¹v̇` is boost rate plus `i` times turn rate; here their ratio is all a
ray keeps). The ray's change falls with the local power `1 + ε_j`; §3.3 is the case `ε = 1`, the
directions off the current not growing at all. A uniform multiplier of the current is a shift of
the clock's origin and changes no exponent.

### 3.5 The leak is the clock

Give the site the form the carry already has, `x^(k+1) = γ x^k + κ g^k`, `γ = 1 − δ`. The amplitude
rests at `ρ* = κσ₁/δ`, and at rest

```text
dτ = (κ/ρ*) dk = (δ/σ₁) dk:      mode j decays as e^(−δ ε_j k) and turns δ(ω_j − ω₁)/σ₁ a tick
```

The exponents and turns of §3.4 are the same numbers; the leak carries them from the logarithm of
the tick count to the tick count, `ln(k + a) ↦ δk` (`agent-inferred`). A site's clock runs at its
leak over its growth, and at `δ = 0`, the built tick, it has no rate on the ticks. With the
carry's coupling `κ = N₀δ` the resting amplitude is `N₀σ₁` at every leak, the weight of the tick
`m` back is `κγ^m`, and the mean age is `1/δ` ticks, against the built tick's equal weights over
every tick so far. This is the house's rule read as a statement about time: a store that holds
without upkeep has no clock of its own, and the only time left to it is the count of what has
been poured in.

## 4. G149 re-read

Region: 10,432 held places, each opened alone among its stretch's written places (code 2,069, web
2,041, science 2,069, books 2,069, wikidata 2,184), sixteen ticks on states trained at four, the
line's and the level's second-lap means (`MEAN.3000`), the card; the receipt prints, for the whole
set and not by slice, the mean length of each tick's change of the opened place's chart and the
mean cosine of two successive changes. G149 was read on November 13 as a relaxation with no gap
seen, the ratio of successive changes rising from 0.633 to 0.906 (`tree`,
`tower.field-tick-return`).

The ruler (`mean_ruler.py`, `mean_ruler.txt` beside this record; arithmetic on the receipt's two
series) prints, from tick 5 on:

| tick | ratio, line | ratio, level | `(k − 1)/(k + 1)` | power on `ln k`, line | level | bend an e-fold |
|---|---|---|---|---|---|---|
| 5 | 0.633 | 0.637 | 0.667 | 2.05 | 2.02 | 2.5 |
| 6 | 0.680 | 0.681 | 0.714 | 2.12 | 2.11 | 2.0 |
| 8 | 0.764 | 0.763 | 0.778 | 2.02 | 2.03 | 1.6 |
| 10 | 0.824 | 0.821 | 0.818 | 1.84 | 1.87 | 1.5, 1.4 |
| 12 | 0.862 | 0.859 | 0.846 | 1.71 | 1.75 | 1.3 |
| 14 | 0.888 | 0.885 | 0.867 | 1.61 | 1.65 | 1.3 |
| 16 | 0.906 | 0.903 | 0.882 | 1.53 | 1.58 | 1.2 |

- **The ratio is the running mean's.** With the opening counted as one tick and no number fitted,
  `(k − 1)/(k + 1)` stands within 0.035 of the read ratio at every tick from 5 to 16 on both
  states (the largest gap at tick 6). The weight that makes `c_k (k + a)(k + a − 1)` most level is
  `a = 1.15` on the line and `1.00` on the level, where its largest over its least is 1.14 and
  1.12: an opening of mass one, the row of §2.
- **The rate belongs to the logarithm.** Read as a rate on the ticks the decay falls 4.6 and 4.4
  times between tick 5 and tick 16; read as a power of the tick count it moves 1.34 and 1.28
  times. No gap was seen because the gap was sought on the ticks.
- **The current is not fixed.** The power falls from 2.1 to 1.53 on the line and 1.58 on the
  level: the decay is faster than a fixed current's through tick 9 and slower after it, which on
  §3.4 is a mixture of exponents, the smaller taking over, the local exponent standing near a half
  at tick 16 and still falling (directions off the ray that grow at about half the dominant
  rate).
- **The bend.** The angle of the mean cosine, times the tick, is the turn of the change's
  direction an e-fold of ticks. It falls from 2.5 radians at tick 5 and stands near 1.3 from tick
  12 on (the cosine is printed to three places, which is 0.1 radian at tick 16). A mixture of real
  exponents on unlike directions bends by the standard deviation of its exponents an e-fold
  (`1 − cos = h² Var(p)/2` over a step `h` of `ln k`), which is under one radian for exponents
  between zero and two. So 1.3 is a turn on the logarithmic clock, or steps in the current where
  a head's discrete support changes, or the places' unlikeness under a mean of cosines (the angle
  of a mean cosine stands over the mean angle). The mean cannot say which; a place-by-place read
  can (§7, reading 2).
- **What sixteen ticks bought.** At `a = 1` the clock at tick 16 stands at `ln 17/ln 5 = 1.76`
  times its value at tick 4. Sixteen ticks looked less than twice as far as the trained four, and
  four times as far is tick `5⁴ − 1 = 624`.

**What the logs print on the premise** (the amplitude's growth, which no log on `main` prints by
tick). G158's receipt prints the reaction's size `m²` by tick (ticks 0 to 2 of four, readers
pooled, level 3 lap mean, on that reading's own grain). With one place open it falls from tick 0
to tick 2 in every head on both texts, by 1.9 to 5.5 times (head 0 on training documents 0.589 to
0.309, head 2 0.172 to 0.031). Under the cut's mask it falls 1.25 to 4.3 times in heads 0, 2 and 3
and stands level in head 1 (8.84, 9.16, 8.66 on training documents). A pair's number on a filling site falls so, but
that grain mixes the amplitudes with the shares' sharpening and with the reader's raw state, so
it is a hint and no reading of the amplitude.

Not claimed: that the amplitude grows as `k + 1` (inferred from the ratios, unread); that any
place turns; anything about the code by stage, which is least at the trained four (1.18 nats a
place on the line, 1.16 on the level) and 2.850 and 2.815 at sixteen, where the mean's opening
share has gone from a fifth to a seventeenth.

## 5. What this says of a loop

All of §5 is `agent-inferred`.

### 5.1 A loop's swings stretch

A reaction that reads rays pushes by a bounded amount, so on a pair whose two sites have filled to
`σ(k + a)` the pair's number is `s q_k = s q₁ ((1 + a)/(k + a))²` (the mirror's
`q ≤ γ_h² p_ij²/(‖x_i‖‖x_j‖)`, `tower.field-reaction-mirror`), and its angle a tick is
`θ_k = θ₁(1 + a)/(k + a)` once small. Through tick `K` the pair has turned

```text
Θ(K) = θ₁ (1 + a) Σ_(k=1..K) 1/(k + a) ≈ θ₁ (1 + a) ln(K + a) + const:      a = 1, K = 16:  Θ = 4.88 θ₁
```

So a half swing inside sixteen ticks asks `θ₁ ≥ 0.64` at the first tick, `s q₁` of about 0.4, at
the tick where both sites are their raw openings; and each later half swing takes about
`e^(π/(θ₁(1 + a)))` times every tick before it (11.5 times at that strength, the second ending
near tick 200 and the third near 2,300). A loop weaker than that at its first tick shows
successive cosines that are positive and rise toward one, which is the line this record took from
the relayed summary. A mode makes the same number of swings before it dies on either clock,
`(ω_j − ω₁)/(2π(σ₁ − σ_j))` an e-fold of its decay; what the filling changes is that each swing
costs a multiple of all the ticks before it, where a site at rest pays the same ticks for each.

### 5.2 Nothing is damped

No term of the built tick loses anything: a site keeps every push it ever took. The turn winds
down because the site grows heavier by a share a tick, as a spinning body that takes on mass turns
slower with nothing rubbing on it. The difference decides the answer. Friction is answered by a
drive. A filling site is not: a drive adds to the mass too.

### 5.3 The carried rate reads here as the opening's weight

The tick's return built on the host (`tower.field-tick-return`) gives, at a steady current,
`u = ρ g`: every current multiplied by `ρ = 2^ℓ`. On §3.4 a uniform multiplier is a shift of the
clock's origin, `a ↦ a/ρ`. So on a site that only fills, `ℓ` reads as the opening's weight
against the currents, and not as a rate; it regains its roots (`1 → γ` and `Γ`) once the site has
a leak.

### 5.4 A drive on a filling site is heard at one over its age

A place that arrives when a site has aged `k` ticks moves that site's ray by at most
`pG/(σ(k + a))` a tick, `p` its share of the site's current: the first-tick effect of an arrival
falls as the site's age, and moving the mean by a fixed part takes a number of ticks in proportion
to that age. With a leak the same arrival is heard at `pGδ/(N₀σ)` whatever the age, inside a
window of `1/δ` ticks. The drive and the leak are one design in the tree already: the carry's
drive is charged through the friction it leaks by.

### 5.5 A rest state is an answer that one tick checks

With a leak the rest state obeys `x* = N₀ g(x*)`: a fixed point of the site's own map, which one
tick checks at a declared grain, and from which the remaining travel is a fixed multiple
`1/(δ ε)` of the last change. A filling site has no rest state (`‖x‖` grows by `σ₁` a tick), and
the travel left after tick `k` is `(k + a)/ε` times the last change, which no fixed tolerance
bounds without knowing `ε`. Brandon set self-induction beside searches whose answers are cheap to
check and named inverse kinematics; a loop's rest state under a drive is that shape, checked in a
tick and found by a relaxation whose time `1/(δε)` runs away where the gap closes.

### 5.6 The same computation under other names

`from training`, each restated on the objects, with what transfers.

- **Conformal time.** In a medium whose lengths scale by `a(t)`, a wave keeps its shape on the
  clock `dη = dt/a(t)` and its pitch read on `t` falls as `1/a`; at `a ∝ t`, `η = ln t`. Here the
  scale is the site's amplitude and `t` the tick: a filling site redshifts its own loop. This is
  the machine's instance of the question of the lens of 20:11Z, how expansion relates to loudness:
  a site's loudness is the scale of its clock. Only the re-clocking transfers.
- **Aging.** A system with no stationary state answers a push applied at age `t_w` over a time in
  proportion to `t_w`, its two-time readings being functions of the ratio of the times. §5.4 is
  that statement of a site.
- **An estimator's gain.** The mean is the least-squares estimate of a constant, at the gain
  `1/(k + 1)` (the row of §2); a constant gain follows a state that moves, inside a window
  (Kalman 1960). A passage that keeps arriving is the moving case.
- **A circuit.** One store charged by a current with no leak and no second store is an
  integrator: its pole sits at zero frequency, a constant drive makes a ramp, and a ring needs
  the second store and a pole off the axis (`em.dissipating-contact-two-clocks`; the two-stores
  record of this day: a clock is two stores' product).

## 6. Standing

Self-induction is Brandon's assertion, and no reading named here is a test of it: each reads a
build, and this record's point is that the build's site is a store on which no loop can hold a
pitch, which the source and a public receipt show before any reaction is added.

His instruction of 20:25Z governs the division of work: the engineering thread derives and decides
on its own. This record is what theory concluded for him; it is no order, it asks no build and no
run, and whether a site is given a leak, in what form, founded how (the built tick is the end
`δ = 0`, so a leak whose chart opens there keeps the line bit for bit), with what parity and what
guesses, is the engineering thread's. A build is one attempt.

Scope: the reading bears on a loop meant to hold itself and on ticks that run while a passage
arrives. It says nothing against a pass of four ticks as a way to settle a place: a mean of what
a place hears is a lawful settling, and the line's level stands as read.

## 7. Readings that would settle it, and what does not transfer

None is ordered; each guess is offered, to be fixed or replaced by whoever reads.

1. **The amplitude by stage.** The lane amplitude (`scale` of `lane_chart`, which the forward
   already forms) of an opened place by stage, by slice. Offered guess: at the median place the
   amplitude at stage 16 is 3 to 4.5 times its amplitude at stage 4 in every slice (3.4 for a
   fixed current with the opening as one share, 2 for currents of unlike directions, 1 for a state
   at rest). A miss under 2.5 removes this record's mechanism, and the ratios of §4 would need
   another.
2. **The bend, place by place.** From the charts read-depth already writes, on the host: each
   place's power on the logarithmic clock and the cosine between its change at tick `k` and at
   tick `2k` (`k` = 4, 8), by slice. Offered guess: the median place's bend an e-fold over ticks
   12 to 16 is under 0.75 radian, the mean's 1.3 being the places' unlikeness. A miss says places
   turn on the logarithmic clock in the built tick, with no reaction added.
3. **The free ring with a reaction** (already run by the engineering thread; this thread has seen
   a relayed summary and no receipt, so this guess is not blind in its sign). Its bend an e-fold
   by stage, as `mean_ruler.py` prints it. Offered guess: at a turning strength the bend over
   stages 8 to 16 stays within 1.5 times of level, as it does on the built tick (1.6 to 1.2).

Not transferred: the cosmology, the glass and the filter of §5.6 (charts; no part is designed from
them); the spinning body of §5.2 beyond the re-clocking; any value for a leak. The amplitude's
growth is inferred and reading 1 is its read.

Recorded failures this record could repeat, and how it avoids them: a design called new before the
tree was searched (§2: the mean is `receiver.referent-mass`, the leak is the carry's, and the
missing term is named against them); a figure repeated from a summary (the engineering thread's
four readings are named without a figure; every number here is from `g149_depth.txt`,
`g158_reaction.txt` or the ruler); a guess on a premise the logs had settled (§4 reads what the
logs print on the amplitude before reading 1's guess); a law ruled on one mean (the bend is left
open because a mean of cosines cannot decide it); a reading called a test of an assertion (§6).

## 8. Atlas rows, and what is owed

Rows added: `motion.unit-power-push-log-clock` (geometry), `tower.field-tick-running-mean`
(objects), and with §9 `motion.relaxed-step-three-kinds` (geometry). The scope of
`tower.field-reaction-mirror` gains the readings that read it (G160 to G162) and of
`tower.field-tick-running-mean` the ruler's figures on G162.

Owed: no Lean statement is owed by this record, which adds no law of the machine (#410 gains no
box). The running mean and its share are `HNN/ReferentMass`'s and the shear's finite series
`Geometry/Motion`'s; the re-clocking of §3.4 is a change of variable. A leak along the tick, if
built, would owe its statements with its builder, as the carry's did (`HNN/CarryGate`).

## 9. Read after: the reaction's and the release's readings at their receipts

Written near 21:50Z. The engineering thread's receipts for G159 to G164 reached `main` at 21:14Z
(`78cdfa6d0`), nine minutes before this record's first commit (`d1294143e`, 21:23Z). This thread
had not fetched them and read them only after that commit, so §7's guesses were written without
them, and guess 3 keeps its mark as not blind in its sign. Every figure below is from
`g161_strength.txt`, `g162_ring.txt`, `g163_release.txt` or `g164_release.txt` under the junction
record's `_receipts/`, or from this record's ruler on the second of them
([mean_ruler_g162.txt](2026-11-13_THE_BUILT_TICK_IS_A_RUNNING_MEAN_ON_A_SITE_THAT_ONLY_FILLS_ITS_CLOCK_ON_THE_RAYS_IS_THE_LOGARITHM_OF_THE_TICK_COUNT_A_LOOPS_SWINGS_STRETCH_AS_THE_SITE_FILLS_AND_A_LEAK_IS_THE_SITES_CLOCK_receipts/mean_ruler_g162.txt)).
All are readings from level 3's lap mean (`MEAN.3000`), on the host, of seen text. Their programs
were read at source (`Field::pass`'s mirror stage, `Field::free_ring`, `read_release`).

### 9.1 With the reaction on, the free ring is still a running mean, and its bend rises with the strength

G162 opens 280 places alone (48 a slice in four slices, 88 in wikidata), runs 16 ticks, and after
every tick but the last adds every head's mirror at one strength `s` to the state. Its changes
are the opened places' charts' (the root of the mean squared change a place) and its cosines are
pooled over places, where G149's were means a place. The ruler, over ticks 5 to 16:

| strength `s` | rate on ticks, first over last | power on the log, first over last | power, ticks 12 to 16 | bend an e-fold, ticks 12 to 16 | bend at tick 8, at tick 16 |
|---|---|---|---|---|---|
| −0.1 (the like sign) | 3.95 | 1.14 | 1.89 | 1.20 | 1.29, 1.24 |
| 0 (the built tick) | 5.29 | 1.53 | 1.46 | 1.63 | 1.83, 1.60 |
| +0.1 (the turn's sign) | 5.47 | 1.58 | 1.25 | 2.00 | 2.49, 1.89 |
| +0.5 (the turn's sign) | 3.43 | 0.99 | 1.46 | 3.15 | 4.38, 2.95 |

Read (`agent-inferred`):

- **No strength gives the decay a rate on the ticks.** Read as a rate it falls 3.4 to 5.5 times
  over the twelve ticks; read as a power of the tick count it moves 0.99 to 1.58 times. The
  mirror's step is a ray's size added to a state that only fills, so §3 holds with it on. What
  the junction record's §13.8 calls the tick's relaxation damping the turn is, at source, the
  site ageing under the turn (§5.1, §5.2): the turn's angle a tick falls as one over the tick
  count and nothing takes it out.
- **Guess 3 held, narrowly.** At `s = +0.5` the bend an e-fold runs 4.38 at tick 8 to 2.95 at
  tick 16, a factor 1.48 against the guess's 1.5, and stands between 2.95 and 3.39 from tick 11; at
  `s = +0.1` 2.49 to 1.89, a factor 1.31; the built tick's own, on these places, 1.83 to 1.60.
- **Unguessed: the bend rises with the strength through zero**, 1.20, 1.63, 2.00 and 3.15 radians
  an e-fold over ticks 12 to 16, and at the small strengths the power on the logarithm moves the
  other way (1.89, 1.46, 1.25). That is what a pair of real rates does as a skew part is added to
  it: the gap closes and the phase opens (`motion.unit-power-push-log-clock`: a gap is an exponent
  and a turn a phase on `ln k`). Under the like sign the opened place is the nearest of the four
  to a current that keeps its direction (largest over least 1.06 at `a = 0.25`, the power 2.04 at
  tick 5 and 1.79 at tick 16). The two small strengths are one fact, the sign of a slope at zero,
  and `+0.5` continues it.
- **A cosine of successive changes cannot read a slow swing.** It falls below zero only where one
  tick turns the change by more than a quarter turn. At `s = +0.5` the largest angle a tick is
  1.46 radians at stage 3 (cosine 0.115), and it is 0.55 at stage 8 and 0.18 at stage 16. Cosines
  positive at every stage are what a site that fills gives for any loop whose swing is longer
  than four ticks. So G162 reads that this loop does not reverse within a tick or two. Whether it
  swings on its own clock G162 leaves open, and its own figures say it bends more the harder it
  is turned.
- G159 to G161 are the engineering thread's and stand as it read them. One check by region
  (`g161_strength.txt`): the gains a slice shows at a uniform strength do not carry from seen to
  held text (wikidata, head 0, the cut's masks, `s = −0.1`: 0.015 nats a place lower on seen text
  and 0.021 higher on held), so that a uniform strength buys nothing is not the pooling's doing.

### 9.2 The read that would tell a turn from a wander

Reading 2 of §7 names it: the cosine of the change at one tick against the change at a later
one. The ruler prints the two ends between which it must fall for tick 16 against tick 8, from
the successive cosines alone: every tick's turn in one plane and one sense (the cosine of the
summed angles), or every tick's turn unlike the ones before it (the product of the cosines).

| strength `s` | summed angle, ticks 9 to 16 | one plane | unlike planes |
|---|---|---|---|
| −0.1 | 0.79 | 0.71 | 0.96 |
| 0 | 1.10 | 0.45 | 0.92 |
| +0.1 | 1.40 | 0.18 | 0.88 |
| +0.5 | 2.23 | −0.61 | 0.71 |

Offered guesses, fixed here before any such read and ordered by no one: pooled over the same
280 places, the change at tick 16 against the change at tick 8 pairs **below 0.3 at `s = +0.5`**
and **below 0.75 on the built tick**. A value over 0.5 at `s = +0.5` says the added bend is a
wander of unlike directions and the reaction, at this strength, turns nothing a lag can see. A
value below zero is a reversal, which a turn gives and which real rates give only once, by an
overshoot of modes far from orthogonal; sixteen ticks are too few e-folds to tell those two apart,
and a run to tick 64 (2.4 e-folds past tick 5 where sixteen give 1.0) would.

### 9.3 The release returned at a lag replaces where the tick fills

G163 and G164 read a region eight times, each pass after the first opening every open place on
its face from the pass before. A pass begins from its opening again, so across passes the loop
is closed by **replacement**: it has a rate, one a pass, where the ticks inside a pass have none.

- **A place alone** (122 places, one open a stretch and silent as a source, so the loop is its own
  opening and no contact's): from pass 3 the faces' change is level, 25,152 to 26,584 on `2^(−16)`
  shares a place, and the successive cosine falls from −0.767 at pass 3 to −0.994 at pass 8,
  −0.989 to −0.999 in every slice (in science the change first falls, 28,911 to 12,981). A change
  of level size reversed each pass is the half-turn about an anchor at a restitution of one
  (`junction.restitution-family` at `Γ = 1`, `2P − I`): at passes 7 and 8 the change grows 1.6%
  and 1.9% a pass. Its period is two passes whatever the loop is. It is the update's period, the
  two-cycle `tower.field-echo` names for a symmetric loop replaced synchronously, and it carries
  no pitch of the loop's own.
- **The mean** (G164; `o_(p+1) = (o_p + F(o_p))/2` at source, each class's share rounded up) is a
  leak of one half on the pass clock: a multiplier `λ` of the pass becomes `(1 + λ)/2`, and a
  half-turn goes to zero. Pooled, the change falls 32,706, 17,564, 5,782, 2,933, 1,534 and then
  stands near 1,550 to 1,750. By slice that is three behaviours: code settles (446 at pass 8 and
  falling); web and books keep a small two-cycle (cosines −0.92 and −0.95 at pass 8, at 1,893
  and 1,561 against 28,256 and 31,353 without the mean); science and wikidata drift one way
  (+0.62 and +0.82). The pooled state it settles toward codes 1.80 nats a place at pass 8 against
  1.19 at the first read.
- **Mutual** (5,523 places on the cut's masks, each also a source at its face): under the mean the
  change stops falling after pass 4 (6,403, then 8,154, 9,260, 9,073, 7,773), the cosines stand at
  0.64 to 0.77 from pass 5, the code rises from 3.01 to 5.34 and the face's expected code falls
  from 3.04 to 2.02. A drift one way that does not slow is what a multiplier over one gives: a
  boost. Without the mean the cosines are mixed (−0.46 to +0.09), the flip and the boost
  together, and the code reaches 6.41. Neither read sets a site's echo (`read_release` builds its
  regions with none), so the cavity term the tree holds (a region's `Echo`, taken out in `Field::pass`; §15.3 of
  the record of November 1) is not in them.

One family carries these and the tick (`agent-inferred`; the relaxed iteration of numerical
analysis, the linear mixing of a self-consistent loop and the damping of a message-passing
iteration are its names from training). For `x ← (1 − δ)x + δF(x)` with `F`'s multiplier `λ`
about its fixed point, the step's multiplier is `1 − δ(1 − λ)`:

- a flip (`λ < −1`) settles where `δ < 2/(1 − λ)`. A leak cures it, so a flip is a matter of the
  clock;
- a boost (`λ > 1`) settles at no leak: `1 − δ(1 − λ) > 1` for every `δ > 0`. Its cure is not
  read here. The round trip's share is small where G151 read it (the median written row's
  `B = 0.00068`), which leans against the cavity term alone, and the tree's other candidate is a
  deposit that passes through the loop, the engineering thread's stated next design;
- a turn (`λ = e^(iφ)`) keeps a pitch, `arg(1 − δ + δe^(iφ))`, and loses
  `2δ(1 − δ)(1 − cos φ)` of its power a step: a finite quality (`store.finite-quality`). It is
  the one kind of the three whose period is the loop's and not the update's.

The built tick is the end `δ → 0` with the push kept (§3.5): no rate, the logarithmic clock. G164
is `δ = 1/2`, G163 `δ = 1`. So the day's readings sort onto the Swing's kinds, each by how its
loop is closed:

| reading | the loop is closed by | what it shows |
|---|---|---|
| G149, G162 at `s = 0` | nothing: a one-way read | free fall: a power of the tick count |
| G162 at `s = −0.1` | the reader's reaction, like sign | a boost: the gap widens, the bend falls |
| G162 at `s = +0.1`, `+0.5` | the reader's reaction, the turn's sign | the bend rises; a turn if §9.2's read holds |
| G163 alone | a place's own release a pass later, replaced | a half-turn at a restitution of one |
| G163 and G164 mutual | the places' releases to one another | a boost toward certainty |

### 9.4 What theory concludes

1. **Inside a pass nothing can ring or settle in ticks, with a reaction or without**, because the
   site has no rate. G162 shows it at four strengths. That is a property of this realization's
   site and of no loop.
2. **Between passes the release replaces**, and the two real kinds appear: a half-turn where a
   place hears only itself, which is the update's own period and which a mean removes, and a
   boost where places hear one another, which no mean removes.
3. **A pitch of a loop's own is the third kind, a turn**, and of the day's readings only the
   reaction at the turn's sign leans toward one, on a clock that stretches. Where it can keep a
   pitch is a site that leaks as it fills: there a turn has its period in ticks and a finite
   quality, a flip is cured, and a boost still asks its own cure. Against the three things the
   junction record's §8 asks of such a build (a store of the rate, the echo known as the site's
   own, a pump), this record changes the first: on a site that fills, the carried rate reads as the
   opening's weight (§5.3), and the leak is what gives the loop a clock.
4. **On the assertion.** No reading here is a test of self-induction (§6). What they do show is
   the smallest state of this build that reproduces itself: a place opened each pass on the mean
   of its last opening and the face that opening gave reaches, in the code slice (25 places), a
   face that gives itself back within eight passes (the change 446 of 33,790 and falling). One
   pass checks such a state, where reaching it took the loop. It reads worse than the first read
   (1.52 nats a place against 0.72 in that slice), and no deposit has passed through that loop.

Nothing here is an order, and §6 stands: the forms, the foundings and the next read are the
engineering thread's.
