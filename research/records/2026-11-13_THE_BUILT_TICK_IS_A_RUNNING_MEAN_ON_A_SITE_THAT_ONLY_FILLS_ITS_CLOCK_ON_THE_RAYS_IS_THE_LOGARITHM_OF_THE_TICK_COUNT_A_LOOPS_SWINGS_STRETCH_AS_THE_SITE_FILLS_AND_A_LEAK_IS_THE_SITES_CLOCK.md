# The built tick is a running mean on a site that only fills, so its clock on the rays is the logarithm of the tick count; a loop's swings stretch as the site fills; and a leak is the site's clock

Refs #404 #406. Status: [theory's reading of the built tick's own time, with one ruler on a
public receipt; November 13, 21:20Z], by the theory thread, which holds no runs. Nothing here is
built and nothing here is an order. Every statement carries one of three grades: `tree` (an atlas
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
`contact.carry-coupling-through-the-leak`, `contact.pass-reach-gap`. Two atlas rows enter (§8). No
row is amended and no owner moves.

## 1. Why this record exists

Brandon asked on November 13 (18:21Z) that the readings of self-induction reach theory to think
about, whether they hold or miss, and said in the same message that self-induction is something he
asserts and that no reading is a test of it. The engineering thread has since read a reader's
reaction on its source four ways (its G159 to G162: the pair's decomposition, the reaction in the
form of the read's mirror at first order, at finite strength, and in the free ring at sixteen
ticks). Their receipts were not on `main` at this writing, so **no figure of theirs is repeated
here**; what reached this thread is a relayed summary, of which this record uses one qualitative
line (relayed at 20:58Z, to be read at its receipt when it lands): with the reaction on at a
turning sign, the free ring showed no reversal within sixteen ticks, and the engineering thread
read that as the tick's relaxation damping the turn and named a drive (the passage still arriving
while the ticks run) as its next design.

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
(objects).

Owed: no Lean statement is owed by this record, which adds no law of the machine (#410 gains no
box). The running mean and its share are `HNN/ReferentMass`'s and the shear's finite series
`Geometry/Motion`'s; the re-clocking of §3.4 is a change of variable. A leak along the tick, if
built, would owe its statements with its builder, as the carry's did (`HNN/CarryGate`).
