# The rings as a search for keys, pinned before the run: neither the search nor the prior holds

**Date:** 2026-09-28. Refs #28, #73, #63. THE_REBUILD §4, "The ring-search experiment", wave C.

**Occasion.** The learner record's §2 ("The rings as the search") and §14.1 ("The decisive ring
experiment") restored the rings to a second role: not features inside a predictor, which campaign 2
measured and found adding no bits
([campaign 2](2026-09-26_CAMPAIGN_TWO_THE_RINGS_AND_CONTACTS_ARE_LAWFUL_AND_ADD_NO_BITS_ON_TEXT.md)),
but proposal dynamics for the search for keys. This record fixes the claim, the bank, the work
unit, the controls, the seeds and the criteria before the measured run. The harness is
`research/notebook/hnn_design/hnn_ring_search.rs`; its header states every declaration below. The
harness and its driver `hnn::ring::PumpedRing` were retired after the run, as nothing else consumed
them; both are at commit `10a837fd`, where the commands below reproduce the run.

## 1. The claim

`[definition; agent-inferred]` Two hypotheses, measured and reported separately:
- **(1) Search.** A bank of coupled rings locks onto a future-equivalent key in less work than
  enumerating keys and than menu propagation, all work charged, on the blind moiré, the parity
  moiré and the rotor crib.
- **(2) Prior.** The fraction of the bank's initial configurations landing on each lock, over a
  certified finite partition, tracks the mass law `2^(−ℓ)`, `ℓ` the key's description length.

What survives Astra's counterexamples (§14.1: tongue width, basin measure and a description prior
are three quantities; `K^q` tongue scaling is not universal; a raw Stern–Brocot path is not a
prefix code without its length) is narrower: a lock proposes a key, exact receiver constraints
certify it, and the certification is charged to the arm that proposed.

## 2. The bank

`[definition; agent-inferred]` The bank is the HNN's own ring law, run by a new driver at the ring's
owner, `hnn::ring::PumpedRing` (atlas `parametron.pumped-passage`): a ring's resonator through a
schedule of pump stages that moves only the pump's strength, each tick the resonator's own
`ResonatorOperands::step`, the sheets read after each tick. The passage closes when every tick's
executed balance closes and the storage telescopes with the pump's work at each switch,
`½⟨u, (K_new − K_old) u⟩` (Lean `HNN/Ring.ring_material_commit_work`, which admits the pump block).
The bank runs in the word lattice's executed chart `(L_c, D_c, L_w) = (32, 16, 16)`, with `h = 1`,
`Y = 1`, `C = I`, `D = 0` (the port carries the loss), the pump standing on the real axis.

- **The moiré bank.** One ring per rate `p/q` of the moiré family (`2 ≤ q ≤ 8`: 21 rings), whose
  nodes are its rotor's `q` ports. Its contacts are its own geometry: each port joined to its two
  neighbours at `−1` (for `q ≥ 4`) and to its half-turn partner at `+2` (two nearest partners at `+1`
  each for odd `q`). The ring's first Fourier pair, whose sign pattern is a grating's half-turn sheet,
  is then its softest mode; `K = c₀I + A` with `c₀` the least point of `2^(−10)ℤ` making `K ⪰ 0`.
  The certified spectra (the inertia owner, in-phase block, `(+, 0, −)`):

  | `q` | `c₀` | unpumped | pumped at `σ = 1/4` |
  |---|---|---|---|
  | 2 | 2 | (1, 1, 0) | (1, 0, 1) |
  | 3 | 1 | (1, 2, 0) | (1, 0, 2) |
  | 4 | 2 | (2, 2, 0) | (2, 0, 2) |
  | 5 | `1145/512` | (5, 0, 0) | (3, 0, 2) |
  | 6 | 3 | (4, 2, 0) | (4, 0, 2) |
  | 7 | `3123/1024` | (7, 0, 0) | (5, 0, 2) |
  | 8 | `3497/1024` | (8, 0, 0) | (6, 0, 2) |

  The pump crosses the bifurcation of the first Fourier pair alone. The drive is the terrain's
  phase-carried moment: at tick `t` ring `p/q`'s rotor stands at port `t·p mod q`, and the cell's
  encoding enters that node's in-phase storage port: the blind sheet tuple as `Σ_i (1 − 2s_i)`
  (the layers superposed; no ring is told which layer is which), the parity color as
  `1 − 2·cell`. The schedule is `σ = 0` for `T_A = 2^8` ticks, then `σ = 1/4` for `T_B = 2^5`.
  A ring proposes the gratings whose half-turn sheets lie nearest its sheets, each followed by its
  two adjacent phase classes (the lock's reading at the port grain with its unresolved fibre).
  Rings of different rates exchange no power, as the terrain's gratings do not.
- **The crib bank** is the Bombe's diagonal board as parametrons: one node per wire (menu port,
  image), 49 wires; each menu edge `a — b` with stage `W` joins wire `(a, i)` to `(b, W i)` at `−1`,
  so `K` is the wire graph's Laplacian. A seed hypothesis enters as a kick `−1` at its wire;
  `σ = 0` for 1 tick, then `σ = 1/4` for `2^3` ticks drives each lit component's constant mode past
  the bifurcation. The lit wires propose the board when each menu port holds exactly one and their
  images are distinct (the Bombe's stop).
- **The nonlocking control** is the same bank with the pump at zero throughout: the rotors still
  carry the cells rigidly and the resonators still integrate them, but no bifurcation selects a
  sheet.

## 3. The work unit, the certificate and the arms

`[definition; agent-inferred]` **The work unit** is one exact elementary operation (an integer or
rational addition, subtraction, multiplication, division, remainder, comparison, table lookup or
carry), common to all arms and counted as an integer. The harness header lists each arm's charges.
The bank's are the owner's: a tick `6n² + 15n` at realified width `n` on the lattices, a sheet read
`2n`, and each stage's preparation `n³ + 6n² + 2n³(1 + 3·steps)` for the chart's refinement. The
executed balance each tick also forms is the law's receipt, not the motion, and is not charged;
every passage's closure is checked and counted. The moiré rings are data-free, so their preparation
is charged once per terrain; the crib board's `K` is the menu's, so its preparation is charged per
key. Wall time is printed beside.

**Certification**, charged to the arm that proposed:
- `[proved-standard]` A moiré key's emission has a period dividing `T_c` (the lcm of its
  denominators), and the terrain's a period at most `T_max` (8 for one channel, `280 = 2^3·5·7` for
  three gratings). Agreement on the passage's first `T_max + T_c − 1` cells makes the two periodic
  words equal forever (Fine and Wilf, 1965, the two-word form).
- `[proved-derived]` A crib key `(k, S)` is future-equivalent when it reproduces the passage and the
  passage revisits a joint state (ring 0's phase, ring 1's position, the cell). Under every key the
  next cell and the next state are functions of the state (ring 0 moves on the cells alone, ring 1 by
  its lock and ring 0's carry), so a key that reproduces a closed cycle repeats it. There are
  `5·7·7 = 245` joint states, so a passage of `2^9` cells always revisits one.

**The arms**, each stopping at its first certified key:
- **enumeration**: the blind moiré channel by channel over the family's gratings in the owner's
  order; the parity moiré over joint keys in lexicographic order of the three gratings' indices;
  the crib over keys `0, …, 6` and boards in lexicographic order;
- **menu propagation** on the crib: `hnn::keys::crib_menu` and `Menu::propagate`, one key at a
  time, its survivors certified. `hnn::keys` reads a stage menu, and the moiré carries no stage or
  plugboard, so no menu is declared on the moiré terrains;
- **the bank** and **the nonlocking control**: every ring's passage, then its proposals certified in
  ring order; on the parity moiré as triples of distinct proposals; on the crib key by key, seed by
  seed.

## 4. The pins

`[definition]` Fresh seeds, disjoint from every seed used before (the terrain notebook's
`20260927`, the chase's `20261001` to `20261364`, the tests' small seeds):
- **blind moiré**: the sheet tuple, `k = 3` gratings with `q ≤ 8` (`N_8 = 122 = 2·61` gratings,
  `122³ = 2^3·61^3` joint keys), `2^10` cells, seeds `20262801 + s`, `s < 8`;
- **parity moiré**: the same family, the parity color, seeds `20262811 + s`, `s < 8`;
- **rotor crib**: campaign 1's field (population `2^16`) with ring 1 (7 ports) locked at every port,
  the other rings at configuration 0, a drawn key and plugboard (`7·7! = 35280 = 2^4·3^2·5·7^2`
  keys), `2^9` cells, menu offset 1, seeds `20262821 + s`, `s < 8`;
- **development** (the preflight only, never a measurement): `20262701`, `20262711`, `20262721`.

**(2)'s partition and mass law.** The bank is undriven: a prior precedes the passage it weighs, and
a driven basin is a posterior, (1)'s subject. Each ring's initial in-phase displacement is a sign
pattern in `{−1, +1}^q` (velocities and quadratures zero); the bank's configurations are the
product over its 21 rings, `2^122`, a certified finite partition read exactly. A ring's lock time
`τ` is the first read of `T_B` from which its sheets stay equal to its last read, when that read is
exactly a grating's sheet (`∞` otherwise). The bank lands on the ring that locks first; a tie is a
plural lock, and no lock at all is none. The rings are independent, so ring `r`'s basin is
`Σ_t P(τ_r = t) ∏_(s ≠ r) P(τ_s > t)`, exact from each ring's own `2^q` patterns. Undriven, a
ring's motion depends on `q` alone; its patterns are read by rotation orbits (its forms are
circulant), and the equivariance is checked on every pattern for `q ≤ 4`. The mass law over the
bank's rates is `π(p/q) = 2^(−ℓ)/Z`, `ℓ = n + 2⌊log₂ n⌋ + 1`, with `n` the Stern–Brocot path length
of `p/q` (the sum of its partial quotients less one) coded after its Elias gamma length, so the
code is self-delimiting: `ℓ(1/2) = 2`, `ℓ(1/3) = ℓ(2/3) = 5`, `ℓ(1/8) = ℓ(7/8) = 12`.

## 5. The criteria, the falsifier and the adoption

`[definition]` Fixed before the run:
- **(1)** holds on a terrain when the bank certifies a key on every seed and its work summed over
  the seeds, with its declaration, is strictly below each control's (enumeration, the nonlocking
  control, and menu propagation on the crib; a control that misses a seed has no finite sum).
  (1) holds when it holds on all three terrains.
- **(2)** holds when the total variation between the basins (the plural and no-lock masses
  included, against zero mass) and `π` is at most `1/4`, and no rate with a strictly shorter
  description has a strictly smaller basin.
- **The falsifier.** If neither holds, the reading "rings as proposal dynamics" is refuted for the
  HNN's ring law, and this record says so plainly.
- **Adoption.** If (1) holds, the rings are declared the key search's proposal dynamics beside menu
  propagation (`hnn::keys`). Otherwise they are recorded as not a search.

## 6. The preflight and the projection

`[established-bounded; measured]` The preflight ran every arm on the three development seeds, one a
terrain, and timed three of (2)'s passages, on 24 cores. Each moiré seed's bank or control arm ran
in under 1 s and its enumeration in under 10 ms; the crib's board bank in under 200 ms; three
`q = 8` passages of (2) in 140 ms. The peak resident set was 33,532 kB. The run is projected under
one minute and under 64 MB; it stops at 10 minutes of wall time or 20 GB resident, and a run that
passes either is reported as incomplete. The preflight's readings are development readings, not
this record's measurement.

`[disclosure]` Two declarations were fixed on the development seeds before this pin:
- the full-coverage crib certificate was unmet (a crib's cells do not visit every transition). The
  revisit certificate replaced it;
- the blind bank's exact decoding was off by one class where two layers share a denominator. Each
  ring of that denominator reads both layers, one of them permuted by the ratio of the rates, and
  the mixed first Fourier pair lands on a class boundary. The lock's unresolved fibre (the adjacent
  classes) replaced it.

No parameter of the bank's dynamics was changed.

## 7. The run

`[established-bounded; measured]` Run once on the pin of `c2f577f1`
(`cargo run --release -p holonics --example hnn_ring_search -- run`), in 6,887 ms at a peak
resident set of 174,500 kB on 24 cores, within the projection. Every passage's balance closed: 672
of 672 moiré passages, 78 of 78 crib passages and 91 of 91 of (2)'s orbit passages. Every certified
key was checked against the truth after the fact, and every one was future-equivalent to it.

### (1) Search: the work to a certified key

Summed over the 8 seeds of each terrain; a moiré bank's sum adds its declaration once (the 21 rings'
data-free solves, 3,795,456 for the bank and 3,795,456 for the control).

| Terrain | Bank | Nonlocking control | Enumeration | Menu propagation |
|---|---|---|---|---|
| Blind moiré | 7 of 8 seeds certified: none | 7 of 8: none | 8 of 8: 25,566 | not declared |
| Parity moiré | 6 of 8: none | 7 of 8: none | 8 of 8: 53,017,545 | not declared |
| Rotor crib | 8 of 8: 1,512,813,925 | 8 of 8: 1,512,813,925 | 8 of 8: 460,880 | 8 of 8: 268,218 |

- **Blind moiré.** The bank spent 6,423,444 to 6,424,242 a seed; enumeration's first certified key
  cost 2,412 to 3,756. On the seven seeds both certified, the bank with its declaration spent
  48,762,630 against enumeration's 21,810: `2235 rem 17280 over 21810` times as much. Both banks
  missed seed 20262808, whose truth holds two layers of one rate (`5/8 @ 4/8` and `5/8 @ 7/8`).
- **Parity moiré.** The bank spent 6,434,409 to 7,640,115 on the seeds it certified; enumeration
  5,253 to 23,415,123. The bank was below enumeration on three seeds (20262813: 7,550,019 against
  13,559,913; 20262814: 7,389,705 against 11,372,970; 20262816: 7,640,115 against 23,415,123) and
  above on three. It missed 20262811 and 20262817; the control missed 20262811 only. On the six seeds
  the bank certified, its work with the declaration was 46,079,115 against enumeration's 51,347,856
  on the same seeds. This is a reading on a subset that the bank's own success selects, not a
  comparison the criterion admits.
- **Rotor crib.** The bank and the control are equal on every seed: the pump changes no proposal.
  Each certified at key 0 (the rotor gauge puts a member of the truth's orbit at every key). The bank
  spent `5640 rem 64405 over 268218` times menu propagation's work and `3282 rem 205765 over 460880`
  times enumeration's. On seed 20262827, 186,471,264 of its 187,571,979 is the preparation of key 0's
  two 98-wide solves.

**(1) fails on all three terrains.**

### (2) Prior: the basins of the undriven bank

Each ring's `2^q` initial sign patterns, by the read of `T_B` at which the ring locks (the rotation
equivariance held on every pattern for `q ≤ 4`):

| `q` | locked at the first read | locked later | no lock |
|---|---|---|---|
| 2 | 2 of 4 | 0 | 2 |
| 3 | 3 of 8 | 0 | 5 |
| 4 | 4 of 16 | 0 | 12 |
| 5 | 15 of 32 | 0 | 17 |
| 6 | 42 of 64 | 0 | 22 |
| 7 | 63 of 128 | 0 | 65 |
| 8 | 112 of 256 | 32 | 112 |

Over the bank's `2^122` configurations, every rate of one `q` has one basin (undriven, a ring's
motion depends on `q` alone):

| `q` | the basin of each rate, exact | on `2^(−24)ℤ` | the mass law `π` of its rates |
|---|---|---|---|
| 2 | `3^10·5^8·11^2·13^6·17^4 / 2^99` | `[29, 30)` | `1/2`: `512/807` |
| 3 | `3^11·5^7·11^2·13^6·17^4 / 2^99` | `[17, 18)` | `64/807` each |
| 4 | `3^9·5^8·11^2·13^6·17^4 / 2^99` | `[9, 10)` | `32/807` each |
| 5 | `3^11·5^9·11^2·13^6·17^3 / 2^99` | `[26, 27)` | `1/5`, `4/5`: `4/807`; `2/5`, `3/5`: `32/807` |
| 6 | `3^11·5^8·7·11·13^6·17^4 / 2^99` | `[56, 57)` | `2/807` each |
| 7 | `3^12·5^7·7·11^2·13^5·17^4 / 2^99` | `[28, 29)` | `1/7`, `6/7`: `1/807`; the rest `4/807` |
| 8 | `3^4·5^8·11^2·13^6·17^4·331 / 2^98` | `[27, 28)` | `1/8`, `7/8`: `1/1614`; `3/8`, `5/8`: `4/807` |

(`Z = 807/2048`.) The plural lock carries `1 − 3^2·5^7·11·13^5·17^3·311·677·3793 / 2^98` of the
configurations, in `[1 − 597/2^24, 1 − 596/2^24)`; no lock at all carries
`3^2·5^8·7^4·11^2·13^6·17^4 / 2^99`, in `[10/2^24, 11/2^24)`.
Every basin lies below its mass, so the total variation is `1 − Σ_r basin(r)`, with
`Σ_r basin(r) = 22122889006909061118515625 / 2^99` in `[585/2^24, 586/2^24)`: far above `1/4`. The
basins do not fall with the description (the `q = 6` rates' is the largest); 114 ordered pairs have
a strictly shorter description with a strictly smaller basin.

**(2) fails.**

### The verdict

Neither hypothesis holds. By the falsifier fixed in §5, the reading "rings as proposal dynamics"
is **refuted for the HNN's ring law**: on these terrains the bank of pumped rings is not a key
search. The adoption statement's second branch applies: the rings are recorded as not a search, and
menu propagation (`hnn::keys`) remains the key search.

## 8. What the measurement located

- **The lock does no search.** On every terrain the nonlocking control proposed as well as the
  pumped bank: identical proposals on the crib, 7 and 7 certified seeds on the blind moiré, 7 against
  6 on the parity moiré. The pump's bifurcation amplifies an in-phase pattern that the integration
  has already formed. Where the bank finds anything, the linear phase-carried moment finds it: a ring
  resonating at its own rate (RIDE), not a lock.
- **The work is the bank's fixed passage, not the key space.** The moiré bank's work is its 21
  rings' 288 ticks, 6,423,444 to 7,640,115 a seed whatever the key space. Enumeration's is the key
  space's: 2,412 to 3,756 on a channel's 122 gratings, and 5,253 to 23,415,123 on the parity moiré's
  1,815,848 joint keys. The two meet only where the key space is large, and there the bank was
  below enumeration on 3 of 8 seeds.
- **A ring holds one phase of its rate.** One ring per rate cannot hold two layers of one rate (blind
  seed 20262808).
- **A parity product starves a ring's moment.** `[proved-derived]` A ring's phase-carried moment of a
  parity product is, at each of its ports, its own layer's sheet there times the mean of the product
  of the other layers' spins `1 − 2s` over the ticks that visit the port. A partner layer balanced on
  every class of ticks those visits fix makes that mean zero. On 20262811 (`6/7`, `3/8`, `1/6`) the
  `3/8` layer is balanced on each parity class of the tick, so the `6/7` and `1/6` rings are starved;
  the `3/8` ring's moment is its pattern alternated by the `1/6` layer's parity-dependent mean
  (`±1/3`), whose first Fourier pair is the pattern's third harmonic. No triple certified.
- **The crib's board bank is the Bombe at the price of a solve.** Its lit wires are the support of
  the linear response to the seed's kick, which is the Bombe's current; the pump changes none of them.
  Preparing the 98-wide solve costs almost all of its work.
- **Independent rings lock together.** Undriven, every ring whose initial first-Fourier projection
  has a grating's sheet locks at the first pumped read, so the bank lands on a plural lock in all but
  `[596/2^24, 597/2^24)` of its configurations (single locks `[585/2^24, 586/2^24)`, no lock
  `[10/2^24, 11/2^24)`). The single-rate basins follow the rings' sign
  combinatorics, not `2^(−ℓ)`. A linear bank has no mechanism by which one lock excludes another,
  and coupling its rings into one connected linear network would give one dominant mode, whose
  basins are two half-spaces.

## 9. Obligations

Owed in #62 (the harness relies on them; none is a new law in an owner):
- Fine and Wilf's theorem in its two-word form (the moiré certificate);
- the crib's revisit certificate: a key that reproduces a cycle of the joint state repeats it;
- the rotation equivariance of a circulant ring's pumped passage on the word lattice (the orbit
  reading of (2), checked on every pattern for `q ≤ 4`);
- the starved moment: a ring's phase-carried moment of a parity product vanishes against a
  balanced, independent partner layer;
- the pumped passage's telescoping with its switch work, as one Lean statement composed from
  `HNN/Ring.{ring_material_commit_work, ring_tick_executed_energy_balance}`.
