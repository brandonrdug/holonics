# The rings as a search for keys, pinned before the run

**Date:** 2026-09-28. Refs #28, #73, #63. THE_REBUILD §4, "The ring-search experiment", wave C.

**Occasion.** The learner record's §2 ("The rings as the search") and §14.1 ("The decisive ring
experiment") restored the rings to a second role: not features inside a predictor, which campaign 2
measured and found adding no bits
([campaign 2](2026-09-26_CAMPAIGN_TWO_THE_RINGS_AND_CONTACTS_ARE_LAWFUL_AND_ADD_NO_BITS_ON_TEXT.md)),
but proposal dynamics for the search for keys. This record fixes the claim, the bank, the work
unit, the controls, the seeds and the criteria before the measured run. The harness is
`research/notebook/hnn_design/hnn_ring_search.rs`; its header states every declaration below.

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

Pending: the pinned run follows this commit and is recorded here without changing §§1–6.
