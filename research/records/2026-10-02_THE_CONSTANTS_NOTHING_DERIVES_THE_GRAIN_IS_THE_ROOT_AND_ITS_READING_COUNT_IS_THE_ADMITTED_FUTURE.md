# The constants nothing derives: the receiver's grain is the root, and its reading count is the admitted future

**Date.** October 2. **Issues.** #73, #63, #62. **Grade.** [derivation; agent-inferred] with a
source-inspected census. No code changed, no machine run. One exterior measurement on the
repository's own text ([receipts](2026-10-02_THE_CONSTANTS_NOTHING_DERIVES_receipts/)). Read at
`5dab4c71`.

**Lessons this audit could repeat** ([the lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md)):
- a declared constant standing in for a derivation;
- a refusal answered with a larger limit (lesson 9);
- an uncertified deposition step (lesson 5).

Every derivation below states its assumptions. Nothing here edits the
[contact loop](2026-10-02_THE_CONTACT_LOOP_THE_RETURN_REACHES_EVERY_CONTACT_AND_ITS_CHANGE_IS_RELEASED_BEFORE_THE_LATER_CUT.md);
§3 refines that record's §11.

## 1. The question

The contact loop's §11 found that the receiver's grain `L_R = ⌈1/ε_bits⌉` comes from a declared
code tolerance `ε_bits = 1/16` bit that nothing derives. This record asks the same question of
every constant on the physics path: the receiver, the comparison, the contacts and channel, the
deposit and its certificates, the release, and the word and exposure.

For each constant it gives:
- where it is;
- what it sets the scale of;
- whether anything derives it;
- what it should be derived from.

Pure capacity limits (carrier widths, iteration ceilings) are listed only when they could reach a
reading.

## 2. The tree: one scale root, its allocations, and the other declared roots

Almost everything that sets a reading scale hangs off **one declared root**, the receiver's code
tolerance `ε_bits = 1/16` (`hnn/field.rs:349`). Through `L_R = 16` it sets:

| Consumer | Rule | Chosen factor inside the rule |
|---|---|---|
| the receiving face's phase classes and fibre (`receiver/face.rs:1105`, `GrainCell::of`) | `k_c = ⌊L_R(f − n)⌋`, fibre `< 1/L_R` | none |
| the HNN release tolerance (`hnn/reference.rs:1403`) | `1/L_R` | none |
| every learned locus's carrier lattice (`hnn/field.rs:462`) | `L_ℓ = ⌈log₂(2 L_R X_ℓ)⌉` | the 2: half a grain to the lattice |
| the word's precisions (`hnn/chart.rs:143`) | `D_c = ⌈log₂(8 L_R X_w w e_max)⌉`, `L_c = 2D_c`, `L_w = ⌈log₂(12 L_R X_w e_max)⌉` | a quarter grain to the charts, a quarter to the transients |
| the chart rule of each normal law (`hnn/constitution.rs:1035`) | `D_ℓ = 2L_ℓ + 1 − ⌊log₂ L_R⌋` | a quarter grain to the chart release |
| the population chart (`hnn/moment.rs:384`) | `L_ν = ⌈log₂(2 L_R n*)⌉` | the 2 |
| the landmark tree's widths (`compression/landmark/context.rs:1189`, `:1205`) | `M_p`, `W` from `3·B·L_R·…` and `12·B·L_R·…` | quarter grains |
| the placement's openness (`hnn/field.rs:371`) | path attenuation at least `1/L_R` | none |
| the resonator grain and Floquet ladder (`hnn/constitution.rs:4395`) | from the lattice | none |
| the release `½·2^(−L−k_m)` (`hnn/constitution.rs:597`) | from the lattice | the code `k_m` (§5) |

The other declared roots are independent of it:
- **The field's clock and graph:** periods 5, 7, 11, 13, their locks and the 4-cycle. These are
  structural (D), and the aeon is their first passage.
- **The contact geometry:** quarter-turn placements and `L = 1`, which give `β_a = 2` and the
  attenuations `1, 1/4, 1/16`.
- **The material scales:** `h = 1`, `Y_g = Y_a = 2`, and the openings `c = 1`, `b = F = ½`,
  `f = ½`, `E_0 = ±½` (§6).
- **The receiver's other declarations:** aperture `A = 2`, depth `D = 4`, crib 64, the
  population priors `[1, 1]`, the stop prior `½` and the Krichevsky–Trofimov `½` (§8).
- **Several declared limits** that stand where the lattice already gives an edge (§7).

## 3. The receiver's grain, derived

### 3.1 The criterion

The grain partitions each class's exponent `v_c` (bits) into cells of width `1/L_R`, and the face
never reads the fibre inside a cell. The coarsest right grain is the one at which **the fibre hides
nothing the receiver could confirm from its own readings**. A partition cannot do the converse:
two media on either side of a cell edge read differently however close they are, which is the
boundary effect §11 found at 14 windows.

### 3.2 The steps

1. **Same-cell media.** Two media whose exponents for every class fall in the same cell differ by
   `|δ_c| < 1/L` for every `c`. A shift common to every class is absorbed by the normalizer, and
   a variable confined to an interval of length below `2/L` has variance below `1/L²`
   (Popoviciu). So `Var_p(δ) < 1/L²`. The bound is approached by two classes at `½` each,
   shifted `±1/L`, so it is tight.
2. **The information per reading.** As §11 derived, `D(p′‖p) = (ln 2/2) Var_p(δ) + O(δ³)` bits.
3. **The unit of evidence: one bit, from the two-part code.** Over `N` readings drawn under `p′`,
   coding with `p′` instead of `p` saves `N·D` bits in expectation. A two-part code that uses the
   changed medium must also name which of the two media it uses; with the uniform code on the two
   alternatives that costs one bit. So **the expected two-part code pays for the model's bit exactly
   when `N·D ≥ 1`**.
   - [agent-inferred] The one bit is a choice of model code (equivalently, a likelihood ratio of
     2), and the criterion is on the expectation: the realized log-likelihood sum has variance
     `2ND/ln 2` bits², which at `ND = 1` lies in `(2, 3)` bits². It is the threshold §11 reached
     through Stein's lemma, now read as a description length.
   - A one-standard-deviation criterion on that sum would need `N·D ≥ 2/ln 2` bits and give a
     grain of `1/12` at `N = 1,190`. It is a confidence convention of the same kind; the
     description-length one is kept because the framework compares by code length.
4. **The grain.** The fibre hides nothing whose expected two-part saving pays its bit exactly when
   `N (ln 2/2)/L² ≤ 1`, so `L_R` is the least integer with `2L_R² ≥ N ln 2`.
   - This is decided exactly on an enclosure of `ln 2`
     ([`grain.py`](2026-10-02_THE_CONSTANTS_NOTHING_DERIVES_receipts/grain.py)).
   - Given the same `N`, it is §11's resolution read as a partition.

### 3.3 The reading count `N`: the admitted future, not the aeon

§11 took `N = 1,190`, "the exposure's declared aeon". Three readings show that is the wrong count.

- **1,190 is not a reading of the passage.** It is the mean of the joint clock's first passage
  on uniform bytes: `⌈5·7·11·13·256/(52 + 5·37 + 35·24)⌉ = ⌈1,281,280/1,077⌉`
  (`research/notebook/hnn_design/hnn_exposure.rs:30–34`, `docs/THE_MACHINE.md:402`). The record
  that derived it says the aeon "is a first passage of the joint clock, so any law keyed to its
  length bounds nothing" (2026-09-25 record, §1). On text it varies.
  - Measured on the repository's own prose, an exterior proxy for the cut, which is not readable
    here ([`aeon_proxy.txt`](2026-10-02_THE_CONSTANTS_NOTHING_DERIVES_receipts/aeon_proxy.txt)):
    over `research/records` the mean aeon is `1100 rem 4431 over 14266` cells (14,266 aeons, least
    642, largest 2,826). On the Rust source it is `1398 rem 1885 over 4076`.
- **Nothing the receiver holds is reset at an aeon.** The deposit clock "is not reset at an aeon
  boundary" (`hnn/constitution.rs:363`). A difference between two constitutions is carried by the
  retained constitution and read by every later reading.
- **The code's own guarantees hold uniformly over the whole admitted future.** The lattice's
  release is bounded since a locus's founding, over any run (Lean
  `HNN/LatticeDeposit.release_bounded_since_founding`), and the constitution's header takes its
  budget from "the whole admitted future" rather than from the aeon
  (`hnn/constitution.rs:356–360`). Those bounds are Kraft tails and need no count. The grain does:
  it grows as `√N`, so it needs a finite declared future.

**Decision, agent-inferred.** For an exposure, the grain's `N` is the reading count of its admitted
future: one reading per compared cell, over the population it declares. The field already declares
the population, the cut's length, and refuses one below its floor `n*` (`hnn/field.rs:276`,
`:1115`).
- The standing exposure chose its population at the floor, `6,148 = n*`
  (`docs/THE_MACHINE.md:401`). That gives `L_R = 47`, the coarsest derived grain the field admits.
  `cells all` declares the pinned cut's 171,754 and gives `244`. `L_R` follows each declaration.
- At a later cell the remaining future is shorter, so the needed grain is coarser. A grain fixed at
  the founding from the whole population covers every later moment.
- The grain is then no longer a separate declaration: it is a reading of the declared population.
- **A continuing machine has no finite population.** There the grain has to refine with the
  machine's own reading count, as the release code `k_m` already refines with the deposit clock.
  That is a law change, owed with its Lean statement in #62 (item 4 of §11 below).

Assumptions:
- one reading per compared cell;
- `δ` small enough for the second-order `D` (true below a cell);
- the difference persists through later deposits, transported but not erased. This is assumed,
  not proved.

### 3.4 What the derived grain is, and what it changes

From [`grain.txt`](2026-10-02_THE_CONSTANTS_NOTHING_DERIVES_receipts/grain.txt), with every lattice
by the code's own rules:

| `N` | `L_R` | Lattices: elements/standings 0–3, channels 0–3 | Word `D_c`, `L_c`, `L_w` |
|---|---|---|---|
| declared tolerance, for comparison | 16 | 9, 9, 10, 10; 9, 9, 10, 9 | 19, 38, 15 |
| one window, `A = 2` | 1 | 5, 5, 6, 6; 5, 5, 6, 5 | 15, 30, 11 |
| aeon on prose, proxy 1,100 | 20 | 9, 10, 10, 11; 9, 10, 10, 9 | 19, 38, 15 |
| aeon on uniform bytes, 1,190 (§11) | 21 | 9, 10, 10, 11; 9, 10, 10, 9 | 19, 38, 15 |
| **the exposure's declared population, chosen at `n* = 6,148`** | **47** | **10, 11, 12, 12; 10, 11, 12, 10** | **20, 40, 16** |
| the whole pinned cut, 171,754 | 244 | 13, 13, 14, 14; 13, 13, 14, 13 | 23, 46, 18 |

At the exposure's declared population the grain derives to `1/47`, finer than the declared `1/16`
by a factor in `(2, 3)`.
- **The lattices.** Every lattice becomes finer by one or two bits; `D_c` and `L_w` by one and
  `L_c` by two. So moves between the old and new fine lattice units, which the deposit now
  releases, would be carried.
- **Openness is unchanged.** A contact attenuates by `2^(−Q)` with `Q ∈ {0, 2, 4}`, so every path
  attenuation is a power of `1/4`. At `1/47` the admitted set is `{1, 1/4, 1/16}`, as at `1/16`.
  It first changes at `L_R ≥ 64`; at `244` the path admits `1/64`.
- **Cost.** The constitution's bits rise by those one or two bits per coordinate. `B_Θ = 2^33` has
  never bound (§7).

**The contacts' change against it.** The contact loop measured a largest exponent shift of
`7/2^18` bits.
- It lies below `1/47` by a factor between `2^9` and `2^10`, and below `1/244` by a factor between
  `2^7` and `2^8`.
- Its expected two-part saving pays one bit only past `2·2^36/(49 ln 2)` readings, between `2^31`
  and `2^32`. That sharpens §11's "more than `2^29`".

So §11's finding stands for every population below `2^31` cells, the pinned cut's 171,754
included. The weak coupling is not an artifact of the grain.

## 4. The certified step's constants

**`s = ½`, the station score's curvature** (`hnn/constitution.rs:4639`; header `:51–58`).
- **The derivation in the code is sound.** The base-two score's Hessian in the realified logits is
  `ln 2 (diag p − ppᵀ)`. Gershgorin bounds each row by `2p_i(1 − p_i) ≤ ½`, so the Hessian is
  `⪯ (ln 2/2) I`. The phase part `½ q_t Δ²` has curvature `q_t/4 ≤ ¼` on the other coordinates.
- **It is loose.** The tight constant is `max(ln 2/2, ¼) = ln 2/2`, the supremum, reached at two
  classes of `½`. `½` overstates it by `1/ln 2 ∈ (36/25, 13/9)`.
- **Derived replacement.** Use a rational upper enclosure of `ln 2/2`: `26/75` (since
  `ln 2 < 52/75`), or the dyadic `3/8` (since `ln 2 < 3/4`).
  - With `3/8`, `a/C` rises by the factor `4/3`. Where the curvature bound is the binding one,
    `η` doubles whenever the fractional part of `log₂(a/C)` is at least `log₂(3/2)`.
  - That is a `log₂(4/3)` share of ratios placed log-uniformly within a binary octave.
- **In Lean** `s` is only a hypothesis (`Holon/Deposition.gauss_newton_curvature`, `0 ≤ s`). The
  Hessian bound is owed in #62.

**`η` restricted to powers of two** (`holon/deposition.rs:470`). A representation choice that keeps
the step and carries dyadic. It costs at most a factor 2 below the certified bound `min(a/C, 1/c)`.
It is sound.

**`ηc ≤ 1`, the covector's unit scale** (`holon/deposition.rs:42`, justified at
`hnn/constitution.rs:994–999`).
- It is the chart rule's assumption `‖wηg‖∞ ≤ 1`, under which a chart release moves a read by at
  most `X_ℓ²δ/c_m ≤ 1/(4L_R)`.
- The `1` trades one for one against the chart target `δ`.
- **Derived form:** `ηc ≤ c_m/(4 L_R X_ℓ² δ)`, with `δ` the chart certificate the deposit actually
  measured and `c_m = 1 − 1/(2L_R)`. At a chart certified below its target, this admits a longer
  step with the same guarantee.

**The storage-growth search** (`hnn/constitution.rs:6648`, `ε ∈ {0} ∪ {2^k : −20 ≤ k ≤ 40}`).
- The range is a declared limit. Its top end admits a storage growth up to `2^40` in one deposit,
  which is lesson 9's form.
- **Derived replacement.** Each block's `Q` is positive semidefinite and can be singular (a
  rank-one Gram `ccᵀ`, `hnn/constitution.rs:6634–6640`). The least growth is
  `max(0, λ_max(Q′, Q) − 1)`, the largest generalized eigenvalue, and it exists only when the range
  of `Q′` lies in the range of `Q`; otherwise no `ε` certifies and the deposit is refused, as now.
  `λ_max` is algebraic, so it is attained as an enclosure decided by exact inertia on
  `(1 + ε)Q − Q′ ⪰ 0`, bisected to the receiver's grain instead of over the declared list.

**`FACE = 64`, the spectral face's 16 bits, and the joint halving** are sound as written. Each is
charged, ceiling-rounded or re-certified, and costs at most one dyadic of `η`. The deposition
module's doc says the spectral face's grain is `⌊log₂ max|x|⌋ − 30` (`holon/deposition.rs:557`);
the code uses `− 16` (`:582`).

**A pairing to check, not established.** `certified_step_descends` reads `a` as the first-order
decrease of the score it certifies. The deposit forms `a` from the odometer covector `p̃ − q`
(`hnn/ratio.rs:30–46`), which is not the smooth score's gradient `p − q`. Lean
`HNN/Ratio.odometer_covector_descends` proves only a positive pairing between them. Whether the
certified decrease `½ηa` bounds the smooth score's actual decrease is therefore unstated. The
statement is owed in #62.

## 5. The release's code `k_m`

`k_m = 2⌊log₂ m⌋ + 1`, the Elias-gamma length of the deposit clock (`hnn/constitution.rs:593–599`;
Lean `gammaLength`, `gamma_kraft_lt_one`).
- Any prefix code with `Σ 2^(−k_m) ≤ 1` keeps the proved bound that releases since the founding
  sum below half a unit. Gamma is chosen ("the field's own natural code"), and it is the coarsest
  admissible at the first deposits (`k_1 = 1`).
- **Derivable.** Give each deposit's release a share of the grain the admitted future can confirm
  (§3), instead of half a lattice unit since the founding. The total release then lies below the
  receiver's resolution by construction.
  - With the population's `N`, a release below the `1/L_R` read bound is the same requirement the
    lattice rule already meets.
  - So gamma is admissible but not singled out. Any code meeting Kraft gives the guarantee.

## 6. The field's declared material, gauge and physical

The forward path's dimensionless content (agent-inferred from `hnn/propagation.rs:129–160`,
`:950–960`, the junction's anchor at `:11` and `:1152–1208`, and the transit at `:1327–1384`):
- **The junction** reads `G_a/Y_r = κ_a·(Y_a/Y_r)`, with `κ_a = 2^(−β_a Q_a/2)`.
- **The contact** reads `GC/h`, `GD/2` and `GhK/4`: at the founding `2`, `1/4` and `1/8`. At zero
  contact state the fraction of a difference wave `α_g − α_h` that crosses is `(G/2h)/m_a`, with
  `m_a = 1 + (G/2h)(2C + hD + ½h²K)` (`hnn/propagation.rs:24`, `:387–398`). At the founding
  `G = 2h` (`κ = 1`, `Y_a = 2`, `h = 1`), so it is `1/m_a = 8/27`, with `m_a = 27/8`.
- **Gauge:** the absolute admittance level and the absolute hop unit relative to `C` and `K`, and
  the placement radius (only `βQ` enters).
- **Physical:** `κ_a`, `Y_a/Y_r = 1`, the three contact numbers, and the hop against the ring
  element's implicit unit step (`hnn/propagation.rs:62–66`, `h = 1` there).

How the material is set:
- **`Y_a = 2c²/h`** is the declared matching rule (construction record of September 28, the
  declared-values table). It is exactly `GC/h = 2` at `κ = 1`.
  - It is not a matched termination: at the founding the contact passes `8/27` of a difference
    wave and reflects the rest.
  - So the founding contact material `c = 1`, `b = F = ½` is the root here, and nothing derives it.
- **`β_a = 2`** is derived: the least positive element of the exponent lattice `(2q_Q/L)ℤ` at the
  quarter-turn placements' `q_Q = 1` and `L = 1` (`hnn/field.rs:1004–1018`).
- **`L = 1`** is a representation choice that keeps the conductances rational.

**The coupling these constants set**, for the main line. This is leading order at the first
transit with every `Q_a = 0`, ignoring the element re-entry. I re-did the agent's arithmetic.
- **From the source.** The source junction reads `v_0 = s_0/3` and emits `2s_0/3`. Each contact
  passes `8/27` and each junction weighs an arrival by `G/(Y + 2G) = 1/3`. Over the two paths to
  ring 2 this gives `v_2 = (2/3)^9 s_0`, a factor in `(2^(−6), 2^(−5))`.
- **A change of contact 1's material** moves `1/m` by `−(64/729)(2δC + δD + ½δK)`. So, to
  first order, `|δv_2|` is at most `(2^11/3^12)|s_0|·|2δC + δD + ½δK|`, a coefficient in `(2^(−9), 2^(−8))`, with
  `|s_0| ≤ ½` from `E_0 = ±½`.
- **Before the receiving map.** One channel-lattice unit on `c` (`2^(−9)`, so `2δC = 2^(−7)`)
  therefore moves the receiving anchor by at most `2^3/3^12`, which lies in `(2^(−17), 2^(−16))`,
  before `R`.
- **Against the measurement.** That is the order of the measured shifts (largest `7/2^18`, median
  `41/2^24`). The unread factor is `‖R‖`.

The constants that set it are `Y/G`, the founding contact material through `m = 27/8`, and
`E_0 = ±½`. None is derived. This identifies the weak coupling's constants. It does not settle
why the coupling is weak, which is the main line's question.

## 7. Declared limits that stand where a derivation belongs

| Constant | Where | What derives it |
|---|---|---|
| `B_Θ = 2^33` bits | `hnn/constitution.rs:498` | It is host memory and has never bound (at most `2^21` bits after 40 deposits). The framework's own bound is two-part: the constitution's bits may not exceed the code length it saves on the admitted passage, which the exposure already reads. |
| `ENTRY_BOUND = 3` (`\|E_ij\| ≤ 8`) | `hnn/executed.rs:198` | The largest entry at which a carried read stays inside the certified gain, from `X_ℓ` and the grain. The doc's reason is a measurement ("stayed below 2"). |
| `LADDER_DEPTH = 8` | `hnn/executed.rs:3164` | The ladder already stops where `2ηu < 2^(−L)` (`:3203`). From a start with `2ηu ≤ 1` (the entry hold at `:3175–3176`) its natural depth is at most `L + 1`: 19 trials at the source port's `L = 18` on the population 6,148, 24 at `L = 23` on the pinned cut, 21 at `L = 20` under the grain `1/47`. 8 truncates it. |
| storage growth `[2^(−20), 2^40]` | `hnn/constitution.rs:6648` | the exact generalized eigenvalue (§4) |
| pending capacity 64 | `hnn/reference.rs:703` | It never binds (one or two pending a window), so it is a refusal limit with no scale. |
| aperture `A = 2` | `hnn/field.rs:348` | It is refused above the receiving ring's observability rank (`hnn/receiving.rs:9`, `:1216`). The rank is computed at declaration, so `A` can be read from it. |
| depth `D = 4` | `hnn/field.rs:350` | Chosen on development cells. The depth past which no stored chain has two arrivals is a statistic the tree already holds (`context.rs:250–262`). |
| crib `W_crib = 64` at offset 1 | `hnn/field.rs:354` | The least crib for which each ring's loop fibre is one gauge orbit, a reading of the closing cells. |

## 8. Priors and openings

- **The population's priors `[1, 1]`** (`hnn/receiving.rs:1051`) say the tree and combined faces'
  descriptions are equal. **Derivable:** `π_f ∝ 2^(−|describe_f|)` from the two families' exact
  description lengths, which `Field::describe` computes.
- **The stop prior `½`** (`context.rs:890`).
  - It was chosen by development code length from a declared family of 256 laws, whose top rung
    `J = ⌈log₂(n*·B)⌉ = 16` is derived.
  - The optimal weight at a depth is `stops_d/(stops_d + splits_d)` (`context.rs:972–976`), a count
    the tree holds.
  - The landmark record charges the family "11 bits" in one place and "8 family bits" in another.
    The family has `2^8` laws, so 8 is the consistent figure.
- **The Krichevsky–Trofimov `½`.** It is justified by its minimax regret, an external theorem, not
  by state.
- **`E_0 = ±½`, `f = ½I`, unit slices, `c = I`, `b = F = ½I`, `H_0 = I`, `h_x = 1`**
  (`hnn/constitution.rs:3127–3320`).
  - These are declared. Only `R_0 = 0` and "nonzero, so the factor can move" are argued.
  - `H_0 = I` and `h_x = 1` are the unit-scale-wave assumption that the lattice rule also makes.
    The notebook measures it at each boundary; nothing proves it.

## 9. Precisions that cannot reach a reading

`READING_BITS = 64`, `LOG_OCTAVES = 96`, `LOG_TERMS = 48`, `FIXED = 125`, the 64-bit `grain_floor`,
`KEPT = 127`, `DERIVATIVE_BITS = 192`, `FACE_BITS = 64`, `JOINT_BITS = 128`,
`RESIDUAL_SHIFT = 125`, `CARRIER = 2^127`, and `ring.rs`'s attainment, covector and separation
bits.
- Each is an outward enclosure, a ceiling, a re-certified proposal, or a typed refusal that falls
  back to an exact decision.
- The widest any of them leaves a reading is below `2^(−61)` bits, on `log₂ Z` (a relative
  enclosure width of `2^(−64)` on `Z`), far below every grain above.
- Their bounds against the grain are doc claims or arithmetic, not Lean theorems. They are not
  scales, and none is a root.

## 10. Found in passing

- **The rule `L_R = ⌈1/ε⌉` is written four times:** `hnn/receiving.rs:958`, `hnn/prediction.rs:243`,
  `hnn/field.rs:433` and `hnn/field.rs:1904`. It should have one owner.
- **`hnn_exposure.rs:1040–1041` types `1/16` and `1/21` as literals.** It should read the field's
  tolerance, and the derived resolution from its `N`.
- **`HELD_OUT = 1,190` is hard-coded** in `hnn_exposure.rs:174` and in the card's tests
  (`holonics-cuda/src/hnn/tests.rs:351`).

## 11. Owed in #62

1. The station score's curvature bound in realified logits, `⪯ (ln 2/2) I` on the magnitude part
   and `¼` on the phase part, which makes `s` a theorem rather than a hypothesis.
2. The grain lemma: two media whose exponents share every cell carry less than `(ln 2/2)/L²` bits a
   reading, tight, so over `N` readings they are unconfirmable exactly when `2L² ≥ N ln 2`, to
   second order.
3. The odometer pairing of §4: whether `a` formed from `p̃ − q` bounds the smooth score's
   decrease along the certified ray.
4. For a continuing machine with no declared population, the grain as a reading of the machine's
   own count of readings, refining as `√N`, with the lattices that follow it re-based at each
   refinement (§3.3).

**Status after #151** (`HNN/Ratio/Resolution`):
- Item 1 is proved: `codeLength_quadratic_upper` and `station_score_quadratic_upper`, with the
  constant compared in `station_curvature_constant`.
- Item 2 is proved: `grain_lemma`, `grain_lemma_tight`, `grain_unconfirmable`,
  `grain_criterion_iff` and `derived_grains`.
- Item 3 is answered for a one-hot target. Along the covector itself, `a` bounds the smooth
  score's first-order decrease only up to the factor `1/K`, with `K = 2^(1/L)·2/(e ln 2) < 8/7` at
  `L = 16`. So the code's rule keeps at least `3/8·ηa` of the `½ηa` the certificate states
  (`odometer_pairing_ratio`, `odometer_certified_decrease`, `odometer_ratio_sixteen`). A
  deposit's move through its loci is certified to descend when `(2K − 1)A⁻ < (3 − 2K)A⁺`
  (`deposit_descends`, `deposit_condition_iff`).
- Item 4 is proved for the reads. `L(N) = ⌈√(N ln 2/2)⌉` is the least grain meeting the
  criterion and refines as `√N` (`refiningGrain_spec`, `refiningGrain_growth`). `L(N)` does not
  refine by integer factors, so a schedule that keeps every read is a dyadic one at or above it,
  such as `2^⌈log₂ L(N)⌉` (`grainRead_of_refined`). Re-basing the lattices at each refinement is
  still owed in #62.
