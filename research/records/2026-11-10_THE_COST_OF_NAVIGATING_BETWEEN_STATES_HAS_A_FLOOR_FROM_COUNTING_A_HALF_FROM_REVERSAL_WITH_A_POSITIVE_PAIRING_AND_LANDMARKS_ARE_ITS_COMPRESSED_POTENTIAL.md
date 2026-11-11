# The cost of navigating between states has a floor from counting, a half from reversal with a positive pairing, and landmarks are its compressed potential

Status (2026-11-10, night): a lens joined to its owners, with host rulers on public arithmetic and on one private passage. No machine change. Its consequence for the machine's tick is the subject of [the grip record](2026-11-10_A_GRIP_OF_LETTERS_IS_A_NAVIGATOR_WORD_THE_FIXED_ADVANCE_MOMENT_READS_ONLY_PAIR_TERMS_AND_THE_CONTACTS_PRODUCT_MUST_CARRY_ALONG_ITS_OWN_CIRCLE.md). Refs #73, #410.

[historical] The lens (Brandon, November 10, 22:15 UTC, paraphrased). Landmarks in the p-adic sense and the prime wheel, read as a toroid, are what number theory needs here. Numbers are emergent counts of constrained causality, which is computation. RH, Hodge, algebraic classes and elliptic curves matter as routes into one statement: a theorem about the cost of navigating between configuration states, in which landmarks shrink the volume that has to be searched. The same statement is to be seen in the normality of digits, in Zeno's walk when each step is re-based as one moves, in escape velocity, in Cayley graphs and God's algorithm, in P against NP and unique games, in gyration and the physics of a whip, in the speed of light and spectral gaps, and in digits read as a mapped character set whose operations are inferred from distributions. He asked for the abstract statement, worked on the objects, and not for the official Millennium objects.

This record names the object and the operation, recovers what the atlas holds, states the lens as one chart with its hypotheses, reads it on a public terrain (the prime wheel) and on the code passage, and says what follows for the machine and what does not transfer.

## 1. Recovered

| Part of the lens | Held as | Where |
|---|---|---|
| The prime wheel | the coprime chain cut by one prime at a time; its units hear a mode only through a gcd | `prime.wheel-copy-cut`, `prime.wheel-ramanujan-spectrum` |
| p-adic landmarks | the tower of faces `ℤ/pⁿ` whose sections are `ℤ_p`, plural at every level | `tower.padic-plural` |
| Primes as primitive cycles of a return map | Möbius inversion of closed-route counts; the Euler product; Ihara's determinant | `landmark.primitive-cycle-count`, `landmark.euler-product`, `trace.ihara-zeta` |
| The half on a finite terrain | the tetrahedron's winding roots on `|α|² = q` | `rh.graph-trace-tetrahedron` |
| The half as a Jacobian | the square root of logarithmic transport | `rh.mellin-half-density` |
| The modular scattering scalar | `φ(w) = Λ(2w − 1)/Λ(2w)` and its residual | `rh.modular-scattering-residual`, `rh.modular-scattering-paired-tail` |
| A positive height form | one independent point has a positive regulator | `coupling.rank-one-regulator`, `bsd.rank-clause` |
| Positivity is the content of RH | the Weil receiver of a square: a diagonal plus an off-line cross term | `rh.weil-positivity-under-rh`, `rh.zero-comb-diagonal-cross` |
| A positive pairing places the modes | Hodge index form; Hodge–Riemann positivity gives `|α| = √q` on a curve | `hodge.index-form`, `hodge.colourless-classes-weil`, `trace.hasse-bound`, `landmark.hasse-site-rotation` |
| The certificate of a period | `G ≻ 0`, `M_TᵀGM_T ⪯ ρ²G` | `parametron.floquet-certificate` |
| Diffusion reads frustration to the square root | the connection Cheeger bound; the frustrated cycle | `key.connection-cheeger`, `key.twisted-cycle-square-root` |
| Location is polynomial in what diffuses | unique games on expanders; exponential only in slow modes | `key.unique-games-frontier`, `key.slow-modes-landmarks` |
| A pass reaches one hop | `t` passes are a degree-`t` polynomial; the gap sets the carry | `contact.pass-reach-gap`, `contact.alignment-spectral-gap` |
| Euclid's walk is a word | divide, invert, repeat; the continued fraction in `GL₂(ℤ)` | `lock.euclid-address`, `lock.continued-fraction-word`, `rotation.golden-hurwitz` |
| Gyration | the gyroparallelogram; the carry a loop of two moves leaves | `frame.gyroparallelogram`, `motion.commutator-carry` |
| Digits under a multiplier | a multiplier coprime to a cycle turns it | `radix.multiplier-face-action`, `radix.digit-face-calculus` |

Missing before this record: the cost of a route as one statement (floor, ceiling, half, finding); the distance potential and what a landmark stores of it; the walk of Euclid priced in moves; the composition of two turns as the wheel's own step; normality stated as the absence of resonance; and any read of these on a terrain.

## 2. The chart

**The object.** A terrain is a set `X` of `n` states with a family of `d` moves closed under reversal (navigators). A route is a word in the moves; its cost is its length. The distance `d(x, y)` is the least cost. The move operator `A` sums the moves. The cover `X̃` is the same moves with only their own relations: the free object, on which a word returns only when the relations force it. Two numbers belong to the cover: its growth `g` (the ratio of successive shells) and its radius `ρ` (the growth rate of closed words, `lim m_2k^(1/2k)`).

**The operation that transfers** is the pricing of a route, in four parts.

### 2.1 The floor is a count

[proved-derived] The quotient map from the cover to the terrain does not lengthen a route, so the ball of radius `r` in `X` is no larger than the ball of radius `r` in `X̃`. The mean distance from any state is therefore at least the mean when `n` states fill the cover's shells in order, about `log_g n`. This is the causal bound of the lens: one move a tick, and a cone whose volume is a count. The integers that appear are counts of reachable states under the relations, the sense in which a number is an emergent count of constrained causality: for the moves of 3 below the shells are 1, 1, 2, 2, 4, 6, 10, 16, 26, 42, each the sum of the two before it, `g = φ`.

### 2.2 The ceiling is a gap, and the plain gap is the wrong ruler

[proved-standard] With `λ` the largest nontrivial modulus of `A`, the diameter is at most `⌈ln(n − 1) / ln(d/λ)⌉` (Chung 1989), and a walk is within `√n (λ/d)ᵗ` of uniform after `t` moves. A terrain with no gap pays the square: the frustrated cycle (`key.twisted-cycle-square-root`), relaxation by a potential alone (`contact.pass-reach-gap`).

[proved-standard] The ruler that meets the floor compares `λ` with the cover's radius `ρ`, never with `d`. A terrain is **tempered relative to its cover** when every nontrivial mode has modulus at most `ρ`. Kesten (1959): `ρ = 2√(d − 1)` only for free moves, and any relation raises it. For tempered terrains the typical distance is `(1 + o(1))` times the floor and the walk mixes with a cutoff at the entropic time (Lubetzky–Peres 2016 for Ramanujan graphs; Bordenave–Lacoin 2021 for walks on covered graphs; Sardari 2019 for diameters).

### 2.3 The half comes from reversal with a positive pairing

[proved-derived] Let `B` be an oriented move operator (one step along a route that does not turn back), `q` the number of continuations of a step, and suppose a form `G ≻ 0` with `B†GB = qG` on the nontrivial part. If `Bv = αv` then `q·v†Gv = (Bv)†G(Bv) = |α|²·v†Gv`, so `|α| = q^(1/2)`. The half is the square root of a count, and it is forced by two things only: a reversal (the adjoint) and a positive pairing (the form). This is the equality case of the parametron's certificate.

[proved-standard] Its instances. Weil's proof for curves: Frobenius, the Rosati involution and the positivity of the Hodge index. Serre (1960): a correspondence on a Kähler variety that scales the polarization by `q` has eigenvalues of modulus `q^(k/2)` on `Hᵏ`, by Hodge–Riemann positivity. Grothendieck's standard conjectures: positivity of Hodge type implies the Weil placement. Ihara and Hashimoto: a finite regular graph satisfies its own RH if and only if it is Ramanujan. So in the abstract the lens's "RH and Hodge" is one certificate: Hodge supplies the positive pairing on the classes that closed routes span, reversal supplies the adjoint, and RH is the placement that follows. On a finite graph the first half is free (closed routes span the cycle space) and the second is a property that some graphs have and a cycle does not.

[proved-derived] The same half prices finding. For a symmetric `A`, `(A^(2m))_xy = ⟨Aᵐδ_x, Aᵐδ_y⟩`: a route of length `2m` is two routes of length `m` that meet. Two sweeps from source and target meet when `N(m)² ≥ n`, so a route is found at the cost of `√n` states (Shanks 1971), and in the generic model no fewer suffice (Shoup 1997).

[proved-standard] Escape. On the hyperbolic plane the spectrum of the Laplacian starts at `1/4 = (growth/2)²`. A mode `s(1 − s)` with `Re s = 1/2` propagates; a mode with `s` real in `(1/2, 1)` is bound. The threshold is the lens's escape velocity. For the modular surface the scattering at the cusp is `φ(s) = ξ(2s − 1)/ξ(2s)` (`rh.modular-scattering-residual`), whose poles are at `ρ/2` over the zeros of zeta (Faddeev–Pavlov; Lax–Phillips): RH says the resonances of the wheel's cover sit on `Re s = 1/4`. Selberg's conjecture is that congruence quotients have no bound mode under the threshold; `3/16` is proved, which makes the prime wheels of 3 an expander family (Lubotzky 1994).

### 2.4 A count of primitive cycles keeps half its digits

[proved-standard] `π(x) = Li(x) + O(√x ln x)` is equivalent to RH (von Koch 1901). For a curve of genus `g` over `F_q`, `|N_n − qⁿ − 1| ≤ 2g·q^(n/2)`. For a graph, the count of primitive cycles of length `n` is `qⁿ/n` with an error at `q^(n/2)` if and only if it is tempered. On the objects: the leading mode gives a count its scale and the leading half of its digits; the trailing half is the modes on the circle. The evening's number-form record found the same shape for a different reason (`code.count-digits-second-order`); the two are an analogy and are not identified here.

[proved-standard] The values are volumes. An even zeta value is a power of the turn times a ratio (Euler). An odd one, `ζ(n)` for odd `n ≥ 3`, is a ratio times the volume of a lattice of classes, the regulator of `K_(2n−1)(ℤ)` (Borel 1977). The leading term of an elliptic curve's `L` at its centre is conjectured to be a volume of the same kind: the regulator of its rational points under the height pairing, a positive form (`coupling.rank-one-regulator`; `bsd.rank-clause`). So the elliptic route of the lens is the same certificate read at one point: a positive pairing on classes, and a count whose leading term is its volume.

### 2.5 Normal means no resonance

[proved-standard] `x` is normal to base `b` if and only if `bⁿx` is equidistributed on the circle (Wall 1949), which is the vanishing of every nontrivial character mean `(1/N) Σ e(h·bⁿx)` (Weyl). Equivalently no finite-state reader compresses its digits (Schnorr–Stimm 1972; Dai–Lathrop–Lutz–Mayordomo 2004). Bases are frames: normality to 2 and to 3 are independent (Cassels 1959; Schmidt 1960), and explicit normal numbers exist to one base (Stoneham; Bailey–Crandall 2002). For `π` and `e` it is open.

[interpretation] RH in this chart: the primes resonate with nothing beyond the half. `Σ_(n ≤ x) μ(n) = O(x^(1/2 + ε))` is equivalent to RH (Littlewood 1912). The zeros resonate only at prime powers: `Σ_(γ ≤ T) x^ρ = −(T/2π)Λ(x) + O(ln T)` (Landau 1911), and `γ·ln p/2π` is equidistributed (Hlawka 1975).

### 2.6 Euclid's walk is Zeno's walk with re-based steps

[proved-standard] Each division re-bases the pair: the remainder becomes the unit. The count of divisions on `(p, x)`, averaged over `x`, is `(12 ln 2/π²) ln p + 1.467` (Heilbronn 1969; Porter 1975). Each division fixes `π²/(6 ln 2) = 2.373` nats of the ratio (Lévy 1936; Lochs 1964), against `ln 2 = 0.693` for a fixed halving. The slowest ratio is the golden one (Lamé 1844; `rotation.golden-hurwitz`). Counted in unit moves the walk costs the sum of its quotients, whose mean is `(6/π²)(ln p)²` (Yao–Knuth 1975): a heavy tail, since a single quotient has no mean.

What a letter does to the frame of the next is this re-basing, taken to the machine in the grip record.

### 2.7 The distance is a potential and a landmark stores one column of it

[proved-standard] God's algorithm is descent on `d(·, goal)`; God's number is the diameter. The whole potential has `n` entries. A landmark `L` stores the column `d(L, ·)`, and `|d(L, x) − d(L, y)| ≤ d(x, y)` bounds every distance from below (Goldberg–Harrelson 2005). A set of landmarks resolves the terrain when `x ↦ (d(L_i, x))_i` is injective; its least size is the metric dimension (Slater 1975; Harary–Melter 1976). For a group, a base pins one point at a time and the volume factors, `|G| = Π |orbit_i|` (Sims 1970): each landmark divides what is left to search. The p-adic tower is this with an ultrametric: each digit pins a coset, and the prime wheel is the product of the first digits over its primes, a torus `(ℤ/P)^× = Π (ℤ/p)^×`.

[proved-standard] Nearness is not findability. Shortest words are hard in the worst case (Even–Goldreich 1981; Jerrum 1985; Demaine–Eisenstat–Rudoy 2018 for the cube family). Supersingular isogeny graphs are tempered (Pizer 1990), so every curve is near every other, and a route still costs `√n` to find by two sweeps (Delfs–Galbraith 2016); with the closed routes at a state known, its endomorphisms, the route is polynomial (Kohel–Lauter–Petit–Tignol 2014; Eisenträger–Hallgren–Lauter–Morrison–Petit 2018), and one scheme fell when its public data gave such landmarks away (Castryck–Decru 2022). On the objects: learning is locating keys by loop closure, and a known loop at a state is a landmark.

[proved-derived] A landmark's worth is bounded by its surprise. With context `c`, pin `x` and target `y`: `p(y|c) = Σ_x′ p(x′|c)·p(y|x′, c) ≥ p(x|c)·p(y|x, c)`, so `ln(p(y|x, c)/p(y|c)) ≤ −ln p(x|c)` at every place. A pin that was certain passes nothing on.

### 2.8 Two turns compose into the step

[proved-standard] Two turns of half-angles `α`, `β` about pivots a distance `δ` apart in the hyperbolic plane compose with `c = sin α·sin β·cosh δ − cos α·cos β`: a turn if `|c| < 1`, free fall (a shear) if `c = 1`, a boost of length `2·arcosh c` if `c > 1`. For the modular group's half-turn `S` and third-turn `U`, `α = π/2`, `β = π/3`, `cosh δ = 2/√3`, so `c = 1`: the unit step of the wheel is the free fall that two turns leave. This is the dual of gyration, where two boosts leave a turn (`frame.gyroparallelogram`), and the same carry that `motion.commutator-carry` reads in the affine chart.

[interpretation] The whip. A wave that travels down a line whose inertia per length falls keeps its energy flux, so its velocity rises as the inertia falls; momentum is carried through a chain of pivots, each a moving grip for the next. In the Swing's terms it is a tower thread of boosts. Nothing is claimed here beyond that reading.

### 2.9 Digits are a character set whose operation is read from its spectrum

[proved-standard] Adding `s` on `ℤ/b` permutes the digit symbols with `gcd(s, b)` cycles of length `b/gcd(s, b)`. Its eigenvectors are the characters `χ_k(x) = e(kx/b)` with eigenvalues `e(ks/b)`. For the permutation `P` of `+1`, the plane of `(P + Pᵀ)/2` at `cos(2π/b)` places every symbol on a circle in its order, and `P` itself gives the hand: the order of the digits is recovered from transitions alone. From counted transitions with error `E` the plane is recovered within `sin θ ≤ 2‖E‖/gap` (Davis–Kahan 1970, in the form of Yu–Wang–Samworth 2015), with `gap = 1 − cos(2π/b) = 2 sin²(π/b)`, the distance to the constant mode; on the complement of the constants it is `(1 − cos(2π/b))(1 + 2cos(2π/b))`. The gap falls as the square of the cycle's length, the cycle's own diffusion square (`key.twisted-cycle-square-root`). An operation on symbols is located by the gap of its own turn, with no table of what the symbols mean. This is how a ring increment is located and never authored. The ruler for it on the passage's digits is owed (7).

### The statement

[interpretation] On a terrain with moves closed under reversal:

1. Every route costs at least the count's floor (2.1).
2. Where a positive pairing scales under the move, the modes sit at the half (2.3); the terrain is then tempered relative to its cover and the typical route meets the floor (2.2).
3. Without a landmark, finding a route costs the square root of the volume; each landmark divides the volume by the orbit it pins, and a resolving set turns finding into descent (2.3, 2.7).
4. Where no such pairing exists, diffusion pays the square and slow modes remain, each of which is a landmark not yet founded (`key.slow-modes-landmarks`).

Part 2 is a certificate, never a universal law: a cycle has no such pairing and pays the square. The arithmetic terrains have it by theorems (Weil, Deligne) or are conjectured to (RH, Selberg). The lens's claim that RH and Hodge are faces of one statement is, on the objects, that the certificate's pairing lives on what closed routes span.

## 3. The reads

### 3.1 The prime wheel

The terrain: the projective line over `F_p` (`p + 1` states), the moves `x + 1`, `x − 1` and `−1/x`, from the point at infinity. The floor: the same moves on the rationals. All arithmetic is on integers; floats appear only in the means and the modes.

| p | mean distance | floor | mean/floor | farthest | farthest/mean | mean/ln p | largest nontrivial mode | plain gap ceiling |
|---|---|---|---|---|---|---|---|---|
| 1,009 | 12.2089 | 12.0485 | 1.0133 | 16 | 1.3105 | 1.765 | 2.92391 | 270 |
| 10,007 | 17.1326 | 16.8128 | 1.0190 | 23 | 1.3425 | 1.860 | 2.92751 | 377 |
| 100,003 | 22.0205 | 21.5723 | 1.0208 | 30 | 1.3624 | 1.913 | 2.92884 | 480 |
| 1,000,003 | 26.8920 | 26.3359 | 1.0211 | 38 | 1.4131 | 1.947 | 2.92848 | 573 |
| 10,000,019 | 31.7457 | 31.1545 | 1.0190 | 45 | 1.4175 | 1.970 | not read | |

`mean/ln p` climbs toward `1/ln φ = 2.078`. The wheel's own shells follow the free shells until the wheel is nearly full (at `p = 10,000,019` they agree through radius 27).

The cover. On `PSL₂(ℤ)` with `S`, `T`, `T⁻¹`, the distinct elements written by words of `k` letters number 3, 7, 13, 23, 39, 65, 107 (each the sum of the two before it, and 3). The closed words number `m_2k` = 3, 15, 91, 607, 4273, 31119, 231955, 1758431. The recurrence coefficients of the spectral measure at the identity alternate (`b_odd² ≈ 2.449`, `b_even² ≈ 1.860`), so the spectrum is two bands. The radius reads 2.9288 ± 0.001 (four fits between 2.92832 and 2.93026) and the inner edge 0.200. `2√2 = 2.8284` is the radius the moves would have with no relations.

So at `p ≥ 100,003` the wheel's largest nontrivial mode is within 0.0005 of its cover's radius, its mean distance is within 2.1% of the floor, and the plain gap ceiling stands 15 times over the farthest state.

The straight route: Euclid's divisions with nearest quotients on the shorter pair of the state's lattice around `√p`, counted in moves, each route run on the wheel and checked to arrive. Over every state:

| p | straight/shortest (ratio of means) | share where straight is shortest | share over twice the shortest | their share of the straight cost | 99.9% quantile | worst | divisions on the route |
|---|---|---|---|---|---|---|---|
| 10,007 | 1.1195 | 0.6574 | 0.021 | 0.068 | 5.00 | 5.4 | 3.250 |
| 100,003 | 1.1764 | 0.5848 | 0.032 | 0.107 | 10.92 | 14.3 | 3.974 |
| 1,000,003 | 1.2329 | 0.5170 | 0.041 | 0.143 | 17.39 | 37.5 | 4.693 |
| 10,000,019 | 1.2788 | 0.4578 | 0.048 | 0.167 | 18.44 | 105.3 | 5.407 |

Euclid's divisions on `(p, x)` over every `x` read 6.2877, 8.2308, 10.1704, 12.1093 at the first four primes; with the opening swap counted, 7.2877, 9.2308, 11.1704, 13.1093 against the theorem's 7.2962, 9.2298, 11.1697, 13.1102.

### 3.2 The code passage

Information between two letters `s` places apart (TRAIN, 8,096,768 places, shuffle floor subtracted; one letter's entropy is 3.4146 nats):

| s | 1 | 2 | 3 | 4 | 8 | 16 | 32 | 64 | 128 | 256 |
|---|---|---|---|---|---|---|---|---|---|---|
| nats | 0.734 | 0.387 | 0.244 | 0.162 | 0.0603 | 0.0196 | 0.0109 | 0.0064 | 0.0041 | 0.0031 |

The fall is a power law with a knee: slope −1.31 from 1 to 16, −0.66 from 16 to 256. `I(256)/I(128) = 0.75`. No separation that is a multiple of four from 8 to 64 stands 10% over its neighbours (12 stands 7.5% over).

The surprise of the reader of two letters each side (HELD128, mean code 0.5758 nats) correlates with itself `k` places on by 0.357, 0.205, 0.132, 0.056, 0.033, 0.038 at `k` = 1, 2, 4, 16, 64, 256; the last two stand 6.2 and 5.1 standard errors over zero.

A pin's worth (HELD128; target the next letter; the letter two back known in both readings; 43,214 places). By quartile of the pin's surprise (1.130, 2.074, 2.965, 4.657 nats) the gain to the next letter is 0.492, 0.819, 1.243, 1.685 nats, a share of 0.435, 0.395, 0.419, 0.362 of the surprise. The gain correlates with the surprise by 0.384, and at no place does it exceed the surprise by 0.05.

## 4. Guesses and scores

All fixed at 22:28 UTC, before any of these reads.

| Guess | Fixed | Read | Score |
|---|---|---|---|
| G24a mean/floor | 1.06; rule: 1.10 or under at `p ≥ 100,003` | 1.013 to 1.021 | held: the typical cost meets the floor, closer than guessed |
| G24b farthest/mean | 1.35; rule: 1.5 or under | 1.31 to 1.42 | held |
| G24c straight/shortest at the four primes | 1.10, 1.20, 1.30, 1.40; rule: a rise of 0.05 a decade | over all states 1.12, 1.18, 1.23, 1.28, rises 0.057, 0.057, 0.046; the 5,000-state samples 1.11, 1.19, 1.24, 1.26 | within 0.02 at the first two primes, 0.07 and 0.12 under at the last two; the rule held on two decades of three |
| G24d largest nontrivial mode | 2.88 ± 0.06, within 0.03 of the cover's radius | 2.924 to 2.929; within 0.005 of 2.9288 | held |
| G24e instrument check | Euclid's mean within 0.05 of the theorem | within 0.009 with the opening swap counted | held; the script printed the constant with the swap beside a count without it |
| G25 information by separation | 1.10, 0.60, 0.25, 0.10, 0.04, 0.010, 0.003 at 1, 2, 4, 8, 16, 64, 256; a power law; landmarks at multiples of four | 0.734, 0.387, 0.162, 0.060, 0.020, 0.0064, 0.0031 | power law held (0.75 against 0.30; slope −0.86 from 8 to 256 against −1.0 ± 0.3); values out to 64 guessed about one and a half times too high; the landmark clause missed |
| G26 surprise autocorrelation | 0.15, 0.08, 0.05, 0.02, 0.01 at 1, 2, 4, 16, 64; rule: landmarks remain | 0.357, 0.205, 0.132, 0.056, 0.033 | rule held; every value guessed two to three times too low |
| G27 a pin's worth by quartile | gain 0.03, 0.30, 1.00, 2.30; share falling from 0.8 to 0.5 | gain 0.492, 0.819, 1.243, 1.685; share flat near 0.4 | missed; the identity held at every place |

## 5. What follows for the machine

1. **The grip.** A written letter re-bases the frame of the next (2.6). A moment that advances by a fixed stride reads only pair terms, so the contact's product has to carry along its own circle. That ruling is in the grip record, with its amendment of 00:22 UTC on November 11: the carry runs to its stop inside one tick with a stride chart of its own (its §8). The built field's turned heads already advance at class rates (`tower.field-pace`), so the fixed stride is the plain clock's case and not a description of the built field.
2. **The lack is composition within reach, before reach.** The passage has no one reach (3.2): pairwise information falls as a power law and is 0.06 nats at eight places and 0.02 at sixteen. The joint term of the nearest four letters is 0.48 to 1.04 nats (the grip record). So the carried contact comes first. Reach is second and slow: the surprise that stays correlated at 64 and 256 places is a variable of the passage that no local reader holds, and a coarser level of the tower is what would hold it. A lens of 23:49 UTC put that coarser grain at the unit: contexts that end at unit boundaries read 1.05 nats at four levels where four letters read 1.25 (the grip record §8.2).
3. **Reach on a chain is linear.** A site's mates are its neighbours, so the cover of the field's moves has growth 1, and `K` ticks reach `K` places each side (`contact.pass-reach-gap`). The count's floor says a reach that grows as a power of the ticks needs moves of longer stride, as the wheel's inversion is to its step. This is stated as the bound it is; no stride is ordered here. The scan of the grip record §8.4 is such a move: its reach in one tick is a unit's length.
4. **A lock's worth is bounded by its surprise** (2.7), and reads near four tenths of it on the passage, flat across quartiles. A site that is certain passes nothing to its neighbours when it is locked. This is the measure under the standing ruling that locking the most certain site first is wrong.
5. **Read a gap against the cover, never against the degree.** The wheel is within 2% of its floor while its plain gap ceiling is 15 times loose. A reading of the field's mixing has to name the cover of the field's own moves and its radius.
6. **One potential is a lower bound.** The straight route descends one potential and is the shortest for 46% to 66% of states; a twentieth of the states hold a sixth of its cost. A release that descends one reading has that shape, and the tail is where a second landmark cuts.

**G31, fixed in this record at 23:46 UTC.** The field's own surprise on HELD128, place by place, correlates with itself at `k = 64` by 0.03 or more and at `k = 256` by 0.02 or more: the field holds no variable slower than its ticks reach. Under 0.015 at both: it holds one.

**Read at 00:15 UTC on November 11** by theory, from design's locked visits of the states ct8 and rt4 (the grip record §8.2, `cap_r.py`): 0.031 and 0.029 at `k = 64` (5.8 and 5.4 standard errors) and 0.014 and 0.016 at `k = 256` (1.8 and 2.2). The guess held at 64 on ct8, fell 0.001 short on rt4 and missed at 256. By its rule G31 is undecided. The clearer reading is at short range: the field's surprise is more clustered than the count law's of two letters each side (0.30 against 0.21 at two places), so its misses come in runs about a unit long.

## 6. What does not transfer

- Distance tables, pattern databases and solvers. Each is a table addressed by a state with no balance of its own: a cache by the test of the guide. A landmark in the machine is a founded face whose column is carried by propagation.
- Any statement about a complexity class. The hardness results are worst-case; the chart prices typical routes on tempered terrains.
- Any attack. The isogeny terrain is read for the inference (nearness against findability, a known loop as a landmark), and nothing is built against a deployed scheme.
- The speed of light and a horizon as physics. Only the counting bound and the half transfer.
- The wheel's modes at five primes and the zeros' statistics are readings of an instrument. They are no evidence for RH or for Selberg's conjecture.
- The float fits of the cover's radius belong to the ruler.
- **Against the lessons.** Nothing here is thought as arrays or windows: the reach is a cover's growth, a landmark is a face, a stride is a move. No read is of the machine, so none is counted as progress.

## 7. Owed

- G31 is read (§5); nothing more is owed on it.
- Theory: the ruler of 2.9 on the passage's digits (locate the digit circle from counted transitions and read the gap).
- Theory: the cover's inner band edge (0.200) has no reading yet.
- Lean, for #410: `B†GB = qG` with `G ≻ 0` puts every eigenvalue on `|α|² = q`, as the equality case of the Floquet certificate; `p(y|c) ≥ p(x|c)·p(y|x, c)` and the bound on a pin's gain; `(A^(2m))_xy = ⟨Aᵐδ_x, Aᵐδ_y⟩` for symmetric `A`; the trace of two turns and `c = 1` for `S`, `U`.

## Receipts

Device: host rulers on the PC's VM (2 cores, 3.9 GB), no card and no learner run. The wheel at `p = 10,000,019` took 48 s and the straight route over all its states 18 s; each ran inside one call of at most 180 s. The passage rulers read private data, so only aggregate figures are published.

In `*_receipts/`: `README.md` lists every file.
