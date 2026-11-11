# A deposit's rate is a temperature: its standing spread costs a quarter of the step times the noise whatever the stiffness, a mean of states sheds it, and lap ends are draws that do not remember each other

Status (2026-11-11, 13:11 UTC): derived, and measured on the PC's card and host. The deposit is a linear diffusion, and its standing spread costs a quarter of the step times the noise (two Lean theorems); the section lines print half that cost. Each part of G58 to G67 and of the scan line's G30' and G46 is scored here. Held: the rise of a raised line is its spread, the bound on its price, lap ends as draws that do not remember each other, the saving of a mean of states, the fall inside a raised lap. Missed: my sizes for what a lap's mean sheds (it sheds nearly the whole spread the held code sees), for the scan line's spread, for where the opening's draw sits, and the carry's passing of a third and fourth letter. Decided: a line's level is read at its lap's mean (the rate line stands at 1.7341 nats a place at lap 12, where its lap end read 1.7420); a raised rate is rent on a read (one pair of laps: the raised lap's mean stands 0.0009 under the floor lap's, its lap end 0.0041 above); the rate rule is rebuilt on means; the carry as built gives a term of three sites, worth 0.005 to 0.007 nats a place, and its founding is the next loop's subject. Fixed and unread at close: G68 to G71. Refs #73, #405, #410.

Every guess was fixed with its clock time before its read; the file is in the receipts of the record of the places (`guess_capacity_44_55.txt`, G58 to G67, with the scores of G30' and G46, which were fixed in the two earlier files it names). Machine numbers are integers of the saved states and of the logs' lines; ratios are theirs, released to the digits shown.

## 1. The objects

- **The deposit** ([`tower.field-deposit`](../../docs/atlas/objects.tsv)): at each section the learner steps entry `i` of the constitution by `2^-rate · m_i / s_i`, with `m_i` the covector's first moment (it moves an eighth of the way to each section's covector) and `s_i` the root of its second moment. A part's rate is the base rate times `2^octave` ([`tower.field-part-rates`](../../docs/atlas/objects.tsv)); the floor is octave 0.
- **A lap** is the cycle the passage makes: 1,535 sections, each lap drawing its own paths and masks from its lap count. Two laps with one lap count read the same sections in the same order with the same regions, so their section lines pair.
- **A section line** of the trainer prints, among others, `before` (the section's code on the constitution that stands, before its own step), `predicted` (minus `Σ g_i s_i` for the step it takes) and `external` (the same for the step its moments held before the section's covector moved them).
- **The lap cosine** ([`deposition.lap-cosine-drift-over-noise`](../../docs/atlas/objects.tsv)): the cosine of two successive laps' travels of a part. The part rule moved a part's octave on it; the trend rule moved it on the cosine's trend.
- **A linear diffusion** ([`heat.linear-diffusion-turn-boost`](../../docs/atlas/physics.tsv); Lean `Physics/Thermal/LinearDiffusion`): a drift `A`, a noise covariance rate `D`, and the stationary covariance `Σ` with `A Σ + Σ Aᵀ + D = 0`. The atlas held this law with no consumer in the machine. The deposit is its instance (§2).

## 2. The derivation: a rate is a temperature

[derivation; agent-inferred; quadratic well, first order in the step] Near a rest position `θ*` the code is `½ (θ − θ*)ᵀ H (θ − θ*)` above its floor, with `H` the stiffness, and a section's covector is `H (θ − θ*) + ξ` with the noise `ξ` of covariance `C` (sections draw their own regions). The deposit steps by `P = diag(2^-rate / s_i)`: `θ' = θ − P (H (θ − θ*) + ξ)`. To first order in `P` that is the linear diffusion with `A = −P H` and `D = P C P`.

1. **The standing energy.** `P H Σ + Σ H P = P C P`. Multiply by `P⁻¹` on the left and take the trace: `2 tr(H Σ) = tr(C P)`. The mean code above the rest position is `½ tr(H Σ) = ¼ tr(P C)`, whatever `H` is. With `C_ii = s_i²` (at rest the second moment is the noise's) each entry costs `2^-rate · s_i / 4`. The stiffness sets how fast a direction relaxes (`P H`) and has left what it holds at rest. Lean: `two_mul_trace_stiffness_covariance`.
2. **Half a step in every direction.** Where the noise is the stiffness, `C = H`, the covariance `Σ = ½ P` is stationary: every entry stands at half its own step, uncorrelated with the others, and the drift has no turn (the spread is in detailed balance: it is heat and carries no current). Lean: `stationary_half_step_of_noise_eq_stiffness`. `C = H` is the information equality of a code read at its own law. The field's code is read off its law, so this clause is the form of the statement and no reading of the machine; how far the covectors' covariance stands from the curvature is unread.
3. **What the section lines print.** A section's covector `g` moves the first moment an eighth of the way, `m' = (7/8) m + g/8`, and the entry steps by `2^-rate · m'_i / s_i`. The line's `predicted` is `−Σ g_i` times that step and its `external` is `−Σ g_i · 2^-rate m_i / s_i`, the same for the moment before the covector moved it. So `N = (7/8)·external − predicted = Σ_i 2^-rate g_i² / (8 s_i)` a site, and its mean over a lap is `Σ_i 2^-rate s_i / 8`: half the standing cost of item 1. **The bound on a rate's standing cost is `2N`, read from the logs with no state opened.**
4. **Thermal names.** In the chart of [`wave.cayley-push-einstein`](../../docs/atlas/physics.tsv) (`D = 2 k_BT R`) entry `i` is held at `k_BT_i = 2^-rate s_i / 2` and stores `½ k_BT_i`. A rate is a temperature; a part's octave multiplies it.
5. **What the derivation does not carry.** The second order in the step adds `½ tr(H Σ H P)` to `tr(H Σ)` (the step is finite). The first moment's memory changes how the spread is made and leaves its size at first order. A direction that has not relaxed holds less than its share. A well that is not quadratic moves the mean of the spread off the rest position at second order in the temperature.

6. **A rate is a window.** [derivation; agent-inferred; the information equality in the trace, sites unrelated] An estimate of `d` entries from `n` sites whose code is read at its own law stands at best `d/(2n)` nats a site above the rest position (the chart is the Cramér–Rao bound of statistics; on the objects it is the least excess of a constitution deposited from covectors that reached it in one window). The standing spread of item 1, `¼ tr(P C)`, is `¼ tr(P H)` under that equality, and its ratio to `d/(2n)` is half the window's sections times the mean over entries of `P_ii H_ii`, the mean relaxation rate. So the spread in units of `d/(2n)` counts relaxations: an entry at step `P_ii` against a stiffness `H_ii` holds an estimate from its last `2/(P_ii H_ii)` sections. Raising a rate shortens the window an entry reads through; a mean of states over a lap lengthens it to the lap for every direction that relaxes inside the lap, and leaves the slower directions with the longer windows they already had. What stays behind in the discipline: an estimator chosen for a fixed law. Here the rest position moves, because the other parts deposit, and a window is paid for in the lag behind it.

So a raised rate costs a standing spread in proportion to the rate, and what it buys is speed along each direction, `P H`. The spread is a property of the state under its rates: it is in place as soon as the fast directions relax and gone as soon after the rate falls. It is rent paid at a read, and no debt on the position.

## 3. The readings

The lines of every read are in the receipts; the whole outputs stay on the PC with their sha256 prefixes in the guess file. Three lines of laps are read: the rate line (`rt4` to `rt12`: the part-rate laps, every part at the floor from lap 10), the trend line (`tr1`, `tr2`, `tr3`, trained from the rate line's ninth state under the trend rule) and the scan line (`gc1` to `gc3`, with the carry's chart). A trend lap is paired with the rate line's lap of the same lap count.

### 3.1 The trend line's rise is the spread (G58, scored 09:47 UTC)

The trend rule had raised the second lane's letter rows to 16 and then 32 times the floor, and the line's held joint rose: 1.744261 and 1.747719 nats a place beside the rate line's 1.742788 and 1.742148. Two readings were on offer: a fit to the passage (the trained sections' code falls while the held code rises) and temperature (both rise). I guessed the passage. The section lines read the other sign, weighted by sites, in bits a site:

| pair | trend lap | rate lap | excess | sections above, of 1,535 |
|---|---|---|---|---|
| `tr1`, `rt10` | 3.246464 | 3.243339 | +0.003125 | 1,220 |
| `tr2`, `rt11` | 3.246599 | 3.239652 | +0.006947 | 1,388 |

MISSED; temperature read. A lap draws its own paths and masks, so no fit to the passage was on offer in the form I guessed.

### 3.2 The steady travel is across the block, and the second lane is charging along itself (G59, scored 10:10 UTC)

Every read of a face goes through the lane chart, a ratio to the lane's own power, so the code does not change when everything written into a lane's face is scaled by one factor and the lift's rows of that lane by its inverse. I guessed that the letter rows' steady travel (lap cosines of 0.29 to 0.36 at the floor) ran along that scale. `tools/state_travel.py scale` read it across the block: the cosine of a lap's travel with the block it left is 0.10 to 0.20 where 0.35 to 0.75 was guessed, and the lap cosine with each travel's component along its block removed is 0.315 beside the plain 0.330. MISSED. The pooled writes and lifts of the second lane move the same way, so nothing slides along the lane's scale.

What the read showed beside the guess: the second lane's forms stand at 0.14 to 0.23 of the first lane's, and its key, value and probe charts lengthen 18 to 24 parts in a thousand a lap at the floor, its lift's rows 15 to 18, its out rows 11 to 13. The lengthening is first order in the rate (the value chart reads 71 at four times the rate and 110 at eight). The first lane's blocks move under one part in a thousand.

### 3.3 The spread is in place within a hundredth of a lap, and the letter rows bought no fall (G60, scored 10:17 UTC)

The paired excess of the trained code, by twentieths of the lap. Guessed: in place within the first fifth of `tr1`, and flat after. Read: the first twentieth already holds 0.94 of the lap's mean excess; by eights of sections from the lap's start the excess reads +0.0009, +0.0006, +0.0041, +0.0044 bits. **The spread of a sixteen-fold rate is in place within 16 to 24 sections.** The first half of the guess MISSED on the fast side. After the rise the line fitted to the excess has slope +0.000343 bits a lap (standard error 0.000422) on `tr1` and -0.000638 (0.000512) on `tr2`: flat, HELD. The letter rows took a spread and bought no fall that the trained sections see.

The scan pairs by the same read fall inside the lap: `gc1` less `rt5` by 0.008120 bits a lap (0.000335), `gc2` less `rt6` by 0.002347 (0.000422), `gc3` less `rt7` by 0.003243 (0.000513). The carry's gain is made section after section.

### 3.4 The price, from the logs alone (premise read, 10:34 UTC; G63 part (d), 11:20 UTC)

Lap means of `N` over the 1,535 sections, in millionths of a bit a site, and the paired excess of the trained code over twice the paired excess of `N` (plain means over sections on both sides):

| pair | `N`, trend lap | `N`, rate lap | twice the excess of `N` | excess of the code | ratio |
|---|---|---|---|---|---|
| `tr1`, `rt10` | 6,861 | 4,822 | 4,078 | 3,008 | 0.738 |
| `tr2`, `rt11` | 9,358 | 4,673 | 9,372 | 6,747 | 0.720 |
| `tr3`, `rt12` | 11,948 | 4,757 | 14,384 (292) | 10,648 (184) | 0.740 |

The third pair was guessed before its read (0.68 to 0.82): HELD. With no number fitted, the standing cost of a rate is 0.72 to 0.74 of `2N` at three sets of rates. The premise read first quoted 0.77 and 0.74; those divided a site-weighted excess by a plain one (corrected in the guess file at 11:44 UTC). Why the ratio stands a quarter under one, and the same at three sets of rates, is unread; §2 item 5 names the candidates, and each trend pair also holds a difference of rest positions of unknown sign.

At the floor `2N` reads 9,345 to 9,644 millionths. At 0.73 of it the rate line's state stands about 6,900 millionths of a bit a site, 0.0048 nats, above its rest position, if the old entries rest as the raised parts did. The line's own fall is 0.0002 to 0.0006 nats a lap.

### 3.5 The heat is where the travel reverses (G61, scored 10:57 UTC)

The deposit's step gives every entry's noise one size, so an entry whose covector is small and of one sign travels as far as any, and the plain lap cosine counts entries where the code weighs them. `tools/state_travel.py weighed` reads the lap cosine with each entry's product weighed by the root of its second moment, the heat `2^-rate σ_i / 4` summed by block, and the first-order fall of the code along the travel two laps share. I guessed that the letter rows' steady travel sat in entries of small covectors (a weighed cosine under 0.08). Read: 0.264 to 0.348 weighed beside 0.293 to 0.361 plain. MISSED in all six, and in the two parts that followed from it. The letter rows' steady travel is in the entries that carry the code, and at the raised rates it still bought nothing: the first-order account of the floor, 87 millionths of a bit a lap, times the twelvefold travel is 0.00105 bits a lap, where §3.3 read +0.0003 (0.0004).

The ruler's total heat reads 9 to 12 hundredths over the logs' `2N`. So a heat is quoted from the logs, and the ruler gives the shares between blocks. Shares of the heat at the floor (lap 11), with the weighed cosines of the last three pairs of laps:

| block | hundredths of the heat | weighed lap cosine |
|---|---|---|
| second lane, old contacts' columns of `W` | 9.0 | -0.10, -0.11, -0.22 |
| second lane, read rows | 8.3 | -0.06, -0.13, -0.14 |
| first lane, read rows | 8.0 | -0.02, -0.10, -0.12 |
| second lane, out rows | 7.0 | -0.09, -0.08, -0.11 |
| second lane, old `b` rows | 6.6 | -0.22 each |
| second lane, old `a` rows | 4.9 | -0.28, -0.28, -0.34 |
| both lanes' letter rows | 3.5 | 0.26 to 0.50 |
| value, probe and key charts | 13.7 | 0.01 to 0.26 |

Blocks whose weighed cosine is under zero hold 0.60, 0.69 and 0.66 of the heat on the three pairs. Where the plain and the weighed cosine differ in sign (the second lane's out rows, the moment charts), the entries of small covectors travel in common and the entries that carry the code reverse.

### 3.6 Lap ends do not remember each other, and a third of the travel neither reverses nor repeats (G63, scored 11:20 UTC)

A block at rest about a fixed position whose lap ends are related by `r` reads a lap cosine of `-(1 - r)/2`. At 10:57 UTC I read the reversing blocks' cosines (-0.10 to -0.34) as a memory of one to four laps. The premise, read before the guess, said otherwise: a block's entry steps by at most `2^12` units a section, a free travel of 160,480 units a lap, and the six blocks covered 0.08 to 0.27 of that in the square, which is a relaxation of 0.08 to 0.28 lap and a lap-end memory under 0.03. With no memory, the cosine two and three laps apart is the drift's share and stands above zero; with a memory it stands under. Read, weighed cosines of the six blocks:

| block | one lap apart (mean of the last three) | two laps apart | three laps apart |
|---|---|---|---|
| second lane, old `a` rows | -0.301 | -0.038, +0.027 | +0.065 |
| second lane, old `b` rows | -0.219 | +0.024, +0.021 | +0.138 |
| second lane, old columns of `W` | -0.141 | +0.154, +0.100 | +0.152 |
| second lane, out rows | -0.091 | +0.107, +0.111 | +0.163 |
| first lane, read rows | -0.082 | +0.196, +0.209 | +0.179 |
| second lane, read rows | -0.109 | +0.164, +0.156 | +0.190 |

Eleven of twelve two-lap readings are above zero: HELD. **Lap ends are draws that do not remember each other.** The sizes MISSED: I gave the travel two parts (draws about a position, and the position's steady drift) and each two-lap cosine reads 0.07 to 0.17 under what two parts give. A third part is needed, travel that neither reverses nor repeats. In shares of the squared weighed travel, in the table's order: drift 0.02, 0.06, 0.14, 0.13, 0.20, 0.17; reversed 0.64, 0.56, 0.55, 0.44, 0.55, 0.56; neither 0.34, 0.38, 0.31, 0.44, 0.25, 0.27. Three numbers fit three shares, so this is a description and no test. It excludes a drift whose direction turns over laps, which would read lower at three laps than at two. Whether the third part costs code is unread. Over laps 5 to 12 the drift's share of these blocks has been fading while their spread stays.

### 3.7 The trend line's third lap fell inside its lap (unguessed; one lap)

From the lines of §3.4: the paired excess of `tr3` over `rt12` falls through the lap, with slope -0.003301 bits a lap (0.000705) on twentieths 3 to 20, where trend laps 1 and 2 read -0.000064 (0.000352) and -0.000638 (0.000512). The held joints agree in their own unit: `tr2` to `tr3` fell 0.002377 nats a place where `rt11` to `rt12` fell 0.000198. Lap 3 is the lap at which the second lane's key, value, probe, out and moment charts ran at octaves 2, 4, 2, 2, 2. The line fell about eleven times faster than the rate line while standing 0.0034 nats above it by its spread.

So the decision drawn from §3.3, "a part's rate only falls", was drawn too wide. It stands for the parts trend laps 1 and 2 raised, the letter rows. No guess was fixed on this reading, so it ordered a guess (G64, §5) and no law.

## 4. The mean of states (G62)

`tools/state_travel.py mean` writes a ruler's state: the head of one saved state with its material replaced by the mean, entry by entry, of several states' materials. A held read of it is the lap's own opening read run alone (a lap count of 0: nothing trains, no state is written), about 12 s of card. The controls printed their lap lines' figures (`rt12`, `rt11`, `rt10`, `gc3`). Held joint, nats a place:

| state read | held joint | under the last state's own |
|---|---|---|
| `rt12` (control) | 1.741950 | |
| mean of `rt11`, `rt12` | 1.739429 | 0.002521 |
| mean of `rt10`, `rt11`, `rt12` | 1.738277 | 0.003673 |
| mean of `rt9` to `rt12` | 1.738286 | 0.003664 |
| `gc3` (control) | 1.744995 | |
| mean of `gc2`, `gc3` | 1.739699 | 0.005296 |

Guessed: the three-state mean 0.0010 to 0.0040 under (0.0020), HELD at the band's upper end, and under each of its three states, HELD; the two-state mean 0.0005 to 0.0030 under (0.0013), HELD; the scan line's 0.0000 to 0.0030 under (0.0010), MISSED on the large side.

**What the reads measure.** Where the code curves, the mean of `n` states codes under the mean of their `n` codes by `Σ_{i<j} q_ij / (2n²)`, with `q_ij = (θ_i − θ_j)ᵀ H (θ_i − θ_j)` the code's curvature along the travel between two states. Two states read `q/8`: `q(rt11, rt12) = 0.02096` nats a place. Three read the sum of three `q` over 18, 0.07233, so the two-lap `q` is 1.45 times a one-lap `q`. Draws about one position with no memory give 1 (and `q` is then four times the spread's cost: 0.0052 nats a place); a wander gives 2 and a steady drift 4. So by the curvature's own metric about 0.7 of a lap's squared travel reverses, where the ruler's metric read 0.44 to 0.64 in the six blocks: the stiff directions are the ones that reverse. The scan line's `q(gc2, gc3)` is 0.0403, twice the rate line's.

**A line's level is its rest position's code, and the held joint of a lap's end state is one draw about it.** A lap-end state of the rate line stands about 0.005 nats a place above its rest position, and the scan line's about twice that. Every comparison of two lines made on lap-end states carries each state's own spread.

**The other columns** (no guess was fixed on them). The foil's code falls with the own (the three-state mean: foil 0.004654 under the states' mean foil, own 0.004018 under their mean own), and the information a place is the states' mean less 0.0006. A mean of states sheds a blur that every read carries and adds nothing to what the question gives. The answer's opening code (every answer site unresolved at once) does not curve between these two close states: the two-state mean reads 5.568071 bits a byte beside the two states' mean 5.569221. Between states that stand further apart it curves (§5.5).

**The opening code and the information follow the lap count, with no trend over laps** (from the lap logs; no guess was fixed). Lines that share a lap count end their lap on the same sections, in the same order with the same regions, and their lap-end states read alike in these two columns whatever their rates:

| lap count | opening code, bits a byte | information, nats a place | own joint, nats a place |
|---|---|---|---|
| 5 | rate 5.251122, scan 5.229268 | 0.125128, 0.124475 | 1.754398, 1.747693 |
| 6 | rate 5.767364, scan 5.762134 | 0.129221, 0.129238 | 1.752441, 1.744468 |
| 7 | rate 5.707546, scan 5.743791 | 0.131345, 0.129672 | 1.750560, 1.744995 |
| 8 | rate 5.512970, scan 5.595934 | 0.132695, 0.134964 | 1.745851, 1.744382 |
| 9 | rate 5.761700 | 0.127082 | 1.747237 |
| 10 | rate 5.743272, trend 5.723381 | 0.129138, 0.128900 | 1.742788, 1.744261 |
| 11 | rate 5.601820, trend 5.656959 | 0.130390, 0.132718 | 1.742148, 1.747719 |
| 12 | rate 5.536622, trend 5.609712 | 0.132123, 0.133385 | 1.741950, 1.745342 |

The opening code swings by up to half a bit a byte from one lap end to the next (5.251122 to 5.767364 across lap 6) and the two lines at one lap count stand within 0.09 of each other. Between close states it is first order in the state where the joint is second (§5.5 and §5.7), so it reads where the lap's last sections left the state: a draw of the lap's end, shared by every line that walks the same sections. The own joint and the context code are smooth over laps and carry each line's own level. A fall of the opening code read off three lap ends (`rt10` to `rt12`) is withdrawn (§7).

## 5. The lap's mean as a reading of the trainer, the pair of laps, and the scan line (G64 to G67, G30', G46)

### 5.1 The reading, and its entry into the rate line

`MaterialMean` ([`tower.field-lap-mean`](../../docs/atlas/objects.tsv)) adds the material after each section's deposit and, at the lap's end, writes the mean, entry by entry, as a learner's text beside the lap's state (`MEAN.{lap}`: the state's moments and rates, the material at the mean). It is a reading: no deposit reads it, and the lap's state has the same bytes with it. On the objects it is the constitution viewed at the lap's clock (`view(receiver, grain, clock)`), the scale restriction of the constitution along the passage, and no second store.

The build entered the rate line by reproducing its lap 12 (the rule of November 11): from the state the line handed to lap 12, with that lap's own command, every one of the 1,535 section lines equals the line's (the three times aside), the held joint is the line's 1.741950 nats a place, and the saved state's material and both moments' lines are the line's byte for byte. One line of the saved text is wider: the line's binary wrote fifteen part octaves and `main`'s writes sixteen, the sixteenth the carry chart's, zero on a state with no carry chart; `main`'s reader takes a fifteen-count line by position, and the two commits name the first fifteen parts alike. The compare reads that line by named octaves (`gate12_compare.txt`). The lap's line `FIELD_MEAN states=1535 entries=63606 moved=61460 square=98777612556136` puts the mean 39,408 units a root-mean-square entry from the lap's end.

A state the trainer of `main` writes carries the sixteen-count line, which the rate line's older binary refuses. The means and the pair's states are therefore read by the build that wrote them, after it printed the line's own figure from the line's own state.

### 5.2 The pair of laps (G64, scored 12:43 UTC)

Two laps from the rate line's twelfth state, both drawing lap 13's paths and masks: `rt13` at the floor, and `wm13` with the second lane's key, value, probe, out and moment-face parts at octaves 2, 4, 2, 2, 2 (the octaves trend lap 3 ran them at), every other part at the floor. The state the tool wrote for `wm13` was checked before the lap trained from it: its parts line is the only line that differs from the state `rt13` trained from. Paired by walk position, in millionths of a bit a site:

| | guessed | read |
|---|---|---|
| twice the paired excess of `N` over the lap | 7,500 to 9,500 (8,500) | 8,716 (383): HELD |
| excess of the trained code over twice the excess of `N`, twentieths 2 and 3 | 0.65 to 0.85 (0.75) | 0.864 (0.061): MISSED high, inside a standard error of the edge |
| the same over the whole lap | | 0.969 (0.046) |
| slope of the excess on twentieths 3 to 20, bits a lap | -0.0010 to -0.0040 (-0.0020) | -0.002025 (0.000594): HELD |

**The price is by part.** This pair begins with no difference of rest positions, and the spread of these five parts costs 0.86 to 0.97 of `2N`: the first order of §2 with nothing taken off. The first trend pair was as clean (both laps trained from the rate line's ninth state) and read 0.738 with the letter rows raised sixteen-fold, the lane's face biases eightfold and of these maps only the value chart, fourfold. So the letter rows pay under the bound. They are the blocks whose travel repeats lap after lap (lap cosines of 0.26 to 0.50): a share of the squared covector that `N` counts there is drift, and drift is no spread. That is §2 item 5's clause, now placed.

**A raised rate on the second lane's maps buys a fall on a start two laps share.** Inside the lap the raised lap gains 0.0020 bits a lap on the floor's lap, the figure guessed from trend laps 2 and 3. The spread arrives as before (the excess by eights of sections from the start: 1.4, 6.8, 10.1, 9.4 thousandths of a bit).

> **Withdrawn the same day** ([the follow-up record](2026-11-11_THE_RATE_LINE_STOPS_AT_ITS_REST_THE_ADDED_CONTACTS_CLOSE_A_PLACE_BETWEEN_ITS_WRITTEN_NEIGHBOURS_AND_THE_THIRD_LETTER_IS_OWED_A_CARRY_FOUNDED_AS_A_TURN.md) §2): the slope inside a raised lap is the raised parts' rent falling as their charts lengthen toward a rest length, and no fall of the level. At lap means the raised line led the old rate by 0.00086, 0.00032 and 0.00008 over three laps, and the pair ended.

### 5.3 A lap's mean sheds nearly the whole spread the held code sees (G65 (a), (b), (d), (f); scored 12:47 and 12:53 UTC)

Held reads with a lap count of 0, by the build that wrote the states, after its control printed each lap's own line. Joints and information in nats a place, the opening in bits a byte:

| lap | rates | lap end: joint, opening, information | lap's mean: joint, opening, information | end less mean, joint |
|---|---|---|---|---|
| 12 | floor | 1.741950, 5.536622, 0.132123 | 1.734148, 5.579052, 0.131351 | 0.007802 |
| 13 (`rt13`) | floor | 1.738791, 5.735918, 0.136095 | 1.733318, 5.500395, 0.131060 | 0.005473 |
| 13 (`wm13`) | five parts raised | 1.742902, 5.701424, 0.133885 | 1.732455, 5.437908, 0.131663 | 0.010447 |

Guessed: lap 12's mean 0.0022 to 0.0046 under its end (0.0034), MISSED at more than twice the guess; within 0.0010 of the three-state mean's 1.738277, MISSED (0.004129 under it); `rt13`'s mean 0.0022 to 0.0046 under its end, MISSED; the raised lap's 0.0060 to 0.0110 under its end (0.0085), HELD; the opening and the information of lap 12's mean inside 5.52 to 5.70 and 0.1285 to 0.1320, HELD.

**The held code weighs a direction by its stiffness, and the stiff directions relax far inside a lap.** So a lap's 1,535 states are, for the held code, nearly as many separate draws, and their mean sheds nearly the whole spread; three lap ends shed two thirds of it. I had given the lap's mean a relaxation of 0.08 to 0.28 lap, the figure the travel gave for entries weighed evenly (§3.6), and so made it worth three or four lap ends. In figures: three lap ends that do not remember each other and save 0.0040 under their mean code put the whole spread at 0.0060; lap 12's mean stands 0.0081 under the mean of the last three lap ends. The 0.002 between is unplaced (the lap's mean is centred half a lap later, worth 0.0002 to 0.0003 at the line's fall; a lap end may stand off its lap's centre in a way laps share; the held code need not be quadratic over a lap's spread).

**The mean is the steadier figure and the lower.** Two floor laps' means stand 0.00083 apart where their ends stand 0.00316 apart. The foil's code falls further than the own at a mean (0.0086, 0.0105 and 0.0127 in the three rows, against 0.0078, 0.0055 and 0.0104), so the information a place at a mean is 0.1311 to 0.1317 in all three, inside 0.0006, where the three lap ends read 0.1321 to 0.1361: a lap end is sharper than its lap's mean on right and wrong answers alike, and the swing of the information from lap to lap (§4) is the lap end's draw. At means the opening is ordered: 5.579 at lap 12, 5.500 at lap 13, 5.438 on the raised lap.

### 5.4 The spread is rent and the fall is kept (G65 (e), scored 12:53 UTC)

The raised lap's mean less the floor lap's mean: -0.000863 nats a place (guessed -0.0020 to +0.0008, -0.0005, under zero: HELD). At their lap ends the raised lap stood 0.004111 above. The raised parts' spread is shed whole by the mean, and what the lap bought is kept: half a lap of §5.2's slope is 0.0007 nats a site on the trained sections, and the held answers read 0.0009. The information a place is 0.0006 higher on the raised lap's mean and its opening 0.062 bits a byte lower; the context and unseen codes agree to 0.001.

This is §2's closing sentence put to a read. It is one pair of laps on one walk: the size is one reading, and the sign rests on the pair sharing its walk and on §5.2's slope, 3.4 standard errors under zero. Whether the gain adds with a second raised lap is G68, fixed 13:07 UTC and unread when this record closed.

> **Withdrawn the same day** ([the follow-up record](2026-11-11_THE_RATE_LINE_STOPS_AT_ITS_REST_THE_ADDED_CONTACTS_CLOSE_A_PLACE_BETWEEN_ITS_WRITTEN_NEIGHBOURS_AND_THE_THIRD_LETTER_IS_OWED_A_CARRY_FOUNDED_AS_A_TURN.md) §2): what the first raised lap bought was not kept as a lead. The old rate took it back within two laps (G68, G72), so "the fall is kept" does not stand; "the spread is rent" does.

### 5.5 Means of two lap ends, and the scan line's level (G65 (c), G67; scored 12:11 and 12:45 UTC)

| mean of | held joint | under its two ends' mean code | `q` of the pair |
|---|---|---|---|
| `rt6`, `rt7` | 1.747044 | 0.004457 (guessed 0.0026 to 0.0050: HELD) | 0.0357 |
| `rt7`, `rt8` | 1.744201 | 0.004005 (guessed 0.0026 to 0.0054: HELD at the guess) | 0.0320 |
| `rt11`, `rt12` | 1.739429 | 0.002620 | 0.0210 |
| `gc2`, `gc3` | 1.739699 | 0.005033 | 0.0403 |
| `gc3`, `gc4` | 1.737390 | 0.007299 (guessed 0.0030 to 0.0060: MISSED large) | 0.0584 |

The line with the carry (`gc`, four laps from the rate line's fourth state) stands under the rate line by 0.0067, 0.0080, 0.0056 and 0.0015 at the lap ends of laps 5 to 8, and by 0.007345 (laps 6 and 7; guessed 0.0060 to 0.0100: HELD) and 0.006811 (laps 7 and 8; guessed 0.0020 to 0.0060: MISSED large) at means of two states. The lap ends' closing at lap 8 was the scan line's own wider draw: its lap ends stand further apart at each lap (`q` 0.040, then 0.058) while the rate line's draw in (0.036, 0.032, 0.021). A mean of two states leaves half a spread in, so the two lines' levels at lap means are unread; what is settled is that the carry holds 0.005 to 0.007 nats a place over the rate line from its first lap through its fourth.

The opening of a mean of two states stands under the two states' mean opening by 0.001 (`rt11`, `rt12`), 0.015 (`rt6`, `rt7`), 0.020 (`rt7`, `rt8`) and 0.101 bits a byte (`gc3`, `gc4`): the opening curves between states that stand far apart, and §4's sentence that it does not is true only of close ones (§7).

### 5.6 The carry's gate opened, and no letter past the second passes (G30', G46; scored 13:06 UTC)

The carry (`FieldDeclaration::carry`) is a scan inside one tick: `Q(t) = b(t) + γ(t) Q(t−1)`, read by the next site's contact as `p(t+1) = a(t+1) Q(t)`, with the gate `γ = g/√(1 + |g|²)` of a third chart `g = G r̂` founded at zero. G30' asked of four laps: the third letter back passing 0.21 nats or more of the place's code (0.169 before the carry), the fourth 0.06 or more (0.029), a held joint 0.02 under the rate line's, a mean gate of 0.08. G46 asked for the largest circle's gate (0.25, 0.12 to 0.45) and ruled: a circle at one half with the fourth letter at 0.06 says the scan founds groups; no circle at 0.2 says the gate has not opened and the third chart's rate is the next read.

| lap | the chart's octave | mean gate, tick 4 | largest circle | circles at 0.2 or more | first to fourth letter, nats | letters five to eight |
|---|---|---|---|---|---|---|
| `gc1` | 0 | 0.111 | 0.205 | 1 | 0.568, 0.458, 0.172, 0.032 | 0.038 |
| `gc2` | 0 | 0.153 | 0.286 | 10 | 0.561, 0.456, 0.175, 0.028 | 0.043 |
| `gc3` | 1 | 0.194 | 0.355 | 15 | 0.566, 0.459, 0.172, 0.030 | 0.038 |
| `gc4` | 2 | 0.238 | 0.425 | 16 | 0.564, 0.461, 0.175, 0.030 | 0.040 |

Scores: the third and fourth letters MISSED; letters five to eight HELD at 0.040 and not by the carry (0.038 at its first lap); the held joint MISSED (§5.5); the mean gate opened and MISSED high by three; the largest circle inside its band at the top on question sites (0.4255) and over it on open sites (0.4528); no circle at one half, HELD. Two reads stayed UNREAD: the locked code inside units (the ruler's cut was not run), and the gate at separators against word letters, because the gate's read prints two kinds of site, question and open, and no class of letters. G46's rule fires neither branch.

**The pull on the gate halved lap over lap while its rate doubled.** The rate rule raised the third chart from octave 0 to 1 to 2 (lap cosines 0.611, 0.535, then 0.341 and down), and the mean gate grew 0.0415, 0.0412, 0.0440 a lap all the same. In units of the base rate its travel was 0.111, 0.042, 0.021, 0.011. This was read from the logs before any guess on raising the chart's rate was fixed, and that order is refused on it.

**Why no letter passes** [derivation; agent-inferred]. A letter `d` sites back enters `Q` at the product of `d − 1` gates, and a weak channel's information goes as the square of its amplitude. At a mean gate of 0.24 the third letter's term weighs 0.057 in amplitude and 0.003 of a contact's information (the mean of `|γ|⁴` over circles is 0.0066): under 0.002 nats. G30's basis, that an open gate passes in proportion to its size, was wrong by a power. The first order of the scan, `γ(t) b(t−1)` read by `a(t+1)`, is a term of three sites; it is there from the first lap, and the scan's 0.005 to 0.007 nats a place has that term's age and does not grow as the gate doubles. Founded at zero, every unit longer than three sites stands behind a pull that is itself a product of gates not yet open, which is what a pull that halves each lap looks like.

Circles 16 to 31 hold 2.1 times the gate of circles 0 to 15 at every lap; which contacts those are is unread in the source.

> **Later the same day** ([the follow-up record](2026-11-11_THE_RATE_LINE_STOPS_AT_ITS_REST_THE_ADDED_CONTACTS_CLOSE_A_PLACE_BETWEEN_ITS_WRITTEN_NEIGHBOURS_AND_THE_THIRD_LETTER_IS_OWED_A_CARRY_FOUNDED_AS_A_TURN.md) §8.5): the derivation above stands. The gate is a function of its own site's read, so the scan's first order, `a(t+1) γ(t) b(t−1)`, is the place with its first and second letters together, inside the second letter's pass; the third letter waits behind two gates founded at zero. The gates are complex scalars and commute, which limits the fourth letter and beyond, not the third. The stride ruler `cap_o.py` is this move founded on the unit circle, and the next attempt founds the carry as a turn (that record's §9).

### 5.7 The opening's draw is in the matrices (G66, scored 12:53 UTC)

`tools/state_travel.py graft` writes a ruler's state: one state with some families of its material replaced by another's. Grafts of `rt5`'s families into `rt6` (the two lap ends whose openings stand furthest apart, 5.251122 and 5.767364 bits a byte), each read once; the controls printed their lap lines, and the five parts cover the material.

| part | entries | root-mean-square move | shift of the opening | share of -0.516242 | shift of the own joint |
|---|---|---|---|---|---|
| the classes' biases | 100 | 8.9 | +0.000961 | 0.00 | -0.000009 |
| the other biases | 576 | 61 | -0.096058 | 0.19 | -0.001031 |
| the letters' rows | 19,392 | 930 | +0.002185 | 0.00 | -0.000560 |
| the moment charts, the pace, the temper | 6,674 | 10,120 | +0.046537 | -0.09 | +0.000159 |
| the matrices | 36,864 | 99,783 | -0.502796 | 0.97 | +0.000194 |

Guessed: the five shifts add to within 0.10 of the whole, HELD (-0.549171); the classes' biases and the moment part carry 0.6 or more, MISSED with the sign against; no part over 0.7, MISSED; each graft moves the own joint by under 0.004, HELD, and their sum is above the two lap ends' difference, MISSED. The opening's draw is where the travel is, and the information a place moves with it (-0.004209 of -0.004093). The split of the matrices by family is G71, fixed 13:07 UTC and unread when this record closed.

## 6. What is decided

1. **A line's level, its opening code and its information are read at its lap's mean.** A lap end's read is that state's own and is one draw: at the floor it stands 0.0055 to 0.0078 nats a place above its lap's mean and scatters 0.003 from lap to lap, where the means of successive laps fell smoothly, 0.0003 to 0.0033 a lap over laps 13 to 17 ("two laps' means stand 0.0008 apart" was one pair and is withdrawn, [the follow-up record](2026-11-11_THE_RATE_LINE_STOPS_AT_ITS_REST_THE_ADDED_CONTACTS_CLOSE_A_PLACE_BETWEEN_ITS_WRITTEN_NEIGHBOURS_AND_THE_THIRD_LETTER_IS_OWED_A_CARRY_FOUNDED_AS_A_TURN.md) §2). The rate line's level at lap 12 is 1.7341 nats a place, where its lap end was quoted at 1.7420. Every held figure in the records of November 10 and 11 before this one is a lap end's. The guides carry the rule with this occasion.
2. **A raised rate is rent on a read and no debt on the position** (§2, §5.4), on one pair of laps. The second raised lap beside a second floor lap is G68. *Later the same day:* the rent stands, and the first lap's gain was not kept; the raised pair ended at its third lap ([the follow-up record](2026-11-11_THE_RATE_LINE_STOPS_AT_ITS_REST_THE_ADDED_CONTACTS_CLOSE_A_PLACE_BETWEEN_ITS_WRITTEN_NEIGHBOURS_AND_THE_THIRD_LETTER_IS_OWED_A_CARRY_FOUNDED_AS_A_TURN.md) §2).
3. **The rate rule is rebuilt on means.** The lap cosine at lap ends is held down by the ends' draws (`c = (d² − s²)/(d² + 2s²)` for a lap's travel `d` and end draws of variance `s²` that do not remember each other), which is why the part rule walked every part to the floor. What the cosine reads on means is G69. `tools/part_rates.py trend` is corrected to means or retired once G69 is read.
4. **The price of a raised rate is by part** (§5.2): 0.86 to 0.97 of `2N` on the second lane's maps, under it where a part's travel repeats. No card time is spent on the price by part, since the rule is rebuilt on means, where the price is shed.
5. **The carry as built gives a term of three sites and no more** (§5.5, §5.6): 0.005 to 0.007 nats a place from its first lap, with laps of 1,305 to 1,450 s where the rate line's take 800 to 870 s. Its acceptance failed on the third and fourth letters. The next loop for that law is its founding: a gate founded at zero puts every longer unit behind a product of gates not yet open. Its rate is not the subject, and no further scan lap is run on the built founding. *Later the same day* ([the follow-up record](2026-11-11_THE_RATE_LINE_STOPS_AT_ITS_REST_THE_ADDED_CONTACTS_CLOSE_A_PLACE_BETWEEN_ITS_WRITTEN_NEIGHBOURS_AND_THE_THIRD_LETTER_IS_OWED_A_CARRY_FOUNDED_AS_A_TURN.md) §9 item 4): the founding is a turn, on circles of the carry's own whose return is founded at zero, sized first by the stride ruler at 8 to 64 circles (G81).
6. **The release is read from a lap's mean** if G70 holds (fixed 13:07 UTC): the settle, the re-draw and the reference's locked read on `rt13`'s mean beside its end state. *G70 missed with the sign against* ([the follow-up record](2026-11-11_THE_RATE_LINE_STOPS_AT_ITS_REST_THE_ADDED_CONTACTS_CLOSE_A_PLACE_BETWEEN_ITS_WRITTEN_NEIGHBOURS_AND_THE_THIRD_LETTER_IS_OWED_A_CARRY_FOUNDED_AS_A_TURN.md) §4): the release's reads stay on a lap's end state.
7. **Owed.** The lap lines print the held read of the lap's mean (the reading's consumer; it enters by reproducing a lap). The gate's read by class of site (word letters, separators), which G30' and G46 asked for and the build does not print. Lean (#410): the saving of a mean of `n` states, `Σ_{i<j} q_ij / (2n²)` on a quadratic code (§4), and §2 item 6's ratio of the standing spread to `d/(2n)` under the information equality; both are stated here with their hypotheses and neither is proved in the library.

## 7. Withdrawn

Each of these was said by me in this thread or in the guess file on November 11 and does not stand.

- "The trend rule is void" and "a part's rate only falls", as statements about every part. They stand for the parts trend laps 1 and 2 raised, the letter rows (§3.3, §3.7).
- "The reversing blocks relax within about one to four laps", read from one-lap cosines at 10:57 UTC, and the band it gave for G62's first part (0.0004 to 0.0011). Lap ends do not remember each other (§3.6), and G62 read 0.0037.
- "A block's travel has two parts". Three (§3.6).
- "The standing cost is 0.77 and 0.74 of `2N`". Those divided a site-weighted excess by a plain one. With plain means on both sides: 0.738, 0.720, 0.740 (§3.4).
- "The opening code is falling 1.2 to 2.5 hundredths a lap along the rate line" and "the opening is not at rest", read off three lap ends. The opening code and the information a place follow the lap count across lines and have no trend over laps (§4).
- "A read at a lap's mean cannot stand under 0.0019 nats a site". The figure bounds the directions that relax inside the lap (§2 item 6).
- "A lap's mean should read about as a mean of three or four lap ends" and "it sheds 0.59 to 0.85". It sheds nearly the whole spread the held code sees (§5.3).
- "The standing cost is 0.72 to 0.74 of `2N`" as the price of any raised rate. The price is by part (§5.2).
- "The opening is linear in the state" and "the opening does not curve along a lap's travel". True of close states only (§5.5).
- "The scan line's advantage closed at lap 8". That was its wider draw at a lap end (§5.5).
- "The opening's draw is in the few entries every site reads". It is in the matrices (§5.7).
- "An open gate passes letters in proportion to its size", the basis of G30'. A letter `d` sites back enters at the product of `d − 1` gates (§5.6).
- The order to raise the third chart's rate, held in mind before the scan line's update lines were read. The rule had raised it already and the gate's growth did not follow (§5.6).

## 8. What was wrong in my bases

- G58: I took the rise of the held code for a fit to the passage. A lap draws its own paths and masks, so no lap reads a section twice and no such fit was on offer; the atlas held the diffusion's law (`heat.linear-diffusion-turn-boost`) with no consumer, and I had not grepped it for the deposit.
- G59: I placed the steady travel along the lane's scale because the code cannot see that scale. A direction the code cannot see receives no covector, so nothing is driven along it.
- G60, first half: I gave the spread a fifth of a lap to arrive. A sixteen-fold rate relaxes sixteen times faster.
- G61: I supposed the entries that travel steadily were the ones the code does not weigh. The second moment weighs an entry by the same covectors that move it.
- G63, sizes: two parts where three were needed; the third was in the lag rows the ruler did not yet print.
- G62: both parts that held read near twice my figure, because I discounted the saving for a memory that G63 then read as absent, and the scan line's part missed because I did not carry its longer travel into the guess.
- The opening code: a trend read off three points, against a table of every lap that the logs already printed. The rule of November 11 (read what the logs print about a premise before fixing a guess) covers a reading as it covers a guess.
- G64, the price: I took the first trend pair's ratio, read with the letter rows raised, for the second lane's maps.
- G65, the lap's mean: I weighed directions as the ruler does. The held code weighs them by stiffness, and G62 had already read that the stiff directions are the ones that reverse.
- G67: I gave the scan line a falling spread because the rate line's fell. Its update lines, which I had not read, were raising its hottest parts.
- G66: I placed the draw where every site reads, on the premise that the opening reads every site at once. The travel between two lap ends is in the matrices, a hundred times the letter rows' in the state's units.
- G30': proportion where the law gives a power.
- Clock labels: five entries of the guess file were labelled a minute or two ahead of the clock and were corrected in place, and three more after that rule was written. The label is now taken from the clock inside the command that writes it.

## 9. Receipts

The guess file: `guess_capacity_44_55.txt` in the receipts of [the record of the places](2026-11-11_THE_PLACES_THE_FIELD_GIVES_PUSH_AGAINST_THE_PLACES_IT_MISSES_THE_DEPOSIT_IS_THEIR_DIFFERENCE_AND_TWO_BUILDS_ARE_TIMED_ONLY_INSIDE_ONE_HOLD_OF_THE_CARD.md) (G58 to G67 with their scores; the scores of G30' and G46; G68 to G71 fixed and unread). In this record's receipts directory:

| file | holds |
|---|---|
| `g61_logs.txt`, `g61_part_rate_lines.txt` | the trend and rate lines' lap lines and part-rate updates (§3.1 to §3.5) |
| `weighed_pairs.txt`, `weighed_laps.txt`, `weighed_lag.txt` | the travel ruler's blocks, by pair of states, by lap and by lag (§3.2, §3.5, §3.6) |
| `g63d_lines.txt` | `N` and the paired excess by lap (§3.4) |
| `held_lap_lines.txt` | the held lines of every lap of the three lines (§4) |
| `g62_reads.txt` | the means of two, three and four lap ends (§4) |
| `gate12_compare.txt` | the lap that reproduces the rate line's lap 12 with the build that writes the lap's mean (§5.1) |
| `g64_lines.txt` | the pair of laps (§5.2) |
| `g65_reads.txt` | the lap means' held reads and the mean of `rt6`, `rt7` (§5.3 to §5.5) |
| `g67_reads.txt` | the means of `rt7`, `rt8` and of `gc3`, `gc4` (§5.5) |
| `scan_line_gate_and_release.txt` | the scan line's parts lines, part-rate updates, gate by circle, transmission by letter, lap times, and `gc4`'s release reads (§5.6) |
| `g66_reads.txt` | the grafts of `rt5`'s families into `rt6` (§5.7) |

Device: the PC's card (RTX 4080 SUPER) for every lap and every held read, each read under its own hold of the card lock; the travel ruler, the means and the grafts are host arithmetic on saved states. Laps: `mean-gate12` 872,189 ms, `rt13` 814,181 ms, `wm13` 802,588 ms, each its own run under the lap's bound of 1,215,000 ms (0.72, 0.67 and 0.66 of the bound). A held read takes 10 to 14 s. The build that writes the lap's mean passed `bash tools/gate.sh`, its field and trainer tests (90 and 26) and `bash tools/lean_check.sh` on the PC at f78184a22; `python3 -I tools/test_state_travel.py` holds its controls there and in the cloud clone.
