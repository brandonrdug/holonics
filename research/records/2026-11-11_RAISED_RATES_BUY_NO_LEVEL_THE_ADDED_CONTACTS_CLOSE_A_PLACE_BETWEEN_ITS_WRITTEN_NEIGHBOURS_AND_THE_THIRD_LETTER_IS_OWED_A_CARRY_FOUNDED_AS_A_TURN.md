# Raised rates buy no level: four times the travel buys nothing a lap's mean holds, the added contacts close a place between its written neighbours, and the third letter is owed a carry founded as a turn

Status (2026-11-11, 17:45 UTC): measured on the PC's card and host, and derived. G68 to G82 are scored here (their texts and scores are in `guess_capacity_44_55.txt` in the receipts of [the record of the places](2026-11-11_THE_PLACES_THE_FIELD_GIVES_PUSH_AGAINST_THE_PLACES_IT_MISSES_THE_DEPOSIT_IS_THEIR_DIFFERENCE_AND_TWO_BUILDS_ARE_TIMED_ONLY_INSIDE_ONE_HOLD_OF_THE_CARD.md)); G83 is fixed before its build. Held: the quarter floor of a free walk read at lap means (Lean), the three parts of a lap's travel, the travel that repeats held by the rate, the rents of hot laps at their second lap, the chain ruler as the count tables, what each written letter passes at the line's sixteenth lap mean, the stride ruler's codes and passes at 8 to 64 circles, lap 18's rent. Missed: the raised pair's second lead, the release read from a mean (the sign against), where the opening's draw sits, the hot line's level, the field's code where most of an answer is open, the cost of removing the added contacts, the ruler's gates at 8 and 16 circles, and lap 18's fall (eight times the guess). Decided: raised rates buy no level, so no rate is the subject, while the line still cools at its base rate (1.7248 nats a place at lap 18's mean, about 0.0013 a lap), so a build is scored against the line's laps run beside it; the release reads at lap ends; the added contacts carry the place's two-sided closure and not the third letter; the third letter's route is a carry founded as a turn, its gate charted as a turn and a friction apart (Lean), its first attempt at 16 circles a mate. Refs #73, #405, #408, #410.

This record continues [the heat record](2026-11-11_A_DEPOSITS_RATE_IS_A_TEMPERATURE_ITS_STANDING_SPREAD_IS_SHED_BY_A_MEAN_OF_STATES_AND_LAP_ENDS_ARE_DRAWS_THAT_DO_NOT_REMEMBER_EACH_OTHER.md) (a deposit's rate is a temperature; levels are read at lap means) and repairs it where today's reads overturned it (§10). Machine numbers are integers of the saved states and the logs' lines; ratios are theirs, released to the digits shown. Every guess was fixed with its clock time, taken inside the command that wrote it, before its read.

## 1. The objects

- **A lap's mean** ([`tower.field-lap-mean`](../../docs/atlas/objects.tsv)): the mean, entry by entry, of the material after each of a lap's 1,535 sections, written by the trainer as `MEAN.{lap}`. A line's level is its held joint read at that state (the rule of the record on a deposit's rate, which this record continues).
- **The floor** is the rate line with every founded part at octave 0 (`rt12` to `rt17` here). **The raised line** (`wm13` to `wm15`) trains the second lane's key, value, probe, out and moment-face charts at octaves 2, 4, 2, 2, 2. **The hot lines** (`hot1`, `hot2`) train every entry one and two octaves faster by the learner's rate word (11 and 10 bits beside the floor's 12).
- **A travel** is the difference of two successive lap means, entry by entry. Its **weighed product** with another travel is `Σ_i s_i d1_i d2_i 2^(rate − 32 − 2 grain)` a site, in millionths of a bit, with `s_i` the root of the entry's second moment: the first-order fall of the code that one travel makes along the drift the other read (`tools/state_travel.py weighed`). **Own** is a travel's product with itself; the product **one lap on** and **two laps on** pair it with the next travel and the one after.
- **A graft** (`tools/state_travel.py graft`) writes a ruler's state: one state's material with a named group of entries taken from another. It is read, and no lap trains from it.
- **The held joint** (`FIELD_JOINT_NATS`) is an order-averaged joint code of an answer: `K` of its `m` sites open, `K` uniform on `1..m` by quarters, each open site coded beside the written ones and weighed `m/K`. A law that is one joint law codes every order alike, so its order-averaged code is its left-to-right code less the code of what it is told (the answer's length).
- **The chain ruler** (`cap_t.py` in the receipts; a host instrument, never machinery): the count tables of `DEPTH` left letters read as one Markov chain, each open site coded by the chain's own conditional given every written letter on both sides, with the open letters summed out. Under the run's key it draws the field's own held states, so the two read the same open sites.
- **The transmission read** (`transmission-field`; the founded-parts record's script): the code at a place with only its `d` nearest answer letters written, the rest of the answer open and the question given.

## 2. The raised pair ends (G68, G72)

[measurement; lap means on the card, the lap-mean build; nats a place]

| Lap | Floor's mean | Raised line's mean | Floor less raised | Floor's end less its mean | Raised line's end less its mean |
| --- | --- | --- | --- | --- | --- |
| 12 | 1.734148 | | | 0.007802 | |
| 13 | 1.733318 | 1.732455 | 0.000863 | 0.005473 | 0.010447 |
| 14 | 1.729997 | 1.729678 | 0.000319 | 0.007483 | 0.013319 |
| 15 | 1.727989 | 1.727909 | 0.000080 | 0.005779 | 0.010042 |
| 16 | 1.726734 | | | 0.010691 | |
| 17 | 1.726466 | | | | |
| 18 | 1.724823 | | | 0.006559 | |

- **G68** guessed the second raised lap's lead at 0.0020 (0.0012 to 0.0030) from the first lap's 0.0009 read as the first step of a steady gain. It read 0.000319: missed. The floor's own mean fell 0.0033 in that lap where it had fallen 0.0008 the lap before (guessed 1.7323, read 1.729997: missed low), so "two laps' means stand 0.0008 apart" was one pair and no rule.
- **G72** guessed the raised line's third mean 0.0001 above the floor's (band: 0.0005 under to 0.0008 above) and rt15's mean at 1.7280: both held (0.000080 under; 1.727989). Its guess that the raised line's rent would go on growing (0.0145) missed low (0.010042): the three raised laps read 0.0104, 0.0133, 0.0100.
- **Rule and decision.** The lead stood between 0 and 0.0010 at lap 15, so it is what the first raised lap took, and the pair ended. The raised line stops at `wm15`; the floor ran on.
- **What the slope inside a raised lap was.** Inside laps 13 and 15 the raised line's sections read 0.0079 and 0.0072 bits a site above the floor's and that excess fell through the lap (−0.0020 and −0.0025 bits a lap). At lap means the raised line fell less than the floor over the same laps. So the slope is the raised parts' rent falling as their charts lengthen toward a rest length, and no fall of the level. The record on a deposit's rate read it as a fall that is kept (its §5.2 and §5.4); that reading is withdrawn (§10).

## 3. Between lap means a free walk reads a cosine of one quarter (G69, G73)

[measurement; `tools/part_rates.py update` and `tools/state_travel.py scale` on the host, lap means 12 to 14 beside the lap ends of the same laps]

| Part (floor line) | Lap cosine on means | On lap ends |
| --- | --- | --- |
| second lane's letter rows (enc, before, after) | 0.591, 0.586, 0.580 | 0.360, 0.361, 0.335 |
| value chart's lane | 0.536 | 0.249 |
| face biases | 0.796 | 0.333 |
| added contacts' a and b rows | 0.268, 0.280 | −0.050, −0.026 |
| added columns of W | 0.238 | −0.074 |

- **G69** guessed each of these 0.15 or more above its lap-end cosine: held for all eight (0.22 to 0.46 above), with the face biases above their band.
- **The rule on means has no rest position.** The raised line's means read the same cosines as the floor's at four and sixteen times the rate (the value chart 0.538 at octave 4 beside 0.536 at the floor). Between lap ends a raised rate lowers a part's cosine through its spread, which is what brought the lap-end rule to rest; a mean's cosine does not fall as the rate rises. A rate rule on these cosines would raise a lane an octave a lap without end. It is not run.

[derivation; agent-inferred; checked on drawn walks and proved on its weights in Lean] **The quarter floor.** A walk of free steps of variance `σ²` a lap, read at the means of its laps, has differences of successive lap means of variance `2σ²/3`, and two successive differences share `σ²/6`: the first half of a difference is the second half of the one before, weighed `i` and `n − i`. So the lap cosine between lap means is one quarter for a part that only diffuses, where between lap ends it is zero. With a travel `d` a lap that repeats beside the walk, `s = d²/(d² + 2σ²/3)` is the steady share of the squared travel between means, and the cosine is

```text
c = s + (1 − s)/4,   s = (4c − 1)/3      (lap means)        c_end = d²/(d² + σ²)      (lap ends)
```

- Lean: `Holonics.Physics.Thermal.LapMean` proves the weights (`6 Σ i(n − i) = n(n − 1)(n + 1)`, `6 (Σ i² + Σ (i + 1)²) = n(4n² + 2)`), that own is four times shared and `n` more, so the cosine `(n² − 1)/(4n² + 2)` stands under one quarter at every lap length, and `c = s + (1 − s)/4`. The reindexing from the walk to the weights is cited and owed in #410. Atlas: `deposition.lap-mean-quarter-floor`.
- **One number a block fits both readings.** The second lane's letter rows read 0.591, 0.586, 0.580 on means, which is `d²/σ²` = 0.556, 0.540, 0.523 and predicts 0.357, 0.351, 0.344 at lap ends (read 0.360, 0.361, 0.335), and a travel between lap ends 1.13 times the travel between means (read 1.11 to 1.16).
- **So G69's finding is this quarter plus what the mean sheds.** A cosine of one quarter on means is no travel at all: the added contacts' rows (0.24 to 0.28) are a free diffusion.
- **The scale read (G73; entered after its 0.37 s read came back, so it counts as unguessed).** On the floor the second lane's key, value and probe charts lengthen 18 parts in a thousand a lap, and their steady travel is that lengthening. Raised, the same charts travel 3 and 9 times as far between lap ends at 4 and 16 times the rate (the rate to the power 0.79) with the same cosines, and their lengthening falls lap over lap (the value chart 184, then 107 parts in a thousand). The first lane's travel and the second lane's letter rows are the same on both lines.

## 4. The release is read at a lap's end (G70)

[measurement; the settle, the re-draw, the charge and the reference's locked read on rt13's end state and on rt13's mean, one build]

- **G70** carried the held code's finding to the release: guessed the mean 0.0055 under on the keyed code and 0.010 under at the re-draw's end. Read: the mean stands **above** its lap end at every stage of the release (keyed code +0.036, rest +0.063, the re-draw's end +0.082), with entropy above both neighbouring lap ends at all three stages. Missed, the sign against.
- With everything given the mean reads better, as before: the held joint 0.0055 under its end, the reference's locked code 0.0062 under.
- **Reading.** The release opens the answer's sites and settles by exchange, and there a sharper face decides. The spread a lap end holds sharpens the faces on right and wrong letters alike: it is rent on a reading with everything given and gain on the release.
- **Rule.** The release's reads stay on the lap's end state. The lap-mean rule's scope (a held code, an opening code, an information a place) stands as written and does not reach the release.

## 5. The opening's draw is spread over the maps (G71)

[measurement; nine grafts of one family of rt5 into rt6, the opening read beside rt6's]

- The nine families together moved the opening −0.5028 bits a byte. Alone: the pair contact's a, b and W carry 0.17, 0.30, 0.23 of it (0.70 together; guessed 0.05: missed), out 0.30, read 0.19, and the moments' face 0.03 (guessed 0.30: missed). The nine shifts sum to 1.38 of what the nine did together: the families do not add.
- **What was wrong in the basis.** The open corner was placed in the moments' face because an open site holds no letter. The pair contact reads the face after the current, open or not.
- No family reaches 0.35, so no map is singled out.

## 6. What a lap's fall is made of (G75, G77, G74)

### 6.1 A travel is three parts (G77)

[measurement; `tools/state_travel.py weighed` on the host, with the products one, two and three laps on; millionths of a bit a site, 1,000 of them 0.00069 nats]

[derivation; agent-inferred] Take a block's travel as a travel that repeats, of worth `D` a lap, a walk of free steps of variance `V` a lap, and a draw of variance `R` at each lap end, of which a lap's mean keeps `R'`. Then

```text
lap ends:   own = D + V + 2R,        one lap on = D − R,           two laps on = D
lap means:  own = D + 2V/3 + 2R',    one lap on = D + V/6 − R',    two laps on = D
```

| Laps 13 to 15 | Own | One lap on | Two laps on | D | V | R or R' |
| --- | --- | --- | --- | --- | --- | --- |
| lap ends | 7,070 to 7,333 | −252 to −279 | 917 | 917 | 3,953 | 1,183 |
| lap means | 4,231 to 4,444 | 1,277 to 1,296 | 947 | 947 | 4,085 | 342 |

- The two readings of the walk agree within a thirtieth, with nothing fitted to make them.
- **The travel that repeats** is worth 920 to 950 a lap (0.00066 nats) and read 1,330 three laps before: it falls about a tenth a lap. Three laps on it reads what it reads two laps on, so it is one slow travel.
- **The walk** holds 4,000 a lap where every entry walking free would hold four times the heat, 42,900: a tenth of the deposit's noise goes into directions that no lap restores, and a lap's mean does not shed it.
- **G77** guessed the product two laps on at 300 (0 to 700) on the floor's means: missed high (946.8). Its guess of own held (4,232 to 4,444 against 4,300). Its part on training lines was unreadable: successive laps cut the passage into other sections, so two laps pair by section only at one lap count.
- **G75** had priced the fall from the product one lap on (1,296 and 1,277, 0.0009 nats a lap on both pairs of laps) and found it near the lap means' smaller falls. That agreement was an accident of two terms (`V/6 − R'` = 339).

### 6.2 A lap's travel is cooperative, and a part's worth is not read from its travel (G74)

[measurement; 116 held reads on the card of ruler states: for each of 22 groups that partition the 63,606 entries, the earlier lap mean with the group's entries from the later, and the later with the group's from the earlier]

A group's forward shift `f` is the earlier mean with the group grafted from the later, less the earlier; its reverse shift `r` is the later, less the later with the group grafted from the earlier; its worth is `(f + r)/2`.

[derivation; agent-inferred; second order in the travel] With `g` the covector at the earlier mean, `H` the stiffness, `Δ` the lap's travel and `Δ_g` the group's part of it,

```text
f_g = g·Δ_g + ½ Δ_g H Δ_g,     r_g = g·Δ_g + Δ_g H Δ − ½ Δ_g H Δ_g,     f_g − r_g = −Δ_g H (Δ − Δ_g)
```

so the worths sum to the whole, and forward less reverse is minus the group's travel paired through the stiffness with the others' travel: the group's **coupling**. The guess had named it the group's curvature.

| | Lap 14 | Lap 15 |
| --- | --- | --- |
| the whole fall | −0.003321 | −0.002008 |
| the worths' sum | −0.004144 | −0.002125 |
| the forward shifts' sum less the whole | +0.000594 | +0.003290 |
| share of the base-rate entries | 0.54 | 0.60 |
| share of the second lane's letter rows | 0.09 | 0.07 |
| share of the five raised parts (at the floor) | 0.385 | 0.02 |

- **Cooperative.** The couplings sum to +0.0028 and +0.0068. At lap 15 the forward shifts sum to +0.0013: each group's lap of travel grafted alone **raises** the code, and the whole lowers it by 0.0020. The travel lies along directions that are soft for the whole and stiff for each part.
- **The raised line parted from the floor along such a direction.** At lap 14 the five's entries alone are worth +0.0010 and the rest's −0.0014, their coupling 0.0037, the whole −0.0003; at lap 15, +0.0024, −0.0025, 0.0071 and −0.0001. Raised rates moved the five where the rest followed, and the whole does not price that travel.
- **A part's worth is not its travel's price.** The five's worth by graft is −0.00128 then −0.00005 where the travel's first-order account gives them 0.0002 a lap. G75's rule asked for worths within a third of the account, group by group: refused. So a rate rule has no brake in a host account of travel, and none is built.
- G74's guesses: the base-rate entries' share (0.70, band 0.50 to 0.95) held at both laps; the five's share at lap 14 (0.05) missed high (0.385): the floor took in lap 14 what the raised line had taken from the five in lap 13, which is lap 14's larger fall.

## 7. Four times the travel buys no level (G76)

[measurement; the card, laps 16 and 17 of the floor and of the whole machine one and two octaves hotter (`tools/part_rates.py base` from `rt15/STATE.0`: the learner's rate word 11 for `hot1`, 10 for `hot2`, beside the floor's 12), each lap on the floor's sections (1,535 of 1,535 walk positions with equal sites) and read at its mean; nats a place; travel products in millionths of a bit a site, priced at the floor's rate]

| | Floor | `hot1` (2 times) | `hot2` (4 times) |
| --- | --- | --- | --- |
| lap 16's mean | 1.726734 | 1.726659 | 1.728260 |
| its end less its mean | 0.010691 | 0.025814 | 0.045038 |
| lap 17's mean | 1.726466 | 1.726260 | 1.727243 |
| its end less its mean | 0.006723 | 0.011362 | 0.021845 |
| product one lap on (lap 15's travel with lap 16's) | 1,103.2 | 1,429.1 | 2,076.3 |
| product two laps on (lap 15's with lap 17's) | 753.3 | 1,746.8 | 3,509.5 |

- **The travel that repeats is held by the rate.** Two laps on, the product reads 2.32 and 4.66 times the floor's at two and four times the rate. One lap on it reads 1.30 and 1.88 times, because the travel between the means of laps 15 and 16 covers half of lap 15's travel, the floor's on all three lines, and half of lap 16's: with what repeats moving at the rate the products would read (1 + 2)/2 and (1 + 4)/2 times the floor's, 1,485 and 2,249 with the shared lap's terms added, and they read 1,429 and 2,076, so the hot laps moved along what repeats at 1.86 and 3.54 times the floor's pace, the rate to the power 0.9. The diffusion's drift at first order in the step is the same path walked faster, as the derivation fixed with the guess said.
- **The level does not follow.** At lap means the floor stands 0.000075 and 0.000206 above `hot1` (laps 16 and 17) and 0.001526 and 0.000777 under `hot2`. Four times the travel along what repeats bought nothing a lap's mean holds.
- **The rents fall at the second lap.** A lap end stands above its mean by 0.0107, 0.0258, 0.0450 at the first lap and 0.0067, 0.0114, 0.0218 at the second: 2.41 and 4.21 times the floor's, then 1.69 and 3.25. No step was refused or halved in any of the six laps. Inside the second laps the hot lines' sections code 0.0091 and 0.0270 bits a site above the floor's before their steps.
- **The rule fired.** `hot2`'s product two laps on is 2.5 times the floor's or more, and its lead at lap 17's mean is under 0.0005 (it trails): the travel's worth is not in the held code at this size. No rate is the next subject, and the card goes to the letters past the second.
- [reading; agent-inferred] A lap's mean sheds the spread of directions that relax inside the lap and keeps the slower ones'. At rest every direction's spread costs a quarter of the step times the noise whatever its stiffness, so a hotter machine pays the slow directions' rent in its lap means as they warm: `hot2` paid 0.0015 at its first lap's mean and still 0.0008 at its second. The floor fell 0.00027 in its seventeenth lap, under what the travel that repeats was worth three laps before (0.00066 a lap, §6.1), and I read the line as near its rest. Its eighteenth lap fell 0.00164 (G82, missed): the falls into laps 15 to 18 read 0.00201, 0.00126, 0.00027 and 0.00164, about 0.0013 a lap, and one lap's fall is a draw of that scatter. The line still cools at its base rate; what stands is that raised rates bought no level (§9 item 1, §10).

## 8. The local joint, calibrated (G78, G79, G80)

### 8.1 The chain ruler on all places

[measurement; `cap_t.py` on the PC's host, six processes, under the run's key so that it draws the field's own held states; nats a place]

- Left to right, on all 43,470 held places: 2.709884, 1.981518, 1.467117, 1.239279 at one, two, three and four left letters. On the places with at least `d` letters before them (43,214, 43,087 and 42,960 at two, three and four) the chains equal the grip record's count tables within 0.00005, eight figures of eight: the chain is the tables. The 256 places at the answers' starts code at 0.72 nats each, which is the 0.0075 by which G78's control missed (§11).
- The length's code is 0.021807. At two letters the order-averaged code is 1.959719, its four quarters' mean against left to right less the length's 1.959711. A chain of count tables is one joint law, so it codes every reading order alike ([`code.chain-one-law-order-averaged`](../../docs/atlas/information.tsv)).
- By quarter of the open count (quarter 1 the fewest open): 1.107310, 1.554855, 2.172100, 2.996697 at two letters; every fourth site open 0.917457; every site open 3.310590.
- At three letters the read by quarter passed its deadline (3,309 s, projected 2,206 s from two letters' 201 s scaled by the states, 74,185 against 6,758) and was stopped with its process group. It printed no strata and is not relaunched; a next read changes its partition.

### 8.2 The field by quarter of open sites

[measurement; the card, `rt16`'s mean read held by the build that prints `FIELD_JOINT_STRATA` (atlas [`tower.field-joint-code`](../../docs/atlas/objects.tsv)), after it reproduced the lap's own held line, 1.726734; nats a place]

| Quarter | 1 | 2 | 3 | 4 |
| --- | --- | --- | --- | --- |
| open sites | 5,333 | 16,153 | 26,922 | 38,725 |
| the field, its own question | 0.668675 | 1.269788 | 2.029184 | 2.929850 |
| the field, the next problem's question | 0.769827 | 1.409309 | 2.182878 | 3.068779 |
| the chain of two left letters | 1.107310 | 1.554855 | 2.172100 | 2.996697 |
| the field less the chain | −0.4386 | −0.2851 | −0.1429 | −0.0668 |

The field stands under the chain of two left letters at every fill, most where most of the answer is written and least where most is open. What it holds beyond two letters it holds through its written neighbours and its question; with nearly everything open it holds hardly more than the two-letter chain.

### 8.3 What each written letter passes

[measurement; the card, `transmission-field` open-0 on the founded-parts record's problems; the code at a place with its `d` nearest answer letters written on the left, or `d` on each side, the rest open; nats a place]

| State | left d = 0 to 4 | each added left letter passes | both sides d = 1 to 4 |
| --- | --- | --- | --- |
| `ct8` (64 contacts, eighth plain lap) | 3.214, 2.678, 2.239, 2.069, 2.040 | 0.536, 0.439, 0.169, 0.029 | 1.939, 1.299, 1.139, 1.091 |
| `ctrl41` (32 contacts, its line's lap 41) | 3.216, 2.677, 2.251, 2.088, 2.060 | 0.540, 0.426, 0.163, 0.029 | 1.968, 1.346, 1.181, 1.137 |
| `rt16`'s mean (64 contacts) | 3.196, 2.624, 2.175, 1.993, 1.959 | 0.571, 0.450, 0.182, 0.033 | 1.860, 1.194, 1.029, 0.989 |
| `rt16`'s mean, the added contacts' `W` columns at zero | 3.265, 2.705, 2.318, 2.152, 2.123 | 0.560, 0.388, 0.166, 0.029 | 2.007, 1.401, 1.233, 1.196 |
| the text's count tables | 3.481, 2.710, 1.898, 1.423, 1.224 | | 1.564, 0.569, 0.419, 0.397 |

- The reading build printed `ct8`'s table as the founded-parts record does, nine figures of nine.
- Between `ct8` and `rt16`'s mean the third letter's pass moved 0.013 and both sides at two letters 0.105: the laps between located the place's closure and not the third letter.
- The third letter passes 0.182 at the line's sixteenth lap mean, where the stride ruler of the grip record passes 0.183 on 16 circles and 0.367 on 64. That is a match of heights at 16 circles, and no reading that the field holds the ruler's law.

### 8.4 What the doubling of the contacts moved

[measurement; the 32-contact control arm's state beside the 64-contact line's, and `rt16`'s mean with the added contacts' columns of `W` taken from the founding state `g0`, where all 2,048 are zero (`tools/state_travel.py graft`, a ruler's state, read and never trained from)]

- The trained 32-contact state passes the third letter at 0.163 and reads both sides at two letters 1.346; its held joint 1.817565, its quarters 0.1096, 0.1194, 0.0910, 0.0435 above `rt16`'s mean's.
- With the added contacts' return at zero the held joint rises 0.131870 to 1.858604 (quarters +0.1466, +0.1647, +0.1475, +0.0690), both sides at two letters rise 0.206589, and the third letter's pass falls 0.015485.
- **So the added contacts carry the place's two-sided closure and not the third letter.** Both the trained state and the lesion read them worth least where most of the answer is open: a contact closes a place against written neighbours.
- A lesion of a co-adapted part costs more than the part's growth gained (the 32-contact line stands 0.034 above `ct8` at lap ends and the lesion 0.132 above `rt16`'s mean): the rest of the field leans on the added contacts.

### 8.5 The carry's scan, read from the code

[derivation; agent-inferred, read from the scan in `Field`'s forward and from `gamma_of` in `crates/holonics/src/hnn/tower/field.rs`; atlas [`contact.carried-product`](../../docs/atlas/objects.tsv)]

The carry (`hnn-field-v14k`) runs the move `z → γ(t) z + b(t)` along the strand inside one tick, `Q(t) = b(t) + γ(t) Q(t−1)`, and the place reads `p(t+1) = a(t+1) Q(t)`. Its gate `γ(t) = g(t)/√(1 + |g(t)|²)` comes from a chart of site `t`'s own read, `g(t) = G r̂(t)`. Unrolled,

```text
p(t+1) = a(t+1) [ b(t) + γ(t) b(t−1) + γ(t) γ(t−1) b(t−2) + … ]
```

- The first term is the pair. The second is a term of three sites at first order in the gate: the place with its first and second letters together, which lies inside the second letter's pass (the scan raised it 0.02, the heat record §5.6). The third letter enters behind two gates, and a letter `d` back behind `d − 1`: a weak channel's information goes as the square of its amplitude, so as `|γ|^(2(d−1))`. Founded at `G = 0`, the move is `z → b`, every carried letter dropped at once, and the far letters wait behind gates that deposition must first open; the pull on the gate halved lap over lap (§5.6 there).
- The gates are complex scalars, so they commute: from four sites on, the scan reads the letters between its two ends as a product without their order. That limits the fourth letter and beyond, and it is not the third letter's failure.
- The stride ruler `cap_o.py` is this same move, `m = Σ_k (Π_(j<k) α[u_j]) β[u_k]`, with its gate `α` founded on the unit circle. On 16 circles it passes the third letter at 0.183, on 64 at 0.367, its gates contracting to 0.68 to 0.76 at three letters as it fits.

## 9. What is decided

1. **No rate is the subject, and the line still cools** (G76, G82). Two and four times the rate travelled 2.3 and 4.7 times as far along what repeats and bought nothing a lap's mean holds (§7), so the next loop is not a rate. The line itself still cools at the base rate: lap 18's mean read 1.724823, 0.00164 under lap 17's, its end 1.731382. So a build of the next law is scored only against the line's own laps run beside it on the same sections (G82's rule), and it enters the line by reproducing `rt18` with its new law off.
2. **The release is read at a lap's end** (G70, §4). The lap-mean rule's scope stands as written and does not reach the release.
3. **Contacts close a place between its neighbours** (G80, §8.4). The added contacts carry 0.207 nats a place of the two-sided code at two letters each side and 0.015 of the third letter. A growth of contacts is the route for the local closure, sized as a partition over the joints a site holds with its guess fixed first, and never the route for the third letter.
4. **The third letter's route is the carry, founded as a turn** [derivation; agent-inferred]. In the Swing a move with nothing deposited is a stationary grip, which turns without work; a push, friction or a moving grip boosts. The built carry founded its move at `γ = 0`, which is total friction: every carried letter is dissipated at the next site, and nothing past the first letter reaches a place until deposition has opened every gate between. Founded as a turn, `|γ| = 1` at founding, a letter `d` back enters at modulus one, its pull is first order at every distance, and deposition locates the turn's phase from the faces and the leak (the boost toward rest) that the ruler reads at 0.68 to 0.76. So that a trained field continues bit for bit, the carry runs on circles of its own whose return `W` is founded at zero, as the growth by contacts founds its added columns ([`tower.field-growth-by-contacts`](../../docs/atlas/objects.tsv)). The ruler's word on its own circles beside its pair tables is that form. How many circles a mate it needs was read first (G81): on 8, 16, 32 and 64 circles the ruler passes the third letter at 0.136, 0.197, 0.273 and 0.363 and the fourth at 0.052, 0.041, 0.056 and 0.079, its gain at the third letter a doubling of circles rising (0.061, 0.076, 0.090), so no partition of the third letter's information binds inside the range read; its gates contract the harder the fewer its circles (mean `|α|` at three letters 0.58, 0.60, 0.72, 0.77). The build, its card realization, its parity, its adjoint and its guess follow, and it enters the line by reproducing `rt18` with the carry off.

   **The gate, charted as a turn and a friction apart** [derivation; agent-inferred, 17:25 UTC]. The built gate `g/√(1 + |g|²)` ties the gate's modulus to its phase through a fixed `1`, an unlocated friction, and cannot hold a turn without friction. The ruler's gates fit moduli from 0.58 to 0.99 by letter while their phases carried the order, so the two are charted apart:

   ```text
   γ(t) = γ̂(q(t)) / (1 + d(t)),   γ̂(q) = ((4 − q²) + 4 i q) / (4 + q²),   d = max(0, h)
   q = Q r̂(t) + q_b,   h = H r̂(t) + h_b   (real charts, one row a carry circle)
   δq = (4 / (4 + q²)) Im(conj(γ) δγ),   δh = −Re(conj(γ) δγ) / (1 + d) where h ≥ 0, else 0
   ```

   - `γ̂` is the ring's Cayley tick of `i q/2` on one circle (`lean/Holonics/HNN/CarryGate.lean`, `carryTurn_eq_cayley`; `HNN/Ring.cayleyTick`): it keeps the circle (`carryTurn_normSq`), is rational and has no singular point, where `g/|g|` would be singular at `g = 0` with a covector going as `1/|g|`. The friction `1/(1 + d)` is the implicit step of a pure dissipation, monotone in `d` and never past a sign change (the damped Cayley step flips its sign past `d = 2`). So the gate is the move's polar factorization, turn times boost toward rest, and `|γ|² = 1/(1 + d)² ≤ 1` (`carryGate_normSq`, `carryGate_normSq_le_one`): the move is passive by its form.
   - `max(0, h)` with its right derivative at `0` lets friction open at first order from rest; an even function of `h` such as `1/√(1 + h²)` has a zero covector at `h = 0` and would never open.
   - Founded: `Q`'s rows drawn as the growth by contacts draws `a` and `b` (uniform on `±√(3/D)`, so `q` opens at unit power and a site's turn is a phase of about a radian set by its own read), `q_b = H = h_b = 0` (`d = 0`, a turn without friction, `carryGate_zero`), and the circles' `W` at zero, so the grown field is the trained field bit for bit at founding. The carry runs on the last `C` complex contacts, its circles of its own; the first `f/2 − C` stay the plain pair contact. `C` is carried in the declaration's head line, never a run switch. The first attempt is at 16 circles a mate (`C = 32`, `f = 128`, which runs as built). G83 fixes its guess on three laps `tc1` to `tc3`, each paired with the line's own lap on the same sections (`rt19` to `rt21`), and the rule that sizes what follows: a third-letter lead of 0.015 or more with a held joint 0.004 or more under its pair's grows the carry to the largest count a mate, in fours, whose lap the card runs with a saved state inside the hour and within 12 GB; a lead under 0.008 sends the next loop to the built object against the law, with no growth.
   - What it could repeat, checked: no authored routine (the move is the field's own, located by deposition); no cache (a carry circle is a store, a balance over the strand of what arrives `b`, what is kept `γ` and what leaks `d`, read through a port `a`); no width as a dial (`C` from the built pair contacts' count and then from the ruler, in fours); the deposit's step certificate covers the new charts as it covers `a` and `b`; the built gate's founding at zero, the located cause of the carry's failure (the heat record §5.6), is repaired and not carried; nothing modality-specific.
5. **G78's place between the chains is unread.** The three-letter chain by quarter waits on a changed partition; the next law does not wait on it, since §8.3 and §8.4 place the third letter's lack at every fill alike.

## 10. Withdrawn

Each of these was said on November 11, in a record, a guess or a reply, and does not stand.

- "Two laps' means stand 0.0008 apart" as a rule. It was one pair; the next lap's mean fell 0.0033 (§2).
- "The rate line stops at its rest", this record's title until 17:45 UTC, and "at this law the line stands near its rest, 1.726466 at lap 17's mean, falling 0.0003 a lap" (§9 item 1), with the same in the construction state and the rebuild. It was one lap's fall; lap 18 fell 0.00164 (G82, §7). What stands is that raised rates bought no level.
- The slope inside a raised lap as a fall that is kept (the heat record's §5.2 and §5.4). It is the raised parts' rent falling toward a rest length, and the old rate took back the first lap's lead within two laps (§2).
- A rate rule on the lap cosine between lap means. A mean's cosine does not fall as the rate rises, so the rule has no rest position (§3).
- A part's worth read from its travel's first-order price. Grafts read the five raised parts at −0.00128 and −0.00005 where the account gave 0.0002 a lap (§6.2).
- G75's agreement of the product one lap on with the lap means' falls as a pricing of the fall. It was two terms meeting (`V/6 − R'` = 339, §6.1).
- The product one lap on at lap ends as the travel that repeats. It is that travel less the lap end's draw (§6.1).
- "The scan keeps one complex number a contact and its gates commute, so it holds sums of pairs of sites and never a term in two earlier letters together", written into the heat record's §5.6 and its §6 item 5 this afternoon from the hand-off's "a scalar gate a circle passes nothing past the second letter". The gate is a function of its site, so the scan's first order is a term of three sites (§8.5); the commuting gates limit the fourth letter and beyond. The heat record's derivation, that a letter `d` back waits behind `d − 1` gates founded at zero, stands, and its sentence that the carry's founding is the next loop's subject is restored there.
- "The field stands where rank-16 readers stand" as a reading of what the field holds. It was a match of heights: two codes of one size say nothing of one law (§8.3).
- "The field's lack sits at middle fills", held an hour before G78 was fixed (§8.2).

## 11. What was wrong in the bases

- G68: the first raised lap's lead taken as the first step of a steady gain, beside a floor whose next lap fell four times as far.
- G70: the held code's finding carried to the release without reading how the release decides (by exchange, where a sharper face wins).
- G71: the open corner placed in the moments' face because an open site holds no letter; the pair contact reads the face after the current, open or not.
- G72: the raised line's rent guessed to go on growing; it stood at 0.010 to 0.013.
- G74: forward less reverse named the group's curvature; it is the group's coupling with the rest.
- G75 and G77: the product one lap on read as the travel that repeats; it carries `V/6 − R'` beside it.
- G76, first lap: the one-lap-on product fixed without the geometry of a lap's mean (half of it is the shared lap's, the floor's on every line), and the rents set from the lower of the floor's earlier lap ends (0.0055 to 0.0078) where lap 16's read 0.0107. Its second lap: the lead guessed to grow with the travel, from the drift alone, without the rent of the slow directions warming.
- G78: the control fixed at the grip record's 1.9890 without reading which places that figure was printed on; the field's code by quarter guessed evenly short of the chain, where with most open it stands within 0.07 of it.
- G80: the lesion's cost guessed from the growth's gain, where the rest of the field leans on the added contacts; and the quarters' spread under the trained 32 contacts fixed on no basis, as the guess said.
- G81 (c): one floor for the gates' contraction at every count of circles, where the fewer the circles the harder the word's gates contract.
- G82 (a): lap 17's fall taken as the line's trend, where the falls before it scattered from 0.0003 to 0.0033 a lap; a band set from one fall is narrower than the falls are.

## 12. Receipts

The guess file: `guess_capacity_44_55.txt` in the receipts of [the record of the places](2026-11-11_THE_PLACES_THE_FIELD_GIVES_PUSH_AGAINST_THE_PLACES_IT_MISSES_THE_DEPOSIT_IS_THEIR_DIFFERENCE_AND_TWO_BUILDS_ARE_TIMED_ONLY_INSIDE_ONE_HOLD_OF_THE_CARD.md) (G68 to G82 with their scores; G83 fixed). The PC's lines are in the receipts of [the heat record](2026-11-11_A_DEPOSITS_RATE_IS_A_TEMPERATURE_ITS_STANDING_SPREAD_IS_SHED_BY_A_MEAN_OF_STATES_AND_LAP_ENDS_ARE_DRAWS_THAT_DO_NOT_REMEMBER_EACH_OTHER_receipts/):

| file | holds |
| --- | --- |
| `g76_hot_lap_lines.txt` | the six laps of G76 with their means' held reads, lock times and pair lines (§7) |
| `g76_weighed_3_*.txt`, `g76_weighed_4_*.txt` | the travel products on three and four lap means and on lap ends (§7) |
| `g77_*.txt` | the lag products and the training pairs (§6.1) |
| `g78_chain_left.txt`, `g78_chain_depth2.txt`, `g78_chain_depth3.txt` | the chain ruler left to right, by quarter at two letters, and the stopped read at three (§8.1) |
| `g78_field_strata.txt` | the field's held read by quarter at `rt16`'s mean (§8.2) |
| `g79_transmission_rt16_mean.txt` | what each letter passes at `rt16`'s mean (§8.3) |
| `g80_states.txt`, `g80_transmission_*.txt`, `g80_held_*.txt` | the states, the control, the 32-contact state and the lesion (§8.3, §8.4) |
| `g81_stride_ruler.txt` | the stride ruler on 8, 16, 32 and 64 circles at two, three and four letters, with its gates (§9 item 4) |
| `g82_rt18_lines.txt` | the line's lap 18, its mean's held read and its section lines' summary (§7, §9 item 1) |
| `g83_*.txt` to `g110_*.txt` | the later laps, reads, rulers and releases of the line and of the circle line after it (G83 to G110, te1 to te6 among them), each file named for its guess, whose design and score are in the guess file |

Device: the PC's card (RTX 4080 SUPER) for every lap, held read and transmission read, each under its own hold of the card lock; the travel products, grafts and chain rulers are host arithmetic on saved states and on the held passage. Laps of G76: 873 to 891 s alone on the host, 916 to 1,038 s while the three-letter chain's six processes shared it, every lap inside its bound of 1,215,000 ms. A held read takes 10 to 14 s, a transmission read about 150 s. The chain at two letters took 201 s on six processes at 0.59 GB each; at three it was stopped at 3,316 s past its deadline of 3,309 s (projected 2,206 s, a third short). Lap 18 took 963.1 s on the card and its mean's held read 12.2 s, 1.07 times the projection. The ruler's twelve fits are host arithmetic, 1,500.3 to 1,502.6 s each, peaks 581 to 801 MB. The build that prints the strata passed `bash tools/gate.sh` on the PC at cf4dd2495 (837 s).
