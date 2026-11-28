# A unit is founded by its saving over its pool's choice, held by a leaky count, and moved at its own mean's rate

[interpretation at weight 0.65, with four finite statements in Lean and the guesses G-Z58 to G-Z73 fixed before their reads;
the formal thread, November 27, on the lead's question of 22:51 UTC] Status: the description charge and the store's upkeep for
the first step of Fable's whole-project review (units founded on the card by October's lap law), written as one composition, with
what it predicts for the lead's build.

## 1. The question

Brandon asked that the review be acted on, and its first step is units founded on the card. A recurring run becomes a part when
holding it whole is cheaper than its pieces under a description charge, and the fixed-rate step no longer moves what was founded.
Its acceptance is that what a lap founds is still held after the next lap, and that the same span is cut alike at least 0.9 of
the time (0.56 today). The lead's build founds at the lap crossing when `n · (c − log₂ U) > L · log₂ A + log₂ |P|`, cuts a run
whole at its ends where its carry reads above background, and leaks the store by a lap's fade, refreshed by recurrence. It asked
for the law of the charge and of the upkeep.

## 2. What the tree holds

- The lap law's charge is the choice among the pool and the material's precision: `(S/(S − drop))^N > N |P|²`, about
  `½ log₂ N + log₂ |P|` bits (atlas `contact.lap-founds-reachable`, `contact.charge-falls-with-evidence`, Lean
  `HNN/ChargeThreshold`; [the staircase record](2026-10-25_A_LAP_OVER_THE_SAME_TEXT_FOUNDS_ONLY_WHAT_THE_LAST_LAP_MADE_REACHABLE_SO_LEARNING_CLIMBS_STAIRCASES_AND_STEPS_AT_EACH_FOUNDING.md) §2, §4).
- The October merge law founds a pair of present units into one when the complete code falls, charging the pair's choice
  `2 log₂ A + 1` and the alphabet's growth (atlas `hnn.founded-units`): 1,062 units on the GSM8K training problems.
- One law founds, prunes and recharts, and a coordinate the passage never reaches costs nothing (atlas `code.rank-one-founding`).
- A chain becomes its own part once meeting it whole costs less over its meetings than rebuilding it, and the reader keeps both
  paths at the cheaper and a bit (atlas `tower.chain-becomes-a-part-held-beside-its-pieces`, Lean `two_paths_code_le`).
- A charge is its news, so an address reads its own ratio and a heavy address saturates (Lean `delta_charge_contracts`).
- A stepped pass took 308 of 495 held units to 55 in October (the review, October 24 to 26).

## 3. The composition (0.65)

A founded unit `u` holds two quantities and a rate, and one inequality founds it, holds it and releases it.

```
n_u ← l · n_u + [u met]                     evidence: a leaky count, l = e^(−1/τ) a place, τ the store's leak
x_u ← x_u + (e − x_u) / (n_u + 1)           material: the leaky mean, its rate cooled by its own count
s_u = c_pieces − c_whole                    saving at a meeting, both codes read by the state before it
found ⇔ Σ_meetings s_u > log₂ |P| + 1       the charge: the pool's choice and the two-paths bit
held  ⇔ n_u · s̄_u > b_u                    the upkeep: b_u the unit's share of the store's background
```

**The charge is the pool's choice alone.** A code read meeting by meeting, each meeting coded by the state before it, pays its own
description. The first meeting spells the unit through its pieces, so its letters are paid there. A whole read by the level's own
face from its own leaky mean pays the material's precision, about `(A − 1)/2 · log₂ n`, inside its code as it learns. What is left
to charge is the choice among the pool's candidates, `log₂ |P|`, and the bit of keeping both paths. Charging the spelling again
counts the description twice: a six-letter word at `A = 155` would pay 44 bits above the pool's 20. `c_whole` is the level's own
code for the unit at that place, not a flat `log₂ U`, which overprices a common unit and underprices a rare one.

**The material moves at its own mean's rate.** The delta step at rate `1/(n + 1)` from the mean of `n` meetings is the mean of
`n + 1` (Lean `cooled_rate_is_mean`), and with the leak it is the mean over the leak's span. So a unit's rate is a state of its
own store and cools by its own travel, and no fixed-rate step reaches what a founding placed. This is October's sufficient
statistic. The stepped pass that erased 308 founded units to 55 is the configuration this replaces.

**The upkeep is a band, not the founding test run backward.** A unit met `m` times a lap holds its count at `m/(1 − l)` and climbs
toward it from below (Lean `leaky_count_fixed`, `leaky_count_rises_below_fixed`): a unit that keeps recurring keeps its evidence,
and one that stops leaves by the leak. Its description is paid once at its founding, so holding it costs only what its row costs
every other read, its share `b_u` of the background `√(‖F‖²/J)` that every read stands on. The unit is founded above
`log₂ |P| + 1` and released below `b_u`. The band between them is what carries a founding across the next lap. One threshold for
both, at a lap's fade, releases every unit that came in a burst.

**The cut.** Where a run's carry reads above the background it is cut whole at its ends (a word is cut only at its ends, the word
record §3). Depth is located at the read and never at the charge (the word record §22), so the store is charged at every meeting
and the founding decides only what the level above reads as a unit.

## 4. What it predicts

- G-Z58 (0.6): with the band, at least 0.9 of a lap's foundings are held after the next lap; with one threshold at a lap's fade,
  under 0.8.
- G-Z59 (0.55): on the same lap, the charge `log₂ |P| + 1` with prequential codes founds at least twice as many units as
  `L · log₂ A + log₂ |P|`, and the founded units' same-cut rate on recurrences stands within 2 points of the heavier charge's.

Both are fixed in `research/records/receipts/2026-11-26_nested_cycles/GUESS.txt` before the build is read. What does not transfer
from October: the merge law's alphabet growth is a flat code's price; on the store a unit's naming cost is the level's face, and
its growth is the background its row adds.

## 5. The cut weighs each start by the boundary before it (the lead's second cut form, November 28, 00:20 UTC)

The lead's first founding on 2,000 rows made 1,111 units, lengths 2 to 5 at the cap of `J/18 = 227` each and 123, 54 and 26 of
lengths 6, 7 and 8, under the charge `(n − 1)(c − log₂(U + 2)) > log₂ |P| + 1` with `n` a leaky count. Its first cut matched units
from the last anchor with keys counted from the run's start; the anchor moved with her news, the misalignment cascaded, epochs
went from 3.74 to 5.08 places and same-cut from 0.559 to 0.510. The second form counts keys back from a run's end and reads every
suffix of length 1 to 8 at each place: an anchor where a unit ends and none may still run, none where a suffix is a unit's proper
prefix (unless the epoch spans 8), and otherwise the news's anchor.

No unit has length 1, so every symbol that opens a unit marks a prefix at depth 1, and a test of membership suppresses a news
anchor at almost every place. **The composition (0.6): a prefix speaks only for a start that stands on a boundary.** Each suffix
`s_d` is a parse, a unit begun `d` places back, and it is as strong as the boundary before it, `a(t − d)`: one where her news
anchored or a unit ended there, the news-free prior elsewhere. Each key weighs by its leaky mass over the background `b`:

```
m_end(s)  = b + Σ n_u over units ending at s
m_cont(s) = b + Σ n_u over units with s as a proper prefix
w(d)      = a(t − d) · Π_(j<d) (1 − a(t − j))          the chance that t − d is the last boundary
end(t)    = Σ_d w(d) · m_end(s_d)/(m_end(s_d) + m_cont(s_d)) + Π_d (1 − a(t − d)) · news(t)
cont(t)   = Σ_d w(d) · m_cont(s_d)/(m_end(s_d) + m_cont(s_d))
cut at t ⇔ end(t) > cont(t)
```

The starts are disjoint parses of one string, so their masses add: the fibre's sum over parses (§17 of the word record), read
one-sided. A parse begun `d` places back is disjoint from the nearer ones only if no boundary stood between, so its weight is the
chance that `t − d` is the last boundary, `w(d) = a(t − d) Π_(j<d) (1 − a(t − j))`, and each key is read as its ratio,
`m_end/(m_end + m_cont)` against `m_cont/(m_end + m_cont)`. The first statement of this law (00:22 UTC) left the factor out, so
each start counted as if it were the last and the continuing side gathered about a quarter from every depth where a suffix opens
a unit (the lead's probe, 01:05 UTC: the units cut a unit's meetings whole 0.107 of the time against 0.093 without them, and less
at lengths 6 to 8); that is the formal thread's miss, scored in the receipt, and G-Z64 reads the corrected weights; the product of §23 there joins reads of one symbol and is a different composition. The weights come from her news and
the store's end marks and never from the cut's own past decisions, so nothing cascades and the cut stays a function of the last
eight places. Where no unit speaks every mass is `b` and the cut is her news anchor (Lean `cut_at_background_is_news`). A depth-1
prefix suppresses only right after a boundary, and there it competes on mass. The cap of eight is the store's own, since past the
longest unit no key has continuation mass. The cap of `J/18` a length binds at lengths 2 to 5 and is an extent set by hand; the
upkeep band of §3 sets the count where a unit's saving falls under its row's share of the background. G-Z60 and G-Z61 are fixed on
the stability read.

## 6. A candidate's ends are where its readings agree, read as her mean news after each suffix (the lead's stability read, 00:56 UTC)

On W134's end over the 16 held passages at 3,700 places, her news alone cuts a recurring word alike 0.576 of the time at 3.77
places an epoch. Every unit form cuts less alike: from the last anchor 0.510 (5.08 places), by membership 0.346 (7.95), by the
weighted parses of §5 0.450 (3.81, 2,074 units). G-Z60 and G-Z61 held, and the forms stand under the cut they were built on. The
units were founded from her epochs, which are one meeting's anchors and cross word boundaries ("e th", " of", "ing "), so a
candidate carries that meeting's noise and a suffix parse that ends inside a word carries the word before it.

**The composition (0.65).** A word's ends are where its readings agree (the word record §3). Agreement over meetings is a property
of the span's type, read as a mean over its meetings, never one meeting's anchor:

```
ν̄(s) ← ν̄(s) + (ν_(t+1) − ν̄(s)) / (n_s + 1),   n_s ← l n_s + 1      at each suffix key s_k, k = 1 to 8
end after t ⇔ ν̄(s_t) > ν̄(s_(t−1))                                  the depths joined as the product of their reads
inside ⇔ ν̄ falls                                                     the path does not branch, a split there is free
candidate = a run between consecutive ends, founded by §3's charge
```

`ν̄(s)` is her news at the place after the suffix `s`, a leaky mean whose rate cools by its own count (Lean `cooled_rate_is_mean`):
the stream's branching entropy after `s`, the same at every meeting of `s`. An end stands where it rises, where the paths that
pass through `s` part. Inside a word it falls, the path does not branch, and every split there reads alike (the word record's
"its inside is every split at once"). The depths join by the product of §23 there, so an unmet key is flat (Lean
`flat_factor_normalizes`) and the shallow keys, which reach no word before, decide inside a word. The chart is Harris's successor
peaks (1955), which the tree read at the second level on November 26 as the transitional dip (Saffran, Aslin and Newport 1996,
the record of a class's mean word §11); here it is read at the first level from her own news. The lead's proposal, runs between
places where her news anchors at nearly every meeting, is the same law with her anchor in place of her news; the mean keeps the
density and needs no fraction handed in. G-Z62 reads the rise cut alone, with no units, so the ends are read before any founding
stands on them; G-Z63 reads the units founded between them.

## 7. The units are the cut's vocabulary, and the cut's store holds only what her face lacks (the lead's reads, 01:25 and 01:27 UTC)

The rise cut with no units cut a recurring word alike 0.974 of the time at 2.07 places an epoch, and the peak cut, a rise with no
rise after it, 0.940 at 3.14, against her news alone at 0.576 and 3.77 (G-Z62 half held: the rate far over, the epoch under the
band; the band was the formal thread's own setting, and an epoch is set by no band). Units founded between the ends, 1,995 in the
peak form and 1,866 in the rise form, cut whole 0.309 and 0.386 of their meetings against 0.082 and 0.071 with news alone (G-Z63
missed), and 0.64 to 0.96 of the meetings whose first place the cut anchors, rising with length in the peak form. A unit is cut
whole only where its start is an end, so its share over all meetings is the starts' cover times the started share; a short unit
met inside a longer held unit is read inside it, which is the two paths of §2. Counting those meetings as whole lifts the peak
units to 0.697 and the rise units to 0.582, not to the 0.8 that G-Z67 asked: nesting explains part of the uncut starts, and the
rest stand where the word before reaches into the cut's keys. The stability is the type mean's, and the units are its vocabulary.

A same-cut rate is read with the cut's density and where its ends fall: a cut that is a function of the last eight symbols cuts a
recurring word alike wherever the word before does not reach its keys, and a cut at every place cuts every word alike. Read
against the spaces, 0.972 of the places after a space carry a peak end (her news alone 0.600), and 0.519 of the peak ends fall
there, the rest inside words (G-Z65 held): the peak cut keeps the word's ends and cuts about once more inside a word.

**The composition (0.6).** The mean of her news after a suffix is the mean of her own face's entropy there plus the mean of what her
face lacks: a cross-entropy is the entropy of her face and the divergence of the stream from it.

```
ν̂(s_t) = H(p_t) + δ̄(s_t)                                    her face's entropy for the next place, plus the store
δ̄(s) ← δ̄(s) + ((ν_(t+1) − H(p_t)) − δ̄(s)) / (n_s + 1)     at k = 1, 2, n_s ← l n_s + 1 (Lean cooled_rate_is_mean)
end after t ⇔ ν̂ peaks at t                                   as in §6
```

Her state already reaches past eight places, so the long depths are hers to read and need no keys. The store holds the residual,
which is her miscalibration after a short suffix and no larger than the divergence, keyed at depths 1 and 2. The full field of §6,
a mean per depth to eight, is the host ruler's own quantity and is lawful as a store on her rings with entries shared at a
residue. It is held beside this form as the configuration to build if the meeting's own entropy loses the stability: `H(p_t)`
belongs to the meeting, so the cut is no longer a function of the type alone, and G-Z66 reads what that costs. Units of units are
founded by the same charge from the runs of these units, the staircase of October 25, and no epoch is handed to the level above.

The lead's read of 03:23 UTC took that cost: the meeting's entropy with the store of what it lacks cut alike 0.764 of the time at
3.21 places, the divergence a mean 0.0163 nats, so her meeting drove the cut (G-Z66 missed), and the composition above is withdrawn
for the cut. The type form stands, and its depth is short: the type mean at depths 1 and 2 alone cut alike 0.947 at 3.16 places, level
with depth 8, on 8,825 keys.

**A depth speaks over its field's own background (0.6).** On a store addressed on `J` circles, each depth a mean field `M_k` and a
count field `C_k = Σ_v n_v χ_v`, a key's count reads its own `n_u` and a crosstalk of variance `Σ_v n_v²/(2J)`; since
`‖C_k‖² ≈ J Σ_v n_v²`, the field's background is `b_k = ‖C_k‖/(J√2)`, read from the field itself. The depths join by
`w_k(s) = (Ĉ_k(s) − b_k)_+`: a depth speaks for a suffix only where that suffix was met more than its field's noise, which is §3's
upkeep band read at the cut and the floor of the suffix store's ruler. A weight taken over zero gives half the unmet deep keys a
crosstalk weight near `b_k`, and that weight follows the word before.

The lead's read of 03:31 UTC scored it: over zero, depths 1 to 8 at `J = 4,096` cut alike 0.874 (G-Z68 held), and over `b_k`
0.865 (G-Z69 missed), since `b_k` is the commonest keys' crosstalk (`b_2 = 424` against a depth-2 key's mean of 70 meetings) and the
weight over it silences the rare keys without separating them. Depths 1 and 2 kept 0.645, 0.774 and 0.815 of the type cut's ends at
`J = 1,024`, 4,096 and 8,192, and the share of places after a space carrying a peak end fell from 0.969 to 0.753 (G-Z70 half held:
the same-cut rate stood near 0.9 by construction, and the field's size showed in where the ends fall). The count-cooled step read
a run's mean with 2.5 nats rms a meeting at 4,096.

**A key's charge stands at its residues (0.65).** On `J` circles each key's charge is spread over every entry, so the crosstalk at
every key is the sum over all keys' charges and the commonest set it; the step at `1/(n + 1)` is a mean only where a key's read is
its own entry (Lean `cooled_rate_is_mean`), so a key's first meetings, charged at rate one, enter every other read and nothing
repays them. On two coprime rings `p₁` and `p₂`, each key's charge stands at one residue a ring, an entry holds a sum and a count
shared only by the keys at that residue, its mean is the sum over the count with nothing left elsewhere, and a heavy key pollutes
its own residues alone. The rings tell `p₁ p₂` pairs apart: resolution bought by agreement among coprime parts, the grain law of
November 21, and the rows a symbol's word shares at a residue (November 12). A key is read at the ring whose count is least, an
upper bound on its own count, so its weight needs no positive part. A leak on the sum and the count is the store's upkeep of §3 and
enters as its own arm; a leak common to the sum and the count leaves their ratio the leaky mean, so at a fixed state it moves only
the weights and the tracking. The lead's read of 03:35 UTC held it (G-Z71): on two primes near 4,096 the store keeps 0.996 of the
type cut's peak ends, and its read of a run's mean errs 0.17 nats rms against the phasor store's 2.5.

**A deeper run speaks by its increment over its parent (0.55).** The type cut's depths join by their counts,
`ν̂ = Σ_k S_k / Σ_k N_k`, and every meeting of a run is a meeting of its last octet, so `N_1 ≥ N_2 ≥ … ≥ N_8`: the last octet
weighs most at every place, and a deeper run moves the read by its share of the counts, most where it agrees with its parent. That
depths 1 and 2 stand level with depth 8 is then the join's and not depth's: the last octet alone keeps 0.958 of the type cut's
peak ends at depths 1 and 2 and 0.947 at depths 1 to 8, and cuts 0.951 alike at 3.06 places (G-Z72 held). The flag of the
word record's §23 joins nested reads by their increments: a run reads as its parent's mean moved toward its own at its credibility,

```
m̂_k = m̂_(k−1) + Z_k (m_k − m̂_(k−1)),   Z_k = N_k / (N_k + c_k)
```

where the count join is `c_k = N_(k−1)`, the parent outvoting the child, and `c_k = 1` is the cooled step of §3 begun at the
parent's read, a new run starting where its shorter suffix stands. The store's own spread sets `c_k` between them: the variance of
her news within a run over the spread of the children's means, a third sum at each residue with the same leak (Bühlmann's
credibility, 1967). It enters as its own arm after the residue store.

## 8. A cut is read as the writer can name it (the lead's forward read, 08:50 UTC)

On the store's lap the held cavity read her text 0.0235 nats a place cheaper than the control's, and her forward code on 100 held
cut rows (19,200 places) read 1.0931 against the control's 1.0846, worse at every octave of age past the cut and most at age 1
(+0.048), the worth of the past about equal on both.

**The composition (0.8 on the take, 0.7 on the cause).** A section is crossed in the stream's order, so a line whose product is its
writes is taken on the code its writer draws from, `Σ_t −log p(x_t | x_<t)`; the atlas measured the regime on November 21
(`release.writer-regime`: what the field founds where its sites hear both sides is not what it writes where they hear only the
past). The cavity is a ruler of what the state holds, and two arms compare on it only where neither arm's input at a coded place is
a function of that place. The store's cut is: an anchor stands at `t` where the rise at `t − 1` has no rise at `t`, and the rise at
`t` reads her mean news after the run ending at `x_t` (`Units::rise_anchors`), while a region's training cut is drawn over its own
classes on both sides (`level_cut_units` with `before` false on the card), so a site at `t` reads a phase its own symbol placed.
The cavity credits that as code; the writer cannot name it, and the place that opens an epoch pays most. The repair is the strand's
law of November 18 read at the store's anchors: an open site at `t` reads only the anchors `x_<t` names and stands in the epoch of
the place before it, as `level_anchors_before` gives her news. It enters as one change, the same cut and the same units with only
their reading made causal; the rise form, which decides an end from `x_≤t` alone, changes the cut, the epochs and the units, and is
an arm of its own. G-Z73 reads the one-sided peak.

## 9. Owners

- Lean: `HolonicsResearch/HNN/OwnCycleCells.lean`, `leaky_count_fixed`, `leaky_count_rises_below_fixed`,
  `cooled_rate_is_mean` and `cut_at_background_is_news` (checked); §6 composes `cooled_rate_is_mean` and `flat_factor_normalizes`
  and adds no statement; §7 composes `cooled_rate_is_mean` and adds none.
- Atlas: `tower.chain-becomes-a-part-held-beside-its-pieces` (objects).
- Guesses: G-Z58 to G-Z73.
- The engine: the founding build is the lead's; this record changes no code.
