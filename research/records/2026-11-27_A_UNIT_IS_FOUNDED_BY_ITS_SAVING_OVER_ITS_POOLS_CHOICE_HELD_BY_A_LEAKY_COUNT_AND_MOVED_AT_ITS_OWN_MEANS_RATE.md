# A unit is founded by its saving over its pool's choice, held by a leaky count, and moved at its own mean's rate

[interpretation at weight 0.65, with three finite statements in Lean and the guesses G-Z58 and G-Z59 fixed before their reads;
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

## 5. Owners

- Lean: `HolonicsResearch/HNN/OwnCycleCells.lean`, `leaky_count_fixed`, `leaky_count_rises_below_fixed` and
  `cooled_rate_is_mean` (checked).
- Atlas: `tower.chain-becomes-a-part-held-beside-its-pieces` (objects).
- Guesses: G-Z58 and G-Z59.
- The engine: the founding build is the lead's; this record changes no code.
