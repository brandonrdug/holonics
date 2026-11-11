# Receipts: the host and the card as one surface

Host rulers for [the record](../2026-11-11_THE_HOST_AND_THE_CARD_ARE_ONE_SURFACE_WORK_IS_PLACED_BY_RATE_AND_WIDTH_THE_SURFACES_MEET_AT_CARRIES_AND_COST_IS_OWED_AT_MERGES.md). They are instruments on the host, never machinery. The train passage, the held problems and design's locked visits are private and are not here; the logs hold numbers only.

| File | What it is |
|---|---|
| `cap_t.py` | The ruler. `cap_t.py grains` counts the events of each grain of the train passage. `cap_t.py news rt4 ct8` reads design's locked visits (`locked-visit-v1`, 467 bytes a place) and reports how the covector mass and the code lie over the held places. It loads the class kinds and the unit ruler from `cap_q.py` (in the grip record's receipts) and reads the visits under the directory named by `HOLONICS_VISIT`. |
| `cap_t_grains.log.txt` | The grains of the train passage (G37a). |
| `cap_t_news.log.txt` | The two locked visits (G37b to G37d). |
| `guess_capacity_37_40.txt` | The guesses as fixed, with their times: G37 and G38 (read and scored), G39 and G40 (unread). G38 is scored from design's samples of the card and the host process (numbers relayed by design; its logs stay in its run directory). |
| `guess_capacity_33_43.txt` | The later entries of the same file: G33 read, the control for G30′, the part-rate guess scored and its correction to equal laps, G41 fixed, G40 read, G42 fixed and G43 fixed, each with its time. |
| `prof_rt9_train.profile.txt`, `prof_rt9_redraw.profile.txt` | The profile lines of design's two profiled card reads from the ninth lap's state (`FIELD_PROFILE` by entry, `FIELD_PROFILE_SPLIT`, `FIELD_CARD`, the card's opening line and the run's wall time and peak resident set): 301 training sections and a re-draw read of 32 held problems. Numbers only; the full logs stay in design's run directory. |
| `phase_rt9_train.phases.txt` | The phase lines of design's unprofiled phase trace on 311 training sections from the same state (`FIELD_PHASE` by mark, `FIELD_CARD`, wall time and peak resident set: 213.5 s, 786,680 KiB). |
| `profile_budget.py` | A host ruler on those lines: each part's share of the elapsed time, the entries by kernel time, the short launches, and the counts a batch. `python3 profile_budget.py prof_rt9_train.profile.txt`. |

The device: the rulers ran on the host, two cores of a virtual machine beside the main checkout, under a minute a part, and used no card. The two profiled reads are design's, on the RTX 4080 SUPER under the card lock, each alone: the training read projected at 200 s by its declared bound of 200,000 ms and measured at 212.7 s of wall with a peak resident set of 814,552 KiB; the re-draw read 93.9 s and 765,760 KiB.
