# Receipts: a flock of unlike members

Host instruments for [the record](../2026-11-11_A_FLOCK_OF_UNLIKE_MEMBERS_JOINS_A_ROUND_ONLY_AT_ITS_OWN_GRAIN_A_PAIRS_TELESCOPING_PART_IS_TAKEN_ONCE_A_SITE_AND_A_GROUP_DETECTS_THROUGH_ITS_CONTACTS.md). They are rulers, never machinery. No passage, state or run log is here; the files hold numbers only.

| File | What it is |
|---|---|
| `flock_share.py`, `flock_share.log.txt` | The share of a round between the card and the host's lanes (§4.3), from the counters of the November 7 run's log (a region 4,316 µs on the card, 1,004,941 µs on one host lane, a pool of 20). For each round size it finds the least time by trying every split, the same by the filling rule `T*(n)`, and the fixed point of the built rule (`LanesField::split`), then prints the run's own figures. Integers only. `python3 flock_share.py`; under a second on one core, no card. |
| `guess_capacity_41_47.txt` | The guess file's entries from 04:47 to 05:02 UTC as written: G41 scored, G45, G46 and G47 as fixed with their times, and the two corrections of the host's rate. Two of its notes are wrong and are kept with the entries that correct them. |

The device: the script ran on a cloud container's host core and used no card and no private material. The counters it starts from are design's, relayed from the November 7 run's `lanes.log` on the PC (RTX 4080 SUPER, a pool of 20 host threads); that log stays in its run directory.
