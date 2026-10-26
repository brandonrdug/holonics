# The pass lowers the role on seen problems too, so the copy loses its margin

October 26. Refs #404, #405, #386. The read the third lap's record fixed
([record](2026-10-26_THE_THIRD_LAP_FOUNDS_THE_CLOCK_AFTER_EQUALS_AND_ITS_PASS_LOWERS_THE_ROLE_FROM_53_TO_43.md)
§4), on Brandon's PC at `7f0921b4b`. Grades: [measured] for what the runs printed, [agent-inferred]
for each reading of them. Receipts:
[`…_receipts/`](2026-10-26_THE_PASS_LOWERS_THE_ROLE_ON_SEEN_PROBLEMS_TOO_SO_THE_COPY_LOSES_ITS_MARGIN_receipts/RUN.md).

Computational object: the helical pair interaction, here the pair contact between the answer's first
arrival and the arrival the blank line's clock holds, read at the output face. The read touches faces
and placement only; the helix, the level's pair contacts, cell holonomy, tube and tower thread stay
as the tower has them.

## 1. The role on seen and held-out problems

[measured] The training text's own named answers that open with the name (1,074, read with the
training text as both the heard and the read text), beside the held-out ones (97). "First" counts the
answers where the face gives the answer's first unit the largest mass; the bands count the classes
carrying more than it.

| state | seen: first | seen: 1 above | seen: 2–4 | seen mean code | held out: first | held out: 1 above | held-out mean code |
|---|---|---|---|---|---|---|---|
| `copyD8` (clock after `"any "`) | 0 | 8 | 44 | 6.471 | 0 | 2 | 6.800 |
| `lapT8` (its twin pass) | 0 | 11 | 65 | 6.364 | 0 | 1 | 6.718 |
| `lapD8` (the blank line's clock founded) | **695** | 196 | 100 | 2.577 | **53** | 27 | 2.876 |
| `lap3T8` (one more pass, nothing founded) | 561 | 281 | 137 | 2.877 | 37 | 36 | 3.253 |
| `lap3D8` (one more pass, `"="` founded) | 599 | 261 | 96 | 2.889 | 43 | 29 | 3.158 |

- From `lapD8` to `lap3T8` the seen answers keep the largest mass in 530 of 695 and gain it in 31;
  the held-out keep 36 of 53 and gain 1. `lap3D8` beside `lap3T8` keeps 490 of 561 and gains 109
  seen, keeps 33 of 37 and gains 10 held out.
- The answers that leave the first place go mostly to the next band: one class above the name, seen
  196 to 281, held out 27 to 36.

## 2. The decision

[agent-inferred, by the rule fixed in the third lap's §4] The seen role falls with the held-out one
(695 to 561 and 53 to 37 over the same pass), and the seen answers' mean code rises 0.300 bits with
the held-out's 0.377. A readout learning the seen names would raise the seen role. So the copy is
losing its margin over a pass, and the name is pushed to second place more often than lost.

## 3. The next read: the margin taken apart, its decision fixed now

[definition; agent-inferred] The third lap's §4 names the next read: the copy's own weights before and
after the pass. A weight alone does not say what the margin lost, so the read takes the margin apart
at each named answer's opening:

```text
margin = z[first unit] − z[rival] = readout's own part + raise on the first unit − raise on the rival
```

The rival is the other class carrying the largest mass. The raise on a class is the sum of the copies
`⟨r_A, x⟩ + b_A` of the clocks holding it there. `Tower::read_clocks` hands each cell's face, each
clock's held class and each copy's raise to an exterior reader, computed by the copy's own law
(`clock_copy` now adds `clock_raises`). `read-tower-clock-cells` prints each clock's bias, row square
and reach, and writes the parts at the reads the observer requests. The observer's `copies` mode sums
them per state and, over the answers the state before gave the largest mass, the mean change of each
part, split by whether they are kept.

The read runs on `lapD8`, `lap3T8` and `lap3D8`, over the training text and held out. Over the seen
answers `lapD8` gave the largest mass and `lap3T8` lost, the part whose mean change is largest in size
names the cause, fixed before the read:
1. **The raise on the first unit falls most:** the copy's own steps lower it over the pass. The next
   loop reads the copy's covector at the held cells over the pass, where the name recurs and where it
   does not.
2. **The readout's own part falls most:** the pass raises another class at the opening through the
   readout. The next loop reads which classes the rivals are and what the readout's covector does there.
3. **The raise on the rival rises most:** another clock's copy outbids the name (the clock after
   `"any "` holds a counted noun, the clock after `"="` a result). The next loop reads the copies
   against each other at the cells where two clocks hold different classes.

`lapD8/STATE` stays the state the role and John are read from, and no lap is taken until the read
decides.

## 4. The recorded failures this loop could repeat

- **Seen material graded as unseen.** The seen role is a diagnosis beside the held-out role and is
  never counted toward item 3 of a lap's acceptance.
- **Bits read as progress.** The pass lowered both codes and both roles; the code is read beside.
- **A refusal answered with a larger limit.** No further lap is taken. The next read's deadline is
  fixed from the largest measured wall (38.3 s), not raised past a failure.
