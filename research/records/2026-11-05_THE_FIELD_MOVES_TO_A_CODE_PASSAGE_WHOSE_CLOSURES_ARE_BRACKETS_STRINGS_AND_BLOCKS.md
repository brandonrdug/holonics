# The field moves to a code passage, whose closures are brackets, strings and blocks

November 5, 2026. Refs #73 #404 #406. The field learner's passage changes from GSM8K to Python code by Brandon's direct
request; this record fixes the boundary codec, the held split, the run and the first reading's prediction.

## The request

[project-postulate; Brandon, November 5, 16:29 UTC] GSM8K is mostly a benchmark; the field moves to
`flytech/python-codes-25k` going forward, so the work is "less about English and arithmetic and more about general logical
cohesion", where "a lot more pattern matching dynamics" can be seen. He authorized the download.

## The passage

[definition; agent-inferred] The dataset (MIT licence, 24,813 rows of instruction, input and output; 99 distinct bytes;
outputs a median 247 bytes, at most 2,061; 20,795 opening with a code fence, 13,674 holding blank lines; 6,027 instructions
over several lines) is converted at the exterior boundary by `tools/code_passage.py` into passages of records: each problem
`question US answer RS` (`0x1F`, `0x1E`, neither in the data), the question the instruction and, where the row has one, a
newline and its input, the answer the output, every byte as the row holds it. `problems_of` reads such a passage beside the
blank-line blocks of GSM8K (the trainer's test `a_passage_of_records_keeps_its_blank_lines`); the blank-line blocks would
have cut the answers at their blank lines and the questions at their second line. The units are the bytes (`UNITS0`).

The held problems are 128, the first in a keyed order (SHA-256 of `held128 | question US answer`) among the 23,995 rows
whose instruction and output each stand in no other row, so no held question or answer is met in training (seen material
graded as unseen is a recorded failure); the other 24,685 rows train, and the trainer withholds its own 128 of them by its
keyed order, as before. The answer extent is 2,062 places (GSM8K's 1,229) and the reach 3,771. Dataset roles are exterior
codec information; the passages stay under `.local/` and are never published.

## The run (code84)

[agent-inferred] A fresh field founded on the GSM8K line's declaration (width 32, four heads of eight modes, two still,
32 contacts, four ticks, sections of 16; the byte alphabet changes, so no GSM8K state carries over), on the card, under the
laws that stand along the GSM8K line: the boundary port along the writer's path and its keyed passage of path problems in
training, the octave writer and the one-place refine at release (the field record's §16.47). The path's states follow the
writer's octave order (the octave writer's read on a state trained in one keyed order wrote 1.49 times held, its end's faces
not having met those states; §16.47), so the founding trains on the states its writer meets; the run was relaunched with
that law before its parity began. First the sampled parity on
one section of this passage, then a cost read that sets the lap bound, then three segments of two laps each (about 1,543
sections a lap against GSM8K's 413, so a lap is about an hour by projection: a stated long run of about eight card-hours),
each followed by the opening read on the held and the first 128 training problems, the drift read (the 128 held, read 64,
one key) and a write of 32 held problems. The GSM8K chains finish the steps they hold (path75's second segment, keyed79's
first) and stop; boundary73 stopped before its fifth.

## The first reading, fixed before the first write

[definition; agent-inferred, the unified-theory reading of November 5, 16:36] On code, decimals are one small family; the
first laps measure whether the field's own dispersion already closes what code opens. `code_closure.py`, inside each
answer's fence and outside comments: brackets (an opener closes where its own closer meets it), strings (a literal closes
at its own quote, a single-quoted one before its line ends) and blocks (a `:` line closes where an indented body follows it
to its dedent), each opener's span its places to its closing byte, near under 6 and far 6 or more (the near field,
`lcm(2, 3)`); for each family and span the share of openers closing there, written against held. **Prediction**: depth is
a sum, a first-order trace the content pace can carry, while a string's state is a parity (torsion 2) that no additive
ring holds, so far strings close under 0.5 of held and below far brackets. **Rule**: any closure under 0.5 of held is the
build's next subject, by the ring law (a closed rule as a move `ρ ← μρ + r` keyed by its seam and arriving class, `μ`, `r`
and the periods located by loop closure on the card; code's closures are additive or a half-turn, which the solenoid's
dyadic and triadic rings carry); if none is, the names (an identifier used where it is bound) are read next.
`code_reading.py` beside it reads the fences, whether the code parses as Python (an exterior reading the machine never
reads) and the identifiers' share standing in the question and in the held answer. Read against the held answers
themselves, both readers return the held figures (closure ratio 1.00 in every family and span; 26 of the first 32 held
answers parse).

## The first lap

[measurement] code84's segment 1 (from the founding, on the fluxing step, the tiled affine map at the founding's width and
the card pool by best fit; path states over the whole room): lap 0 read the 1,535 sections in 1,688 card-seconds (1.10 s a
section; the cost read had bounded a lap at 2,320 s), every step deposited. The withheld problems' code fell from 6.644 to
3.029 bits a byte; on the 128 held, the context read from 6.644 to 3.065 and the foil to 3.069 (the question's effect 0.004
bits a byte), the opening (every answer place open) to 6.337. The segment was stopped after lap 0 and its held read, and the
run continues from that state under the cut path states (`code84_cont_launch.sh`).

[definition; agent-inferred, November 5, the unified-theory reading of 18:53, parts 1 and 3] **A path state ends five
places past its front, and a state with nothing open is none** (`opening_region`, `Port::stop`): before a void is resolved
the region is cut `NEAR − 1` places past the front octave's end, the faces at and before it the whole room's bit for bit (the
field tests' near-field cut), and the margin is read and not compared (the port's stop; on the card a zero covector row);
past a resolved void the region keeps the room. The trainer's tests pass with the cut states (the margin is the near
field's, a state past a void keeps the room, a state with nothing open is skipped and the next takes its place on its own
draw). Part 2 (regions end five places past their lowest void, the members' keyed tail retiring) is declared after these
have run, at the same seed, with this run as its foil.

[measurement; agent-inferred] **The cut path states, read** (`code84_seg1.txt`). Their sampled parity on this passage passed,
every read equal (a section's 26 regions read 23,133 sites against 55,891 over the whole room). The cost read from lap 0's
state: 376 sections at 369 ms (at most 1,388) against 1,259 ms over the whole room, 3.4 times, a lap bounded at 679 s, so a
pass over the 11.2 MB is about nine and a half minutes. Lap 0's state read: the opening's expected length less held −28.1
on the held (+15.3 on the training problems; `B` 93 and 81 against the law's 132 and 152); the drift to read 64 on the 128
−129.6 ± 11.6, far past the two-sided bound's −20 (one lap under the octave path, read to be followed, not yet judged). Its
write of the 32, in runs below a bit: 108 card-seconds and 1,203 reads; 0.415 of the held bytes, 27 of 32 shorter; 26
fences opened and 14 closed; one answer parses as Python; 0.02 of its identifiers stand in the question (0.26 held).
**Against the closure reading fixed before this write**: written over held, brackets 0.27 near and 0.22 far, strings 0.22
and 0.30, blocks 0.42 far; every closure is under 0.5 of held, so by the rule closure is the build's subject (the ring law),
and the prediction that far strings close below far brackets fails (0.30 against 0.22). One lap in, with answers too short
to hold their closures.

[definition; agent-inferred, November 5, the unified-theory reading of 19:32, part 2 of 18:53] **A region ends five places past
its lowest void** (`FIELD_TAIL_NEAR`, `near_tail`, declared against the keyed tail): a training region's tail is the void and
the five places past it, a path state past a resolved void ends five places past it, the withheld read's tail is cut alike, so
every place before the end keeps its near field and no problem hears the codec's room. The trainer's tests pass under it (the
keyed tail's own test stands aside). **Prediction, fixed before launch**: from code84's lap-0 state, two laps at the same seed,
held code on the context and opening reads stays no higher than code84's segment 2 at equal laps (within its spread), and lap
time falls again, about 1.6 times fewer sites than parts 1 and 3 alone. **Rule**: held code above that spread means the room's
voids shaped what training learned about the end, and where the writer closes needs its own law (code85).

[measurement; agent-inferred] **Segment 2: the cut was not cost-only** (`code84_seg2.txt`). Two laps on the cut path states,
600 and 580 card-seconds a lap (3.4 times lap 0's). The held context code 3.065 → 2.467 → 2.181, the foil 2.192 (the
question's effect 0.011 bits a byte), the joint code 2.68 → 2.34. But the opening's length law collapsed: its void mass 0.02
to 0.04 at every distance (the law's 0.41 to 0.92), its expected length less held +1,649 (`B` 1,653 against the law's 132),
and the L-based drift +1,649 → +1,174 by read 64. The cut dropped the far open places' boundary comparisons, which carried
covector (the sampled parity compares card and host under one law, both cut, and so never compared the cut learner with the
whole room's; the near-field test compared the kept faces, not the covector), and those comparisons taught the opening its
length. The opening and the L-based drift now read states the field no longer trains. The write of the 32 (runs, 7,407
reads, 674 s): 1.749 of the held bytes (16 longer, 16 shorter; the correlation with held −0.139), 7 of 24 opened fences
closed, one answer parsing, 0.18 of its lines parsing alone (0.14 at held length, two answers), 0.37 of its words in the
training vocabulary; the closures against held 0.53 and 0.50 (brackets, near and far), 0.66 and 0.54 (strings), 0.48
(blocks, far). Its ends: three of 32 within two places after a closing fence (seven written), 29 elsewhere at a steady one in
528 places, about one in two held lengths: the writer ends in unclosed content at a steady rate, a sense of length kept at
about half its hazard.
