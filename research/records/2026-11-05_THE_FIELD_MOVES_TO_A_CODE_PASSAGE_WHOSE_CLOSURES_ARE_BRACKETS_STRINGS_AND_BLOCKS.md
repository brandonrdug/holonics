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
