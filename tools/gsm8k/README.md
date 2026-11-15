# GSM8K exterior framing

The scripts partition and frame passages for the listener. Dataset content, keys and raw output
remain exterior. No generation is graded against the answer key's numeric answers or scored on its
delimiter pattern.

[retired, November 2] The written-rule reads (`written_rules.py`, with `card_written.py` writing their inputs),
the copy partition (`copy_roles.py`), the calculation roles (`calc_roles.py`) and the numeral-ring probe
(`numeral_rings.py`) paired answer numerals with the question's, counted copied numbers or labelled calculation
roles as a reading's acceptance: the numeral matcher's exterior (antipattern record, instance 4). With them went
their n-gram baseline (`ngram_release.py`) and the variants' copy claim (`tools/gsm8k_variants.py`, which counted
the question's numbers taken into a variant's calculations). Git history keeps them.
`digit_units.py` writes a cause-test foil of the founded units with every digit-bearing unit removed;
it is never the product
(`research/records/2026-10-26_THE_SECOND_LAP_WRITES_BACK_225_OF_1572_HEARD_CALCULATIONS_SO_THE_DIGIT_UNITS_ARE_TESTED_AS_THE_CAUSE.md`).

1. Run `python3 -I tools/gsm8k/partition.py TRAIN_JSONL PARTITION_JSON` to group normalized
   questions and declare development rows from the training split. The standard test split is
   listed by count only; no test content is read.
2. Create an output directory, then run
   `python3 -I tools/gsm8k/frame_gsm8k.py TRAIN_JSONL PARTITION_JSON OUT_DIR`.
   Learning and development-read frames contain their answer passages. Development-release
   frames contain only source passages and empty targets.
3. The listener example that read these frames (its `observed` and `sections` routes) retired with the
   examples (C8 of #603); it is held at [`8a77b7755`](https://github.com/brandonrdug/holonics/tree/8a77b7755/crates/holonics/examples/listener).

Releases on sets no run has read require separate processes from saved states, after continuing
resume is available. The literal key read width and online baseline orders are exterior
readings. The field's exact-bit constitution budget remains fixed and refusals are reported.

Run synthetic partition/framing checks with `python3 -I tools/gsm8k/test_tools.py`.

For the tower (record `research/records/2026-10-30_THE_COARSE_LEVEL_HEADS_FOR_THE_TRACE_OF_WHAT_COMES_NEXT_AND_THE_FINE_LEVELS_READ_ITS_HEADING.md`, §43):
`tower_passage.py TRAIN_JSONL PARTITION_JSON OUT_DIR` renders each problem `question` END `answer` END
(END the record separator) with each byte's region (Q question, P prose, N digits outside the
calculations, M the calculation markup), the written rules' texts and six development questions as
flux prompts.
The `complete_language` example's host route `read-written-coupling HELD HELD_SHA DIR` (retired with the examples, C8 of #603) read each free release in
`DIR/FREE.tsv` for its least-friction coupling with the held-out answer (`receiver::coupling`: `λ`, `F*`, plateaus),
in the bytes and in the numerals, beside its contact with its own and the next question, and writes `DIR/COUPLING.tsv`.
