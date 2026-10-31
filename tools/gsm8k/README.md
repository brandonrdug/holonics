# GSM8K exterior framing

The scripts partition and frame passages for the listener. Dataset content, keys and raw output
remain exterior. No generation is graded against the answer key's numeric answers or scored on its
delimiter pattern.

The written-rule reads (`written_rules.py`) read a release on all held-out problems by rules fixed
before the read: whether it stays on the problem's words, whether each calculation it writes is the
exact value of its own expression, and whether its first calculation takes the question's numbers;
and, at each calculation of a held-out answer, whether the value written after its `=` is that
expression's exact value. None reads the answer key, none selects a release, and nothing they read
enters the machine. `ngram_release.py` writes an exterior n-gram baseline's releases for the same
reads. The rules and their reason are in
`research/records/2026-10-26_THE_HELD_OUT_PROBLEMS_ARE_READ_BY_WRITTEN_RULES_AND_THE_MARKUP_IS_WRITTEN_AT_ITS_EQUALS.md`.
With `pair` the rules compare two releases calculation by calculation at the equals.
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
3. Build the host listener with `cargo build -p holonics --example listener`.
   Declare one route explicitly:
   - `--route observed --learn FRAME --learn-count N --population P --keys KEY_FILE` runs one
     continuing trunk. Every source and answer cell is compared, deposited and ingested. At the
     question end a private fork draws a continuation and writes it before the answer is read.
     Its maximum is the longest passage delivered so far. Population is fixed before content is
     read; its typed horizon ends the run without increasing it. This route has no cap flag,
     precision publication or serialized resume. Nothing the run reads is called unseen.
   - `--route sections --max-release-octets C --learn FRAME --learn-count N` retains the section
     boundary route for explicit parity. Add either `--read FRAME --read-count N` or
     `--release FRAME --release-count N --keys KEY_FILE` in separate processes. The CUDA example
     accepts only this route and refuses `observed` by name until its device fork is available.

Releases on sets no run has read require separate processes from saved states, after continuing
resume is available. The literal key read width and online baseline orders are exterior
readings. The field's exact-bit constitution budget remains fixed and refusals are reported.

Run synthetic partition/framing checks with `python3 -I tools/gsm8k/test_tools.py`.

For the tower (record `research/records/2026-10-30_THE_COARSE_LEVEL_HEADS_FOR_THE_TRACE_OF_WHAT_COMES_NEXT_AND_THE_FINE_LEVELS_READ_ITS_HEADING.md`, §43):
`tower_passage.py TRAIN_JSONL PARTITION_JSON OUT_DIR` renders each problem `question` END `answer` END
(END the record separator) with each byte's region (Q question, P prose, N digits outside the
calculations, M the calculation markup), the written rules' texts and six development questions as
flux prompts; `card_written.py prompts HELD` writes the free and calculation prompts for the card's
release route (cut at the separator 0x1F, `TOWER_PROMPT_SEPARATOR=31`) and `card_written.py convert`
turns its releases into the `FREE.tsv` and `MARKS.tsv` that `written_rules.py` reads.
