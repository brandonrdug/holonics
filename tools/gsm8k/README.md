# GSM8K exterior framing

The scripts partition and frame passages for the listener. Dataset content, keys and raw output
remain exterior. No generation is graded against numeric answers or delimiter patterns.

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
