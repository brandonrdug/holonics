# CONVERSATION CONSEQUENCE 01

**GRADE: WORLD-SIDE CONTACT STROKE CHOSEN · PRE-DATA APPARATUS · NO NEW SOMA LAW · NO CARD
MEASUREMENT YET**

This observation closes the next bounded part of `FORMULA §XLII`: radiation from the already
measured conversation horizon changes world material, and the changed material returns later
through the ordinary gaze eye.  It does not turn Mail into a drive and does not add an actuator,
decoder, selector, score, or gaze controller to Soma.

## The exact cut

The gaze organ already gives the world the position of every contact:

```text
contact q at gaze event t lands at p(t,q) = g[t] + q
```

Soma returns one 39-word radiation row for that same contact and event.  Word zero is the native
producer-state face already typed by the radiation wire: `FOLD | STEP | CUT | BRICK`.  This first
bounded actuator exposes that face directly to an 8-bit grayscale material cell:

```text
flags = 0      => the world cell does not change
flags != 0     => canvas[p(t,q)] <- flags
```

The assignment is a **chosen transducer face**, not a claim that flags are color, meaning, force,
or the identity of the whole radiation row.  No palette or scale is applied: the canonical values
`0`, `1`, `3`, and `15` cross numerically unchanged.  The complete 39-word row remains the output
of record beside this declared compression.

All contacts at one gaze event are co-present and land at distinct translated positions.  They do
not compete, sum, vote, or alter each other.  Gaze-time orders successive events.  The world ledger
records `(t, q, position, prior cell, next cell, full-row digest)` for every actual mark.  Replaying
that ledger backward must restore the source PGM byte-exactly; this exact inverse is owed because
the instrument introduced the gauge seam.

## Histories and controls

The source canvas and later gaze are identical throughout.

- `broad-own`: the broad species receives the canvas marked by its own probe radiation.
- `broad-foil`: the same broad sleeping body receives the canvas marked by the exact-reverse
  history's real probe radiation.  This isolates world material at a common receiver.
- `reverse-own`: the reverse species receives its own marked canvas.
- `repeat-own`: the fresh broad repeat receives its own marked canvas.

Each of those successor bodies then receives the byte-identical `then-proceed` eye page.  The
`broad-own-then` versus `broad-foil-then` comparison therefore holds the contemporary light fixed;
only the standing consequence of the prior world stroke differs.

The repeat must be exact through source, action ledger, changed canvas, later radiation, and next
body.  The broad and reverse action canvases must differ before the card runs.  The foil is a real
lawful worldline, never an empty or null surface.

The returned eye manifest carries the unchanged exact synthesis text beside the changed visual
field.  This is ordinary world collocation.  The source is not rewritten to pretend the marks were
already in the text.

## Commands

From `src/soma/`:

```bash
python3 -B observations/conversation-consequence-01/make_world.py
python3 -B observations/conversation-consequence-01/verify_world.py
bash observations/conversation-consequence-01/gate_cuda.sh
bash observations/conversation-consequence-01/run_cuda.sh
python3 -B observations/conversation-consequence-01/read_results.py
bash observations/conversation-consequence-01/run_later_cuda.sh
python3 -B observations/conversation-consequence-01/read_later_results.py
```

Generated worlds and every result are create-new.  No file is overwritten.
