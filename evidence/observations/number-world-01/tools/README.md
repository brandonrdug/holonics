# Lived-atlas event extraction

`extract_atlas_events.py` reads the create-new text artifact written by
`life --cuda-continue` and emits deterministic JSON for the canvas/HTML lived atlas. It is only a
boundary parser. It does not lay out, combine, rank, score, or classify paths.

The complete local renderer and its exact operating instructions are in [`atlas/`](atlas/README.md).

```bash
python observations/number-world-01/tools/extract_atlas_events.py \
  observations/number-world-01/results/run-a.txt \
  --manifest observations/number-world-01/MANIFEST.tsv \
  --output observations/number-world-01/results/run-a-atlas-replay.json
```

The output path is create-new. Omit `--output` to write JSON to standard output. The measured v2
artifact is `results/run-a-atlas.json`; its exact operation and gates are declared in
[`atlas/README.md`](atlas/README.md).

## Two axes, not one

The current CUDA continuation report names two distinct chart faces:

- `radiation_receiving_axis` is the archived body's pre-light standing axis. Raw radiation grips
  were constructed against this chart, and every raw touch carries this axis and
  `coordinate_frame=pre_light_standing` beside its quotient/remainder row and column.
- `edge_receiving_axis` is the post-light receiving chart after the edge integration. New Mail
  landings inhabit this chart. Every Mail current retains source range, landing order, exact grip,
  and its own quotient/remainder row and column. This chart must not be used to reinterpret the
  earlier raw grips.

If the edge carries `256 -> 512`, a raw grip is therefore divided by 256, not 512. This extractor
does not silently zero-extend it into the later chart.

## Exact source relation

Every lineage retains:

- the staged source path;
- its exact inclusive-start/exclusive-end record range;
- the raw record in canonical `ascii::escape_default` text and byte-exact hexadecimal form; and
- every adjacent delivered event's overlapping two-octet range and text in the same two forms.

With `--manifest`, the join is exact on `(source,start,end)`, delivery order, octet extent, and
record SHA-256. The extractor copies `domain`, `family`, operands, face, unit relation, and paired
line verbatim from the declaration; it never guesses a family from equation text.

## Event face

Events remain in lineage/atom order. Each carries the complete 39-word radiation-v2 row, flags,
fold/quiet face, and an optional touch with grip, chart coordinates, occupied face, CUT face, and
completed-brick typed construction. Atom zero remains explicit aperture padding.

The CUDA artifact currently prints `TermCounts` only for the complete lineage. Those values appear
as `term_totals`; each event's `term_delta` is explicitly `null`. Assigning a lineage total to one
event would fabricate a chronology that the artifact does not expose.

Run the isolated parser gate with:

```bash
python -m unittest discover \
  -s observations/number-world-01/tools/tests -v
```
