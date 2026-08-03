# Number-world lived atlas

This is a dependency-free boundary instrument for the exact CUDA observation. It does not alter
the engine, calculate a machine response, move a machine coordinate, or feed an observer class back
into the body.

## Open the measured run

From `src/soma/observations/number-world-01`:

```bash
python -m http.server 8123 --bind 127.0.0.1
```

Then open either address:

```text
http://127.0.0.1:8123/tools/atlas/
http://127.0.0.1:8123/tools/atlas/?artifact=../../results/run-a-atlas.json
```

The query target must be same-origin over HTTP. The second form is the reproducible headless entry.
The file control is a local fallback. Loading or validation errors remain visible in the status
line.

The complete v2 artifact is `results/run-a-atlas.json`. It carries 10,011 lineages, 46,138 raw
touches, and 430,788 receiving-edge Mail landings. The loaded overview is
`results/atlas-overview.png`.

```text
b74afd63a73781098366377a0c7241b7adc1dcddb1e0f07270d85c82e431f76e  results/run-a-atlas.json
ad9f2a749205e686b11282c94fb8348572a2439ed6a4a7351f5cf6efc5de7d15  results/atlas-overview.png
```

## The two chart faces

- Raw radiation is drawn only on the archived pre-light standing axis 256. A plotted point is the
  center of its exact integer `(row, column)` cell. Ordered lines join only that lineage's actual
  successive touches.
- Mail is drawn separately on the post-light receiving axis 1024. Its ordered landing sequence is
  never projected back into the raw chart.
- Quiet events and folds without touches have no lawful chart coordinate. The inspector's ordered
  raw-event strip retains them as `Q` and `F`; it never invents a point.
- Exact coordinate collisions remain coincident. Selecting one opens every visible coincident
  event in the inspector rather than displacing points for legibility.

Filters are reversible across declared domain, operator family, outcome, and exact lineage ids or
ranges. Selecting an event with `paired_line` enables the exact numeric and unit-A comparison.
Operator family remains independent from every endpoint class.

Canvas controls are keyboard accessible: arrows pan, plus and minus zoom, and Home restores the
whole axis. Exact lineage and event or landing inputs provide a fully textual route to every record.

## Observer overlays

Prime, semiprime, and prime-power marks are derived after the run only when the complete ordered
positive multiplication incidence is present. For this world the check requires all 280 declared
relations through 64. It then derives nontrivial-factor incidence, followed by prime factor chains.

The overlays do not claim separated regions. They interleave on the lived construction. Faces 4,
9, 25, and 49 therefore carry both semiprime and prime-power marks. Reversed factor orders remain
separate lineages even when their evaluated face agrees.

## Recreate the complete artifact

The extractor follows create-new observation practice. Choose a path which does not yet exist:

```bash
python tools/extract_atlas_events.py \
  results/run-a.txt \
  --manifest MANIFEST.tsv \
  --output results/run-a-atlas-replay.json
```

Schema `soma.lived-atlas.events.v2` requires both coordinate faces and every exact Mail current.
The reader refuses the earlier v1 shape because an axis without its landing construction is not a
complete atlas.

## Deterministic gates

From `src/soma`:

```bash
python -m unittest discover -s observations/number-world-01/tools/tests -v
node observations/number-world-01/tools/atlas/tests/atlas-core.test.js
node --check observations/number-world-01/tools/atlas/atlas.js
node --check observations/number-world-01/tools/atlas/atlas-worker.js
```

The gates cover separate raw and Mail axes, exact source ranges, ordered landings, complete
multiplication incidence, dual semiprime and prime-power marking, filters which preserve empty
selections, numeric and unit pairing, and ordered quiet, fold, touch, CUT, and brick faces.
