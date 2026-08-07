# CAPTION RECOGNITION 02 · THE PHOTOGRAPH POINTS

**Grade:** SEQUENCE LISTENER BUILT · CUDA MEASURED · EXACT REPEAT

Two separate experience lights present information-rich photographs through the gaze eye with one
honest real-text caption apiece. The body sleeps and is read whole at each edge; the listener keeps
only its own exact Mail. Both photographs then return co-present without captions. Their radiation
is rendered against the real text carried by the two earlier lights.

The paired species receives fish→fish-caption, then sunrise→sunrise-caption. The apparatus-matched
sibling receives the same images, gaze, captions, caption extents, edge order, and probes, changing
only the collocation to fish→sunrise-caption and sunrise→fish-caption. Each caption is 44 octets
including newline. A direct point is an occupied probe event attributed to the earlier caption
source and rendered beside those exact bytes. Every matching, nonmatching, or shared point is
preserved; none is scored or crowned.

The two 256×256 source photographs are system-installed sample material under `/usr/share/projectM`.
`generate.sh` removes only their JPEG container and color basis into exact 8-bit P5 fields. Each
field presents 512 co-present contacts × 12 world-supplied gaze events.

Both uncaptained photographs point into their honestly paired real captions at strict row-local
events. The complete response also contains cross-caption and shared-caption points. Swapping only
caption collocation changes 605/1,024 probe worldlines and 1,761/12,288 raw rows; reversing the two
paired experience edges changes 983 worldlines and 3,949 rows. The paired repeat is exact across
every probe row and all three sleeping bodies. Full accounting is in `results/RESULTS.md` and
`../../RESEARCH/2026-07-13_THE_PHOTOGRAPH_POINTS_INTO_LANGUAGE.md`.

Run from `src/soma` after `./observations/caption-recognition-02/generate.sh`:

```bash
SOMA_OBSERVATION_OUT=observations/caption-recognition-02/results/paired.txt \
SOMA_PERIPLUS_DIR=observations/caption-recognition-02/results/paired-bodies \
  ./target/release/life --cuda-eye-sequence \
  observations/caption-recognition-02/fish.eye \
  observations/caption-recognition-02/sunrise.eye --probe \
  observations/caption-recognition-02/fish-probe.eye \
  observations/caption-recognition-02/sunrise-probe.eye

SOMA_OBSERVATION_OUT=observations/caption-recognition-02/results/swapped.txt \
SOMA_PERIPLUS_DIR=observations/caption-recognition-02/results/swapped-bodies \
  ./target/release/life --cuda-eye-sequence \
  observations/caption-recognition-02/fish-swapped.eye \
  observations/caption-recognition-02/sunrise-swapped.eye --probe \
  observations/caption-recognition-02/fish-probe.eye \
  observations/caption-recognition-02/sunrise-probe.eye
```

The repeat uses the paired command with create-new output paths. The order sibling exchanges only
the two experience-manifest positions. `analyze.py`, `compare.py`, and `probe_diff.py` reproduce the
declared reads without entering the machine. `./verify.sh` checks every pinned fixture and artifact,
regenerates those reads, normalizes the repeat's create-new paths, and compares all repeated bodies.
