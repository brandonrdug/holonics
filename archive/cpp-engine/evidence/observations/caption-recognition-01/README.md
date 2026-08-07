# CAPTION RECOGNITION 01 · POINTING INTO REAL TEXT

**Grade:** CUDA MEASURED · DARK/SPARSE APERTURE WITNESS

Three honestly separate experience lights present a shape through the gaze eye together with one
real-text caption. The body sleeps and is read whole between lights while the same boundary
listener retains only the material it fed. A fourth, uncaptained light presents all three images
again. The read is direct: each probe's raw radiation is rendered beside any earlier caption
material whose standing enclosure it physically touches.

The primary species receives triangle→triangle-caption, circle→circle-caption, and
square→square-caption. The apparatus-matched sibling receives the same fields, gaze, edge order,
caption set, caption extents, current count, and samples, but rotates the collocations:
triangle→circle-caption, circle→square-caption, square→triangle-caption. The two species then
receive the exact same uncaptained probes. If the pointing follows the rotated experience rather
than an observer-authored shape name, the association belongs to collocation.

Every caption is 46 octets including its final newline. Each field is an exact 512×96 P5 plane;
each gaze presents 512 co-present contacts × 12 samples. No caption is present in the probe, no
answer head or text lookup enters the body, and the observer does not rank links. A direct caption
point is an occupied probe touch whose retained material is the earlier real caption itself.

The paired run is retained as a negative instrument read. Across the combined 1,536-contact /
18,432-sample probe, only eight events touched, one touch reached occupied standing, and no event
entered caption Mail. Sparse outlines under this gaze were almost entirely THE DARK TREAD; the
fixture did not expose the requested relation. The information-rich photographic successor is
measured at `../caption-recognition-02/`.

```bash
./observations/caption-recognition-01/generate.sh

SOMA_OBSERVATION_OUT=observations/caption-recognition-01/results/paired.txt \
SOMA_PERIPLUS_DIR=observations/caption-recognition-01/results/paired-bodies \
  cargo run --release -p life -- --cuda-eye-sequence \
  observations/caption-recognition-01/triangle.eye \
  observations/caption-recognition-01/circle.eye \
  observations/caption-recognition-01/square.eye \
  --probe \
  observations/caption-recognition-01/triangle-probe.eye \
  observations/caption-recognition-01/circle-probe.eye \
  observations/caption-recognition-01/square-probe.eye

SOMA_OBSERVATION_OUT=observations/caption-recognition-01/results/rotated.txt \
SOMA_PERIPLUS_DIR=observations/caption-recognition-01/results/rotated-bodies \
  cargo run --release -p life -- --cuda-eye-sequence \
  observations/caption-recognition-01/triangle-rotated.eye \
  observations/caption-recognition-01/circle-rotated.eye \
  observations/caption-recognition-01/square-rotated.eye \
  --probe \
  observations/caption-recognition-01/triangle-probe.eye \
  observations/caption-recognition-01/circle-probe.eye \
  observations/caption-recognition-01/square-probe.eye
```
