# COUPLED PAGE 01 · THE GAZE CARRIES THE FIELD

**Grade:** EYE BUILT · WHOLE SLEEPING BODY HOST/CUDA EXACT · COUPLED-PAGE CUDA MEASURED · BOUNDED
CROSS-SENSE RELATION ⊕ APPARATUS-MATCHED CAPTION-CONTENT CLEAVAGE MEASURED

This is the first bounded instrument for `FORMULA §XXXI` and
`RESEARCH/2026-07-13_THE_GAZE_CARRIES_THE_FIELD.md`. It asks one narrow question:

> Does an exact caption/source current co-present with a rendered arithmetic construction change
> the body's later reading of one common eyes-only arithmetic tableau?

The eye removes an exact binary-PGM container and presents one temporal intensity current per
aperture contact. All contacts share the declared gaze history and are co-present. Neither contact
coordinates, raster order, image levels, features, thresholds, labels, nor a scale choice enter
the body. The PGM field, aperture, and gaze are this bounded observer instrument, not production
limits.

## Delivered construction

The context field renders:

```text
2*4=4*2=8
```

The coupled context also presents the exact source and the honest caption:

```text
reversed products share the face eight
```

The eyes-only foil presents the identical context field and gaze without those two material
currents. The apparatus-matched content foil presents the identical field, gaze, exact source, lane
count, and 40-octet caption extent, changing only the caption to:

```text
blue herons cross quiet marshes at dusk
```

All three siblings then receive the identical eyes-only tableau:

```text
8/2=4    8/4=2
```

The later field is not an expected answer. The read is the later construction itself: radiation,
touches, winding, terms, and resulting topology, real against both foils. The eyes-only sibling
shows that added material bends the gaze; the matched caption sibling shows that content changes
which route and enclosures the later gaze traverses. Neither installs or consults a decoder.

## Bounded instrument

- exact scalar field: `512x96`, binary PGM (`P5`), maximum 255;
- aperture: `32x16` contacts, hence 512 co-present visual currents;
- gaze: 12 supplied positions; each contact carries 12 temporal intensity samples;
- common gaze and later field are byte-identical between real and foil;
- typography is fixed only so the observation is reproducible.

`generate.sh` creates the two exact fields with ImageMagick. The manifests are the complete organ
boundary declarations. Run the host/CUDA eye seam first, then the two create-new lifecycle reads.
The exact read, repeat hashes, and next controlled history are deposited in
[`results/RESULTS.md`](results/RESULTS.md).

```bash
./observations/coupled-page-01/generate.sh

cargo run --release -p life -- \
  --eye-card observations/coupled-page-01/context-coupled.eye

cargo run --release -p life -- \
  --eye-card observations/coupled-page-01/context-content-foil.eye

SOMA_OBSERVATION_OUT=observations/coupled-page-01/results/coupled.txt \
SOMA_PERIPLUS_DIR=observations/coupled-page-01/results/coupled-bodies \
  cargo run --release -p life -- --cuda-eye-cycle \
  observations/coupled-page-01/context-coupled.eye \
  --later observations/coupled-page-01/later.eye

SOMA_OBSERVATION_OUT=observations/coupled-page-01/results/visual-foil.txt \
SOMA_PERIPLUS_DIR=observations/coupled-page-01/results/visual-foil-bodies \
  cargo run --release -p life -- --cuda-eye-cycle \
  observations/coupled-page-01/context-visual-only.eye \
  --later observations/coupled-page-01/later.eye

SOMA_OBSERVATION_OUT=observations/coupled-page-01/results/content-foil.txt \
SOMA_PERIPLUS_DIR=observations/coupled-page-01/results/content-foil-bodies \
  cargo run --release -p life -- --cuda-eye-cycle \
  observations/coupled-page-01/context-content-foil.eye \
  --later observations/coupled-page-01/later.eye
```
