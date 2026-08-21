#!/usr/bin/env bash
set -euo pipefail

# Typst embeds the creation instant in PDF metadata. Fix that apparatus coordinate so rerendering
# the same source returns the same PDF bytes; layout invariance is still graded separately.
export SOURCE_DATE_EPOCH=0

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source_root="$repo_root/research/fixtures/m0_mathematical_source_circulation"
natural_pdf="$repo_root/tmp/pdfs/2608.13553-heat-kernel-geometry.pdf"
natural_pdf_identity="9518ea5939a53650f82d7b016e017df5e7cacfc1d8728e0ac2aaa25bf68fc4e5"
face_root="$repo_root/output/m0_mathematical_source_circulation/faces"
control_root="$repo_root/tmp/pdfs/m0-source-circulation-controls"

if [[ ! -f "$natural_pdf" ]]; then
  echo "missing fixed natural-document source: $natural_pdf" >&2
  exit 2
fi

read -r observed_natural_identity _ < <(sha256sum "$natural_pdf")
if [[ "$observed_natural_identity" != "$natural_pdf_identity" ]]; then
  echo "fixed natural-document identity moved: $observed_natural_identity" >&2
  exit 3
fi

mkdir -p "$face_root/synthetic" "$face_root/natural" "$control_root"

{
  typst --version
  pdftocairo -v 2>&1 | head -n 1
  pdftoppm -v 2>&1 | head -n 1
  pdftotext -v 2>&1 | head -n 1
  rsvg-convert --version
  sha256sum "$natural_pdf"
  printf '%s\n' \
    'typst compile harmonic-baseline.typ -> PDF/SVG/PNG' \
    'typst compile harmonic-reflow.typ -> SVG/PNG' \
    'typst compile harmonic-perturbed.typ -> SVG/PNG' \
    'rsvg-convert harmonic-conjugation.svg -> exact addressed diagram raster' \
    'typst compile reflow/perturbed -> temporary PDF; pdftotext -bbox-layout; remove temporary PDF' \
    'pdftocairo -svg: synthetic PDF page 1; natural source pages 5 and 10' \
    'pdftoppm -png -r 144: synthetic PDF page 1; natural source pages 5 and 10' \
    'pdftotext -bbox-layout: synthetic PDF page 1; natural source pages 5 and 10'
} > "$repo_root/output/m0_mathematical_source_circulation/apparatus.txt"

typst compile "$source_root/harmonic-baseline.typ" \
  "$face_root/synthetic/harmonic-calibration.pdf"
typst compile --format svg "$source_root/harmonic-baseline.typ" \
  "$face_root/synthetic/harmonic-baseline-source.svg"
typst compile --format png --ppi 144 "$source_root/harmonic-baseline.typ" \
  "$face_root/synthetic/harmonic-baseline-source.png"
typst compile --format svg "$source_root/harmonic-reflow.typ" \
  "$face_root/synthetic/harmonic-reflow-source.svg"
typst compile --format png --ppi 144 "$source_root/harmonic-reflow.typ" \
  "$face_root/synthetic/harmonic-reflow-source.png"
typst compile --format svg "$source_root/harmonic-perturbed.typ" \
  "$face_root/synthetic/harmonic-perturbed-source.svg"
typst compile --format png --ppi 144 "$source_root/harmonic-perturbed.typ" \
  "$face_root/synthetic/harmonic-perturbed-source.png"
rsvg-convert --width 1920 --height 440 "$source_root/harmonic-conjugation.svg" \
  --output "$face_root/synthetic/harmonic-conjugation-diagram.png"

typst compile "$source_root/harmonic-reflow.typ" \
  "$control_root/harmonic-reflow-control.pdf"
typst compile "$source_root/harmonic-perturbed.typ" \
  "$control_root/harmonic-perturbed-control.pdf"
pdftotext -f 1 -l 1 -bbox-layout "$control_root/harmonic-reflow-control.pdf" \
  "$face_root/synthetic/harmonic-reflow-control-bbox.html"
pdftotext -f 1 -l 1 -bbox-layout "$control_root/harmonic-perturbed-control.pdf" \
  "$face_root/synthetic/harmonic-perturbed-control-bbox.html"
rm -f \
  "$control_root/harmonic-reflow-control.pdf" \
  "$control_root/harmonic-perturbed-control.pdf"

pdftocairo -svg -f 1 -l 1 \
  "$face_root/synthetic/harmonic-calibration.pdf" \
  "$face_root/synthetic/harmonic-baseline-pdf.svg"
pdftoppm -f 1 -l 1 -singlefile -png -r 144 \
  "$face_root/synthetic/harmonic-calibration.pdf" \
  "$face_root/synthetic/harmonic-baseline-pdf" >/dev/null
pdftotext -f 1 -l 1 -bbox-layout \
  "$face_root/synthetic/harmonic-calibration.pdf" \
  "$face_root/synthetic/harmonic-baseline-pdf-bbox.html"

for page in 5 10; do
  pdftocairo -svg -f "$page" -l "$page" "$natural_pdf" \
    "$face_root/natural/heat-fisher-page-$page.svg"
  pdftoppm -f "$page" -l "$page" -singlefile -png -r 144 "$natural_pdf" \
    "$face_root/natural/heat-fisher-page-$page" >/dev/null
  pdftotext -f "$page" -l "$page" -bbox-layout "$natural_pdf" \
    "$face_root/natural/heat-fisher-page-$page-bbox.html"
done

(
  cd "$repo_root"
  sha256sum \
    research/fixtures/m0_mathematical_source_circulation/harmonic-source.typ \
    research/fixtures/m0_mathematical_source_circulation/harmonic-baseline.typ \
    research/fixtures/m0_mathematical_source_circulation/harmonic-reflow.typ \
    research/fixtures/m0_mathematical_source_circulation/harmonic-perturbed.typ \
    research/fixtures/m0_mathematical_source_circulation/harmonic-conjugation.svg \
    tools/build_m0_source_fixture.sh \
    output/m0_mathematical_source_circulation/apparatus.txt \
    output/m0_mathematical_source_circulation/faces/synthetic/* \
    tmp/pdfs/2608.13553-heat-kernel-geometry.pdf \
    output/m0_mathematical_source_circulation/faces/natural/* \
    > output/m0_mathematical_source_circulation/face-identities.sha256
)

echo "$face_root"
