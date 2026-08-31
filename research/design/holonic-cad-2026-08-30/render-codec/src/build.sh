#!/bin/bash
S=$(cd "$(dirname "$0")" && pwd)
OUT=$S/../holonic-render-codec.html
{
cat $S/head.html
echo '<script>'
cat $S/core.js $S/colour.js $S/quadfield.js $S/poly.js $S/fields.js $S/models.js $S/glyphs.js $S/regions.js $S/brackets.js $S/hatch.js $S/receivers.js $S/minkowski.js $S/circuit.js $S/bord.js $S/polygraph.js $S/codec.js $S/paper.js $S/app.js $S/app3.js
echo '</script>'
cat $S/tail.html
} > $OUT
echo "built $(wc -c < $OUT) bytes"
