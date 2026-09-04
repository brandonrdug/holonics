# Soma receiver observatory

This is a read-only instrument for inspecting one declared receiver-relative section of an exact
world artifact. It does not first draw a whole body in an absolute room. The world supplies the
root, coordinates, metric or pairing, and lawful restriction/rebase map; the canvas is a disposable
face of that declaration.

Serve the repository root, then open the instrument:

```sh
python3 -m http.server 8017
```

`http://localhost:8017/src/soma/tools/observatory/`

## Default instruments

- **Prime / axis section** reads one common integer through distinct cyclotomic residue fibers.
  The base is the declared divisor-test order; each exact vertex retains `(p,q,r)` from `n=qp+r`
  and its symbolic `zeta_p^r` phase. A zero-pole hit closes a composite and survival FOUNDS a new
  valuation basis. Neighbor samples stay unjoined. Bounded affine relations such as
  `2*53-1=3*5*7` are named as separate exact rows.
- **Prime / succession strings** holds one prime axis while source chronology sweeps it. Direct
  `zeta_p^r` and conjugate `zeta_p^(-r)` strings retain quotient, residue, complete winding,
  recurrence, and every source event. Their visible p-gons are rational-series enclosures of the
  cyclotomic embedding, not evaluated angles.
- **Primorial rebase**, selected inside Prime, shows exact self-similarity as restriction followed
  by rebase. It exposes the `COPY -> CUT -> JOIN` rows between rational residue strips; no circle
  constant or visual resemblance supplies the recurrence.
- **Zeta / scale-turn series** exposes every prime power as `(p,k,p^k)`, the formal scale
  `k*ell_p`, exact squared amplitude `1/p^k`, and retained Gaussian-rational coefficients for the
  direct, conjugate, reciprocal, and reflected-conjugate character sheets. Logarithms are retained
  atanh series with explicit tails.
- **Zeta / valuation rebase** shows `Law(N/60 | 60 divides N) = Law(N)` for exact finite valuation
  cylinders at `sigma=2`. Both ordered factorizations of 60 survive as separate event strings.
  The amplitude hand is the retained formal series for `exp(+/-i*ell_60)`, not a decimal angle.
- **Critical** uses exact rational Cayley and stereographic maps. Its Smith field retains each
  listed-zero factor and nearest local factor leader; it never sums the finite field into a giant
  scalar. The residual view keeps each lower and upper endpoint as a separate exact ratio and does
  not form a midpoint. The open construction is stated directly: carry the complete prime-power
  and archimedean trace and close every contributing character in the unitary dual.
- **Carrier** renders only one selected causal path from the linguistic-code rest artifact. That
  artifact retained cellular topology but not the application inscription, so this panel cannot
  claim what its paths were about. Whole-body counts remain testimony and are not rendered as a
  particle stack. The live `linguistic-code` command is retired because its regional incidence was
  derived from inscription lengths; only the read-only historical observer remains.

The default artifacts are:

- `observations/bounded-polyglot-geometric-world-01/REPORT.json`
- `observations/interval-explicit-formula-world-01/build-01/EXPLICIT.json`
- `observations/interval-explicit-formula-world-01/LMFDB-FIRST-64-ZEROS.tsv`
- `observations/eros-linguistic-code-world-01/host-run-09/CONSTITUENTS.json`

The 17 MB carrier report is lazy: it is not fetched or parsed unless **Carrier** is selected.

## Scientific boundary

- `Lambda` and Soma are unchanged by observation. Controls select a world-supplied receiver cut;
  no control returns to the machine.
- There is no free-orbit camera. Every scene supplies integer chart coordinates; section scale
  changes only their final pixel presentation.
- Every selectable mark resolves to an exact row in the analytical table. The complete receipt can
  be exported as JSON. Canvas coordinates never establish identity or causality.
- No analytical path uses a JavaScript floating-point value. Integers remain safe integers;
  fractions are reduced `BigInt` ratios; `pi`, logarithms, exponentials, sine, and cosine are
  retained rational series with explicit remainder enclosures. Imported decimal testimony is
  converted to exact ratios without a midpoint. Only the browser's final integer-coordinate to
  pixel transform is disposable.
- Each fixed residue fiber is a finite cyclotomic polygon. Its lifted section is an ordered bundle chart, not an
  absolute product embedding. A new prime axis and a prime-square horizon are stratified seams,
  not fabricated smooth Ricci curvature. Ricci flow would require a world-supplied evolving metric
  and connection.
- Lightning, static potential, and probability-field language is represented structurally: leaders
  traverse only afforded local sheets, pole contact closes a path, and a surviving path changes
  later terrain. The instrument does not assert that arithmetic is a physical electromagnetic or
  quantum field.
- The display keeps exact receipt extent, selected relation extent, and presented marks distinct.
  Hiding a layer or changing scale never rewrites the source artifact.

## Exact checks

```sh
node --test src/soma/tools/observatory/observatory-core.test.js
```

The tests check the receiver laws, refuse the former absolute whole-body cellular plot, reject
fractional JavaScript numbers anywhere in analytical scenes, and reject direct transcendental
evaluation in the exact core.

## Export a live rest cut

The explicit observer command remounts each named rest read-only and writes one disposable carrier
report:

```sh
cd src/soma
cargo run -q -p life -- linguistic-code-observe \
  observations/eros-linguistic-code-world-01/host-run-09/CONSTITUENTS.json \
  ecology=observations/eros-linguistic-code-world-01/host-run-09/ecology.rest \
  remove-then-reverse=observations/eros-linguistic-code-world-01/host-run-09/remove-then-reverse/world.rest \
  reverse-then-remove=observations/eros-linguistic-code-world-01/host-run-09/reverse-then-remove/world.rest
```

The output path must not already exist. This command presents no current, emits no radiation, and
does not rewrite source rest.
