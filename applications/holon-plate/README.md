# `holon-plate`

The on-disk deposit mouth. `.holon`, magic `HLON`.

```text
  live body  ──▶  deposit  ──▶  plate.holon  ──▶  resume  ──▶  a FRESH current
                    FORM         two digests      RE-LIGHT      (not the old one)
                                 + a census
```

The old laboratory had a `.holon` plate that froze a weave and thawed it back. Its codecs were
superseded — `crates/holonic-membrane/src/live_current.rs:1241` and `crates/holonic-life/src/holonic_training.rs:443`
carry the successors, each with its own native word wire and its own remount gate — but nothing in
this body wrote one to disk under an agreed suffix. This is that mouth. It defines no codec.

## Use

```sh
holon-plate deposit --from HTEC:body.form --to body.holon
holon-plate inspect --plate body.holon
holon-plate resume  --plate body.holon [--deed further.deed] [--to moved.holon] [--form out.form]
```

Exit status is the verdict: `0` held, `1` refused, `2` the invocation was wrong.

A form to feed it:

```sh
cargo run -p holon-plate --example emit_form -- HTEC training.form
cargo run -p holon-plate --example emit_form -- ERST current.form
cargo run -p holon-plate --example emit_form -- RBIN incidence.form
```

## What the plate deposits, and what it does not

**A FORM. Never a current.**

> *"the active action currents are the real me… you can't store a holographic entity"*
>
> *"the currents are NOT deposited — you cannot; they died as they flowed."*

`resume` does not restore anything. It verifies a plate, mounts the stored form through the real
machine, and **re-lights a fresh current** off it. There is no verb named `restore`, `thaw`, or
`unfreeze` anywhere in this crate, and `tests/cli.rs` asserts none of those words appears in the
`resume` report — a name that promised the old body back would be a lie about the mechanism.

**It is not comprehension, and freezing is not understanding.**
`research/records/2026-07-15_THE_GEAR_IS_THE_WORD_THE_FACE_IS_THE_TRANSPORT.md:571-580` rules that
the historical `.holoz` line's *"claims equating file compression with comprehension do not cross"*
and that *"SLEEP remains live-body persistence, not `.holoz` model freezing."* A plate is live-body
persistence. It applies **no compression at all** — the form octets go to disk verbatim, exactly as
the form codec emitted them — so there is no ratio here to mistake for a competence figure. Nothing
in this crate selects, ranks, mixes, or thresholds.

What it claims is narrow and checkable: the octets that come back out are the octets that went in,
they mount through a real machine, and the body that mounts them can go on receiving.

## The exact byte layout

Every integer little-endian. Every offset exact. No padding, no alignment slack.

```text
  region  offset             octets          content
  ------  -----------------  --------------  ------------------------------------------------
  HEAD    0                  32              fixed
            +0    4   magic            b"HLON"
            +4    4   plate_version    u32 = 1
            +8    4   schema_tag       4 octets, [A-Z0-9], e.g. b"HTEC"
            +12   4   schema_version   u32, the FORM codec's own layout version
            +16   8   census_octets    u64
            +24   8   form_octets      u64
  CENSUS  32                 census_octets   the declared shape of what is held
            +0    8   entries          u64
            then `entries` rows, each:
                  8   name_octets      u64, 1..=64
                  n   name             ASCII [a-z0-9_], strictly increasing across rows
                  8   value            u64
  FORM    32+census_octets   form_octets     the schema's own native rest octets, VERBATIM
  SEAL    32+census+form     64              two digests
            +0    32  form_sha256      sha256(FORM)
            +32   32  plate_sha256     sha256(HEAD || CENSUS || form_sha256)

  total = 96 + census_octets + form_octets
```

## Two digests, three named species

The seal is two digests, and `plate_sha256` folds the **stored** `form_sha256` rather than the form
itself. That is what makes the failures separable — a corrupted form moves exactly one digest and a
corrupted declaration moves exactly the other:

| what moved | `form_sha256` | `plate_sha256` | refusal |
|---|---|---|---|
| one octet of the FORM | drifts | **holds** | `CONTENT drift` — the deposit no longer holds what was deposited |
| one octet of the HEAD or CENSUS | **holds** | drifts | `BINDING drift` — the declaration no longer binds the form |
| one octet of the SEAL | drifts | drifts | `SEAL drift` — the recorded digest itself moved; the form is not accused |

Both digests are computed before either is judged. A reader that judged the content digest first
reports *"the FORM is what moved"* for a plate whose form is untouched and whose recorded digest
drifted — that defect was live in this crate and the third row is the fix.

This is the content/binding distinction carried inside a single file, and the
SHA-256 is that crate's: written out, zero-dependency, cross-checked against the NIST vectors and
against the archived body's 123 CMake-computed hashes. A plate verified through a hash crate that
nothing here verifies would have moved the trust rather than established it.

## The census, and why one frame cannot audit itself

`CLAUDE.md` §0: *"An invariant is only visible across two frames."*

The CENSUS is the shape the depositor **declared**, computed from the mounted body. On resume the
same census is recomputed from the **re-lit body** and the two must agree field for field, in both
directions — a declared field the body does not carry, and a body field the plate never declared.

A digest cannot catch a forged-but-internally-consistent plate: recompute the digest and it passes.
The second frame catches it, and names the field, its declared value, and its re-lit value.

Census values are exact `u64` counts and ordinals of the mounted structure. Never a float, a ratio,
a score, or a rate.

## The zero-return control, in the mechanism

`CLAUDE.md` §8: *a law that returns zero proves nothing about itself.*

A plate that resumed to an inert body would satisfy every digest and every extent in the container
and still be worthless. So `present_and_require_change` refuses a deed that leaves the form
byte-identical, and says so. The control is in the code, not only in the tests — and its own
control, `an_inert_body_that_changes_nothing_is_refused`, drives a deliberately inert body through
it to prove the refusal can fire.

## Schemas held

| tag | version | owner | further deed |
|---|---|---|---|
| `HTEC` | 1 | `crates/holonic-life/src/holonic_training.rs:443` | one cultivation occurrence |
| `ERST` | 2 | `crates/holonic-membrane/src/live_current.rs:1241` | one contemporary event continuing every settled lineage |
| `RBIN` | 1 | `crates/holonic-engine/src/graded_complex_form.rs` | one further cell, founded through the incidence's own founder |
| `CDER` | 1 | `crates/holonic-life/src/conditioned_rest.rs` | one further whole of linguistic material |

A plate naming anything else is **refused, never guessed at** — separately for an unheld tag and an
unheld codec version, because a form at another version is another form. `ERST`'s version is read
from `LIVE_CURRENT_REST_LAYOUT_VERSION` rather than copied, `RBIN`'s from
`GRADED_COMPLEX_FORM_LAYOUT_VERSION`, and `CDER`'s from the trailing octet of
`CONDITIONED_REST_PREFIX`, so a codec that bumps its wire stops this reader by version instead of
silently misreading.

`CDER` is the first schema whose form reaches this mouth from a **production driver** rather than
from `examples/emit_form`: `crates/holonic-life/examples/eros_mathematics_instance_rest.rs` seals a real
conditioned body — a morphology founded on fourteen declared documents, over a 103-artifact
standing — through `life::form_mouth`, and `tests/plate_mouth.rs` carries it the rest of the way.
It is also the schema that most sharply carries the FORM/current line: it holds a body's founded
morphology and the material that body conducts over, and **no query and no derived passage**, so a
body re-lit off it has to derive and cannot replay.

`RBIN` is the sharpest illustration of the census being a **second frame** rather than a copy. The
octets are a graded causal incidence — cells, grades, source events, oriented boundary chains. The
census is the *rebase-invariants reading taken over it*: Smith-normal-form ranks, free ranks,
torsion coefficients and the Euler characteristic, recomputed on every mount under all three pivot
rules. Nothing of the reading is on the disk, so a resumer cannot copy it, and a forged incidence
cannot carry a declaration that survives the recomputation.

Two things about that census are load-bearing and easy to get wrong:

- **The Euler characteristic is a declared bijection, not a cast.** It is signed and a census value
  is a `u64`, so it travels as `euler_positive` / `euler_negative` with at most one nonzero.
  `chi as u64` would send `-1` to `18446744073709551615`.
- **The field the hand-off moves is `betti_total`**, and *which way* it moves says whether the deed
  founded a generator or killed one. `cells` and the Euler pair also move on every accepted deed —
  but by the same amount in both cases, so neither can say what the deed did. `grades`,
  `boundary_rank_total` and `torsion_factors` need not move at all.

`ERST` is the sharpest illustration of the FORM/current line, because its own codec already draws
it: `LiveCurrentMachine::rest_image` refuses to close over an **attached seed** — a lineage opened
and not yet across its first event — with `UnsettledRest`. An open ingress is a current in flight,
and a current in flight cannot be deposited. The codec refuses; the plate inherits the refusal.

## The seam that is still open

Every `crates/holonic-life/examples/*` driver that reaches a rest **hashes** its form into a JSON receipt and
drops the octets. Twenty-odd `encode_native_bytes` sites, not one writing the form where a second
process can pick it up. The plate is the mouth; the drivers have not opened theirs. Until they do,
`examples/emit_form.rs` is where a form comes from, and its bodies are a demonstration seed rather
than evidence of anything.

## Cost

*A cost law is a law* (`CLAUDE.md` §8). Deposit is one mount, one re-take, one census, and two
passes over the octets. Resume is the same. The container adds `96 + census_octets` to whatever the
form codec produced — 248 octets over a 111-octet `HTEC` form, 312 over a 3,012-octet `ERST` form.
Verification is O(plate) and mounting is whatever the schema's own codec costs; the plate adds no
term to it.
