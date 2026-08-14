# The cut becomes the codec's, and the later current rides the deposit

**Date:** 2026-08-13
**Truth status:** `established-bounded [measured]` for both returns; `implemented-exact` for the
carriers; **`open`** for everything the goal's first clause still owes.
**Evidence:** `measured` — 2,189 workspace tests passing with 0 failures over 42 result lines, three
new falsifiers named below, and one new driver run end to end.
**Occasion:** the goal set 2026-08-13 — *the arrival lands at a location it did not choose, deposits
into the terrain, and a later current rides the deposit.*
**Canon path:** `canon/THE_INFORMATION_ENGINE.md` §5 states the mouth; this record is what was built
against it.

---

## 1 · The addressing was already repaired, and the fixtures already fire

Both convictions standing on the live material mouth are closed in source, and this was established
by reading the owners rather than by trusting the roadmap row:

- `soma/life/src/text_material/import.rs` `container_address` takes `path.file_name()`, and
  `founded_record_identity` founds on the record address. The host path is out of the identity.
- `record_conversation` takes the rollout conversation from the `session_meta` record alone; the
  fallback to the message id is gone.

And the fixtures that could not fire now do:
`a_rollout_conversation_is_the_session_and_never_a_message_identity` declares a `session_meta`
carrying **both** `id` and `session_id` with distinct values, so a fallback would be visible; and
`one_container_read_at_two_host_paths_founds_one_identical_body` reads one container at two paths.

**What remains on that plan is the re-seal**, not the repair: the sealed corpus on disk was written
under the old law and its address is stale.

## 2 · The cut is the codec's, and so is the identity

`soma/life/src/incidence_production.rs` cut every occurrence with `split_whitespace()` and keyed each
site on `(causal_rank, patch_string)`. Two authored decisions sat where no caller could vary them,
and together they meant the mouth admitted exactly one material: **whitespace-delimited UTF-8
compared by byte equality.** The winding was taken over `patch.as_bytes()`, so any other material's
windings would have been read off a UTF-8 rendering of its identity rather than off the material.

`DeclaredOccurrence.text: String` is now `inscription: Vec<Patch>`, and a `Patch` carries two things
that were previously one:

```text
octets    the material's OWN carrier at this position, unnormalized;
          adjacency founds ∂ and the §III windings are taken over it
identity  what the codec declares makes two patches THE SAME PATCH
```

`DeclaredOccurrence::from_text` is the text codec, **declared rather than authored** — whitespace
cut, identity equal to surface — so every prior reading is bit-identical. `Site` gained `octets`
beside `surface`, and both `found` and `admit_later` read the codec's patches instead of cutting.

**The founding identity is the codec's; the revision is behavioural, and it is not this type's job.**
`crate::decomposing_codec` compresses the reading and re-cuts at the collapsed pair's own separating
word. Founding under conduct would be circular — the complex must exist before its conduct partition
does — so the codec declares and the returned collapse revises. That also means a wrong grain at the
mouth is **a collapsed pair carrying a shortest separating word**, not an uncertainty cost, which is
the framing the corpus refuses.

**Three falsifiers, each able to fail:**

| falsifier | what it establishes |
|---|---|
| `a_material_that_is_not_text_admits_and_its_windings_come_from_its_own_octets` | patches of `0xAA 0x55` and `0x00 0xFF` — not valid text — admit, and the site's winding is **14**, the material's, where the identity `"w0"` would have given **6** |
| `declaring_a_different_patch_identity_founds_a_different_complex` | the same octets under two declared identities found different complexes; a total collapse returns `NoContact` rather than a one-site reading that looks like an answer; a partial merge founds a strictly coarser complex |
| `the_text_codec_reproduces_the_previous_internal_cut` | the control: identity equals surface, octets equal the identity's bytes, and the declared surface round-trips |

**Bound.** The three library callers of `DeclaredOccurrence` — `algorithmic_material`,
`material_incidence`, `recurrent_section` — and every driver now declare through the text codec, so
**no material other than text is yet admitted by anything that runs.** The type admits it; nothing
supplies it. A weight-file or audio codec is the next material, and it is not built.

## 3 · The later current rides the deposit, and removing the deposit removes the ride

`soma/life/examples/the_later_current_rides_the_deposit.rs`. Nothing in this tree measured this
before: `canon/THE_INFORMATION_ENGINE.md` §0 measures the body as a descent with no return edge, and
the spine's own audit is that *"the engine has no `q_n = q_m` anywhere. It is a strict pipeline."*

The shape is admit A → admit B on the changed terrain → **withdraw A** → admit the *same* B on the
restored terrain → compare. Step three is what makes step five mean anything: if the withdrawal were
not exact, a difference between the two readings of B could be an artifact of a damaged complex.

**Measured, on a standing terrain of 10 constituents, 13 contacts, 5 closed boundaries:**

```text
A = "the return founds the arc and the arc carries the leader"
      reached 4 · reopened 2 · saturated 2 · untouched 1 · FOUNDED 2
      founded: "the and arc"   "the founds return"

B with A standing      reached 6 · reopened 4
B with A withdrawn     reached 4 · reopened 2

the control            10 constituents · 13 contacts · 5 closed boundaries
                       5 emissions bit-identical to the standing terrain

reopened ONLY with the deposit standing:   "the founds return"   "the and arc"
```

**The two compounds the later current reopened only when the deposit stood are exactly the two the
deposit founded.** The ride is named cell by cell rather than counted, and it is removed by removing
the structure — which is the ablation shape the operating contract requires of any claim that a
returned deposit changed later conduct.

The driver refuses rather than reporting a success in two places: if the deposit deposits nothing it
says so, because *if nothing was deposited, nothing passed*; and if the two readings of B agree in
every coordinate it names that a falsification, because a later current blind to a real change of
terrain did not ride anything.

## 4 · The attachment is two-sided, and its law has a measured aperture

An arrival used to land on standing by **identity coincidence alone**: its patches founded
constituents, and any that keyed equal to a standing constituent at the same causal rank became that
constituent. The terrain contributed nothing, which is what `H.0466` refuses — *"ground is not a
passive terminal selected from above"*, with the requirement that a world *"admit plural upward
leaders and retain connected and unconnected outcomes instead of manufacturing one ground
endpoint."*

`IncidenceComplex::attachment` is that law. Every exposed standing constituent reaches toward every
arriving one, and **§IV decides with both sides**: donor and acceptor are opposed boundary roles, so
a pair meets when the roles are opposed and refuses when they are the same. Neither side chooses the
attachment point. Both polarities are read off the complex's own bonds and `⪯` edges — so this is
not the preimage of a field a driver authored, and the gauge check proves the material moves it.

**And the law has a measured aperture, which the driver reported rather than passing over.** On the
driver's dense material every constituent both donates and accepts somewhere, so every constituent is
`Both` and **20 of 20 attempts met**. That is a statement about the material, not a success: a check
whose outcome cannot vary tests nothing. The driver says so and then runs the discriminating control
on material with genuine endpoints:

```text
     alpha    donor  ✕  donor    delta      winding 2  sheet -1
     alpha    donor ──▶ acceptor epsilon    winding 1  sheet  1
      beta     both ──▶ donor    delta      winding 2  sheet -1
      beta     both ──▶ acceptor epsilon    winding 1  sheet  1
     gamma acceptor ──▶ donor    delta      winding 2  sheet -1
     gamma acceptor  ✕  acceptor epsilon    winding 1  sheet  1
```

Four met, two did not, and each refusal carries the material's own reading of the gap it could not
cross rather than being deleted. Two falsifiers hold it:
`the_attachment_is_two_sided_and_retains_the_unconnected_attempts` requires **both** outcomes to be
present and the verdict to follow from both polarities;
`changing_the_terrains_material_moves_which_attempts_meet` is the gauge check — the same arrival
against a chain gives `6 attempts, 4 met`, against a cycle gives `6 attempts, 6 met`.

**The honest bound: the polarity law discriminates only where the terrain has endpoints.** On dense
material it is degenerate, and no finer law is built. Whether the gap itself should decide — the
§III winding is carried on every attempt and consulted by nothing — is open, and authoring a
threshold on it is exactly the contaminant the level rule forbids.

## 5 · What this does not establish

One deposit, one later current, one declared extent, at grade 0, on the driver's own declared
material. **No return crosses a world boundary**, `q_n = q_m` is not closed, and nothing here
survives a source-detached remount. The material mouth's **re-seal** is still owed, and no material
other than text is admitted by anything that runs.

**Two gates are red and both are the by-construction kind for uncommitted work.**
`closure-manifest` reddens because `soma/life` and `crates/holonic-engine` sources moved.
`architecture-lint` reddens on `+6 Vec` and `+3 BTreeSet` in `incidence_production.rs`, and that is
**genuine new ownership rather than an artifact**: a site now retains the material's own octets in
addition to its identity, which is exactly what the mouth ontology requires. The gratuitous share was
removed — two `.collect()` calls became loops and an exhibition helper stopped building a vector —
and the residual is owed as a stated widening when the baseline is re-emitted at commit.
