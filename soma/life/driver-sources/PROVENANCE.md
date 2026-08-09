# `soma/life/driver-sources/` — the inputs the `eros_*` drivers refuse without

Twenty-four drivers under `soma/life/examples/` take a declared input file as `argv[1]` and refuse
at startup without it. Before 2026-08-08 no such file existed anywhere in this repository:
`find . -iname 'SOURCE*.json'` returned nothing, so every one of those drivers was inert while its
organ was intact. This directory is that missing input, and nothing else.

**Every file here is one of two kinds, and each file says which inside itself.**

- `RECOVERED` — lifted whole from the frozen laboratory at commit `a07ff376`, read through
  `git -C /home/b/Workspaces/laboratory show a07ff376:<path>` and never from its working tree. The
  only edit is a `provenance` member added at the top of the JSON object; no driver's deserializer
  reads it and none of them declares `deny_unknown_fields`. The laboratory's own measurements are
  untouched.
- `CONSTRUCTED` — produced here by a named extractor from material tracked in **this** repository,
  with every hash, byte count and census computed from those bytes at extraction time. The
  extractor is committed beside the driver it feeds, so the file can be rebuilt and diffed.

There is a third kind this directory deliberately does **not** contain: a source with authored
numbers in it. Four drivers need a measurement that cannot be taken on this machine
(`eros_audio_contextual_ecology`, `eros_audio_ctc_path_fiber`, `eros_ctc_temporal_surface`,
`eros_self_emanated_law`). They remain inert. A fixture with invented Whisper attention weights or
invented CTC probability words would make them exit 0 and would be worse than the refusal, because
the refusal is honest.

## What is here

| directory | kind | feeds | recovered from |
|---|---|---|---|
| `eros-cohered-corpus-01/` | RECOVERED | `eros_cohered_corpus`, `eros_resonant_corpus_current`, `eros_resonant_generation` | `src/soma/observations/eros-cohered-corpus-01/SOURCE.json` |
| `eros-contextual-retriangulation-01/` | RECOVERED | `eros_contextual_retriangulation` | same path, that observation |
| `eros-exact-algorithm-ecology-01/` | RECOVERED | `eros_exact_algorithm_ecology` | same |
| `eros-holonic-training-ecology-01/` | RECOVERED | `eros_holonic_training_ecology` | same |
| `eros-parent-on-open-substitution-01/` | RECOVERED | `eros_parent_on_open_substitution` | same |
| `eros-pretrained-ecology-cultivation-01/` | RECOVERED | `eros_pretrained_ecology_cultivation` | same |
| `eros-residual-chart-cultivation-01/` | RECOVERED | `eros_residual_chart_cultivation` | same |
| `eros-retriangulating-branch-transport-01/` | RECOVERED | `eros_retriangulating_branch_transport` | same |
| `eros-transformer-contextual-hexis-01/` | RECOVERED | `eros_transformer_contextual_hexis` | same |
| `eros-transformer-translation-atlas-01/` | RECOVERED | `eros_transformer_translation_atlas` | same |
| `transformer-block-atlas-01/` | RECOVERED | `eros_transformer_seeded_ecology` | `experiments/informant-ecology/results/transformer-block-atlas-01/` |
| `transformer-context-recomposition-01/` | RECOVERED, **still blocked** | `eros_self_emanated_law` | `experiments/informant-ecology/results/transformer-context-recomposition-01/manifest.json` |
| `eros-morphological-language-generation-01/` | **CONSTRUCTED** | `eros_morphological_language_generation` | built by `soma/life/examples/morphological_language/freeze_source.py`, a port of the laboratory's `experiments/causal-language/sidecar/freeze_source.py` |
| `eros-morphological-language-generation-bounded-01/` | **CONSTRUCTED, bounded** | the same driver, at a declared generation aperture of 2 tokens instead of the laboratory's 256 | same extractor, `--maximum-generated-tokens 2` |
| `eros-holonic-constituent-ecology-01/` | RECOVERED, **no owner here** | — | the driver for `eros.holonic-constituent-ecology.source.v1` did not survive the transition |
| `eros-holonic-execution-paths-01/` | RECOVERED, **no owner here** | — | same, for `eros.holonic-execution-paths.source.v1` |
| `eros-ordinary-text-ecology-01/` | RECOVERED, **no owner here** | — | same, for `eros.ordinary-text-ecology.source.v1` |

The last three are kept because they are the material a port of those three drivers would need and
because they cost 18 KB; they feed nothing today and no claim may cite them as a run.

## Two entries that are recovered and still do not run

`transformer-context-recomposition-01/manifest.json` is the **correct** manifest for
`eros_self_emanated_law` — the `transformer-relational-field-01` one that the other sources cite
carries no `input_artifacts` member at all, so the driver refuses it at parse. With the correct
manifest the driver gets further and refuses later, at a named file: the two 33,139,024-byte
activation captures under `runs/transformer-block-atlas-01/captures/`. Zero `.safetensors` files are
tracked at `a07ff376`, so those are gone from every surface this repository may read. What *did*
pass on the way there is worth recording: `verify_extent` checked the real local
`model.safetensors` against the manifest's declared 2,969,854,224 bytes and it holds.

`eros-morphological-language-generation-01/` carries the laboratory's declared generation aperture
of 256 tokens per prompt, and **a run at that aperture does not return.** The measurement is in the
file's own `generation_aperture_note` and it is a cost law, not a source defect: on a 23-passage
corpus in a release build, one prompt at 1/2/4 tokens costs 57 ms / 403 ms / 55,098 ms, and 8 tokens
did not return inside 200,000 ms. `MorphologicalLanguageEcology::generate` branches
super-exponentially in `maximum_generated_tokens`. The `-bounded-01` companion is the same corpus at
aperture 2 and it returns; the aperture is declared in both files so the bound is never mistaken for
the law.

## The one file with a rename

`transformer-block-atlas-01/LABORATORY_RESULTS.md` is the laboratory's `RESULTS.md`, recovered
whole and renamed. `canon/THE_DOCUMENT_LAW.md` §1.8 records that this repository's live
observation-result genre is **empty**, and `tools/resolve_named_paths.py` enforces that record: a
file named `RESULTS.md` appearing anywhere in the live tree contradicts the canon entry that says
the genre is absent. The content is the laboratory's, unedited; only the name moved, so that
recovering an input does not silently falsify a canon claim about a different thing.

For the same reason this directory is `driver-sources/` and not `observations/`: the allow file
carries `canon/THE_DOCUMENT_LAW.md :: observations/ :: §1.8's defect row states the live
observation genre directory is absent; that absence is the row`.

## External artifacts these inputs point at

Two files named inside the recovered sources live outside this repository and were verified present
on this machine:

- `tokenizer.json` of `allenai/OLMo-2-0425-1B-Instruct` at revision
  `48d788eca847d4d7548f375ad03d3c9312f6139e`, sha256
  `73fd5254624f39a88e3faac6a8e11300fc3c735ed37880d4f4f08db898eaecca` — **matches the frozen
  source's declared digest exactly**, which is why `eros_resonant_generation`'s own tokenizer gate
  passes. It is passed to that driver as `argv[2]`.
- `model.safetensors` of the same snapshot, named by `eros_self_emanated_law`. Present, but that
  driver also needs activation-capture `.safetensors` that were never tracked in the laboratory
  (`git ls-tree | grep -c '\.safetensors$'` returns **0** at `a07ff376`), so it stays inert.

Nothing here downloads anything and no driver fed from this directory executes a model. The
transformer material is a frozen extract of measurements already taken; the drivers read integers.
