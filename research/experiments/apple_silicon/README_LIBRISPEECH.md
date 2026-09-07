# Bounded LibriSpeech speech companion

`prepare_librispeech_dev_clean.py` fetches a deterministic, bounded subset of the Hugging Face
OpenSLR mirror `openslr/librispeech_asr`, configuration `clean`, split `validation`. OpenSLR SLR12
identifies this split as the development clean speech set (`dev-clean`), licensed CC BY 4.0. The
script resolves and records the exact Hugging Face commit, retains each original FLAC byte span,
transcript, speaker ID, and chapter ID, and writes a decoded mono signed PCM16 WAV at 16 kHz.

The default is 100 clips. The validation parquet is streamed; the selected subset is kept under
`.local/datasets/librispeech-dev-clean-subset/` and the full source parquet is not materialized by
the script. `soundfile` decodes FLAC and writes PCM16 WAV; sample rate, channel count, and source
subtype are checked before conversion. No model, pretrained weights, ASR/TTS, native learner,
segmentation, or playback is invoked. Transcripts remain local provenance metadata and are not
sent to a native learner by the acquisition script. The separate, explicitly invoked
`holonics-speech` application can mount them as ordinary later byte occurrences; see
[the acoustic guide](../../../docs/ACOUSTIC_EXPERIMENTS.md).

```sh
VENV=.local/venvs/apple-silicon/bin/python
"$VENV" research/experiments/apple_silicon/prepare_librispeech_dev_clean.py
```

Primary provenance: [OpenSLR SLR12](https://www.openslr.org/12) and the
[OpenSLR Hugging Face dataset card](https://huggingface.co/datasets/openslr/librispeech_asr).
