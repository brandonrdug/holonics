# Holonics audio apparatus

This is a bounded macOS application boundary for finite audio capture and playback. It does not
implement HNA, a learner, VAD, segmentation, speech recognition, a waveform template, or native
current manufacture. Captured audio is an exterior occurrence and its WAV/JSON outputs remain
codec and receiver artifacts for a later native ingress owner.

The tool uses the installed AVFoundation/CoreAudio/AudioToolbox SDK. `devices` is read-only. A
finite `capture` run records mono signed PCM16 WAV plus a chronology receipt. The receipt retains
the hardware format, channel count, sample rate, per-buffer sample/host timestamps, offsets,
dropped or late frame counts, overflow/gap fields, conversion clipping/refusal counts, and
permission result. Dropped frames and gaps are derived only when successive sample timestamps
prove a discontinuity. AVAudioEngine tap callbacks do not expose a reliable late/overflow signal,
so those optional receipt fields are omitted (`nil`), meaning unobserved rather than zero. The PCM16 conversion is explicitly
cold: channel averaging, float quantization, clipping, and non-finite refusal are reported and do
not become native state.

Capture keeps the finite PCM output in memory under an explicit projected working-set budget,
selected with `--max-memory-mib` and defaulting to 512 MiB (including the collector and final RIFF
serialization); larger requests are refused before device start. There is no arbitrary duration
ceiling; positive finite requests are checked against this budget and the WAV 32-bit data extent.
SIGINT/SIGTERM and
`AVAudioEngineConfigurationChange` stop the engine, preserve the accepted partial chronology and
write a partial WAV plus a `completed: false` receipt with the exact termination reason. A buffer
whose sample timestamp moves backwards or overlaps the preceding accepted buffer is refused and
retained as an explicit timestamp refusal rather than flattened into the chronology.

Build and inspect without opening the microphone:

```sh
./applications/holonics-audio/build.sh
applications/holonics-audio/.build/holonics-audio --help
applications/holonics-audio/.build/holonics-audio devices
applications/holonics-audio/.build/holonics-audio self-test-wav
applications/holonics-audio/.build/holonics-audio capture --seconds 5 --max-memory-mib 512 --wav out.wav --receipt out.json
```

Capture requires macOS microphone permission. If permission is absent, the tool reports that
capture could not start and names the permission/device action. Playback resolves and records the
default output device name/UID and the output node's actual format, alongside the scheduled source
file frame interval and the host-time interval observed by the process. The host endpoints are
not DAC timestamps. The `.dataPlayedBack` player completion callback records the scheduled frame
count as consumed; interruption, route change, signal, or timeout leaves played-frame count `null` and
preserves the exact termination reason. AVAudioFile and the device's format conversion remain
exterior to the native recurrence.

The receipt includes the measured `mach_timebase_info` numerator and denominator: elapsed host
ticks × numerator / denominator gives nanoseconds. Capture timestamps retain validity flags;
invalid sample/host timestamps do not establish a gap or clock match. Playback scheduling
coordinates and observed host intervals remain distinct from calibrated DAC timing.
