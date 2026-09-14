# Retired fitted-wave adapter

[historical] This preserves the uncommitted, caller-configured predictor-wave experiment
removed while integrating predictive normal material into the existing generator neighborhood.
`adapter.patch` records the removed tracked-file delta against `b823d5e8`; the two `.snapshot`
files retain the earlier applied-normal helper source, including the now-unused pair seed and
point-observation kernels. The applied normal graph itself remains a live shared primitive.

[definition] These files are source evidence, not a build target or construction order. The
private `BindPredictorWave`/`PredictWave`/`ObserveWave` path supplied its condition and maintained
another wave state. Current source uses the existing neighborhood and coupled body instead.
The earlier local measurement files under `research/experiments/fitted_wave_release/` remain
preserved; they are not evidence for the new consuming integration. No API from this removed
uncommitted path is claimed as a supported released wire format.
