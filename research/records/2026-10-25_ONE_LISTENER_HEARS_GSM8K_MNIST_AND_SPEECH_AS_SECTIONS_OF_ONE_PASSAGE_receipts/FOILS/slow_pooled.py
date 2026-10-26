"""Pooled covariance on the four slowest rungs of each level's carried modes (modes 32..63 of 64,
re and im: 64 coordinates a level), the tower's state at the label."""
import importlib.util, sys, time
spec = importlib.util.spec_from_file_location('probe', sys.argv[1]); probe = importlib.util.module_from_spec(spec); spec.loader.exec_module(probe)
train, held = probe.faces(sys.argv[2], 64, 2, 64)[1], probe.faces(sys.argv[3], 64, 2, 64)[1]
for level in (0, 1):
    t0 = time.time(); idx = [level * 128 + i for i in range(64, 128)]
    a = [(c, [x[i] for i in idx]) for c, x in train]; b = [(c, [x[i] for i in idx]) for c, x in held]
    model = probe.fit(a, 64); kept, sc = probe.scatter(a, model, 64)
    near = sum(probe.nearest_scaled(model, kept, sc, x) == c for c, x in b)
    a2 = [(c, [x[i] for i in kept]) for c, x in a]; b2 = [(c, [x[i] for i in kept]) for c, x in b]
    lda = probe.pooled(a2, probe.fit(a2, len(kept)), len(kept))
    print(f"level {level} slow4: nearest_mean_scaled {near} pooled_covariance {'singular' if lda is None else sum(probe.discriminant(lda, x) == c for c, x in b2)} of {len(b)} seconds {int(time.time() - t0)}", flush=True)
