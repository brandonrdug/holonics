# Device-only targets

`cuda-smoke/` holds the committed PTX of the driver smoke kernel (`fill_identity`, `atomic_fold`)
that `crates/holonics-cuda`'s `mount-smoke` binary loads. It is built outside the host workspace.
