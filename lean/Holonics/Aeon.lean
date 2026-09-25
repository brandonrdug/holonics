import Holonics.Aeon.Clock
import Holonics.Aeon.Production

/-!
# Aeon, epoch and cycle

[definition] The standard objects of time (ELEMENTARY_OBJECTS §12). `Holonics.Aeon.Clock` owns the
aeon groupoid, clock readings with carry, the windings/phase split, two-clock locks and
convergent near-returns, the epochs of an aeon at a receiver's section with count as oriented
flux, and epoch towers. `Holonics.Aeon.Production` owns Hodge-decomposed time, Kac and Abramov,
production as path relative entropy, the dynamical zeta and the first law of learning. Every
module reads one aeon, `Aeon.Clock.Groupoid.Aeon`: the Hodge chain, the lock's torus loop, the
epoch ticks and the Markov path are its readings, and a Holarchy's parametric orientation carries
it. Namespaces: `Holonics.Aeon.Clock.*` and `Holonics.Aeon.Production.*`.
-/
