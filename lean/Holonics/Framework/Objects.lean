import Holonics.Geometry.ExteriorBoundary
import Holonics.Framework.HolonObject
import Holonics.Foundation.Holon
import Holonics.Foundation.Standing
import Holonics.Physics.PhaseCarrier
import Holonics.Physics.CoupledIncidence
import Holonics.Physics.HolonicTorusParametronRealization
import Holonics.Physics.InformationDifference
import Holonics.Transport.HelicalPairInteraction
import Holonics.Transport.CellHolonomy
import Holonics.Transport.ContinuingTube
import Holonics.Transport.WorldTube
import Holonics.Transport.SourceMoment
import Holonics.Transport.ReflectiveContinuation
import Holonics.Foundation.FractalPacking
import Holonics.Objects.Pairing
import Holonics.Objects.Deposition
import Holonics.Objects.Ratio
import Holonics.Objects.Parametron
import Holonics.Objects.RelativeCompleteness
import Holonics.Objects.RatioPhase
import Holonics.Objects.RatioBlock
import Holonics.Objects.Retention
import Holonics.Objects.Membrane
import Holonics.Objects.Orientation
import Holonics.Objects.SourceHolon
import Holonics.Objects.SourcePorts
import Holonics.Objects.CommitRebase
import Holonics.Holon.Law
import Holonics.Holon.Generator
import Holonics.Geometry.AffineSwing
import Holonics.Geometry.SwingPotential
import Holonics.Transport.GeneratorTraceFaces
import Holonics.Foundation.FractalString
import Holonics.Holarchy
import Holonics.Aeon
import Holonics.Compression

/-!
# The elementary Holonic objects

[definition] The governing library of `docs/ELEMENTARY_OBJECTS.md`. Importing this module imports
every elementary object's Lean owners and the `Objects/` joins between them; it adds no axioms or
replacement structures. Designs, worker briefs and code state their operations only in these
objects, and a law found anywhere (a target, a record, a campaign) lands in one of these owners
with its consumer. The operator contract in the guide lists every owner; the entry owners are:

| Object | Entry owners |
|---|---|
| Complex, Holon and coholon | `Framework/HolonObject` (`Holon/{Complex,Port,Dirac,Element,Generator,Restriction,Law,Conformance,Deposition,Reaction,Cayley,AffineContact,MomentStorage}`), `Foundation/Holon`, `Objects/Pairing` |
| Constitution and deposition | `Holon/{Element,Deposition}`, `Objects/{Deposition,Retention,CommitRebase}` |
| Navigator | `Holon/Generator`, `Transport/{SourceMoment,GeneratorTraceFaces,ReflectiveContinuation}`, `Foundation/{FractalPacking,FractalString}` (the scale zeta read through the transfer determinant), `Aeon/Production/Zeta` (return words, word counts and the transfer determinant) |
| Swing | `Geometry/{AffineSwing,SwingPotential}` (FractalPacking's reflection is the Swing about ½) |
| Pair contact, tube and tower | `Transport/{HelicalPairInteraction,CellHolonomy,ContinuingTube,WorldTube}` |
| Parametron | `Objects/Parametron`, `Physics/{PhaseCarrier,CoupledIncidence,HolonicMeasuredParametron,HolonicTorusParametronRealization}` |
| Relatively complete region | `Objects/RelativeCompleteness`, `Holarchy/Globe` |
| Ratio | `Objects/{Ratio,RatioPhase,RatioBlock}` |
| Receiver and receipt | `Holarchy/{Reception,Receipt,Hearing}`, `Foundation/Standing` |
| Holarchy | `Holarchy/{Join,View}` |
| Holonic Compression | `Compression/{Core,Landmark}` |
| Aeon, epoch and cycle | `Aeon/Clock/{Groupoid,Reading,Winding,Lock,Epoch,CarryWord}`, `Aeon/Production` |

Namespaces keep their historical names (`Holonics.HolonCore` for the Holon law, for example);
the object map above, not the namespace, is the library's organization.
-/
