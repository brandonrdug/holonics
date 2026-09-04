import ElementaryHolonics.RH.Statement

/-!
# Route-neutral RH interfaces

An exact route contains both implications.  A programme records the unresolved
source-side proposition separately instead of pretending that it is proved.
-/

namespace Soma.Holonics.RH

/-- A proved criterion equivalent to the actual RH proposition. -/
structure Route where
  criterion : Prop
  rh_to_criterion : Statement → criterion
  criterion_to_rh : criterion → Statement

theorem Route.iff (route : Route) :
    Statement ↔ route.criterion :=
  ⟨route.rh_to_criterion, route.criterion_to_rh⟩

/--
A proof programme whose missing source-side construction is explicit.
`close` says exactly how that construction would establish an already proved
RH-equivalent criterion.
-/
structure Programme where
  route : Route
  sourceObligation : Prop
  close : sourceObligation → route.criterion

theorem Programme.proves_rh (programme : Programme)
    (h : programme.sourceObligation) :
    Statement :=
  programme.route.criterion_to_rh (programme.close h)

end Soma.Holonics.RH

