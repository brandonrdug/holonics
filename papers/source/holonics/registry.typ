#import "foundations.typ": foundations
#import "logic-category.typ": logic-category
#import "algorithms.typ": algorithms
#import "algebra-combinatorics.typ": algebra-combinatorics
#import "geometry-calculus.typ": geometry-calculus
#import "topology-analysis-dynamics.typ": topology-analysis-dynamics
#import "manifold-knot-geometry.typ": manifold-knot-geometry
#import "arithmetic-analysis.typ": arithmetic-analysis
#import "algebraic-geometry.typ": algebraic-geometry
#import "transcendence-special-functions.typ": transcendence-special-functions
#import "computation-information.typ": computation-information
#import "mathematical-physics.typ": mathematical-physics
#import "rh-routes.typ": rh-routes
#import "counterexamples.typ": counterexamples

// The sequence is the dependency order used by the synopsis.
#let entries = (
  foundations
  + logic-category
  + algorithms
  + algebra-combinatorics
  + geometry-calculus
  + topology-analysis-dynamics
  + manifold-knot-geometry
  + arithmetic-analysis
  + algebraic-geometry
  + transcendence-special-functions
  + computation-information
  + mathematical-physics
  + rh-routes
  + counterexamples
)

#let entry-by-id(id) = {
  let matches = entries.filter(e => e.id == id)
  assert(matches.len() == 1, message: "entry id must resolve exactly once: " + id)
  matches.first()
}

#let validate-registry() = {
  let seen = ()
  for e in entries {
    assert(not seen.contains(e.id), message: "duplicate entry id: " + e.id)
    for dependency in e.depends {
      assert(
        seen.contains(dependency),
        message: e.id + " depends on missing or later entry " + dependency,
      )
    }
    seen.push(e.id)
  }
}
