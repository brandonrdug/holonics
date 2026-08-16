//! An index is a scalar face of a relation, and the relation stays askable.
//!
//! Brandon, 2026-08-15: *"mathematics objects like tensors have scalar faces, and scalar faces have
//! tensor faces (relative to a perspective). So any kind of collection is a geometrically
//! traversible mathematical object."*
//!
//! That sentence is the addressing law, and it decides what an index is allowed to be. Today
//! [`crate::RelationSpan`] is `{ start: u64, len: u64 }` and a branch node carries `extent: usize`
//! — **scalar faces with the tensor face deleted.** Each is the float argument one level down: keep
//! the magnitude, discard the turn. It is why every invariant computed on an undirected complex
//! held at 16/16 and 39/39 under a boundary-sign flip while twenty-four tests failed, every one of
//! them in a reader that traverses.
//!
//! [`Face`] keeps both. `descend` takes the scalar; `reopen` returns the relation it was taken from.
//! The ascent has a standing owner — `holonic_engine::reopening` reopens a numeric face collapsed to
//! a declared grain, with a typed refusal when the face is coarser than the grain asked of it — and
//! this carrier is the shape that hands it something to reopen.
//!
//! **This does not make addressing exact.** A `Face` whose relation is itself a magnitude has kept
//! two magnitudes. What it makes *possible* is the question, which is the half that was missing.

use serde::{Deserialize, Serialize};

/// A scalar taken from a relation, carried together with the relation it was taken from.
///
/// The invariant is that both faces are always present. There is no constructor that yields a
/// scalar with no relation, which is exactly the shape a bare offset has.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Face<S, R> {
    scalar: S,
    relation: R,
}

impl<S, R> Face<S, R> {
    /// Take a scalar face of a relation. Both are required; that is the whole discipline.
    pub const fn taken(scalar: S, relation: R) -> Self {
        Self { scalar, relation }
    }

    /// The scalar face — an index, an offset, an extent. Lawful to use; never the only thing kept.
    pub const fn descend(&self) -> &S {
        &self.scalar
    }

    /// The relation the scalar was a face of.
    pub const fn reopen(&self) -> &R {
        &self.relation
    }

    /// Both faces at once, for a reader that must not choose between them.
    pub const fn faces(&self) -> (&S, &R) {
        (&self.scalar, &self.relation)
    }

    /// Carry the scalar face into another chart, leaving the relation untouched. A chart transition
    /// on the face alone; the relation is what makes it reversible.
    pub fn map_scalar<T, F: FnOnce(S) -> T>(self, transition: F) -> Face<T, R> {
        Face {
            scalar: transition(self.scalar),
            relation: self.relation,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_face_cannot_be_built_without_its_relation() {
        // There is no `Face::from(3)`. The only constructor takes both, which is the property that
        // makes `RelationSpan { start, len }` unspellable in this carrier.
        let face = Face::taken(3usize, ("clause-7", "clause-9"));
        assert_eq!(*face.descend(), 3);
        assert_eq!(*face.reopen(), ("clause-7", "clause-9"));
    }

    #[test]
    fn the_scalar_may_be_rebased_and_the_relation_survives_it() {
        let face = Face::taken(3usize, "recruits");
        let rebased = face.map_scalar(|at| at * 2);
        assert_eq!(*rebased.descend(), 6);
        // The relation is what a magnitude-only address throws away, and it is still here after a
        // transition on the face.
        assert_eq!(*rebased.reopen(), "recruits");
    }

    #[test]
    fn two_faces_with_the_same_scalar_and_different_relations_are_distinct() {
        let left = Face::taken(1usize, "conducts");
        let right = Face::taken(1usize, "recruits");
        // An index-addressed carrier identifies these. That identification is the collapse this
        // module exists to refuse.
        assert_ne!(left, right);
        assert_eq!(left.descend(), right.descend());
    }
}
