//! A scalar presentation paired with the relation needed by its consumer.
//!
//! Brandon, 2026-08-15: *"mathematics objects like tensors have scalar faces, and scalar faces have
//! tensor faces (relative to a perspective). So any kind of collection is a geometrically
//! traversible mathematical object."*
//!
//! [`Face`] keeps both supplied values. `descend` reads the scalar; `reopen` reads the retained
//! relation. The constructor does not prove that the scalar is a particular projection of that
//! relation, and the relation need not be an original datum or an event archive. Its mathematical
//! adequacy belongs to the operation that constructs and consumes the pair.
//!
//! This is one storage building block for a computational holon, not its entire definition.
//! The complete object also has its actual ports, permitted operations and receiver maps. Bare
//! offsets remain useful storage coordinates when their owning object supplies that structure.

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

    /// Transform the scalar presentation while leaving the relation untouched. This need not be
    /// injective or reversible: a caller may map every scalar to the same value. Reconstructing a
    /// prior face requires an actual decoder from the retained relation or other admitted data.
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
