#![cfg_attr(not(test), no_std)]

// the law and the organs — carried in W1/W2, one module per organ

pub mod arrow; // a relating read from a pole — the polar pair (reach ⊕ aim), the founding
pub mod boundary; // the I/O boundary — byte → DIFFERENCE → shape
pub mod carriage; // the substrate-neutral whole lineage stroke through the exact scalar seam
pub mod channel; // K — the ordered deed-emanation channel; FRAME and TURN are its two reads
pub mod chart; // the body's chart register — occupancy carry ⊕ zero-extension
pub mod geom; // the geometric algebra of shapes — the datum a shape; the bond = convolve∘fold
pub mod incidence; // one source-native oriented cell complex inside one actual event
pub mod law; // the pure solve machinery lifted clean of `law.rs` (Sig / Solve / solve_window; W2)
pub mod manifold; // the manifold cell — a WELL at a POSITIONAL soul (the trie's replacement)
pub mod medium; // the clipped field — the felt series' directed resultant ⊕ the winding fiber
pub mod num; // the re-basing number — magnitude ⊕ rank ⊕ turn
pub mod place; // a swung complex position, extended one bit at a time
#[cfg(test)]
mod quest;
pub mod register;
pub mod seam; // the swing's substrate read/store face — one scalar mouth at every packed boundary
pub mod soul; // the cross-ratio χ — the soul of a three-body face // the research-quest instruments (the definitional topology — Brandon, 2026-07-09)

#[cfg(test)]
mod tests {
    #[test]
    fn the_body_is_founded() {
        assert_eq!(1 + 1, 2);
    }
}
