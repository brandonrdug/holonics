//! **A declared coarser receiver: the once-reached leaf chains released** (U2's acceptance run,
//! candidate (1): `research/records/2026-09-28_U2_F0S_MEMORY_ACCEPTANCE_RUN_PINNED_BEFORE_ITS_SPLIT_IS_READ.md`;
//! #63, #73, #148).
//!
//! [definition; agent-inferred] **The release.** At a boundary its caller declares (the run's aeon
//! boundaries), the tree releases every stored node exactly one arrival reached and the pool letters
//! only those nodes' labels cover. Such a node is a leaf chain ending at its branch's depth: an
//! internal chain exists only where a second arrival parted a chain, and its upper part holds both
//! arrivals. Every kept node's parent is kept (it holds at least its child's arrivals), so a kept
//! label is unchanged and stays contiguous in the compacted pool. A kept node keeps its counts and
//! its chart: its `β` already holds the released children's past (the step `β′ = β k/q̂′`
//! telescopes). A read that reaches a released context stops at the deepest kept node and reads the
//! prior `½` below it, exactly as a context never founded (the test below); a later arrival founds
//! it again from the first-arrival founding chart.
//!
//! [definition] **It is not retention.** The owner's derivation ("Which merges and releases are
//! future-sufficient") refuses it as an exact release: a context seen once predicts its second
//! occurrence. It is a coarser receiver `R′`, priced against the finer by its code-length pair
//! (Lean `Context/Merge.coarsening_within_margin_iff`). The readings the kept charts carry
//! (certificates, cached stop weight, rebase count) are unchanged; after a release the certificates
//! no longer bound the distance to the full tree's ideal weighting, which reads the released
//! subtrees.
//!
//! [definition] The rule reads a node's register total as its arrivals, so it is refused under a
//! capacity ceiling, where a carry lowers the total below the arrivals.
//!
//! The computational object is the helical pair interaction, read as the receiving tree's storage;
//! of the winding guide's six objects this touches the **tower thread** (a released context
//! restricts to its deepest kept ancestor) and **faces and placement** (the face read there); the
//! helix, pair, cell holonomy and tube stay attached through the tree's owner.

use std::collections::HashMap;

use super::{BRANCH_BIT, Capacity, ContextError, Landmarks, key, shape};

/// [definition] **What one release took**: the nodes (each a leaf chain one arrival reached) and the
/// pool letters only they covered.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct OnceReached {
    pub nodes: u64,
    pub letters: u64,
}

impl Landmarks {
    /// **Release the once-reached leaf chains** (module header): every stored node one arrival
    /// reached, and the pool letters only those nodes cover; the kept nodes are renumbered in their
    /// founding order. Refused under a capacity ceiling, and (before anything moves) if a node to
    /// release holds a child.
    pub fn release_once_reached(&mut self) -> Result<OnceReached, ContextError> {
        if self.law.declaration.capacity != Capacity::Unbounded {
            return Err(shape(
                "an unbounded register, whose total is its arrivals",
                0,
                1,
            ));
        }
        let arena = &self.nodes.arena;
        let n = arena.halves.len();
        let released: Vec<bool> = arena
            .halves
            .iter()
            .map(|h| u64::from(h[0]) + u64::from(h[1]) == 4)
            .collect();
        let mut parent = vec![u32::MAX; n];
        for (&edge, &child) in &arena.children {
            let from = (edge >> 32) as u32;
            if released[from as usize] {
                return Err(shape("a once-reached node that holds no child", 0, 1));
            }
            parent[child as usize] = from;
        }
        let bottom = |i: usize| (arena.depths[i] & !BRANCH_BIT) as usize;
        let pool = arena.letters.len();
        let mut kept_cover = vec![0i32; pool + 1];
        let mut released_cover = vec![0i32; pool + 1];
        for i in 0..n {
            let top = match parent[i] {
                u32::MAX => 0,
                p => bottom(p as usize) + 1,
            };
            let end = arena.ends[i] as usize;
            let start = end - (bottom(i) - top);
            let cover = if released[i] {
                &mut released_cover
            } else {
                &mut kept_cover
            };
            cover[start] += 1;
            cover[end] -= 1;
        }
        drop(parent);
        // A letter is released when a released label covers it and no kept label does; the kept
        // letters' new positions are their prefix counts.
        let mut remap = vec![0u32; pool + 1];
        let mut letter_kept = vec![true; pool];
        let (mut kept_running, mut released_running, mut kept) = (0i32, 0i32, 0u32);
        for j in 0..pool {
            kept_running += kept_cover[j];
            released_running += released_cover[j];
            remap[j] = kept;
            if released_running > 0 && kept_running == 0 {
                letter_kept[j] = false;
            } else {
                kept += 1;
            }
        }
        remap[pool] = kept;
        drop(kept_cover);
        drop(released_cover);
        let mut renumber = vec![u32::MAX; n];
        let mut next = 0u32;
        for i in 0..n {
            if !released[i] {
                renumber[i] = next;
                next += 1;
            }
        }
        let taken = OnceReached {
            nodes: (n - next as usize) as u64,
            letters: (pool - kept as usize) as u64,
        };
        let arena = &mut self.nodes.arena;
        kept_only(&mut arena.depths, &released, false);
        kept_only(&mut arena.halves, &released, false);
        kept_only(&mut arena.ends, &released, false);
        kept_only(&mut self.nodes.charts, &released, false);
        for end in &mut arena.ends {
            *end = remap[*end as usize];
        }
        kept_only(&mut arena.letters, &letter_kept, true);
        for root in &mut arena.roots {
            *root = root.and_then(|r| (!released[r as usize]).then(|| renumber[r as usize]));
        }
        let old = std::mem::take(&mut arena.children);
        let mut children = HashMap::with_capacity(old.len().saturating_sub(taken.nodes as usize));
        for (edge, child) in old {
            if !released[child as usize] {
                let from = renumber[(edge >> 32) as usize];
                children.insert(key(from, edge as u32), renumber[child as usize]);
            }
        }
        arena.children = children;
        Ok(taken)
    }
}

/// Keep the entries whose flag equals `keep`, in order.
fn kept_only<T>(values: &mut Vec<T>, flags: &[bool], keep: bool) {
    let mut at = 0;
    values.retain(|_| {
        at += 1;
        flags[at - 1] == keep
    });
}

#[cfg(test)]
mod tests {
    use super::OnceReached;
    use crate::compression::landmark::context::{
        Capacity, LandmarkDeclaration, Landmarks, Letter, LetterFamily, StopPrior,
    };
    use crate::ratio::Rat;
    use num_traits::One;

    fn declaration(capacity: Capacity) -> LandmarkDeclaration {
        LandmarkDeclaration {
            alphabet: 4,
            depth: 3,
            forced: 0,
            population: 64,
            grain: 16,
            family: LetterFamily::cells(),
            prior: StopPrior::half(),
            capacity,
        }
    }

    fn cells(codes: &[usize]) -> Vec<Letter> {
        codes.iter().map(|&code| Letter::Cell(code)).collect()
    }

    fn face(tree: &Landmarks, address: &[Letter]) -> Vec<Rat> {
        (0..4)
            .map(|class| tree.probability(address, class).expect("a face"))
            .collect()
    }

    /// A released context reads exactly as a context never founded below its deepest kept node;
    /// a read along kept nodes is unchanged (the first digit's tree at a context reached twice);
    /// the face stays normalized; the standing round-trips; a later arrival founds the context
    /// again.
    #[test]
    fn a_released_context_reads_as_one_never_founded() {
        let mut tree = Landmarks::new(declaration(Capacity::Unbounded)).expect("a tree");
        // [2, 0, 1] is reached twice; [2, 0, 3] and [2, 1, 1] once; they part below [2].
        for (address, class) in [
            (cells(&[2, 0, 1]), 1),
            (cells(&[2, 0, 1]), 1),
            (cells(&[2, 0, 3]), 0),
            (cells(&[2, 1, 1]), 3),
        ] {
            tree.deposit(&address, class).expect("a deposit");
        }
        let (once, twice, never) = (cells(&[2, 0, 3]), cells(&[2, 0, 1]), cells(&[2, 0, 2]));
        assert_ne!(face(&tree, &once), face(&tree, &never));
        let before_twice = face(&tree, &twice);
        let nodes = tree.nodes();
        let taken = tree.release_once_reached().expect("a release");
        assert!(taken.nodes > 0 && taken.nodes < nodes as u64);
        assert_eq!(tree.nodes() as u64, nodes as u64 - taken.nodes);
        assert_eq!(face(&tree, &once), face(&tree, &never));
        // Classes 0 and 1 read the first digit's tree and the lower half's along kept nodes only;
        // classes 2 and 3 read the upper half's tree, which one arrival reached, now released.
        assert_eq!(face(&tree, &twice)[..2], before_twice[..2]);
        assert_ne!(face(&tree, &twice)[2..], before_twice[2..]);
        let arena = tree.arena();
        assert!(
            arena
                .halves()
                .iter()
                .all(|h| u64::from(h[0]) + u64::from(h[1]) >= 6)
        );
        for address in [&once, &twice, &never, &cells(&[3, 3, 3])] {
            assert_eq!(face(&tree, address).iter().sum::<Rat>(), Rat::one());
        }
        let restored = Landmarks::decode_standing(
            declaration(Capacity::Unbounded),
            &tree.encode_standing(),
        )
        .expect("the released standing decodes");
        assert_eq!(restored, tree);
        // A second release takes nothing; a later arrival founds the context again.
        assert_eq!(
            tree.release_once_reached().expect("a release"),
            OnceReached::default()
        );
        tree.deposit(&once, 0).expect("a deposit");
        assert!(tree.nodes() as u64 > nodes as u64 - taken.nodes);
        let refounded = face(&tree, &once);
        assert_eq!(refounded.iter().sum::<Rat>(), Rat::one());
    }

    /// A tree one arrival reached is released whole and reads as a fresh tree.
    #[test]
    fn a_tree_one_arrival_reached_is_released_whole() {
        let mut tree = Landmarks::new(declaration(Capacity::Unbounded)).expect("a tree");
        let fresh = tree.clone();
        tree.deposit(&cells(&[1, 2, 3]), 2).expect("a deposit");
        let taken = tree.release_once_reached().expect("a release");
        assert_eq!(tree.nodes(), 0);
        assert!(taken.nodes > 0 && taken.letters > 0);
        assert_eq!(tree.held(), 0);
        for address in [cells(&[1, 2, 3]), cells(&[0, 0, 0])] {
            assert_eq!(face(&tree, &address), face(&fresh, &address));
        }
    }

    /// Releases between deposits on a drawn stream (five classes, so a digit is forced; depth six,
    /// so kept chains part after a release): every kept node holds two arrivals or more, every face
    /// read is normalized, and every released standing round-trips through its codec.
    #[test]
    fn releases_between_deposits_keep_the_law() {
        let declared = LandmarkDeclaration {
            alphabet: 5,
            depth: 6,
            population: 512,
            ..declaration(Capacity::Unbounded)
        };
        let mut tree = Landmarks::new(declared.clone()).expect("a tree");
        let mut draw = crate::holarchy::terrain::Draw::new(20_260_928);
        let cells: Vec<usize> = (0..400).map(|_| draw.below(3) + 2 * draw.below(2)).collect();
        let mut taken = OnceReached::default();
        for (at, &cell) in cells.iter().enumerate() {
            let address: Vec<Letter> = (1..=6)
                .map(|back| at.checked_sub(back).map_or(Letter::Boundary, |i| Letter::Cell(cells[i])))
                .collect();
            let total: Rat = (0..5)
                .map(|class| tree.probability(&address, class).expect("a face"))
                .sum();
            assert_eq!(total, Rat::one());
            tree.deposit(&address, cell).expect("a deposit");
            if at % 50 == 49 {
                let step = tree.release_once_reached().expect("a release");
                taken.nodes += step.nodes;
                taken.letters += step.letters;
                assert!(
                    tree.arena()
                        .halves()
                        .iter()
                        .all(|h| u64::from(h[0]) + u64::from(h[1]) >= 6)
                );
                let restored = Landmarks::decode_standing(declared.clone(), &tree.encode_standing())
                    .expect("the released standing decodes");
                assert_eq!(restored, tree);
            }
        }
        assert!(taken.nodes > 0 && taken.letters > 0);
    }

    /// Under a ceiling the register's total is not its arrivals: refused.
    #[test]
    fn a_ceiling_refuses_the_release() {
        let mut tree = Landmarks::new(declaration(Capacity::Ceiling(1))).expect("a tree");
        tree.deposit(&cells(&[1, 2, 3]), 2).expect("a deposit");
        assert!(tree.release_once_reached().is_err());
    }
}
