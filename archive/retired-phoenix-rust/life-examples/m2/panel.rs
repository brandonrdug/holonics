//! The finite M2 boundary-perturbation family.
//!
//! Every aperture is derived from a founded source extent: the first nontrivial successor layer,
//! the first two heads, the PLE width, hidden width, first full layer, first shared layer, and first
//! K/V family.  The declarations remain foreign-realization lineage; M2 classifies no transport by
//! these names.

use holonic_engine::phoenix::cohort::{Site, TowerDeclaration};
use holonic_engine::phoenix::tower::{self, Intervention};

pub fn declarations(tokens: usize) -> Vec<TowerDeclaration> {
    let successor = 1usize;
    let first = 0usize;
    let second = usize::from(tower::HEADS > 1);
    let stored_sliding = tower::FIRST_SHARED - 2;
    let first_full = tower::FULL_LAYERS[0];
    let first_shared = tower::FIRST_SHARED;
    let mut declarations = vec![
        TowerDeclaration::sharing("base occurrence", Site::Nowhere, Intervention::None),
        TowerDeclaration::whole("whole unchanged replay", Site::Nowhere, Intervention::None),
        TowerDeclaration::sharing(
            "source boundary: one PLE-width column family withdrawn wherever x0 enters",
            Site::EveryLayer,
            Intervention::WithdrawEmbeddingColumns {
                from: 0,
                span: tower::PLE_WIDTH,
            },
        ),
        TowerDeclaration::sharing(
            "auxiliary boundary withdrawn at the first successor",
            Site::Layer(successor),
            Intervention::WithdrawPle,
        ),
        TowerDeclaration::sharing(
            "positive duplication before the first successor rebase",
            Site::Layer(successor),
            Intervention::ScaleBeforeInputRebase { by: 2 },
        ),
        TowerDeclaration::sharing(
            "positive duplication after the first successor rebase",
            Site::Layer(successor),
            Intervention::ScaleAfterInputRebase { by: 2 },
        ),
        TowerDeclaration::sharing(
            "chronology replaced by its identity at the first successor",
            Site::Layer(successor),
            Intervention::IdentityChronology,
        ),
        TowerDeclaration::sharing(
            "position order reversed at the first successor",
            Site::Layer(successor),
            Intervention::ReversedPositions,
        ),
        TowerDeclaration::sharing(
            "the first two receiver families exchanged at contact",
            Site::Layer(successor),
            Intervention::PermuteReceiverHeads {
                a: first,
                b: second,
            },
        ),
        TowerDeclaration::sharing(
            "receiver current duplicated before the first successor contact",
            Site::Layer(successor),
            Intervention::ScaleReceiver { by: 2 },
        ),
        TowerDeclaration::sharing(
            "the first local presented family withdrawn at the first successor",
            Site::Layer(successor),
            Intervention::WithdrawKvFamily { family: first },
        ),
        TowerDeclaration::sharing(
            "the first stored presented family withdrawn at its sliding owner",
            Site::Layer(stored_sliding),
            Intervention::WithdrawKvFamily { family: first },
        ),
        TowerDeclaration::sharing(
            "the first shared presented family withdrawn only at the first shared receiver",
            Site::Layer(first_shared),
            Intervention::WithdrawSharedKvFamily { family: first },
        ),
        TowerDeclaration::sharing(
            "the first two carried receiver families exchanged before projection",
            Site::Layer(successor),
            Intervention::PermuteCarriedHeads {
                a: first,
                b: second,
            },
        ),
        TowerDeclaration::sharing(
            "continuing standing withdrawn at the first successor return",
            Site::Layer(successor),
            Intervention::WithdrawResidualAtFirstReEntry,
        ),
        TowerDeclaration::sharing(
            "one hidden-width gated family withdrawn at the first successor",
            Site::Layer(successor),
            Intervention::WithdrawGateSpan {
                from: 0,
                span: tower::HIDDEN,
            },
        ),
        TowerDeclaration::sharing(
            "all but the last key position withdrawn at the first full chronology",
            Site::Layer(first_full),
            Intervention::KeepOnlyLastKeyPosition { tokens },
        ),
        TowerDeclaration::sharing(
            "one PLE-width family withdrawn at the exterior potential boundary",
            Site::Final,
            Intervention::WithdrawFinalSpan {
                from: 0,
                span: tower::PLE_WIDTH,
            },
        ),
    ];
    declarations.push(TowerDeclaration::whole(
        "whole-prefix control for the first shared presented-family withdrawal",
        Site::Layer(first_shared),
        Intervention::WithdrawSharedKvFamily { family: first },
    ));
    declarations
}
