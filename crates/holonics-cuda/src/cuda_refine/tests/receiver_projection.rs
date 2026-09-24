use super::super::*;

/// The exterior order receiver acts on a declared sufficient row cover and leaves a plural
/// interval fibre unresolved rather than asking the host to select a row.

/// The cpu law is exact on its own terms, without a card. A partition is an equivalence, so
/// this checks the property rather than the numbering.
#[test]
fn the_cpu_quotient_separates_exactly_on_the_pair() {
    let classes = [1u32, 1, 1, 2, 2];
    let keys = [10u64, 10, 11, 10, 11];
    let quotient = quotient_on_cpu(&classes, &keys);
    assert_eq!(quotient.classes, 4, "(1,10) (1,11) (2,10) (2,11)");
    assert_eq!(quotient.cell_class[0], quotient.cell_class[1]);
    assert_ne!(quotient.cell_class[0], quotient.cell_class[2]);
    assert_ne!(quotient.cell_class[0], quotient.cell_class[3]);
    assert!(quotient.same_partition_as(&Quotient {
        // A different numbering of the same partition must compare equal.
        cell_class: vec![9, 9, 8, 7, 6],
        classes: 4,
        carrier: QuotientCarrier::Device,
    }));
}
