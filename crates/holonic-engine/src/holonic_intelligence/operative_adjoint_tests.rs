use super::*;
use crate::{embedding_fiber::ResidentReadout, resident_section::ResidentSectionRest};
use super::super::operative_adjoint::{NativeAdjointContraction, add_overlay_adjoints};

#[test]
#[ignore = "requires CUDA; explicit resident adjoint regression"]
fn retained_overlay_pullback_includes_both_factors_and_excludes_staged_deposits() {
    let readout = ResidentReadout::new().expect("CUDA readout");
    let surface = ResidentSurface::on(&readout).expect("resident surface");
    let grain = ResidentGrain(4);
    let mount = |rows, width, words: &[i64]| {
        surface.mount_section_rest(&ResidentSectionRest {
            rows, width, grain,
            bound_octaves: 8,
            intervals: words.iter().map(|word| (*word, *word)).collect(),
        }).expect("exact resident material")
    };
    // The existing deposit law gives U = I and V = [[1,2,0],[0,1,3]], at grain 2^-4.
    // A rectangular, rank-two atom makes swapping a factor or forgetting a transpose visible.
    let presented = mount(2, 3, &[16, 32, 0, 0, 16, 48]);
    let source = mount(2, 2, &[-16, 0, 0, -16]);
    let make_atom = || {
        deposit_from_material(&surface, DepositMaterial {
            differential: &source, differential_octaves: 8,
            presented: &presented, presented_octaves: 8, grain,
        }, NativeReturnAperture { learning_shift: 0, series_terms: 14 }).expect("deposit").0
    };
    let before_atom = surface.census().resident_octets_now;
    let mut retained = vec![make_atom()];
    assert_eq!(surface.census().resident_octets_now - before_atom, (2 * 2 + 2 * 3) * 8,
        "sealed factors retain one endpoint allocation, with no copied upper population");
    let pending = make_atom();
    let differential = mount(1, 2, &[16, 32]); // dy = [1,2].
    let base = || NativeAdjointContraction {
        section: mount(1, 3, &[16, 16, 16]), // dy W = [1,1,1].
        bound_octaves: 8, tiles: 1,
    };
    let before = surface.census();
    let returned = add_overlay_adjoints(&surface, base(), &differential, 8, &retained).expect("held pullback");
    let after = surface.census();
    assert_eq!(after.section_read_outs, before.section_read_outs, "no intermediate section left the card");
    assert_eq!(surface.read_out(&returned.section).unwrap(), vec![(32, 32), (80, 80), (112, 112)]);
    // A candidate formed during the return has not altered the first result. Only publishing it
    // changes the next operation's morphology; then the second atom contributes as well.
    retained.push(pending);
    let next = add_overlay_adjoints(&surface, base(), &differential, 8, &retained).expect("successor pullback");
    assert_eq!(surface.read_out(&next.section).unwrap(), vec![(48, 48), (144, 144), (208, 208)]);
    // The live atom's factors and the original differential remain available and unchanged.
    assert_eq!(surface.read_out(&differential).unwrap(), vec![(16, 16), (32, 32)]);
}
