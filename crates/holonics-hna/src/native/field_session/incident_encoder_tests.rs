use super::*;
use holonic_engine::{
    native_ecology::constitutive_fibre::{
        BoundaryMaterialMaps, BoundaryMaterialSeed, ResidentNormalEnclosureSection,
    },
    native_ecology::constitutive_fibre::ResidentConstitutiveSection,
    resident_section::{ResidentGrain, ResidentSectionRest},
};

fn seed_maps() -> BoundaryMaterialMaps {
    BoundaryMaterialSeed::new(0x91_22_7a, 16)
        .initial_maps(3, 1)
        .unwrap()
}

#[test]
#[ignore = "requires CUDA; codec rechart transports resident E columns and preserves exact selected faces"]
fn permutation_covariance_keeps_pending_symbol_identity_and_rows() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let maps = seed_maps();
    let mut encoder = IncidentEncoder::found(&surface, &maps, ResidentGrain(16)).unwrap();
    let before = encoder.encode(&[0, 1, 2]).unwrap();
    let before_faces = (0..before.rows.rows())
        .map(|row| before.rows.row(row).unwrap().inspect().unwrap())
        .collect::<Vec<_>>();
    let permutation = encoder.rechart(vec![2, 0, 1]).unwrap();
    assert_eq!(permutation.old_to_new, vec![2, 0, 1]);
    // The pending packet names stable identities. Re-encoding it after the
    // permutation must expose the same resident boundary faces in that order.
    let after = encoder.encode(&before.symbols).unwrap();
    let after_faces = (0..after.rows.rows())
        .map(|row| after.rows.row(row).unwrap().inspect().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(before_faces, after_faces);
    assert_eq!(before.symbols, after.symbols);
}

#[test]
#[ignore = "requires CUDA; delayed native anchor return updates only admitted old E columns while appended classes remain fresh"]
fn observed_column_update_skips_new_appended_class() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let maps = seed_maps();
    let mut encoder = IncidentEncoder::found(&surface, &maps, ResidentGrain(16)).unwrap();
    let old = encoder.rest_with_identities().unwrap();
    encoder
        .append_seed_columns(&[(99, maps.encoder[0].clone())])
        .unwrap();
    let expanded = encoder.rest_with_identities().unwrap();
    assert_eq!(expanded.0[..old.0.len()], old.0[..]);
    assert_eq!(expanded.1[..old.1.len()], old.1[..]);

    let pending = encoder.encode(&[0, 1]).unwrap();
    let anchor_packet = surface
        .mount_section_rest(
            &ResidentSectionRest::found(
                2,
                2,
                ResidentGrain(0),
                i64::BITS,
                vec![(1, 1), (1, 1), (1, 1), (1, 1)],
            )
            .unwrap(),
        )
        .unwrap();
    let anchor = ResidentNormalEnclosureSection::from_points(
        ResidentConstitutiveSection::integers(&anchor_packet).unwrap(),
        ResidentGrain(16),
    )
    .unwrap();
    let update = encoder.prepare_return(&pending, &anchor, 1).unwrap();
    assert_eq!(update.columns.len(), 2);
    encoder.publish(update);
    let final_rest = encoder.rest_with_identities().unwrap();
    assert_eq!(
        final_rest.0[final_rest.0.len() - 1],
        expanded.0[expanded.0.len() - 1]
    );
}
