use super::*;

const OCCUPIED_ZERO_WORDS: [u32; SLEEP_V2_FORM_WORDS] =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
const DIRECTED_FORM_WORDS: [u32; SLEEP_V2_FORM_WORDS] =
    [7, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1];

fn legacy_form(words: &[u32; SLEEP_V2_FORM_WORDS]) -> body::medium::RegionalForm {
    body::medium::RegionalForm::unpack_legacy_checked(words)
        .expect("the historical fixture is canonical")
}

fn compact_form(form: body::medium::RegionalForm) -> [u32; SLEEP_V4_FORM_WORDS] {
    let mut compact = [0u32; SLEEP_V4_FORM_WORDS];
    form.pack(&mut compact, 0);
    compact
}

fn put_form(standing: &mut [u32], grip: usize, form: body::medium::RegionalForm) {
    form.pack(standing, grip * body::medium::FORM_WORDS);
}

fn fixture() -> SleepingBody {
    let row_words = body::manifold::carrier_row_words(1);
    let mut carriers = vec![0u32; row_words];
    carriers[body::manifold::CARRIER_CURSOR_LO] = 2;
    body::channel::LineageChannel::from_first_difference(body::manifold::wind(b"the "))
        .expect("the fixture has one formed first difference")
        .pack(&mut carriers, body::manifold::CARRIER_CHANNEL);
    let mut standing = vec![0u32; 16 * body::medium::FORM_WORDS];
    put_form(&mut standing, 2, legacy_form(&OCCUPIED_ZERO_WORDS));
    put_form(&mut standing, 11, legacy_form(&DIRECTED_FORM_WORDS));
    SleepingBody::from_parts(4, 2, row_words as u32, 1, standing, carriers, 2)
        .expect("the fixture is one whole sleeping body")
}

fn plural_fixture() -> SleepingBody {
    let one = fixture();
    let mut carriers = one.carriers().to_vec();
    carriers.extend_from_slice(one.carriers());
    SleepingBody::from_parts(
        one.standing_axis(),
        one.occupancy(),
        one.carrier_row_words() as u32,
        2,
        one.standing().to_vec(),
        carriers,
        one.comprehended_light_bytes(),
    )
    .expect("the plural fixture carries two complete at-rest rows")
}

/// Historical V2–V5 fixtures retain their literal light-local axes outside the active body.
fn historical_axes(sleeping: &SleepingBody) -> Vec<u32> {
    vec![4; sleeping.lineage_count()]
}

fn historical_carriers(sleeping: &SleepingBody) -> (usize, Vec<u32>) {
    let active_row_words = sleeping.carrier_row_words();
    let depth = body::manifold::carrier_row_depth(active_row_words);
    let historical_row_words = historical_carrier_row_words(depth).unwrap();
    assert_eq!(
        active_row_words,
        historical_row_words
            + body::manifold::CARRIER_CONTINUATION_WORDS
            + body::manifold::CARRIER_PENDING_DEED_WORDS,
    );
    let mut historical = Vec::new();
    for row in sleeping.carriers().chunks_exact(active_row_words) {
        assert!(row[historical_row_words..].iter().all(|&word| word == 0));
        historical.extend_from_slice(&row[..historical_row_words]);
    }
    (historical_row_words, historical)
}

fn v5_v6_carriers(sleeping: &SleepingBody) -> (usize, Vec<u32>) {
    let active_row_words = sleeping.carrier_row_words();
    let depth = body::manifold::carrier_row_depth(active_row_words);
    let historical_row_words = v5_v6_carrier_row_words(depth).unwrap();
    assert_eq!(
        active_row_words,
        historical_row_words + body::manifold::CARRIER_PENDING_DEED_WORDS,
    );
    let mut historical = Vec::new();
    for row in sleeping.carriers().chunks_exact(active_row_words) {
        assert!(row[historical_row_words..].iter().all(|&word| word == 0));
        historical.extend_from_slice(&row[..historical_row_words]);
    }
    (historical_row_words, historical)
}

fn legacy_v2(sleeping: &SleepingBody) -> Vec<u8> {
    let (carrier_row_words, carriers) = historical_carriers(sleeping);
    let axes = historical_axes(sleeping);
    let mut archive = vec![
        SLEEP_MAGIC[0],
        SLEEP_MAGIC[1],
        SLEEP_DENSE_VERSION,
        SLEEP_V2_V8_HEADER_WORDS as u32,
        sleeping.standing_axis(),
        sleeping.lineage_count() as u32,
        carrier_row_words as u32,
        (sleeping.standing_axis() as usize
            * sleeping.standing_axis() as usize
            * SLEEP_V2_FORM_WORDS) as u32,
        carriers.len() as u32,
        sleeping.comprehended_light_bytes() as u32,
        (sleeping.comprehended_light_bytes() >> 32) as u32,
        sleeping.occupancy() as u32,
        (sleeping.occupancy() >> 32) as u32,
        0,
    ];
    archive.extend_from_slice(&axes);
    for row in sleeping.standing().chunks_exact(body::medium::FORM_WORDS) {
        let form = body::medium::RegionalForm::unpack(row, 0);
        let mut legacy = [0u32; SLEEP_V2_FORM_WORDS];
        form.pack_legacy_checked(&mut legacy).unwrap();
        archive.extend_from_slice(&legacy);
    }
    archive.extend_from_slice(&carriers);
    bytes(&archive)
}

fn legacy_v3(sleeping: &SleepingBody) -> Vec<u8> {
    let (carrier_row_words, carriers) = historical_carriers(sleeping);
    let axes = historical_axes(sleeping);
    let payload_words = sleeping.occupancy() as usize * SLEEP_V3_RECORD_WORDS;
    let mut archive = vec![
        SLEEP_MAGIC[0],
        SLEEP_MAGIC[1],
        SLEEP_OCCUPIED_VERSION,
        SLEEP_V2_V8_HEADER_WORDS as u32,
        sleeping.standing_axis(),
        sleeping.lineage_count() as u32,
        carrier_row_words as u32,
        payload_words as u32,
        carriers.len() as u32,
        sleeping.comprehended_light_bytes() as u32,
        (sleeping.comprehended_light_bytes() >> 32) as u32,
        sleeping.occupancy() as u32,
        (sleeping.occupancy() >> 32) as u32,
        SLEEP_V3_RECORD_WORDS as u32,
    ];
    archive.extend_from_slice(&axes);
    for (grip, row) in sleeping
        .standing()
        .chunks_exact(body::medium::FORM_WORDS)
        .enumerate()
    {
        let form = body::medium::RegionalForm::unpack(row, 0);
        if form.occupied() {
            archive.push(grip as u32);
            let mut legacy = [0u32; SLEEP_V2_FORM_WORDS];
            form.pack_legacy_checked(&mut legacy).unwrap();
            archive.extend_from_slice(&legacy);
        }
    }
    archive.extend_from_slice(&carriers);
    bytes(&archive)
}

fn legacy_v4(sleeping: &SleepingBody) -> Vec<u8> {
    let (carrier_row_words, carriers) = historical_carriers(sleeping);
    let axes = historical_axes(sleeping);
    let payload_words = sleeping.occupancy() as usize * SLEEP_RECORD_WORDS;
    let mut archive = vec![
        SLEEP_MAGIC[0],
        SLEEP_MAGIC[1],
        SLEEP_COMPACT_VERSION,
        SLEEP_V2_V8_HEADER_WORDS as u32,
        sleeping.standing_axis(),
        sleeping.lineage_count() as u32,
        carrier_row_words as u32,
        payload_words as u32,
        carriers.len() as u32,
        sleeping.comprehended_light_bytes() as u32,
        (sleeping.comprehended_light_bytes() >> 32) as u32,
        sleeping.occupancy() as u32,
        (sleeping.occupancy() >> 32) as u32,
        SLEEP_RECORD_WORDS as u32,
    ];
    archive.extend_from_slice(&axes);
    for (grip, row) in sleeping
        .standing()
        .chunks_exact(body::medium::FORM_WORDS)
        .enumerate()
    {
        let form = body::medium::RegionalForm::unpack(row, 0);
        if form.occupied() {
            archive.push(grip as u32);
            archive.extend_from_slice(&compact_form(form));
        }
    }
    archive.extend_from_slice(&carriers);
    bytes(&archive)
}

fn legacy_v5(sleeping: &SleepingBody) -> Vec<u8> {
    let axes = historical_axes(sleeping);
    let (carrier_row_words, carriers) = v5_v6_carriers(sleeping);
    let payload_words = sleeping.occupancy() as usize * SLEEP_RECORD_WORDS;
    let mut archive = vec![
        SLEEP_MAGIC[0],
        SLEEP_MAGIC[1],
        SLEEP_AXES_VERSION,
        SLEEP_V2_V8_HEADER_WORDS as u32,
        sleeping.standing_axis(),
        sleeping.lineage_count() as u32,
        carrier_row_words as u32,
        payload_words as u32,
        carriers.len() as u32,
        sleeping.comprehended_light_bytes() as u32,
        (sleeping.comprehended_light_bytes() >> 32) as u32,
        sleeping.occupancy() as u32,
        (sleeping.occupancy() >> 32) as u32,
        SLEEP_RECORD_WORDS as u32,
    ];
    archive.extend_from_slice(&axes);
    for (grip, row) in sleeping
        .standing()
        .chunks_exact(body::medium::FORM_WORDS)
        .enumerate()
    {
        let form = body::medium::RegionalForm::unpack(row, 0);
        if form.occupied() {
            archive.push(grip as u32);
            archive.extend_from_slice(&compact_form(form));
        }
    }
    archive.extend_from_slice(&carriers);
    bytes(&archive)
}

fn legacy_v6(sleeping: &SleepingBody) -> Vec<u8> {
    let (carrier_row_words, carriers) = v5_v6_carriers(sleeping);
    let payload_words = sleeping.occupancy() as usize * SLEEP_RECORD_WORDS;
    let mut archive = vec![
        SLEEP_MAGIC[0],
        SLEEP_MAGIC[1],
        SLEEP_NO_AXES_VERSION,
        SLEEP_V2_V8_HEADER_WORDS as u32,
        sleeping.standing_axis(),
        sleeping.lineage_count() as u32,
        carrier_row_words as u32,
        payload_words as u32,
        carriers.len() as u32,
        sleeping.comprehended_light_bytes() as u32,
        (sleeping.comprehended_light_bytes() >> 32) as u32,
        sleeping.occupancy() as u32,
        (sleeping.occupancy() >> 32) as u32,
        SLEEP_RECORD_WORDS as u32,
    ];
    for (grip, row) in sleeping
        .standing()
        .chunks_exact(body::medium::FORM_WORDS)
        .enumerate()
    {
        let form = body::medium::RegionalForm::unpack(row, 0);
        if form.occupied() {
            archive.push(grip as u32);
            archive.extend_from_slice(&compact_form(form));
        }
    }
    archive.extend_from_slice(&carriers);
    bytes(&archive)
}

fn bytes(words: &[u32]) -> Vec<u8> {
    words.iter().copied().flat_map(u32::to_le_bytes).collect()
}

fn words(bytes: &[u8]) -> Vec<u32> {
    bytes
        .chunks_exact(4)
        .map(|word| u32::from_le_bytes([word[0], word[1], word[2], word[3]]))
        .collect()
}

fn active_carrier_start(words: &[u32]) -> usize {
    let standing_words = words[7] as u64 | ((words[8] as u64) << 32);
    SLEEP_HEADER_WORDS + standing_words as usize + words[6] as usize
}

#[test]
fn occupied_forms_cross_one_exact_v9_archive_mouth_with_structural_row_framing() {
    let sleeping = fixture();
    let row_words = sleeping.carrier_row_words();
    let encoded = sleeping.encode();
    let standing_words = 2 * SLEEP_RECORD_WORDS;
    let mut expected_words = vec![
        0x414d_4f53,
        0x5453_4552,
        9,
        16,
        4,
        1,
        1,
        standing_words as u32,
        0,
        row_words as u32,
        0,
        2,
        0,
        2,
        0,
        SLEEP_RECORD_WORDS as u32,
        2,
    ];
    expected_words.extend_from_slice(&compact_form(legacy_form(&OCCUPIED_ZERO_WORDS)));
    expected_words.push(11);
    expected_words.extend_from_slice(&compact_form(legacy_form(&DIRECTED_FORM_WORDS)));
    expected_words.push(row_words as u32);
    let carrier_start = expected_words.len();
    expected_words.extend_from_slice(sleeping.carriers());
    assert_eq!(
        expected_words[carrier_start + body::manifold::CARRIER_CURSOR_LO],
        2
    );
    let expected = bytes(&expected_words);
    assert_eq!(
        encoded, expected,
        "SLEEP v9 has one exact little-endian wire layout"
    );
    assert_eq!(SleepingBody::decode(&encoded), Ok(sleeping.clone()));
    assert_eq!(
        encoded.len(),
        (SLEEP_HEADER_WORDS + 2 * SLEEP_RECORD_WORDS + 1 + row_words) * 4,
    );
    assert_eq!(
        SleepingBody::decode(&encoded).unwrap().body_bytes(),
        ((2 * SLEEP_RECORD_WORDS + row_words) * 4 + 8) as u64,
        "the comprehension measure excludes V9's structural row framing",
    );
    assert_eq!(
        sleeping.body_bytes_for_version(SLEEP_DENSE_VERSION),
        Ok(((16 * SLEEP_V2_FORM_WORDS + row_words
            - body::manifold::CARRIER_CONTINUATION_WORDS
            - body::manifold::CARRIER_PENDING_DEED_WORDS)
            * 4
            + 8) as u64),
        "V2's body measure retains its literal dense seventeen-word rows",
    );
    assert_eq!(
        sleeping.body_bytes_for_version(SLEEP_OCCUPIED_VERSION),
        Ok(((2 * SLEEP_V3_RECORD_WORDS + row_words
            - body::manifold::CARRIER_CONTINUATION_WORDS
            - body::manifold::CARRIER_PENDING_DEED_WORDS)
            * 4
            + 8) as u64),
        "V3's body measure retains its literal eighteen-word records",
    );
    assert_eq!(
        sleeping.body_bytes_for_version(SLEEP_COMPACT_VERSION),
        Ok(((2 * SLEEP_RECORD_WORDS + row_words
            - body::manifold::CARRIER_CONTINUATION_WORDS
            - body::manifold::CARRIER_PENDING_DEED_WORDS)
            * 4
            + 8) as u64),
        "V4's body measure retains its literal carrier prefix",
    );
    assert_eq!(
        sleeping.body_bytes_for_version(SLEEP_AXES_VERSION),
        Ok(
            ((2 * SLEEP_RECORD_WORDS + row_words - body::manifold::CARRIER_PENDING_DEED_WORDS) * 4
                + 8) as u64
        ),
        "V5's body measure includes the continuation tail but predates pending deeds",
    );
    assert_eq!(
        sleeping.body_bytes_for_version(SLEEP_NO_AXES_VERSION),
        Ok(
            ((2 * SLEEP_RECORD_WORDS + row_words - body::manifold::CARRIER_PENDING_DEED_WORDS) * 4
                + 8) as u64
        ),
        "V6 removes only dead axis words and still predates pending deeds",
    );
    assert_eq!(
        sleeping.body_bytes_for_version(SLEEP_UNIFORM_CARRIER_VERSION),
        Ok(((2 * SLEEP_RECORD_WORDS + row_words) * 4 + 8) as u64),
        "V7 adds exactly the pending-deed tail to every active carrier row",
    );
    assert_eq!(
        sleeping.body_bytes_for_version(SLEEP_VERSION),
        Ok(((2 * SLEEP_RECORD_WORDS + row_words) * 4 + 8) as u64),
        "V9 widens the archive extents without changing the identity measure",
    );
    assert!(sleeping.body_bytes_for_version(10).is_err());
    assert!(
        SleepingBody::decode(&encoded[..encoded.len() - 4]).is_err(),
        "a partial body cannot masquerade as a sleep chart"
    );
}

#[test]
fn mixed_complete_carrier_rows_cross_v9_without_becoming_body_bytes() {
    let one = fixture();
    let shallow = one.carriers().to_vec();
    let deep_words = body::manifold::carrier_row_words(3);
    let mut deep = vec![0u32; deep_words];
    deep[..body::manifold::CARRIER_HEADER_WORDS]
        .copy_from_slice(&shallow[..body::manifold::CARRIER_HEADER_WORDS]);
    assert!(body::manifold::carried_frame_is_at_rest(&deep));

    let mut carriers = shallow.clone();
    carriers.extend_from_slice(&deep);
    let sleeping = SleepingBody::from_variable_parts(
        one.standing_axis(),
        one.occupancy(),
        vec![shallow.len() as u32, deep.len() as u32],
        one.standing().to_vec(),
        carriers,
        one.comprehended_light_bytes(),
    )
    .expect("two independently reserved complete currents form one sleeping body");
    assert_eq!(sleeping.uniform_carrier_row_words(), None);
    assert_eq!(
        sleeping.carrier_row_word_extents(),
        [shallow.len() as u32, deep.len() as u32],
    );
    let rows: Vec<&[u32]> = sleeping.carrier_rows().collect();
    assert_eq!(rows, [shallow.as_slice(), deep.as_slice()]);

    let encoded = sleeping.encode();
    let encoded_words = words(&encoded);
    assert_eq!(encoded_words[2], SLEEP_VERSION);
    assert_eq!(encoded_words[6], 2);
    let standing_words = encoded_words[7] as u64 | ((encoded_words[8] as u64) << 32);
    let framing = SLEEP_HEADER_WORDS + standing_words as usize;
    assert_eq!(
        &encoded_words[framing..framing + 2],
        sleeping.carrier_row_word_extents(),
    );
    assert_eq!(SleepingBody::decode(&encoded), Ok(sleeping.clone()));
    assert_eq!(
        sleeping.body_bytes(),
        ((2 * SLEEP_RECORD_WORDS + shallow.len() + deep.len()) * 4 + 8) as u64,
        "the structural row framing is outside standing ⊕ complete carriers ⊕ occupancy",
    );
    assert!(
        sleeping
            .body_bytes_for_version(SLEEP_UNIFORM_CARRIER_VERSION)
            .is_err(),
        "V7 cannot represent independently reserved rows",
    );

    let mut malformed = encoded_words;
    malformed[framing] += 1;
    assert!(
        SleepingBody::decode(&bytes(&malformed)).is_err(),
        "a malformed row extent cannot shift the following current's identity",
    );
}

#[test]
fn a_legacy_dense_v2_chart_semantically_round_trips_through_v9() {
    let sleeping = fixture();
    let legacy = legacy_v2(&sleeping);
    let legacy_words = words(&legacy);
    assert_eq!(legacy_words[2], SLEEP_DENSE_VERSION);
    assert_eq!(legacy_words[7] as usize, 16 * SLEEP_V2_FORM_WORDS);

    let decoded = SleepingBody::decode(&legacy)
        .expect("a literal V2 dense chart remains semantically readable");
    assert_eq!(decoded, sleeping);
    let v9 = decoded.encode();
    assert_eq!(words(&v9)[2], SLEEP_VERSION);
    assert_eq!(words(&v9)[15] as usize, SLEEP_RECORD_WORDS);
    assert_eq!(SleepingBody::decode(&v9), Ok(sleeping.clone()));
    assert_eq!(v9, sleeping.encode(), "a migrated archive is canonical V9");
}

#[test]
fn a_legacy_occupied_v3_chart_semantically_round_trips_through_v9() {
    let sleeping = fixture();
    let legacy = legacy_v3(&sleeping);
    let legacy_words = words(&legacy);
    assert_eq!(legacy_words[2], SLEEP_OCCUPIED_VERSION);
    assert_eq!(legacy_words[7] as usize, 2 * SLEEP_V3_RECORD_WORDS);
    assert_eq!(legacy_words[13] as usize, SLEEP_V3_RECORD_WORDS);

    let decoded = SleepingBody::decode(&legacy)
        .expect("a literal V3 occupied chart remains semantically readable");
    assert_eq!(decoded, sleeping);
    let v9 = decoded.encode();
    assert_eq!(words(&v9)[2], SLEEP_VERSION);
    assert_eq!(words(&v9)[15] as usize, SLEEP_RECORD_WORDS);
    assert_eq!(SleepingBody::decode(&v9), Ok(sleeping.clone()));
    assert_eq!(v9, sleeping.encode(), "a migrated archive is canonical V9");
}

#[test]
fn a_literal_v4_carrier_prefix_migrates_to_v9_with_both_completed_tails() {
    let sleeping = plural_fixture();
    let legacy = legacy_v4(&sleeping);
    let legacy_words = words(&legacy);
    let historical_row_words = sleeping.carrier_row_words()
        - body::manifold::CARRIER_CONTINUATION_WORDS
        - body::manifold::CARRIER_PENDING_DEED_WORDS;
    assert_eq!(legacy_words[2], SLEEP_COMPACT_VERSION);
    assert_eq!(legacy_words[6] as usize, historical_row_words);
    assert_eq!(legacy_words[8] as usize, 2 * historical_row_words);

    let decoded = SleepingBody::decode(&legacy)
        .expect("a literal V4 carrier prefix gains only the completed continuation tail");
    assert_eq!(decoded, sleeping);
    let v9 = decoded.encode();
    let v9_words = words(&v9);
    assert_eq!(v9_words[2], SLEEP_VERSION);
    assert_eq!(v9_words[6] as usize, sleeping.lineage_count());
    assert_eq!(v9_words[9] as usize, sleeping.carriers().len());
    assert_eq!(v9_words[10], 0);
    for row in decoded.carrier_rows() {
        assert!(row[historical_row_words..].iter().all(|&word| word == 0));
    }
    assert_eq!(SleepingBody::decode(&v9), Ok(sleeping.clone()));
    assert_eq!(
        v9,
        sleeping.encode(),
        "the migrated archive is canonical V9"
    );
}

#[test]
fn a_literal_v5_axis_payload_validates_then_dies_in_canonical_v9() {
    let sleeping = plural_fixture();
    let legacy = legacy_v5(&sleeping);
    let legacy_words = words(&legacy);
    assert_eq!(legacy_words[2], SLEEP_AXES_VERSION);
    assert_eq!(legacy_words[5] as usize, sleeping.lineage_count());
    assert_eq!(legacy_words[14..14 + sleeping.lineage_count()], [4, 4]);

    let decoded = SleepingBody::decode(&legacy)
        .expect("a literal V5 body validates and discards its historical local axes");
    assert_eq!(decoded, sleeping);
    let v9 = decoded.encode();
    assert_eq!(words(&v9)[2], SLEEP_VERSION);
    assert_eq!(
        v9.len(),
        legacy.len() + sleeping.lineage_count()
            * body::manifold::CARRIER_PENDING_DEED_WORDS
            * core::mem::size_of::<u32>()
            + 2 * core::mem::size_of::<u32>(),
        "V9 replaces each dead local axis with one framing word, adds two extent words, and adds twelve pending words per lineage",
    );
    assert_eq!(SleepingBody::decode(&v9), Ok(sleeping.clone()));

    let mut malformed = legacy_words;
    malformed[SLEEP_V2_V8_HEADER_WORDS] = 3;
    assert!(
        SleepingBody::decode(&bytes(&malformed)).is_err(),
        "a malformed historical axis is rejected before it is discarded",
    );
}

#[test]
fn a_literal_v6_row_synthesizes_zero_pending_per_lineage_and_rejects_live_continuation() {
    let sleeping = plural_fixture();
    let legacy = legacy_v6(&sleeping);
    let legacy_words = words(&legacy);
    let historical_row_words = legacy_words[6] as usize;
    let depth = v5_v6_carrier_row_depth(historical_row_words).unwrap();
    let continuation = historical_carrier_row_words(depth).unwrap();
    assert_eq!(legacy_words[2], SLEEP_NO_AXES_VERSION);
    assert_eq!(
        historical_row_words + body::manifold::CARRIER_PENDING_DEED_WORDS,
        sleeping.carrier_row_words(),
        "V6 retains literal 72 + 290d + 19 rows",
    );
    let decoded = SleepingBody::decode(&legacy)
        .expect("a literal V6 body synthesizes only the absent pending-deed tail");
    assert_eq!(decoded, sleeping);
    let v9 = decoded.encode();
    assert_eq!(words(&v9)[2], SLEEP_VERSION);
    assert_eq!(
        v9.len(),
        legacy.len()
            + sleeping.lineage_count()
                * (body::manifold::CARRIER_PENDING_DEED_WORDS + 1)
                * core::mem::size_of::<u32>()
            + 2 * core::mem::size_of::<u32>(),
        "V9 adds twelve zero pending words and one structural framing word per V6 lineage, plus two extent words",
    );
    let carrier = SLEEP_V2_V8_HEADER_WORDS + legacy_words[7] as usize;
    let mut active_continuation = legacy_words;
    active_continuation[carrier + continuation + body::manifold::CARRIER_CONTINUATION_PHASE] =
        body::manifold::CONTINUATION_WORD_PATH;
    assert!(
        SleepingBody::decode(&bytes(&active_continuation)).is_err(),
        "V6 rejects an active old continuation before synthesizing the pending tail",
    );
}

#[test]
fn malformed_occupied_records_cannot_cross_the_sleep_mouth() {
    let encoded = fixture().encode();
    let canonical = words(&encoded);
    let first = SLEEP_HEADER_WORDS;
    let second = first + SLEEP_RECORD_WORDS;

    let mut bad_stride = canonical.clone();
    bad_stride[15] -= 1;
    assert!(SleepingBody::decode(&bytes(&bad_stride)).is_err());

    let mut bad_payload = canonical.clone();
    bad_payload[7] -= 1;
    assert!(SleepingBody::decode(&bytes(&bad_payload)).is_err());

    let mut duplicate = canonical.clone();
    duplicate[second] = duplicate[first];
    assert!(SleepingBody::decode(&bytes(&duplicate)).is_err());

    let mut descending = canonical.clone();
    descending[second] = duplicate[first] - 1;
    assert!(SleepingBody::decode(&bytes(&descending)).is_err());

    let mut out_of_range = canonical.clone();
    out_of_range[second] = 16;
    assert!(SleepingBody::decode(&bytes(&out_of_range)).is_err());

    let mut unborn = canonical.clone();
    unborn[first + 1..first + SLEEP_RECORD_WORDS].fill(0);
    assert!(SleepingBody::decode(&bytes(&unborn)).is_err());

    let mut noncanonical = canonical.clone();
    noncanonical[first + 1 + SLEEP_V4_FORM_WORDS - 1] |= 1 << 31;
    assert!(SleepingBody::decode(&bytes(&noncanonical)).is_err());

    let mut rank_out_of_range = canonical.clone();
    rank_out_of_range[first + 1 + 2] = u32::MAX;
    assert!(SleepingBody::decode(&bytes(&rank_out_of_range)).is_err());

    let mut wrong_occupancy = canonical;
    wrong_occupancy[13] = 1;
    assert!(SleepingBody::decode(&bytes(&wrong_occupancy)).is_err());
}

#[test]
fn malformed_carrier_identity_cannot_cross_the_sleep_mouth() {
    let sleeping = fixture();
    let canonical = words(&sleeping.encode());
    let carrier = active_carrier_start(&canonical);

    let mut no_predecessor = canonical.clone();
    no_predecessor[carrier + body::manifold::CARRIER_CURSOR_LO] = 0;
    assert!(SleepingBody::decode(&bytes(&no_predecessor)).is_err());

    let mut one_packet_is_not_a_worldline = canonical.clone();
    one_packet_is_not_a_worldline[carrier + body::manifold::CARRIER_CURSOR_LO] = 1;
    assert!(SleepingBody::decode(&bytes(&one_packet_is_not_a_worldline)).is_err());

    let mut unfinished_dark = canonical.clone();
    unfinished_dark[carrier + body::manifold::CARRIER_DARK_LO] = 1;
    assert!(SleepingBody::decode(&bytes(&unfinished_dark)).is_err());

    let mut missing_k = canonical.clone();
    missing_k[carrier + body::manifold::CARRIER_CHANNEL
        ..carrier + body::manifold::CARRIER_CHANNEL + body::channel::CHANNEL_WORDS]
        .fill(0);
    assert!(SleepingBody::decode(&bytes(&missing_k)).is_err());

    let mut origin_anchor = canonical.clone();
    origin_anchor[carrier + body::manifold::CARRIER_CHANNEL
        ..carrier + body::manifold::CARRIER_CHANNEL + 2 * body::num::COG_WORDS]
        .fill(0);
    assert!(SleepingBody::decode(&bytes(&origin_anchor)).is_err());

    let mut clipped_k_boolean = canonical.clone();
    clipped_k_boolean[carrier + body::manifold::CARRIER_CHANNEL + 3] = 2;
    assert!(SleepingBody::decode(&bytes(&clipped_k_boolean)).is_err());

    let mut clipped_k_turn = canonical.clone();
    clipped_k_turn[carrier + body::manifold::CARRIER_CHANNEL + 4] = 4;
    assert!(SleepingBody::decode(&bytes(&clipped_k_turn)).is_err());

    let mut negative_winding = canonical.clone();
    let winding = carrier + body::manifold::CARRIER_CHANNEL + 6 * body::num::COG_WORDS;
    negative_winding[winding] = 1;
    negative_winding[winding + 2] = 1;
    assert!(SleepingBody::decode(&bytes(&negative_winding)).is_err());

    let mut clipped_header_boolean = canonical.clone();
    clipped_header_boolean[carrier + body::manifold::CARRIER_SUB_FLY_LIVE] = 2;
    assert!(SleepingBody::decode(&bytes(&clipped_header_boolean)).is_err());

    let enclosure = carrier + body::manifold::carrier_enclosure_base(0);
    let mut clipped_head = canonical.clone();
    clipped_head[enclosure + body::manifold::ENCLOSURE_HEAD] = body::register::REGISTER;
    assert!(SleepingBody::decode(&bytes(&clipped_head)).is_err());

    let mut clipped_live = canonical.clone();
    clipped_live[enclosure + body::manifold::ENCLOSURE_LIVE] = body::register::REGISTER + 1;
    assert!(SleepingBody::decode(&bytes(&clipped_live)).is_err());

    let mut absent_active_node = canonical.clone();
    absent_active_node[enclosure + body::manifold::ENCLOSURE_HEAD] = 1;
    absent_active_node[enclosure + body::manifold::ENCLOSURE_LIVE] = 1;
    assert!(SleepingBody::decode(&bytes(&absent_active_node)).is_err());

    let mut unformed_live_fly = canonical.clone();
    unformed_live_fly[enclosure + body::manifold::ENCLOSURE_FLY_LIVE] = 1;
    assert!(SleepingBody::decode(&bytes(&unformed_live_fly)).is_err());

    let deferred = carrier + body::manifold::carrier_deferred_base(1, 0);
    let mut live_scratch = canonical;
    live_scratch[deferred] = 1;
    assert!(SleepingBody::decode(&bytes(&live_scratch)).is_err());
}

#[test]
fn a_canonical_active_continuation_cannot_cross_the_sleep_edge() {
    let sleeping = fixture();
    let mut active = words(&sleeping.encode());
    let carrier = active_carrier_start(&active);
    let row_end = carrier + sleeping.carrier_row_words();
    let depth = body::manifold::carrier_row_depth(sleeping.carrier_row_words());
    let continuation = carrier + body::manifold::carrier_continuation_base(depth);
    active[continuation + body::manifold::CARRIER_CONTINUATION_PHASE] =
        body::manifold::CONTINUATION_WORD_PATH;
    assert!(body::manifold::carried_frame_is_canonical(
        &active[carrier..row_end]
    ));
    assert!(!body::manifold::carried_frame_is_at_rest(
        &active[carrier..row_end]
    ));
    assert!(
        SleepingBody::decode(&bytes(&active)).is_err(),
        "a substrate installment is lawful carriage but not a receiving edge",
    );
}

#[test]
fn a_nonzero_pending_deed_cannot_cross_the_v9_sleep_edge() {
    let sleeping = fixture();
    for kind in body::manifold::PENDING_DARK_BEFORE..=body::manifold::PENDING_PATH {
        let mut active = words(&sleeping.encode());
        let carrier = active_carrier_start(&active);
        let pending =
            carrier + sleeping.carrier_row_words() - body::manifold::CARRIER_PENDING_DEED_WORDS;
        let contact = if kind == body::manifold::PENDING_ENCLOSURE_CO_PRESENT {
            1
        } else {
            0
        };
        active[pending] = body::manifold::pending_control(kind, contact);
        assert!(
            SleepingBody::decode(&bytes(&active)).is_err(),
            "pending species {kind} is lawful carriage but not a receiving edge",
        );
    }
}

#[test]
fn malformed_v2_and_v3_forms_cannot_cross_the_sleep_mouth() {
    let sleeping = fixture();

    let mut v2_unoccupied_data = words(&legacy_v2(&sleeping));
    let v2_dense = SLEEP_V2_V8_HEADER_WORDS + historical_axes(&sleeping).len();
    v2_unoccupied_data[v2_dense] = 1;
    assert!(SleepingBody::decode(&bytes(&v2_unoccupied_data)).is_err());

    let v2_occupied = v2_dense + 2 * SLEEP_V2_FORM_WORDS;
    let mut v2_bad_occupancy = words(&legacy_v2(&sleeping));
    v2_bad_occupancy[v2_occupied + 16] = 2;
    assert!(SleepingBody::decode(&bytes(&v2_bad_occupancy)).is_err());

    let v3_first = SLEEP_V2_V8_HEADER_WORDS + historical_axes(&sleeping).len();
    let v3_form = v3_first + 1;
    let mut v3_bad_boolean = words(&legacy_v3(&sleeping));
    v3_bad_boolean[v3_form + 16] = 2;
    assert!(SleepingBody::decode(&bytes(&v3_bad_boolean)).is_err());

    let mut v3_bad_turn = words(&legacy_v3(&sleeping));
    v3_bad_turn[v3_form + 4] = 4;
    assert!(SleepingBody::decode(&bytes(&v3_bad_turn)).is_err());

    let mut v3_bad_rank = words(&legacy_v3(&sleeping));
    v3_bad_rank[v3_form + 2] = u32::MAX;
    assert!(SleepingBody::decode(&bytes(&v3_bad_rank)).is_err());
}

#[test]
fn the_archive_is_create_new_and_never_overwrites() {
    let sleeping = fixture();
    let serial = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "soma-sleep-v9-{}-{serial}.body",
        std::process::id()
    ));
    let encoded = sleeping.encode();
    let written = sleeping
        .archive_new(&path)
        .expect("the streamed new chart lands once");
    assert_eq!(written, encoded.len());
    assert_eq!(std::fs::read(&path).unwrap(), encoded);
    let overwrite = sleeping
        .archive_new(&path)
        .expect_err("the periplus never overwrites a body");
    assert_eq!(overwrite.kind(), std::io::ErrorKind::AlreadyExists);
    assert_eq!(SleepingBody::read_archive(&path).unwrap(), sleeping);
    assert_eq!(sleeping.verify_archive(&path).unwrap(), written);
    use std::io::Write as _;
    std::fs::OpenOptions::new()
        .append(true)
        .open(&path)
        .unwrap()
        .write_all(&0u32.to_le_bytes())
        .unwrap();
    assert!(sleeping.verify_archive(&path).is_err());
    assert!(SleepingBody::read_current_archive(&path).is_err());
    std::fs::remove_file(path).unwrap();
}

#[test]
fn carrier_rows_stream_to_the_exact_v9_mouth_and_dissipate_at_the_receiving_read() {
    let one = fixture();
    let shallow = one.carriers().to_vec();
    let deep_words = body::manifold::carrier_row_words(3);
    let mut deep = vec![0u32; deep_words];
    deep[..body::manifold::CARRIER_HEADER_WORDS]
        .copy_from_slice(&shallow[..body::manifold::CARRIER_HEADER_WORDS]);
    let mut carriers = shallow.clone();
    carriers.extend_from_slice(&deep);
    let sleeping = SleepingBody::from_variable_parts(
        one.standing_axis(),
        one.occupancy(),
        vec![shallow.len() as u32, deep.len() as u32],
        one.standing().to_vec(),
        carriers,
        one.comprehended_light_bytes(),
    )
    .unwrap();
    let frame = SleepingBodyFrame::from_parts(
        sleeping.standing_axis(),
        sleeping.occupancy(),
        sleeping.carrier_row_word_extents().to_vec(),
        sleeping.standing().to_vec(),
        sleeping.comprehended_light_bytes(),
    )
    .unwrap();
    let serial = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "soma-stream-sleep-v9-{}-{serial}.body",
        std::process::id()
    ));
    let mut archive = frame.archive_new(&path).unwrap();
    for row in sleeping.carrier_rows() {
        archive.write_carrier_row(row).unwrap();
    }
    assert_eq!(archive.finish().unwrap() as u64, frame.archive_bytes());
    assert_eq!(std::fs::read(&path).unwrap(), sleeping.encode());
    assert_eq!(SleepingBody::read_current_archive(&path).unwrap(), sleeping);
    assert_eq!(
        SleepingBody::read_current_receiving_archive(&path).unwrap(),
        (
            frame.standing_axis(),
            frame.occupancy(),
            frame.standing().to_vec(),
            frame.comprehended_light_bytes(),
        ),
        "the receiving read validates every ended current but retains only the inheritable standing face",
    );
    std::fs::remove_file(path).unwrap();
}

#[test]
fn the_v9_frame_carries_more_than_one_u32_of_identity_without_materializing_it() {
    let one = fixture();
    let row_words = body::manifold::carrier_row_words(5_000_000);
    assert!(row_words <= u32::MAX as usize);
    let frame = SleepingBodyFrame::from_parts(
        one.standing_axis(),
        one.occupancy(),
        vec![row_words as u32; 3],
        one.standing().to_vec(),
        one.comprehended_light_bytes(),
    )
    .unwrap();
    assert!(frame.carrier_words() > u32::MAX as u64);
    assert!(frame.archive_bytes() > (u32::MAX as u64) * 4);
    assert_eq!(frame.lineage_count(), 3);
}

#[test]
fn a_zero_extended_form_crosses_v9_semantically_whole() {
    let source = fixture();
    let old_grip = 11u32;
    let new_axis = 8u32;
    let new_grip = body::chart::zero_extend_grip(old_grip, 4, new_axis) as usize;
    let mut standing = vec![0u32; new_axis as usize * new_axis as usize * body::medium::FORM_WORDS];
    let source_at = old_grip as usize * body::medium::FORM_WORDS;
    let target_at = new_grip * body::medium::FORM_WORDS;
    standing[target_at..target_at + body::medium::FORM_WORDS]
        .copy_from_slice(&source.standing()[source_at..source_at + body::medium::FORM_WORDS]);
    let rebased = SleepingBody::from_parts(
        new_axis,
        1,
        source.carrier_row_words() as u32,
        source.lineage_count() as u32,
        standing,
        source.carriers().to_vec(),
        source.comprehended_light_bytes(),
    )
    .unwrap();
    let decoded = SleepingBody::decode(&rebased.encode()).unwrap();
    assert_eq!(
        body::medium::RegionalForm::unpack(decoded.standing(), target_at),
        legacy_form(&DIRECTED_FORM_WORDS),
        "the chart digit moves the grip and leaves its RegionalForm construction whole",
    );
    assert_eq!(decoded, rebased);
}

#[test]
fn malformed_parts_cannot_cross_the_sleep_mouth() {
    let row_words = body::manifold::carrier_row_words(1);
    assert!(SleepingBody::from_parts(
        3,
        0,
        row_words as u32,
        1,
        vec![0u32; 9 * body::medium::FORM_WORDS],
        vec![0u32; row_words],
        2,
    )
    .is_err());

    let source = fixture();
    assert!(SleepingBody::from_parts(
        source.standing_axis(),
        source.occupancy(),
        source.carrier_row_words() as u32,
        0,
        source.standing().to_vec(),
        source.carriers().to_vec(),
        source.comprehended_light_bytes(),
    )
    .is_err());
    assert!(SleepingBody::from_parts(
        source.standing_axis(),
        source.occupancy(),
        source.carrier_row_words() as u32,
        2,
        source.standing().to_vec(),
        source.carriers().to_vec(),
        source.comprehended_light_bytes(),
    )
    .is_err());
}
