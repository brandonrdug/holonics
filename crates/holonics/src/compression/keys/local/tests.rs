use super::*;
use crate::holarchy::terrain::Draw;

fn damaged(truth: &[usize], erased: &[usize], classes: usize) -> DamagedPassage {
    let cells = (0..truth.len())
        .map(|t| (!erased.contains(&t)).then_some(truth[t]))
        .collect();
    DamagedPassage::new(cells, classes, 0).unwrap()
}

/// [implemented-exact] **The cover's certificate.** On 48 cells, regions of 16 at stride 8 read to
/// `r = 4` are the five regions `[0,16) … [32,48)`; an overlap shorter than two turns of the reach,
/// or a stride that does not tile the passage, is refused.
#[test]
fn the_cover_certifies_every_read_distance_on_its_overlaps() {
    let cover = Cover::declare(48, 16, 8, 4).unwrap();
    assert_eq!(
        cover.regions(),
        vec![0..16, 8..24, 16..32, 24..40, 32..48]
    );
    assert!(Cover::declare(48, 16, 8, 5).is_err());
    assert!(Cover::declare(48, 16, 10, 3).is_err());
    assert!(Cover::declare(48, 16, 16, 1).is_err());
}

/// [implemented-exact] **Two local keys, each glued within its half and open across the seam.** On
/// `ℤ/4`, the alternation `0 1 0 1 …` over cells `[0, 24)` (the swap at `δ = 1`, a turn of order 2)
/// and the constant `2` over `[24, 48)` (the identity at `δ = 1`). The region straddling the seam reads
/// a port with two consequences at every distance, so it is empty, and the joins beside it are open;
/// each half's two regions glue uniquely. Every erased cell restricted by one glued region is
/// released equal to its truth, the cell in the empty region's overlap through the half that keys it.
#[test]
fn two_local_keys_glue_within_their_halves_and_release_their_cells() {
    let truth: Vec<usize> = (0..48).map(|t| if t < 24 { t % 2 } else { 2 }).collect();
    let erased = [5, 11, 12, 20, 35, 39, 40, 41, 42];
    let passage = damaged(&truth, &erased, 4);
    let cover = Cover::declare(48, 16, 8, 4).unwrap();
    let local = locate(&passage, &cover, 4).unwrap();
    assert_eq!(
        local.keys,
        vec![
            LocalKey::One(1),
            LocalKey::One(1),
            LocalKey::Empty,
            LocalKey::One(1),
            LocalKey::One(1)
        ]
    );
    assert_eq!(
        local.joins,
        vec![Join::Unique, Join::Open, Join::Open, Join::Unique]
    );
    let spans: Vec<_> = local.glued.iter().map(|glued| glued.span.clone()).collect();
    assert_eq!(spans, vec![0..24, 16..32, 24..48]);
    let releases = local.release(&passage).unwrap();
    for &t in &erased {
        assert_eq!(releases[t], CellRelease::Released(truth[t]), "cell {t}");
    }
    let residual = local.residual_code(&truth, &passage).unwrap();
    assert!(residual.is_empty());
}

/// Whether a completion of a span satisfies a relation at every pair inside it.
fn holds(cells: &[usize], relation: &PairRelation) -> bool {
    (relation.offset()..cells.len()).all(|t| relation.joins(cells[t - relation.offset()], cells[t]))
}

/// [implemented-exact] **A located glued region's family is its member's projection, the release
/// is that projection when it is one class, a plural glued region restricts nothing, and the
/// residual reopens the passage.** On 400 drawn passages of 24 cells over `ℤ/4` (runs of a drawn
/// period-1 or period-2 word, with a drawn cell changed now and then, so that regions key, plural
/// and empty all occur, and every join kind), five drawn cells erased, the cover of regions 8 at
/// stride 4 read to `r = 2`: a glued region has a member exactly when its key is one; for every
/// such region the brute-force joint (every completion of its erased cells under which the member
/// holds at every pair of the span) projects at each cell exactly onto the family the owner restricts
/// it to, the member is refused exactly when no completion satisfies it, every released cell is its
/// projection's one class, and every residual the truth admits reopens the passage exactly.
#[test]
fn the_glued_families_are_the_brute_force_projection() {
    let mut draw = Draw::new(2_026_100_531);
    let cover = Cover::declare(24, 8, 4, 2).unwrap();
    let (mut keyed, mut plural, mut empty, mut released, mut reopened) = (0, 0, 0, 0, 0);
    let mut joins = [0usize; 4];
    for _ in 0..400 {
        let mut truth = Vec::with_capacity(24);
        while truth.len() < 24 {
            let period = 1 + draw.below(2);
            let word: Vec<usize> = (0..period).map(|_| draw.below(4)).collect();
            let run = 4 + draw.below(8);
            for k in 0..run {
                truth.push(if draw.below(16) == 0 { draw.below(4) } else { word[k % period] });
            }
        }
        truth.truncate(24);
        let mut erased = Vec::new();
        while erased.len() < 5 {
            let t = draw.below(24);
            if !erased.contains(&t) {
                erased.push(t);
            }
        }
        let passage = damaged(&truth, &erased, 4);
        let local = locate(&passage, &cover, 4).unwrap();
        for key in &local.keys {
            match key {
                LocalKey::One(_) => keyed += 1,
                LocalKey::Plural(_) => plural += 1,
                _ => empty += 1,
            }
        }
        for join in &local.joins {
            joins[*join as usize] += 1;
        }
        let read = local.families(&passage).unwrap();
        for (index, glued) in local.glued.iter().enumerate() {
            assert_eq!(glued.members.len(), usize::from(matches!(glued.key, LocalKey::One(_))));
            if glued.members.is_empty() {
                continue;
            }
            let span = glued.span.clone();
            let open: Vec<usize> = span.clone().filter(|t| erased.contains(t)).collect();
            let mut projection = vec![Vec::<usize>::new(); span.len()];
            let mut refused = 0;
            for member in &glued.members {
                let mut any = false;
                for code in 0..4usize.pow(open.len() as u32) {
                    let mut cells: Vec<usize> = span.clone().map(|t| truth[t]).collect();
                    for (k, &t) in open.iter().enumerate() {
                        cells[t - span.start] = (code / 4usize.pow(k as u32)) % 4;
                    }
                    if holds(&cells, member) {
                        any = true;
                        for (offset, &class) in cells.iter().enumerate() {
                            if !projection[offset].contains(&class) {
                                projection[offset].push(class);
                            }
                        }
                    }
                }
                if !any {
                    refused += 1;
                }
            }
            assert_eq!(read.refused[index], refused);
            if refused == glued.members.len() {
                continue;
            }
            for (offset, family) in projection.iter_mut().enumerate() {
                let t = span.start + offset;
                family.sort_unstable();
                if read.restricted_by[t] == 1 {
                    assert_eq!(&read.families[t], family, "cell {t}");
                    assert!(read.certified[t] || passage.cells()[t].is_some());
                }
            }
        }
        let releases = local.release(&passage).unwrap();
        for (t, release) in releases.iter().enumerate() {
            if let CellRelease::Released(class) = release {
                released += 1;
                assert_eq!(read.restricted_by[t], 1);
                assert_eq!(read.families[t], vec![*class]);
            }
        }
        if let Ok(residual) = local.residual_code(&truth, &passage) {
            let mut bits = residual.iter().copied();
            assert_eq!(local.reopen(&passage, &mut bits).unwrap(), truth);
            assert!(bits.next().is_none());
            reopened += 1;
        }
    }
    assert!(keyed > 0 && plural > 0 && empty > 0, "{keyed} {plural} {empty}");
    assert!(joins.iter().all(|&count| count > 0), "{joins:?}");
    assert!(released > 0 && reopened > 0, "{released} {reopened}");
}
