//! quest — THE DEFINITIONAL TOPOLOGY (Brandon, 2026-07-09). *"Networking the topology of how word
//! definitions are utilized in compositions"* — the primitive first-contact use-case: feed a real
//! dictionary (Webster's Unabridged 1913, Project Gutenberg #29765) beside real usage (Alice in
//! Wonderland, PG #11), and read whether the DEFINITIONAL faces stand and whether they BEND the
//! reading of usage. Research observations, run by hand (`-- --ignored --nocapture`), each under a
//! minute. Data: `soma/diet/` (gitignored; provenance in `LEDGER.md`).
//!
//! The disciplines hold: keep ALL characters (entries feed whole, no linguist's filter); three-body
//! (the FOIL is the SAME dictionary bytes coprime-scattered — a reversible worldline that coheres its own material; the
//! comparison is form-vs-form, never signal-vs-nothing); the read is a TOPOLOGY (a profile of face-grips), never one scalar; the
//! counts are noise, the content discriminates.
#![cfg(test)]

use crate::manifold::{locate, ErosBody, TermCounts};
use crate::medium::{RegionalForm, FORM_WORDS};

const AXIS: i64 = 1 << 11; // 4M cells — the real-diet scale needs spread (the W3 collision finding, live)
/// entries feed their first stretch — the window is the collocation grain, so a headword networks
/// with its opening definientia; a longer feed only adds body-internal faces. A staging choice, declared.
const ENTRY_WORDS: usize = 40;

fn load(paths: &[&str]) -> Option<std::vec::Vec<u8>> {
    paths.iter().find_map(|p| std::fs::read(p).ok())
}

fn words_of(text: &[u8]) -> std::vec::Vec<&[u8]> {
    text.split(|&b| b == b' ' || b == b'\n' || b == b'\t' || b == b'\r')
        .filter(|w| w.len() >= 2)
        .collect()
}

/// parse Webster entries: an ALL-CAPS line is a headword; the body runs to the next headword.
fn webster_entries(text: &str) -> std::vec::Vec<(std::string::String, std::string::String)> {
    let start = text.find("*** START").unwrap_or(0);
    let mut entries = std::vec::Vec::new();
    let mut head: Option<std::string::String> = None;
    let mut body = std::string::String::new();
    for line in text[start..].lines() {
        let t = line.trim();
        let is_head = t.len() >= 2
            && t.len() <= 24
            && t.chars()
                .all(|c| c.is_ascii_uppercase() || c == ' ' || c == '\'' || c == '-')
            && t.chars().next().is_some_and(|c| c.is_ascii_uppercase());
        if is_head {
            if let Some(h) = head.take() {
                entries.push((h, core::mem::take(&mut body)));
            }
            head = Some(t.to_ascii_lowercase());
        } else if head.is_some() {
            body.push_str(line);
            body.push(' ');
        }
    }
    if let Some(h) = head {
        entries.push((h, body));
    }
    entries
}

/// The test membrane's bounded light-end fold. Dictionary and usage are two lights: every
/// dictionary deed lands in its lane-local spool, that complete configuration integrates once,
/// then a fresh usage current reads the resulting pre-light standing form.
fn integrate_light(standing: &mut [u32], own_regions: &[&[u32]]) {
    let mut forms = std::vec::Vec::with_capacity(own_regions.len() + 1);
    let mut grip = 0usize;
    while grip < standing.len() / FORM_WORDS {
        let at = grip * FORM_WORDS;
        forms.clear();
        forms.push(RegionalForm::unpack(standing, at));
        let mut touched = false;
        for own in own_regions {
            assert_eq!(own.len(), standing.len());
            let form = RegionalForm::unpack(own, at);
            touched |= form != RegionalForm::UNBORN;
            forms.push(form);
        }
        if touched {
            crate::medium::integrate(&forms).pack(standing, at);
        }
        grip += 1;
    }
}

/// Fly dictionary light → integrate at its true edge → fly usage as a later light. `own` is
/// the boundary reservation reused only after the first light has resolved; the body never sees the
/// reset and no state crosses except the standing regional form.
fn ingest(
    dict_stream: &[&[u8]],
    usage: &[&[u8]],
    standing: &mut [u32],
    own: &mut [u32],
) -> (TermCounts, TermCounts, std::vec::Vec<bool>) {
    let dictionary_terms = {
        let mut carrier = std::vec![0u32; 8 * crate::manifold::ENCLOSURE_WORDS];
        let mut eyes = ErosBody::over(standing, own, AXIS, b" d", 1 << 20, &mut carrier);
        for &w in dict_stream {
            eyes.perceive(w, 100);
        }
        eyes.flush_dark();
        eyes.deposited_terms()
    };
    integrate_light(standing, &[own]);
    own.fill(0);

    let mut carrier = std::vec![0u32; 8 * crate::manifold::ENCLOSURE_WORDS];
    let mut eyes = ErosBody::over(standing, own, AXIS, b" u", 1 << 20, &mut carrier);
    let cuts: std::vec::Vec<bool> = usage
        .iter()
        .map(|&w| eyes.perceive(w, 100).thought_completed)
        .collect();
    eyes.flush_dark();
    let usage_terms = eyes.deposited_terms();
    (dictionary_terms, usage_terms, cuts)
}

/// ★ THE DEFINITIONAL FACES STAND — after ingesting the dictionary, the headword→definiens faces hold
/// mass the scattered FOIL worldline (same bytes, its own coherences) does not concentrate the same way.
#[test]
#[ignore]
fn observe_the_definitional_topology() {
    let Some(dict_raw) = load(&["../diet/websters1913.txt", "diet/websters1913.txt"]) else {
        std::eprintln!("  (no dictionary on disk — skipped)");
        return;
    };
    let Some(alice_raw) = load(&["../diet/alice.txt", "diet/alice.txt"]) else {
        std::eprintln!("  (no usage text on disk — skipped)");
        return;
    };
    let dict_text = std::string::String::from_utf8_lossy(&dict_raw);
    let entries = webster_entries(&dict_text);
    std::eprintln!("  Webster's parsed: {} entries", entries.len());

    // the probe vocabulary — words alive in BOTH the dictionary and Alice.
    let probes: [&str; 6] = ["cat", "queen", "garden", "time", "head", "voice"];
    let picked: std::vec::Vec<&(std::string::String, std::string::String)> = probes
        .iter()
        .filter_map(|p| entries.iter().find(|(h, b)| h == p && b.len() > 80))
        .collect();
    // ⊕ a surrounding lexicon: the first entry for each of ~120 frequent Alice words, so the
    // dictionary terrain is a NETWORK, not six islands.
    let alice_body = alice_raw[alice_raw
        .windows(9)
        .position(|w| w == b"*** START")
        .map(|p| p + 600)
        .unwrap_or(0)..]
        .to_vec();
    let alice_words = words_of(&alice_body[..alice_body.len().min(40000)]);
    let mut lexicon: std::vec::Vec<&(std::string::String, std::string::String)> =
        std::vec::Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for w in &alice_words {
        if lexicon.len() >= 120 {
            break;
        }
        let lw = std::string::String::from_utf8_lossy(w).to_ascii_lowercase();
        let lw = lw.trim_matches(|c: char| !c.is_ascii_alphabetic());
        if lw.len() >= 3 && seen.insert(lw.to_owned()) {
            if let Some(e) = entries.iter().find(|(h, b)| h == lw && b.len() > 80) {
                lexicon.push(e);
            }
        }
    }
    std::eprintln!(
        "  the diet: {} probe entries ⊕ {} lexicon entries ⊕ Alice usage",
        picked.len(),
        lexicon.len()
    );

    // the dictionary stream: headword, then its opening body — the definitional worldline.
    let mut dict_stream_owned: std::vec::Vec<std::vec::Vec<u8>> = std::vec::Vec::new();
    for (h, b) in picked.iter().chain(lexicon.iter()) {
        dict_stream_owned.push(h.as_bytes().to_vec());
        for w in words_of(b.as_bytes()).into_iter().take(ENTRY_WORDS) {
            dict_stream_owned.push(w.to_vec());
        }
    }
    let dict_stream: std::vec::Vec<&[u8]> =
        dict_stream_owned.iter().map(|v| v.as_slice()).collect();
    // the FOIL worldline: the SAME dictionary words coprime-scattered (a REVERSIBLE permutation — time-parity
    // unbroken, so nothing is "nulled": the scattered stream is a worldline of its own that coheres its own material; the read is the DIFFERENCE between two worldlines over one substance — a comparison, never signal-vs-nothing).
    let n = dict_stream.len();
    let stride = (0..)
        .map(|k| 101 + k * 2)
        .find(|s| gcd(*s, n) == 1)
        .unwrap();
    let foil_stream: std::vec::Vec<&[u8]> = (0..n).map(|i| dict_stream[(i * stride) % n]).collect();
    std::eprintln!("  dictionary stream {} words · foil stride {}", n, stride);

    let usage = words_of(&alice_body[..alice_body.len().min(40000)]);
    let region_words = (AXIS * AXIS) as usize * FORM_WORDS;
    let mut standing_real = std::vec![0u32; region_words];
    let mut standing_foil = std::vec![0u32; region_words];
    let mut own = std::vec![0u32; region_words];
    let (dict_terms_real, usage_terms_real, cuts_real) =
        ingest(&dict_stream, &usage, &mut standing_real, &mut own);
    own.fill(0);
    let (dict_terms_foil, usage_terms_foil, cuts_foil) =
        ingest(&foil_stream, &usage, &mut standing_foil, &mut own);
    std::eprintln!(
        "  terms (dictionary → later usage): REAL {:?} → {:?} · FOIL {:?} → {:?}",
        dict_terms_real,
        usage_terms_real,
        dict_terms_foil,
        usage_terms_foil,
    );

    // ★ READ 1 — THE DEFINITIONAL FACES: for each probe, the face-profile headword→definientia
    // (the first 12 distinct ≥3-char body words), REAL vs SCATTERED. The topology, per probe.
    std::eprintln!(
        "\n  ★ THE DEFINITIONAL FACES (exact headword→definiens forms, REAL vs SCATTERED):"
    );
    let read_profile =
        |standing: &std::vec::Vec<u32>, h: &str, b: &str| -> std::vec::Vec<(u32, RegionalForm)> {
            let hw = locate(h.as_bytes());
            let mut topology = std::vec::Vec::new();
            let mut taken = std::collections::BTreeSet::new();
            for w in words_of(b.as_bytes()) {
                if taken.len() >= 12 {
                    break;
                }
                if w.len() >= 3 && taken.insert(w.to_vec()) {
                    let g = crate::manifold::face_grip_of(hw, locate(w), AXIS);
                    let at = (g as usize) * FORM_WORDS;
                    if at + FORM_WORDS <= standing.len() {
                        topology.push((g, RegionalForm::unpack(standing, at)));
                    }
                }
            }
            topology
        };
    for (h, b) in &picked {
        let (real, foil) = (
            read_profile(&standing_real, h, b),
            read_profile(&standing_foil, h, b),
        );
        std::eprintln!("    «{h}»:");
        for ((grip, real_form), (_, foil_form)) in real.iter().zip(foil.iter()) {
            if real_form != foil_form {
                std::eprintln!("      #{grip}: REAL {real_form:?} · SCATTERED {foil_form:?}");
            }
        }
    }

    // ★ READ 2 — THE DEFINITIONS BEND THE USAGE-READING: the same Alice, two priors (real dictionary
    // vs scattered dictionary) — where do the thought-cuts diverge?
    let diverge = cuts_real
        .iter()
        .zip(cuts_foil.iter())
        .filter(|(a, b)| a != b)
        .count();
    std::eprintln!(
        "\n  ★ THE COUPLING: the same {} Alice words read from the two priors — {} cut-positions diverge",
        cuts_real.len(),
        diverge
    );
    if let Some(first) = cuts_real
        .iter()
        .zip(cuts_foil.iter())
        .position(|(a, b)| a != b)
    {
        let lo = first.saturating_sub(4);
        let ctx: std::vec::Vec<_> = usage[lo..(first + 4).min(usage.len())]
            .iter()
            .map(|w| std::string::String::from_utf8_lossy(w))
            .collect();
        std::eprintln!("    first divergence at word {first}: …{}…", ctx.join(" "));
    }
}

fn gcd(a: usize, b: usize) -> usize {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}
