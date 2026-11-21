//! [definition; agent-inferred, November 16, the theory thread's Build B of 18:58 UTC, the friction record §3] **The arithmetic world, a
//! receiver at the boundary that answers the field's own act.** The field drafts the next record of the world's passage after a few of the
//! world's own records; the world reads the draft up to its first `= ` (or its first line feed), evaluates the expression it holds, and
//! appends its value and a line feed, or `?` and a line feed where the draft holds no expression it reads. Its reaction is a function of
//! the act alone. It is terrain, an authored routine at the exterior (CLAUDE.md, "No catered machinery": a terrain may generate its truth
//! with authored routines at declared widths); no receiver of the machine computes an answer, and the machine meets only the bytes the
//! world returns, at the places the comparison reads.
//!
//! The world reads as it writes (`tools/arithmetic_world.py`): integers in decimal, the most significant digit first, with no leading zero
//! but for zero itself; `+`, `-` and `*`, with `*` binding before `+` and `-`, each left to right; parentheses; spaces between tokens, any
//! number of them. A value past the world's width (a signed word of 128 bits) is a draft it does not read.

/// The world's reaction to a draft: the draft's places the world read (its expression and the `= `, or up to and with its first line feed,
/// or the whole draft), and the bytes the world appends after them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reaction {
    pub read: usize,
    pub appended: Vec<u8>,
}

/// The world's reaction to the field's draft ([`Reaction`]).
pub fn react(draft: &[u8]) -> Reaction {
    let eq = draft.windows(2).position(|w| w == b"= ");
    let feed = draft.iter().position(|&b| b == b'\n');
    match (eq, feed) {
        (Some(e), f) if f.is_none_or(|f| e < f) => match answer(&draft[..e]) {
            Some(mut v) => {
                v.push(b'\n');
                Reaction { read: e + 2, appended: v }
            }
            None => Reaction { read: e + 2, appended: b"?\n".to_vec() },
        },
        (_, Some(f)) => Reaction { read: f + 1, appended: b"?\n".to_vec() },
        (_, None) => Reaction { read: draft.len(), appended: b"\n?\n".to_vec() },
    }
}

/// [definition; the lead, November 21, Brandon's 04:52Z and 04:54Z (the deterministic panel read nothing at L17, L71 or L75; "do not expect
/// arithmetic or code success without tension reinforcement")] **What the world answers to an expression**, or `None` where it reads
/// none: its value where it is arithmetic ([`value`]); where it is brackets alone (`(`, `[`, `{` and their closers, spaced), the closers
/// that close what stands open, innermost first, spaced (`( [ {` → `} ] )`), and nothing where a closer meets no opener of its kind or
/// nothing stands open; where it is `copy` and digits, the digits; where it is `reverse` and digits, the digits in the other order. Each
/// is a law whose answer is fixed by operands that stand away from the answer's places, which is what the panel found she does not
/// carry. Terrain at the exterior (CLAUDE.md, "No catered machinery"), never the machine's.
pub fn answer(expression: &[u8]) -> Option<Vec<u8>> {
    let text = std::str::from_utf8(expression).ok()?.trim_matches(' ');
    let words: Vec<&str> = text.split(' ').filter(|w| !w.is_empty()).collect();
    let digits = |ws: &[&str]| !ws.is_empty() && ws.iter().all(|w| w.len() == 1 && w.as_bytes()[0].is_ascii_digit());
    match words.first() {
        Some(&"copy") if digits(&words[1..]) => return Some(words[1..].join(" ").into_bytes()),
        Some(&"reverse") if digits(&words[1..]) => return Some(words[1..].iter().rev().copied().collect::<Vec<_>>().join(" ").into_bytes()),
        _ => {}
    }
    if !words.is_empty() && words.iter().all(|w| matches!(*w, "(" | "[" | "{" | ")" | "]" | "}")) {
        let mut open: Vec<&str> = Vec::new();
        for &w in &words {
            match w {
                "(" | "[" | "{" => open.push(w),
                _ => {
                    let want = match open.pop()? { "(" => ")", "[" => "]", _ => "}" };
                    if want != w {
                        return None;
                    }
                }
            }
        }
        if open.is_empty() {
            return None;
        }
        return Some(open.iter().rev().map(|&o| match o { "(" => ")", "[" => "]", _ => "}" }).collect::<Vec<_>>().join(" ").into_bytes());
    }
    value(expression).map(|v| v.to_string().into_bytes())
}

/// [definition; the lead, November 21] **The world's kinds of record**, each one line `EXPRESSION = ANSWER`: a sum, a difference, a product,
/// brackets to close, digits to copy and digits to reverse.
pub const KINDS: [&str; 6] = ["sum", "difference", "product", "close", "copy", "reverse"];

/// SplitMix64, the mixer of the world's draws (the passage's, [`holonics_engine::passage`]).
fn mix(z: u64) -> u64 {
    let z = z.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    let z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// FNV-1a over an expression's octets: the key of [`held`] (`tools/terrain_panel.py` reads the same).
pub fn fnv(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xCBF2_9CE4_8422_2325u64, |h, &b| (h ^ u64::from(b)).wrapping_mul(0x0000_0100_0000_01B3))
}

/// [definition; the lead, November 21] **A held expression**: one in sixteen by its own octets' key, never written into a section, so a
/// panel's held records are unseen whatever the draws. Why by the expression and not the draw: two draws that write one expression are
/// one record to the field.
pub fn held(expression: &[u8]) -> bool {
    // FNV-1a's low bits are its octets' low bits alone (its prime is odd), so the key is mixed before it is read modulo sixteen.
    mix(fnv(expression)) % 16 == 0
}

/// [definition; the lead, November 21] **The world's record of kind `kind` at draw `key`**: its expression and its answer, the expression
/// never [`held`] (a held draw is drawn again at the next key of its stream). Operands: a sum's and a difference's of one to three digits
/// each (a difference's first the larger), a product's of one or two digits by one; brackets one to six deep, each of `(`, `[`, `{`;
/// copies and reversals two to seven digits.
pub fn record(kind: usize, key: u64) -> (Vec<u8>, Vec<u8>) {
    let mut z = mix(key ^ (kind as u64).wrapping_mul(0xA24B_AED4_963E_E407));
    loop {
        let mut draw = |n: u64| {
            z = mix(z);
            z % n
        };
        let mut number = |most: u32| {
            let width = 1 + draw(u64::from(most)) as u32;
            let low = if width == 1 { 0 } else { 10u64.pow(width - 1) };
            low + draw(10u64.pow(width) - low)
        };
        let expression = match KINDS[kind % KINDS.len()] {
            "sum" => format!("{} + {}", number(3), number(3)),
            "difference" => {
                let (a, b) = (number(3), number(3));
                format!("{} - {}", a.max(b), a.min(b))
            }
            "product" => format!("{} * {}", number(2), number(1)),
            "close" => {
                let depth = 1 + draw(6);
                (0..depth).map(|_| ["(", "[", "{"][draw(3) as usize]).collect::<Vec<_>>().join(" ")
            }
            name => {
                let len = 2 + draw(6);
                format!("{name} {}", (0..len).map(|_| draw(10).to_string()).collect::<Vec<_>>().join(" "))
            }
        };
        let expression = expression.into_bytes();
        if !held(&expression) {
            let answered = answer(&expression).unwrap_or_default();
            return (expression, answered);
        }
    }
}

/// The value of an expression as the world writes it, or `None` where the world does not read it.
pub fn value(text: &[u8]) -> Option<i128> {
    let mut at = 0usize;
    let v = sum(text, &mut at)?;
    skip(text, &mut at);
    if at == text.len() { Some(v) } else { None }
}

fn skip(t: &[u8], at: &mut usize) {
    while *at < t.len() && t[*at] == b' ' {
        *at += 1;
    }
}

fn sum(t: &[u8], at: &mut usize) -> Option<i128> {
    let mut v = product(t, at)?;
    loop {
        skip(t, at);
        match t.get(*at) {
            Some(b'+') => {
                *at += 1;
                v = v.checked_add(product(t, at)?)?;
            }
            Some(b'-') => {
                *at += 1;
                v = v.checked_sub(product(t, at)?)?;
            }
            _ => return Some(v),
        }
    }
}

fn product(t: &[u8], at: &mut usize) -> Option<i128> {
    let mut v = atom(t, at)?;
    loop {
        skip(t, at);
        if t.get(*at) == Some(&b'*') {
            *at += 1;
            v = v.checked_mul(atom(t, at)?)?;
        } else {
            return Some(v);
        }
    }
}

fn atom(t: &[u8], at: &mut usize) -> Option<i128> {
    skip(t, at);
    match t.get(*at) {
        Some(b'(') => {
            *at += 1;
            let v = sum(t, at)?;
            skip(t, at);
            if t.get(*at) != Some(&b')') {
                return None;
            }
            *at += 1;
            Some(v)
        }
        Some(d) if d.is_ascii_digit() => {
            let from = *at;
            while *at < t.len() && t[*at].is_ascii_digit() {
                *at += 1;
            }
            let digits = &t[from..*at];
            if digits.len() > 1 && digits[0] == b'0' {
                return None;
            }
            let mut v: i128 = 0;
            for &d in digits {
                v = v.checked_mul(10)?.checked_add(i128::from(d - b'0'))?;
            }
            Some(v)
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// [definition; Build B] The world reads its own records as `tools/arithmetic_world.py` writes them, and answers only the act.
    #[test]
    fn the_world_reads_its_own_records_and_answers_the_act() {
        assert_eq!(value(b"619136 + 272568"), Some(891_704));
        assert_eq!(value(b"(5 * 34) * 1279"), Some(217_430));
        assert_eq!(value(b"4379 * (3 - 627)"), Some(-2_732_496));
        assert_eq!(value(b"0 + ((7113 - 8) - 9)"), Some(7096));
        assert_eq!(value(b"2 + 3 * 4"), Some(14), "a product binds first");
        assert_eq!(value(b"10 - 3 - 2"), Some(5), "left to right");
        for bad in [&b"007 + 1"[..], b"1 +", b"(1 + 2", b"1 + 2)", b"plus", b"", b"1 2", b"99999999999999999999 * 99999999999999999999 * 99999"] {
            assert_eq!(value(bad), None, "{}", String::from_utf8_lossy(bad));
        }
        assert_eq!(react(b"5125 - 73 = 1\n8 + "), Reaction { read: 12, appended: b"5052\n".to_vec() });
        assert_eq!(react(b"5125 -- 73 = 1"), Reaction { read: 13, appended: b"?\n".to_vec() });
        assert_eq!(react(b"cat\n8 = 1"), Reaction { read: 4, appended: b"?\n".to_vec() });
        assert_eq!(react(b"no end"), Reaction { read: 6, appended: b"\n?\n".to_vec() });
    }

    /// [definition; the lead, November 21] The world answers brackets, copies and reversals as it answers sums, and its records are never held.
    #[test]
    fn the_world_answers_its_other_laws_and_writes_no_held_record() {
        assert_eq!(answer(b"( [ {"), Some(b"} ] )".to_vec()));
        assert_eq!(answer(b"( [ ] {"), Some(b"} )".to_vec()));
        assert_eq!(answer(b"( ]"), None, "a closer of another kind");
        assert_eq!(answer(b"( )"), None, "nothing stands open");
        assert_eq!(answer(b"copy 4 8 2 6"), Some(b"4 8 2 6".to_vec()));
        assert_eq!(answer(b"reverse 7 8 9"), Some(b"9 8 7".to_vec()));
        assert_eq!(answer(b"reverse 7 88"), None);
        assert_eq!(answer(b"3 + 4"), Some(b"7".to_vec()));
        assert_eq!(react(b"{ [ ( = ) ] }\n"), Reaction { read: 8, appended: b") ] }\n".to_vec() });
        assert_eq!(fnv(b"a"), 0xAF63_DC4C_8601_EC8C, "FNV-1a's published value for one octet");
        for kind in 0..KINDS.len() {
            for key in 0..400u64 {
                let (e, a) = record(kind, key);
                assert!(!held(&e), "a held record written");
                assert_eq!(answer(&e), Some(a.clone()), "{}", String::from_utf8_lossy(&e));
                assert!(!a.is_empty());
            }
        }
        assert_eq!(record(0, 7), record(0, 7), "a record is its key's");
    }
}
