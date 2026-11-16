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
        (Some(e), f) if f.is_none_or(|f| e < f) => match value(&draft[..e]) {
            Some(v) => Reaction { read: e + 2, appended: format!("{v}\n").into_bytes() },
            None => Reaction { read: e + 2, appended: b"?\n".to_vec() },
        },
        (_, Some(f)) => Reaction { read: f + 1, appended: b"?\n".to_vec() },
        (_, None) => Reaction { read: draft.len(), appended: b"\n?\n".to_vec() },
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
}
