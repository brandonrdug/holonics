//! Exterior family + native continuation checkpoint; no frozen producing Word is retained.
use super::*;
use crate::hnn::reference::observed::ObservedStream;

fn number<T: std::str::FromStr>(it: &mut std::str::SplitWhitespace<'_>) -> Result<T, HnnError> {
    it.next()
        .and_then(|s| s.parse().ok())
        .ok_or_else(|| refused("the bounded reciprocal checkpoint syntax"))
}
fn member(it: &mut std::str::SplitWhitespace<'_>) -> Result<JointMember, HnnError> {
    Ok(JointMember {
        hypothesis: number(it)?,
        antecedent: number(it)?,
        consequence: number(it)?,
    })
}
impl JointFamily {
    /// Every tuple, menu, channel, address and last returned constraint; not two projections.
    pub fn checkpoint(&self) -> String {
        let mut s = format!(
            "joint-family-v1 {} {} {} {} {} {} {} {} {} {} {}\n",
            self.menu[0].classes(),
            self.menu.len(),
            usize::from(self.transposed),
            self.positions[0],
            self.positions[1],
            self.testimony[0],
            self.testimony[1],
            match self.channel {
                JointChannel::Exact => 0,
                JointChannel::AtMostOneChanged => 1,
                JointChannel::BothMayChange => 2,
            },
            self.bound.members,
            self.bound.visits,
            self.members.len()
        );
        for r in &self.menu {
            s += &format!("{}", r.offset());
            for x in r.map() {
                s += &format!(" {}", x.map_or_else(|| "-".into(), |x| x.to_string()));
            }
            s.push('\n');
        }
        for m in &self.members {
            s += &format!("{} {} {}\n", m.hypothesis, m.antecedent, m.consequence);
        }
        match &self.last_constraint {
            None => s += "none\n",
            Some(ms) => {
                s += &format!("some {}\n", ms.len());
                for m in ms {
                    s += &format!("{} {} {}\n", m.hypothesis, m.antecedent, m.consequence);
                }
            }
        }
        match &self.separating_return {
            None => s += "none\n",
            Some((position, class, lift)) => {
                s += &format!("some {position} {class} {}", lift.len());
                for x in lift {
                    s += &format!(" {x}");
                }
                s.push('\n');
            }
        }
        s
    }
    pub fn from_checkpoint(
        text: &str,
        maximum_bytes: usize,
        ceiling: JointBound,
    ) -> Result<Self, HnnError> {
        if text.len() > maximum_bytes {
            return Err(refused("the reciprocal family checkpoint byte bound"));
        }
        let mut it = text.split_whitespace();
        if it.next() != Some("joint-family-v1") {
            return Err(refused("the reciprocal family checkpoint version"));
        }
        let classes: usize = number(&mut it)?;
        let count: usize = number(&mut it)?;
        let transposed: usize = number(&mut it)?;
        let positions = [number(&mut it)?, number(&mut it)?];
        let testimony = [number(&mut it)?, number(&mut it)?];
        let channel = match number::<usize>(&mut it)? {
            0 => JointChannel::Exact,
            1 => JointChannel::AtMostOneChanged,
            2 => JointChannel::BothMayChange,
            _ => return Err(refused("the saved joint channel")),
        };
        let bound = JointBound {
            members: number(&mut it)?,
            visits: number(&mut it)?,
        };
        let n: usize = number(&mut it)?;
        let visits = count
            .checked_mul(classes)
            .and_then(|v| v.checked_mul(classes))
            .ok_or(HnnError::CountOverflow)?;
        if count == 0
            || classes == 0
            || transposed > 1
            || bound.members > ceiling.members
            || bound.visits > ceiling.visits
            || visits > bound.visits
            || n > bound.members
        {
            return Err(refused("the saved complete-family allocation/work bounds"));
        }
        let mut menu = Vec::new();
        for _ in 0..count {
            let offset = number(&mut it)?;
            let mut map = Vec::new();
            for _ in 0..classes {
                map.push(match it.next() {
                    Some("-") => None,
                    Some(x) => Some(
                        x.parse()
                            .map_err(|_| refused("a saved joint relation class"))?,
                    ),
                    None => return Err(refused("a complete saved joint relation")),
                });
            }
            menu.push(
                PairRelation::new(offset, map)
                    .map_err(|_| refused("the saved relation admission"))?,
            );
        }
        let (mut family, _) = Self::declare(
            menu,
            if transposed == 1 {
                [positions[1], positions[0]]
            } else {
                positions
            },
            if transposed == 1 {
                [testimony[1], testimony[0]]
            } else {
                testimony
            },
            [(0..classes).collect(), (0..classes).collect()],
            channel,
            bound,
        )?;
        if transposed == 1 {
            family = family.swapped();
        }
        let mut members = Vec::new();
        for _ in 0..n {
            let m = member(&mut it)?;
            if !family.members.contains(&m) || members.contains(&m) {
                return Err(refused(
                    "each saved whole joint member has full declared support",
                ));
            }
            members.push(m);
        }
        family.members = members;
        family.last_constraint = match it.next() {
            Some("none") => None,
            Some("some") => {
                let n: usize = number(&mut it)?;
                if n > bound.members {
                    return Err(refused("a saved constraint's member bound"));
                }
                let mut v = Vec::new();
                for _ in 0..n {
                    v.push(member(&mut it)?);
                }
                if v.iter().any(|m| {
                    m.hypothesis >= count || m.antecedent >= classes || m.consequence >= classes
                }) {
                    return Err(refused("a saved constraint's declared classes"));
                }
                Some(v)
            }
            _ => return Err(refused("the saved constraint")),
        };
        family.separating_return = match it.next() {
            Some("none") => None,
            Some("some") => {
                let p = number(&mut it)?;
                let c = number(&mut it)?;
                let n: usize = number(&mut it)?;
                if n > bound.visits {
                    return Err(refused("a saved return's lift bound"));
                }
                let mut lift = Vec::new();
                for _ in 0..n {
                    lift.push(number(&mut it)?);
                }
                Some((p, c, lift))
            }
            _ => return Err(refused("the saved separating return")),
        };
        if it.next().is_some() || family.checkpoint() != text {
            return Err(refused(
                "one complete canonical correlated family checkpoint",
            ));
        }
        Ok(family)
    }
}

fn hex(s: &str) -> String {
    s.as_bytes().iter().map(|b| format!("{b:02x}")).collect()
}
fn unhex(s: &str) -> Result<String, HnnError> {
    if !s.is_ascii() || !s.len().is_multiple_of(2) {
        return Err(refused("the reciprocal origin encoding"));
    }
    let v = (0..s.len())
        .step_by(2)
        .map(|n| {
            u8::from_str_radix(&s[n..n + 2], 16)
                .map_err(|_| refused("the reciprocal origin encoding"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    String::from_utf8(v).map_err(|_| refused("the reciprocal origin encoding"))
}
fn origin_text(origin: &ReturnOrigin) -> String {
    match origin {
        ReturnOrigin::Observed => "observed".into(),
        ReturnOrigin::Entailed {
            family,
            menu,
            channel,
            source,
        } => format!(
            "entailed {} {} {} {}",
            hex(family),
            hex(menu),
            hex(channel),
            hex(source)
        ),
    }
}
fn parse_origin(s: &str) -> Result<ReturnOrigin, HnnError> {
    let tokens = s.split_whitespace().collect::<Vec<_>>();
    match tokens.as_slice() {
        ["observed"] => Ok(ReturnOrigin::Observed),
        ["entailed", f, m, c, s] => Ok(ReturnOrigin::Entailed {
            family: unhex(f)?,
            menu: unhex(m)?,
            channel: unhex(c)?,
            source: unhex(s)?,
        }),
        _ => Err(refused("the saved reciprocal origin")),
    }
}

/// Exterior, complete continuation plus finite contextual family. Native retention remains the
/// existing ContinuingState; the bounded crib/pending/testimony are explicitly beside it.
pub struct ReciprocalCheckpoint {
    native: ContinuingState,
    crib: String,
    pending: String,
    pub family: JointFamily,
    pub origin: ReturnOrigin,
}
impl ReciprocalCheckpoint {
    pub fn capture(
        stream: &ObservedStream,
        family: &JointFamily,
        origin: ReturnOrigin,
        ring: usize,
    ) -> Result<Self, HnnError> {
        Ok(Self {
            native: stream.resident().continuing_state(ring)?,
            crib: stream.crib().unplaced_checkpoint()?,
            pending: stream.pending_checkpoint(),
            family: family.clone(),
            origin,
        })
    }
    pub fn to_text(&self) -> String {
        let parts = [
            self.native.to_text(),
            self.crib.clone(),
            self.pending.clone(),
            self.family.checkpoint(),
            origin_text(&self.origin),
        ];
        let mut s = "reciprocal-continuation-v1\n".to_owned();
        for p in &parts {
            s += &format!("{}\n", p.len());
            s += p;
        }
        s
    }
    pub fn from_text(
        text: &str,
        maximum_bytes: usize,
        material_budget: u64,
        family_bound: JointBound,
    ) -> Result<Self, HnnError> {
        if text.len() > maximum_bytes {
            return Err(refused("the combined reciprocal checkpoint byte bound"));
        }
        let mut rest = text
            .strip_prefix("reciprocal-continuation-v1\n")
            .ok_or_else(|| refused("the combined reciprocal checkpoint version"))?;
        let mut parts = Vec::new();
        for _ in 0..5 {
            let (n, s) = rest
                .split_once('\n')
                .ok_or_else(|| refused("the reciprocal section length"))?;
            let n: usize = n
                .parse()
                .map_err(|_| refused("the reciprocal section length"))?;
            let p = s
                .get(..n)
                .ok_or_else(|| refused("the reciprocal complete section"))?;
            parts.push(p);
            rest = &s[n..];
        }
        if !rest.is_empty() {
            return Err(refused("the complete reciprocal checkpoint end"));
        }
        Ok(Self {
            native: ContinuingState::from_text(parts[0], material_budget)?,
            crib: parts[1].into(),
            pending: parts[2].into(),
            family: JointFamily::from_checkpoint(parts[3], maximum_bytes, family_bound)?,
            origin: parse_origin(parts[4])?,
        })
    }
    pub fn restore(
        &self,
        reference: &Reference,
        field: &Field,
        opening: Constitution,
    ) -> Result<ObservedStream, HnnError> {
        let resident =
            reference.mount_continued(field, &Current::at_rest(field), opening, &self.native)?;
        let next = resident
            .moments
            .values()
            .next()
            .ok_or_else(|| refused("the reciprocal saved source moment"))?
            .cells();
        let crib = ObservedCrib::from_unplaced_checkpoint(
            field,
            &resident.current,
            usize::try_from(next).map_err(|_| HnnError::CountOverflow)?,
            &self.crib,
        )?;
        // Binding through actual testimony rejects a family silently transplanted onto another
        // occurrence/current. Calibration/pairing must still be admitted before any next deposit.
        for (&position, &class) in self.family.positions.iter().zip(&self.family.testimony) {
            crib.addressed_lift(field, &resident.current, position, class)?;
        }
        ObservedStream::restore_checkpoint(resident, crib, &self.pending)
    }
}
