use super::*;
use std::fmt::Write;
fn get<T: std::str::FromStr>(t: &mut std::str::SplitWhitespace<'_>) -> Result<T, HnnError> {
    t.next()
        .and_then(|s| s.parse().ok())
        .ok_or(refuse("complete class material fields"))
}
fn frame(parts: &[String]) -> String {
    let header = parts
        .iter()
        .map(|p| p.len().to_string())
        .collect::<Vec<_>>()
        .join(" ");
    format!("class-input-v1\n{header}\n{}", parts.join(""))
}
fn unframe(text: &str) -> Result<Vec<&str>, HnnError> {
    if text.len() > 8 * 1024 * 1024 {
        return Err(refuse("bounded class input checkpoint"));
    }
    let mut l = text.splitn(3, '\n');
    if l.next() != Some("class-input-v1") {
        return Err(refuse("class input version"));
    }
    let sizes = l
        .next()
        .ok_or(refuse("class checkpoint sizes"))?
        .split_whitespace()
        .map(str::parse::<usize>)
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| refuse("class checkpoint lengths"))?;
    if sizes.len() != 4 {
        return Err(refuse("four class checkpoint parts"));
    }
    let mut rest = l.next().ok_or(refuse("class checkpoint payload"))?;
    let mut out = Vec::new();
    for n in sizes {
        if !rest.is_char_boundary(n) {
            return Err(refuse("class checkpoint byte boundary"));
        }
        out.push(&rest[..n]);
        rest = &rest[n..];
    }
    if !rest.is_empty() {
        return Err(refuse("no trailing class checkpoint bytes"));
    }
    Ok(out)
}
impl ClassInput {
    fn identity(&self) -> String {
        format!(
            "class-coordinate-port-v1|{}|{}|{:?}|{:?}|{}",
            self.ring,
            self.context_coordinate,
            self.units,
            self.resident.field,
            self.boundary.immutable_identity_text()
        )
    }
    pub fn to_text(&self) -> Result<String, HnnError> {
        let native = self.resident.continuing_state(self.ring)?.to_text();
        let crib = self.crib.unplaced_checkpoint()?;
        let mut body = format!(
            "{} {} {} {} {} {} {} {} {} {} {} {} {} {} ",
            self.bounds.branches,
            self.bounds.pending,
            self.bounds.precision_bits,
            self.bounds.rational_bits,
            self.bounds.max_features,
            self.bounds.max_scalar_work,
            self.accepted,
            self.work.actual_arrivals,
            self.work.material_publications,
            self.work.successful_fit_proposals,
            self.history.len(),
            self.branches.len(),
            self.pending.len(),
            0
        );
        for c in &self.history {
            write!(body, "{c} ").expect("string");
        }
        for b in &self.branches {
            write!(body, "{} {}\n", b.id, b.material.checkpoint_text()).expect("string");
        }
        for p in self.pending.values() {
            write!(
                body,
                "{} {} {} {} {} {} ",
                p.address, p.commit, p.previous, p.current, p.context, p.actual
            )
            .expect("string");
            for l in &p.lift {
                write!(body, "{l} ").expect("string");
            }
            for z in &p.feature {
                write!(body, "{} {} ", z[0], z[1]).expect("string");
            }
        }
        Ok(frame(&[self.identity(), native, crib, body]))
    }
    #[allow(clippy::too_many_arguments)]
    pub fn restored(
        reference: &Reference,
        field: &Field,
        opening: Constitution,
        pairing: PairingDeclaration,
        boundary: PairedObservation,
        ring: usize,
        context_coordinate: usize,
        units: String,
        text: &str,
    ) -> Result<Self, HnnError> {
        let parts = unframe(text)?;
        let expected = format!(
            "class-coordinate-port-v1|{ring}|{context_coordinate}|{units:?}|{field:?}|{}",
            boundary.immutable_identity_text()
        );
        if parts[0] != expected {
            return Err(refuse("same immutable class boundary/field/context/units"));
        }
        let state =
            crate::hnn::constitution::ContinuingState::from_text(parts[1], opening.budget())?;
        let resident =
            reference.mount_continued(field, &Current::at_rest(field), opening, &state)?;
        resident.admit_exact_current()?;
        boundary.check_material(&resident.constitution)?;
        let n = field.alphabet();
        let f = 6 * n + 1;
        let mut t = parts[3].split_whitespace();
        let bounds = ContextualBounds {
            branches: get(&mut t)?,
            pending: get(&mut t)?,
            precision_bits: get(&mut t)?,
            rational_bits: get(&mut t)?,
            max_features: get(&mut t)?,
            max_scalar_work: get(&mut t)?,
        };
        bounds.admit()?;
        let accepted = get(&mut t)?;
        let work = ClassInputWork {
            actual_arrivals: get(&mut t)?,
            material_publications: get(&mut t)?,
            successful_fit_proposals: get(&mut t)?,
        };
        let nh: usize = get(&mut t)?;
        let nb: usize = get(&mut t)?;
        let np: usize = get(&mut t)?;
        if get::<u8>(&mut t)? != 0
            || nb == 0
            || nb > bounds.branches
            || nh > 2
            || np > bounds.pending
            || f > bounds.max_features
            || (2 * f).pow(3) as u64 * nb as u64 > bounds.max_scalar_work
            || resident.moments.len() != 1
            || resident.moments.values().next().map(SourceMoment::cells) != Some(accepted)
            || !field.is_source(ring)
            || context_coordinate >= field.ring(ring).width()
            || units.is_empty()
            || work.actual_arrivals != accepted
            || nh as u64 != accepted.min(2)
        {
            return Err(refuse("class checkpoint finite native/empirical counts"));
        }
        let history = (0..nh)
            .map(|_| get(&mut t))
            .collect::<Result<Vec<usize>, _>>()?;
        let crib = ObservedCrib::from_unplaced_checkpoint(
            field,
            &resident.current,
            usize::try_from(accepted).map_err(|_| HnnError::CountOverflow)?,
            parts[2],
        )?;
        let tail: Vec<_> = crib
            .entries()
            .iter()
            .rev()
            .take(nh)
            .map(|c| c.class)
            .rev()
            .collect();
        // The closing crib intentionally clears at an actual aeon closure; the
        // retained last-two testimony may straddle it. Cross-check every still
        // available suffix without fabricating missing earlier crib entries.
        if !history.ends_with(&tail) || history.iter().any(|&c| c >= n) {
            return Err(refuse(
                "actual last-two class testimony equals the bounded native crib",
            ));
        }
        let mut branches = Vec::new();
        let mut ids = std::collections::BTreeSet::new();
        for _ in 0..nb {
            let id = get(&mut t)?;
            if !ids.insert(id) {
                return Err(refuse("distinct class support ids"));
            }
            let len = 5 + 2 * f * f + 4 * n * f;
            let tokens = (0..len)
                .map(|_| t.next().ok_or(refuse("complete class material")))
                .collect::<Result<Vec<_>, _>>()?
                .join(" ");
            let material = EmpiricalMaterial::restored_text(&tokens, f, n, &bounds)?;
            if material
                .normal()
                .iter()
                .chain(material.cross())
                .chain(material.applied())
                .flatten()
                .any(|z| !z[1].is_zero())
                || material.observations() != work.material_publications
            {
                return Err(refuse("real class material and once-only formation count"));
            }
            branches.push(ClassInputBranch { id, material });
        }
        let mut pending = BTreeMap::new();
        for _ in 0..np {
            let address = get(&mut t)?;
            let commit = get(&mut t)?;
            let previous = get(&mut t)?;
            let current = get(&mut t)?;
            let context = get(&mut t)?;
            let actual = get(&mut t)?;
            let lift = (0..field.rings().len())
                .map(|_| get(&mut t))
                .collect::<Result<Vec<_>, _>>()?;
            Current::at(field, lift.clone())?;
            let saved = (0..f)
                .map(|_| Ok([get(&mut t)?, get(&mut t)?]))
                .collect::<Result<Vec<Complex>, HnnError>>()?;
            bounds.check(saved.iter().flat_map(|z| z.iter()))?;
            if address < 2
                || address >= accepted
                || previous >= n
                || current >= n
                || actual >= n
                || commit > resident.constitution.commit()
                || saved != feature(n, previous, current, &context)
                || pending.contains_key(&address)
            {
                return Err(refuse(
                    "original class return source/frame/actual testimony",
                ));
            }
            pending.insert(
                address,
                ClassInputPending {
                    address,
                    commit,
                    lift,
                    previous,
                    current,
                    context,
                    feature: saved,
                    actual,
                },
            );
        }
        if t.next().is_some()
            || work.material_publications + np as u64 != accepted.saturating_sub(2)
        {
            return Err(refuse("unconsumed class-return accounting"));
        }
        Ok(Self {
            resident,
            crib,
            pairing,
            boundary,
            ring,
            context_coordinate,
            units,
            bounds,
            history,
            accepted,
            branches,
            pending,
            work,
        })
    }
}
