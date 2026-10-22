//! Bounded exterior closing-crib persistence for the unplaced observation chart.
//! The crib is the finite current aeon's closing operand, not learned retention.
//! Placed observations are refused explicitly; this codec never drops their placement.

use super::*;

impl ObservedCrib {
    /// Exact, versioned exterior checkpoint for the unplaced route.
    pub fn unplaced_checkpoint(&self) -> Result<String, HnnError> {
        if self.entries.iter().any(|entry| entry.placement.is_some()) {
            return Err(HnnError::ContinuingState {
                what: "the unplaced crib codec cannot save placed observations",
            });
        }
        let lift = self.opening_lift.as_ref().map_or_else(
            || "-".to_owned(),
            |lift| {
                lift.iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" ")
            },
        );
        let mut out = format!(
            "observed-unplaced-crib-v1\n{} {} {}\n{lift}\n",
            self.opening,
            self.next,
            self.entries.len()
        );
        for entry in &self.entries {
            use std::fmt::Write;
            writeln!(out, "{} {}", entry.position, entry.class).expect("String writing");
        }
        Ok(out)
    }

    /// Reconstruct the finite closing operand and check its endpoint against the saved
    /// native moment/current. The declared crib window bounds allocation before parsing.
    pub fn from_unplaced_checkpoint(
        field: &Field,
        current: &Current,
        expected_next: usize,
        text: &str,
    ) -> Result<Self, HnnError> {
        let bad = || HnnError::ContinuingState {
            what: "the bounded unplaced observed crib",
        };
        let mut lines = text.lines();
        if lines.next() != Some("observed-unplaced-crib-v1") {
            return Err(bad());
        }
        let counters: Vec<_> = lines.next().ok_or_else(bad)?.split_whitespace().collect();
        if counters.len() != 3 {
            return Err(bad());
        }
        let opening: usize = counters[0].parse().map_err(|_| bad())?;
        let next: usize = counters[1].parse().map_err(|_| bad())?;
        let count: usize = counters[2].parse().map_err(|_| bad())?;
        if next != expected_next
            || opening > next
            || count > field.crib().window
            || count != (next - opening).min(field.crib().window)
        {
            return Err(bad());
        }
        let line = lines.next().ok_or_else(bad)?;
        let opening_lift = if line == "-" {
            None
        } else {
            let tokens: Vec<_> = line.split_whitespace().collect();
            if tokens.len() != field.rings().len() {
                return Err(bad());
            }
            Some(
                tokens
                    .into_iter()
                    .map(|value| value.parse::<BigInt>().map_err(|_| bad()))
                    .collect::<Result<Vec<_>, _>>()?,
            )
        };
        if opening_lift.is_some() != (count != 0) {
            return Err(bad());
        }
        let mut entries = Vec::with_capacity(count);
        for position in next - count..next {
            let tokens: Vec<_> = lines.next().ok_or_else(bad)?.split_whitespace().collect();
            if tokens.len() != 2 {
                return Err(bad());
            }
            let held: usize = tokens[0].parse().map_err(|_| bad())?;
            let class: usize = tokens[1].parse().map_err(|_| bad())?;
            if held != position || class >= field.alphabet() {
                return Err(bad());
            }
            entries.push(ObservedCribCell {
                position,
                class,
                placement: None,
            });
        }
        if lines.next().is_some() {
            return Err(bad());
        }
        if let Some(lift) = &opening_lift {
            let start = Current::at(field, lift.clone())?;
            let cells: Vec<_> = entries.iter().map(|entry| (entry.class, None)).collect();
            let placed = OccurrencePlacement::observed_crib(field, &start, &cells)?;
            if placed.arrivals().last().map(Vec::as_slice) != Some(current.lift()) {
                return Err(bad());
            }
        }
        Ok(Self {
            opening,
            next,
            opening_lift,
            entries,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::tests::support::{contact, small_field};

    #[test]
    fn bounded_unplaced_crib_restores_and_rejects_a_changed_endpoint() {
        let field = small_field(&[2, 2], vec![contact(0, 1, 1, 0)], 1);
        let mut current = Current::at_rest(&field);
        let mut crib = ObservedCrib::new(0);
        // Longer than the crib window: its finite opening lift must move with eviction.
        for at in 0..field.crib().window + 3 {
            let class = at % field.alphabet();
            let before = current.clone();
            let mut lift = current.lift().to_vec();
            field.step_class(&mut lift, class, None).unwrap();
            current = Current::at(&field, lift).unwrap();
            crib.push(&field, &before, class, None, field.crib().window)
                .unwrap();
        }
        let text = crib.unplaced_checkpoint().unwrap();
        let restored =
            ObservedCrib::from_unplaced_checkpoint(&field, &current, crib.next, &text).unwrap();
        assert_eq!(restored, crib);
        assert_eq!(restored.unplaced_checkpoint().unwrap(), text);
        assert!(
            ObservedCrib::from_unplaced_checkpoint(
                &field,
                &Current::at_rest(&field),
                crib.next,
                &text
            )
            .is_err()
        );
        assert!(
            ObservedCrib::from_unplaced_checkpoint(&field, &current, crib.next + 1, &text).is_err()
        );
        assert!(
            ObservedCrib::from_unplaced_checkpoint(
                &field,
                &current,
                crib.next,
                &text.replacen("0 19 16", "0 19 17", 1)
            )
            .is_err()
        );
    }

    #[test]
    fn unplaced_crib_codec_refuses_to_drop_an_actual_placement() {
        let field = small_field(&[2, 2], vec![contact(0, 1, 1, 0)], 1);
        let current = Current::at_rest(&field);
        let placement = OccurrencePlacement::at(&field, &current, &[vec![0]]).unwrap();
        let mut crib = ObservedCrib::new(0);
        crib.push(&field, &current, 0, Some(&placement), field.crib().window)
            .unwrap();
        assert!(crib.unplaced_checkpoint().is_err());
        let empty = ObservedCrib::new(0);
        assert_eq!(
            ObservedCrib::from_unplaced_checkpoint(
                &field,
                &current,
                0,
                &empty.unplaced_checkpoint().unwrap()
            )
            .unwrap(),
            empty
        );
    }
}
