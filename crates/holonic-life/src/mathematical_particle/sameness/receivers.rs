use super::*;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReceiverFaceRelation {
    pub(super) receiver_occurrence: String,
    pub(super) left_index: usize,
    pub(super) right_index: usize,
    pub(super) left: ExactValue,
    pub(super) right: ExactValue,
    pub(super) ordering: ExactOrdering,
    pub(super) witness: RelationWitness,
}

impl ReceiverFaceRelation {
    pub fn from_return(
        receiver: &ValueReceiverReturn,
        left_index: usize,
        right_index: usize,
    ) -> Result<Self, MathematicalParticleError> {
        let left = receiver.values().get(left_index).cloned().ok_or(
            MathematicalParticleError::MalformedRelation("receiver-face"),
        )?;
        let right = receiver.values().get(right_index).cloned().ok_or(
            MathematicalParticleError::MalformedRelation("receiver-face"),
        )?;
        let ordering = left.compare(&right);
        let witness = match ordering {
            ExactOrdering::Equal => {
                RelationWitness::established(BTreeSet::from([receiver.occurrence().to_owned()]))
            }
            ExactOrdering::Open => RelationWitness::open(
                "the exact receiver could not order the two faces",
                BTreeSet::from([receiver.occurrence().to_owned()]),
            ),
            ExactOrdering::Less | ExactOrdering::Greater => {
                RelationWitness::separated(receiver.occurrence())
            }
        };
        Ok(Self {
            receiver_occurrence: receiver.occurrence().to_owned(),
            left_index,
            right_index,
            left,
            right,
            ordering,
            witness,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassificationReceiverReturn {
    occurrence: String,
    classes: BTreeMap<String, Vec<u8>>,
}

impl ClassificationReceiverReturn {
    pub fn found(
        occurrence: impl Into<String>,
        classes: BTreeMap<String, Vec<u8>>,
    ) -> Result<Self, MathematicalParticleError> {
        let occurrence = occurrence.into();
        if occurrence.is_empty() || classes.is_empty() || classes.values().any(Vec::is_empty) {
            return Err(MathematicalParticleError::MalformedRelation(
                "classification",
            ));
        }
        Ok(Self {
            occurrence,
            classes,
        })
    }

    pub fn occurrence(&self) -> &str {
        &self.occurrence
    }
    pub fn classes(&self) -> &BTreeMap<String, Vec<u8>> {
        &self.classes
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SimilarityReceiverReturn {
    occurrence: String,
    frame: String,
    /// Subject -> characteristic -> exact receiver bytes.
    characteristics: BTreeMap<String, BTreeMap<String, Vec<u8>>>,
}

impl SimilarityReceiverReturn {
    pub fn found(
        occurrence: impl Into<String>,
        frame: impl Into<String>,
        characteristics: BTreeMap<String, BTreeMap<String, Vec<u8>>>,
    ) -> Result<Self, MathematicalParticleError> {
        let occurrence = occurrence.into();
        let frame = frame.into();
        if occurrence.is_empty()
            || frame.is_empty()
            || characteristics.is_empty()
            || characteristics.values().any(|family| family.is_empty())
        {
            return Err(MathematicalParticleError::MalformedRelation(
                "characteristic-similarity",
            ));
        }
        Ok(Self {
            occurrence,
            frame,
            characteristics,
        })
    }

    pub fn occurrence(&self) -> &str {
        &self.occurrence
    }

    pub fn frame(&self) -> &str {
        &self.frame
    }

    pub fn characteristics(&self) -> &BTreeMap<String, BTreeMap<String, Vec<u8>>> {
        &self.characteristics
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ClassificationRelation {
    pub(super) classifier_occurrence: String,
    pub(super) left_subject: String,
    pub(super) right_subject: String,
    pub(super) left_class: Vec<u8>,
    pub(super) right_class: Vec<u8>,
    pub(super) witness: RelationWitness,
}

impl ClassificationRelation {
    pub fn from_return(
        returned: &ClassificationReceiverReturn,
        left: impl Into<String>,
        right: impl Into<String>,
    ) -> Result<Self, MathematicalParticleError> {
        let left_subject = left.into();
        let right_subject = right.into();
        let left_class = returned.classes.get(&left_subject).cloned().ok_or(
            MathematicalParticleError::MalformedRelation("classification"),
        )?;
        let right_class = returned.classes.get(&right_subject).cloned().ok_or(
            MathematicalParticleError::MalformedRelation("classification"),
        )?;
        let witness = if left_class == right_class {
            RelationWitness::established(BTreeSet::from([returned.occurrence.clone()]))
        } else {
            RelationWitness::separated(&returned.occurrence)
        };
        Ok(Self {
            classifier_occurrence: returned.occurrence.clone(),
            left_subject,
            right_subject,
            left_class,
            right_class,
            witness,
        })
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SimilarityRelation {
    pub(super) receiver_occurrence: String,
    pub(super) frame: String,
    pub(super) left_subject: String,
    pub(super) right_subject: String,
    /// Every declared characteristic stays individually inspectable.
    pub(super) characteristics: BTreeMap<String, (Vec<u8>, Vec<u8>)>,
    pub(super) witness: RelationWitness,
}

impl SimilarityRelation {
    pub fn from_return(
        returned: &SimilarityReceiverReturn,
        left: impl Into<String>,
        right: impl Into<String>,
    ) -> Result<Self, MathematicalParticleError> {
        let left_subject = left.into();
        let right_subject = right.into();
        let left_family = returned.characteristics.get(&left_subject).ok_or(
            MathematicalParticleError::MalformedRelation("characteristic-similarity"),
        )?;
        let right_family = returned.characteristics.get(&right_subject).ok_or(
            MathematicalParticleError::MalformedRelation("characteristic-similarity"),
        )?;
        if left_family.keys().collect::<BTreeSet<_>>()
            != right_family.keys().collect::<BTreeSet<_>>()
        {
            return Err(MathematicalParticleError::MalformedRelation(
                "characteristic-similarity",
            ));
        }
        let characteristics = left_family
            .iter()
            .map(|(name, left)| (name.clone(), (left.clone(), right_family[name].clone())))
            .collect::<BTreeMap<_, _>>();
        let equal = characteristics.values().all(|(left, right)| left == right);
        let witness = if equal {
            RelationWitness::established(BTreeSet::from([returned.occurrence.clone()]))
        } else {
            RelationWitness::separated(&returned.occurrence)
        };
        Ok(Self {
            receiver_occurrence: returned.occurrence.clone(),
            frame: returned.frame.clone(),
            left_subject,
            right_subject,
            characteristics,
            witness,
        })
    }
}
