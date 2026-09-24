//! **The retained fibre and its separator: what a restriction's defect keeps.**
//!
//! [definition] A restriction `π : X → T` merges the sources of one fibre `π⁻¹(t)`
//! (`Foundation/Holon.lean::Holon.PreimageFibre`); a reading `ρ` descends through `π` exactly when
//! it is constant on every fibre (`Holon/Restriction.lean::descent_total`). When it does not, the
//! typed defect ([`crate::restriction::Descent::Defect`]) retains two things and nothing else is
//! owed: the **fibre** — every source `π` merges, no representative selected — and the
//! **separator** — a merged pair with the witness that separates it and the two readings
//! (`Holon/Restriction.lean::Descent.defect`). A retained separated pair refutes every coarse
//! reading (`Holon/Restriction.lean::descent_defect_refutes_factoring`).
//!
//! ```text
//! PreimageFibre   (t, π⁻¹(t))                          a class fibre of a discrete quotient
//! AffineFibre     particular + span(radical) = A⁻¹(y)  a linear preimage (Holon/Restriction.lean::affineFibre_mem)
//! Separation      (x, y, witness, ρ x, ρ y), π x = π y, ρ x ≠ ρ y
//! ShortestSeparator  a Separation whose witness is a shortest input word and its separating receiver
//! FibreDefect     every retained fibre and every separator of one failed descent
//! ```
//!
//! [definition] **One object, many wires.** The reconstruction and preimage fibres of the tree
//! are instances of these types (plan phase 10 disposition). Where an instance's wire already
//! names its two fields differently, its [`FieldNames`] marker carries those names, so the alias
//! serializes, deserializes and debug-prints byte-for-byte as the struct it replaced
//! ([`crate::fibre_field_names`] declares a marker).

use std::fmt;
use std::marker::PhantomData;

use num_traits::Zero;
use crate::geometry::Rat;
use serde::de::{self, DeserializeSeed, IgnoredAny, MapAccess, SeqAccess, Visitor};
use serde::ser::SerializeStruct;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::exact_linear::{ExactLinearError, ExactRatMatrix};

/// [definition] **The wire names of a two-field fibre.** An instance keeps the struct name, the
/// two field names and the unknown-field policy of the wire it replaced.
pub trait FieldNames {
    /// The struct name serde and `Debug` report.
    const NAME: &'static str;
    /// `[first, second]` field names.
    const FIELDS: &'static [&'static str];
    /// `#[serde(deny_unknown_fields)]`.
    const DENY_UNKNOWN: bool;
}

/// Declare a [`FieldNames`] marker: `fibre_field_names!(pub Marker = "Name", "first", "second", deny)`
/// (or `allow` for a wire that ignores unknown fields).
#[macro_export]
macro_rules! fibre_field_names {
    ($vis:vis $marker:ident = $name:literal, $first:literal, $second:literal, deny) => {
        $crate::fibre_field_names!(@marker $vis $marker = $name, $first, $second, true);
    };
    ($vis:vis $marker:ident = $name:literal, $first:literal, $second:literal, allow) => {
        $crate::fibre_field_names!(@marker $vis $marker = $name, $first, $second, false);
    };
    (@marker $vis:vis $marker:ident = $name:literal, $first:literal, $second:literal, $deny:expr) => {
        #[doc = concat!("Wire names of `", $name, "` (`", $first, "`, `", $second, "`).")]
        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
        $vis struct $marker;
        impl $crate::restriction::fibre::FieldNames for $marker {
            const NAME: &'static str = $name;
            const FIELDS: &'static [&'static str] = &[$first, $second];
            const DENY_UNKNOWN: bool = $deny;
        }
    };
}

fibre_field_names!(pub NativeMembers = "PreimageFibre", "native", "members", deny);
fibre_field_names!(pub ParticularRadical = "AffineFibre", "particular", "radical", deny);

fn serialize_pair<N: FieldNames, S: Serializer, A: Serialize, B: Serialize>(
    serializer: S,
    first: &A,
    second: &B,
) -> Result<S::Ok, S::Error> {
    let mut state = serializer.serialize_struct(N::NAME, 2)?;
    state.serialize_field(N::FIELDS[0], first)?;
    state.serialize_field(N::FIELDS[1], second)?;
    state.end()
}

enum PairKey {
    First,
    Second,
    Other,
}

struct PairKeySeed<N>(PhantomData<fn() -> N>);

impl<'de, N: FieldNames> DeserializeSeed<'de> for PairKeySeed<N> {
    type Value = PairKey;

    fn deserialize<D: Deserializer<'de>>(self, deserializer: D) -> Result<PairKey, D::Error> {
        deserializer.deserialize_identifier(self)
    }
}

impl<'de, N: FieldNames> Visitor<'de> for PairKeySeed<N> {
    type Value = PairKey;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("field identifier")
    }

    fn visit_u64<E: de::Error>(self, index: u64) -> Result<PairKey, E> {
        match index {
            0 => Ok(PairKey::First),
            1 => Ok(PairKey::Second),
            _ => Ok(PairKey::Other),
        }
    }

    fn visit_str<E: de::Error>(self, key: &str) -> Result<PairKey, E> {
        if key == N::FIELDS[0] {
            Ok(PairKey::First)
        } else if key == N::FIELDS[1] {
            Ok(PairKey::Second)
        } else if N::DENY_UNKNOWN {
            Err(E::unknown_field(key, N::FIELDS))
        } else {
            Ok(PairKey::Other)
        }
    }

    fn visit_bytes<E: de::Error>(self, key: &[u8]) -> Result<PairKey, E> {
        match std::str::from_utf8(key) {
            Ok(key) => self.visit_str(key),
            Err(_) if N::DENY_UNKNOWN => {
                Err(E::unknown_field(&String::from_utf8_lossy(key), N::FIELDS))
            }
            Err(_) => Ok(PairKey::Other),
        }
    }
}

struct PairVisitor<N, A, B>(PhantomData<fn() -> (N, A, B)>);

impl<'de, N: FieldNames, A: Deserialize<'de>, B: Deserialize<'de>> Visitor<'de>
    for PairVisitor<N, A, B>
{
    type Value = (A, B);

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "struct {}", N::NAME)
    }

    fn visit_seq<S: SeqAccess<'de>>(self, mut seq: S) -> Result<(A, B), S::Error> {
        let first = seq
            .next_element()?
            .ok_or_else(|| de::Error::invalid_length(0, &self))?;
        let second = seq
            .next_element()?
            .ok_or_else(|| de::Error::invalid_length(1, &self))?;
        Ok((first, second))
    }

    fn visit_map<M: MapAccess<'de>>(self, mut map: M) -> Result<(A, B), M::Error> {
        let mut first = None;
        let mut second = None;
        while let Some(key) = map.next_key_seed(PairKeySeed::<N>(PhantomData))? {
            match key {
                PairKey::First => {
                    if first.is_some() {
                        return Err(de::Error::duplicate_field(N::FIELDS[0]));
                    }
                    first = Some(map.next_value()?);
                }
                PairKey::Second => {
                    if second.is_some() {
                        return Err(de::Error::duplicate_field(N::FIELDS[1]));
                    }
                    second = Some(map.next_value()?);
                }
                PairKey::Other => {
                    map.next_value::<IgnoredAny>()?;
                }
            }
        }
        Ok((
            first.ok_or_else(|| de::Error::missing_field(N::FIELDS[0]))?,
            second.ok_or_else(|| de::Error::missing_field(N::FIELDS[1]))?,
        ))
    }
}

fn deserialize_pair<'de, N: FieldNames, D: Deserializer<'de>, A, B>(
    deserializer: D,
) -> Result<(A, B), D::Error>
where
    A: Deserialize<'de>,
    B: Deserialize<'de>,
{
    deserializer.deserialize_struct(N::NAME, N::FIELDS, PairVisitor::<N, A, B>(PhantomData))
}

/// [definition] **One fibre `π⁻¹(t)` of a discrete quotient**, retained whole: the coarse (native)
/// image and every member `π` sends there, no representative selected
/// (`Foundation/Holon.lean::Holon.PreimageFibre`). `C` is the member container the instance
/// keeps (an ordered `Vec` or a `BTreeSet`).
pub struct PreimageFibre<T, C, N = NativeMembers> {
    /// The coarse image `t`.
    pub native: T,
    /// `π⁻¹(t)`.
    pub members: C,
    names: PhantomData<fn() -> N>,
}

impl<T, C, N> PreimageFibre<T, C, N> {
    pub fn new(native: T, members: C) -> Self {
        Self {
            native,
            members,
            names: PhantomData,
        }
    }

    /// The same fibre under another wire's names.
    pub fn renamed<M>(self) -> PreimageFibre<T, C, M> {
        PreimageFibre::new(self.native, self.members)
    }

    /// Read the image and the members through charts (e.g. an index population into its items).
    pub fn map<U, D, M>(
        self,
        image: impl FnOnce(T) -> U,
        members: impl FnOnce(C) -> D,
    ) -> PreimageFibre<U, D, M> {
        PreimageFibre::new(image(self.native), members(self.members))
    }
}

impl<T: Clone, C: Clone, N> Clone for PreimageFibre<T, C, N> {
    fn clone(&self) -> Self {
        Self::new(self.native.clone(), self.members.clone())
    }
}

impl<T: PartialEq, C: PartialEq, N> PartialEq for PreimageFibre<T, C, N> {
    fn eq(&self, other: &Self) -> bool {
        self.native == other.native && self.members == other.members
    }
}

impl<T: Eq, C: Eq, N> Eq for PreimageFibre<T, C, N> {}

impl<T: std::hash::Hash, C: std::hash::Hash, N> std::hash::Hash for PreimageFibre<T, C, N> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.native.hash(state);
        self.members.hash(state);
    }
}

impl<T: fmt::Debug, C: fmt::Debug, N: FieldNames> fmt::Debug for PreimageFibre<T, C, N> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct(N::NAME)
            .field(N::FIELDS[0], &self.native)
            .field(N::FIELDS[1], &self.members)
            .finish()
    }
}

impl<T: Serialize, C: Serialize, N: FieldNames> Serialize for PreimageFibre<T, C, N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serialize_pair::<N, _, _, _>(serializer, &self.native, &self.members)
    }
}

impl<'de, T: Deserialize<'de>, C: Deserialize<'de>, N: FieldNames> Deserialize<'de>
    for PreimageFibre<T, C, N>
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let (native, members) = deserialize_pair::<N, _, _, _>(deserializer)?;
        Ok(Self::new(native, members))
    }
}

/// Why a declared affine fibre is not the preimage it claims to be.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum AffineFibreDefect {
    /// The particular point, a radical direction or the target has the wrong length.
    #[error("the fibre's coordinates do not match a {rows}×{columns} operator")]
    Shape { rows: usize, columns: usize },
    /// `A · particular ≠ target`.
    #[error("the particular point does not reach the target")]
    ParticularMisses,
    /// A radical direction is zero, repeated, or not in `ker A`.
    #[error("radical direction {index} is zero, repeated or outside the kernel")]
    Radical { index: usize },
}

/// [definition] **The affine preimage `A⁻¹(y) = particular + span(radical)`**, retained instead of
/// choosing the particular point as if it were an inverse (`Holon/Restriction.lean::affineFibre_mem`:
/// every point of the span reaches the target). [`ExactRatMatrix::preimage_fibre`] returns one.
pub struct AffineFibre<N = ParticularRadical> {
    /// One point with `A · particular = y`.
    pub particular: Vec<Rat>,
    /// Directions spanning the retained part of `ker A`.
    pub radical: Vec<Vec<Rat>>,
    names: PhantomData<fn() -> N>,
}

impl<N> AffineFibre<N> {
    pub fn new(particular: Vec<Rat>, radical: Vec<Vec<Rat>>) -> Self {
        Self {
            particular,
            radical,
            names: PhantomData,
        }
    }

    /// The `(particular, kernel)` pair [`ExactRatMatrix::preimage_fibre`] returns.
    pub fn from_preimage((particular, radical): (Vec<Rat>, Vec<Vec<Rat>>)) -> Self {
        Self::new(particular, radical)
    }

    /// The same fibre under another wire's names.
    pub fn renamed<M>(self) -> AffineFibre<M> {
        AffineFibre::new(self.particular, self.radical)
    }

    /// The fibre's retained dimension.
    pub fn dimension(&self) -> usize {
        self.radical.len()
    }

    /// `particular + Σ cᵢ radicalᵢ`, or `None` when the coefficient count or a length disagrees.
    pub fn point(&self, coefficients: &[Rat]) -> Option<Vec<Rat>> {
        if coefficients.len() != self.radical.len() {
            return None;
        }
        let mut point = self.particular.clone();
        for (coefficient, direction) in coefficients.iter().zip(&self.radical) {
            if direction.len() != point.len() {
                return None;
            }
            for (coordinate, entry) in point.iter_mut().zip(direction) {
                *coordinate += coefficient * entry;
            }
        }
        Some(point)
    }

    /// **Is this the affine preimage of `target` under `operator`?** `A · particular = target`,
    /// and every radical direction is nonzero, distinct and in `ker A`. The span then lies in
    /// the fibre (`Holon/Restriction.lean::affineFibre_mem`).
    pub fn check_preimage(
        &self,
        operator: &ExactRatMatrix,
        target: &[Rat],
    ) -> Result<(), AffineFibreDefect> {
        let (rows, columns) = (operator.rows(), operator.columns());
        let shape = AffineFibreDefect::Shape { rows, columns };
        if self.particular.len() != columns || target.len() != rows {
            return Err(shape);
        }
        let reached = operator
            .apply(&self.particular)
            .map_err(|_: ExactLinearError| shape.clone())?;
        if reached != target {
            return Err(AffineFibreDefect::ParticularMisses);
        }
        for (index, direction) in self.radical.iter().enumerate() {
            let repeated = self.radical[..index].contains(direction);
            let image = if direction.len() == columns {
                operator.apply(direction).ok()
            } else {
                None
            };
            let in_kernel = image.is_some_and(|image| image.iter().all(Zero::is_zero));
            if repeated || direction.iter().all(Zero::is_zero) || !in_kernel {
                return Err(AffineFibreDefect::Radical { index });
            }
        }
        Ok(())
    }
}

impl<N> Clone for AffineFibre<N> {
    fn clone(&self) -> Self {
        Self::new(self.particular.clone(), self.radical.clone())
    }
}

impl<N> PartialEq for AffineFibre<N> {
    fn eq(&self, other: &Self) -> bool {
        self.particular == other.particular && self.radical == other.radical
    }
}

impl<N> Eq for AffineFibre<N> {}

impl<N: FieldNames> fmt::Debug for AffineFibre<N> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct(N::NAME)
            .field(N::FIELDS[0], &self.particular)
            .field(N::FIELDS[1], &self.radical)
            .finish()
    }
}

impl<N: FieldNames> Serialize for AffineFibre<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serialize_pair::<N, _, _, _>(serializer, &self.particular, &self.radical)
    }
}

impl<'de, N: FieldNames> Deserialize<'de> for AffineFibre<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let (particular, radical) = deserialize_pair::<N, _, _, _>(deserializer)?;
        Ok(Self::new(particular, radical))
    }
}

impl ExactRatMatrix {
    /// [`Self::preimage_fibre`] as the core [`AffineFibre`].
    pub fn affine_fibre<N>(
        &self,
        target: &[Rat],
    ) -> Result<Option<AffineFibre<N>>, ExactLinearError> {
        Ok(self.preimage_fibre(target)?.map(AffineFibre::from_preimage))
    }
}

/// [definition] **A separated merged pair** — the Lean defect `Descent.defect x y merged separated`
/// (`Holon/Restriction.lean::Descent`): two members of one fibre, the witness that separates them
/// (the residuals, a word and receiver, a coordinate) and the two readings, which differ.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Separation<M, W, V> {
    left: M,
    right: M,
    witness: W,
    readings: (V, V),
}

impl<M, W, V> Separation<M, W, V> {
    pub fn new(left: M, right: M, witness: W, readings: (V, V)) -> Self {
        Self {
            left,
            right,
            witness,
            readings,
        }
    }

    pub fn left(&self) -> &M {
        &self.left
    }

    pub fn right(&self) -> &M {
        &self.right
    }

    /// The two members, `(left, right)`.
    pub fn pair(&self) -> (M, M)
    where
        M: Clone,
    {
        (self.left.clone(), self.right.clone())
    }

    /// What separates them.
    pub fn witness(&self) -> &W {
        &self.witness
    }

    /// `(ρ left, ρ right)`.
    pub fn readings(&self) -> &(V, V) {
        &self.readings
    }
}

impl<M, R, V> Separation<M, (R, R), V> {
    /// A factor break's witness: `(π.residual(x_left), π.residual(x_right))`, which differ
    /// (`Foundation/ContinuingTower.lean::Transition.residual_separates`).
    pub fn residuals(&self) -> &(R, R) {
        &self.witness
    }
}

/// [definition] **A shortest separator**: a pair one quotient merged that later conduct separates,
/// with the shortest input word after which a receiver sees the difference and what that receiver
/// returned (`Foundation/CausalRelevance.lean::futureHistory_quotientNe_returns_separator`). A
/// terminus — one continues and the other does not — is itself a distinction. The field and serde
/// struct names are the receiver-exact compression's collapsed-pair wire.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename = "CollapsedPair")]
pub struct ShortestSeparator<M, I, R, O> {
    pub left: M,
    pub right: M,
    /// The shortest word; never empty (an empty word is the one-shot reading, which merged them).
    pub distinguishing_word: Vec<I>,
    /// The receiver that finally sees it, and what the two returned.
    pub witness: Option<(R, O, O)>,
    /// True when the word separates them by a terminus rather than by two observations.
    pub separated_by_terminus: bool,
}

impl<M, I, R, O> ShortestSeparator<M, I, R, O> {
    /// The separating receiver, when one returned.
    pub fn receiver(&self) -> Option<&R> {
        self.witness.as_ref().map(|(receiver, _, _)| receiver)
    }

    /// What the left member returned to the separating receiver.
    pub fn left_observation(&self) -> Option<&O> {
        self.witness.as_ref().map(|(_, left, _)| left)
    }

    /// What the right member returned to the separating receiver.
    pub fn right_observation(&self) -> Option<&O> {
        self.witness.as_ref().map(|(_, _, right)| right)
    }

    /// Read members, word letters, receiver and observations through charts (a naming chart, an
    /// index population).
    pub fn map<M2, I2, R2, O2>(
        self,
        mut member: impl FnMut(M) -> M2,
        letter: impl FnMut(I) -> I2,
        receiver: impl FnOnce(R) -> R2,
        mut observation: impl FnMut(O) -> O2,
    ) -> ShortestSeparator<M2, I2, R2, O2> {
        ShortestSeparator {
            left: member(self.left),
            right: member(self.right),
            distinguishing_word: self.distinguishing_word.into_iter().map(letter).collect(),
            witness: self
                .witness
                .map(|(r, left, right)| (receiver(r), observation(left), observation(right))),
            separated_by_terminus: self.separated_by_terminus,
        }
    }

    /// The core separation: witness `(word, receiver)`, readings the two observations (absent on
    /// a terminus).
    pub fn separation(&self) -> Separation<M, (Vec<I>, Option<R>), Option<O>>
    where
        M: Clone,
        I: Clone,
        R: Clone,
        O: Clone,
    {
        Separation::new(
            self.left.clone(),
            self.right.clone(),
            (self.distinguishing_word.clone(), self.receiver().cloned()),
            (
                self.left_observation().cloned(),
                self.right_observation().cloned(),
            ),
        )
    }
}

/// [definition] **The typed defect of a failed descent retains its fibres and its separators**:
/// every fibre the restriction merges and every merged pair a reading separates. Nothing further
/// is owed to reconstruct what the restriction hid.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FibreDefect<F, S> {
    fibres: Vec<F>,
    separators: Vec<S>,
}

impl<F, S> FibreDefect<F, S> {
    pub fn new(fibres: Vec<F>, separators: Vec<S>) -> Self {
        Self { fibres, separators }
    }

    /// The retained fibres.
    pub fn fibres(&self) -> &[F] {
        &self.fibres
    }

    /// The separators, in the owner's declared order.
    pub fn separators(&self) -> &[S] {
        &self.separators
    }

    /// The first separator (the one a first-defect scan meets); `None` only for a defect built
    /// without one.
    pub fn first(&self) -> Option<&S> {
        self.separators.first()
    }

    pub fn into_parts(self) -> (Vec<F>, Vec<S>) {
        (self.fibres, self.separators)
    }
}

impl<T, S> FibreDefect<PreimageFibre<T, Vec<usize>>, S> {
    /// How many declared pairs the restriction merges: `Σ C(|fibre|, 2)` over the retained fibres.
    pub fn merged_pairs(&self) -> usize {
        self.fibres
            .iter()
            .map(|fibre| fibre.members.len() * fibre.members.len().saturating_sub(1) / 2)
            .sum()
    }

    /// The retained fibre containing a declared source position.
    pub fn fibre_of(&self, index: usize) -> Option<&PreimageFibre<T, Vec<usize>>> {
        self.fibres
            .iter()
            .find(|fibre| fibre.members.contains(&index))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64) -> Rat {
        Rat::from_integer(n.into())
    }

    #[test]
    fn the_affine_fibre_is_the_preimage_and_every_span_point_reaches_the_target() {
        // A = [1 1 0; 0 0 1], y = (2, 3): fibre (2,0,3) + span((-1,1,0)).
        let operator =
            ExactRatMatrix::new(vec![vec![q(1), q(1), q(0)], vec![q(0), q(0), q(1)]]).unwrap();
        let target = vec![q(2), q(3)];
        let fibre: AffineFibre = operator.affine_fibre(&target).unwrap().unwrap();
        assert_eq!(fibre.dimension(), 1);
        fibre.check_preimage(&operator, &target).unwrap();
        for c in -2..=2 {
            let point = fibre.point(&[q(c)]).unwrap();
            assert_eq!(operator.apply(&point).unwrap(), target);
        }
        let mut wrong = fibre.clone();
        wrong.radical.push(vec![q(1), q(0), q(0)]);
        assert_eq!(
            wrong.check_preimage(&operator, &target),
            Err(AffineFibreDefect::Radical { index: 1 })
        );
        let mut repeated = fibre.clone();
        repeated.radical.push(repeated.radical[0].clone());
        assert_eq!(
            repeated.check_preimage(&operator, &target),
            Err(AffineFibreDefect::Radical { index: 1 })
        );
        assert_eq!(
            fibre.check_preimage(&operator, &[q(2), q(4)]),
            Err(AffineFibreDefect::ParticularMisses)
        );
        assert!(
            operator
                .affine_fibre::<ParticularRadical>(&target)
                .unwrap()
                .is_some()
        );
    }

    #[test]
    fn a_shortest_separator_reads_as_a_separation() {
        let separator: ShortestSeparator<u8, char, &str, u32> = ShortestSeparator {
            left: 1,
            right: 2,
            distinguishing_word: vec!['a', 'b'],
            witness: Some(("r", 10, 11)),
            separated_by_terminus: false,
        };
        let separation = separator.separation();
        assert_eq!(separation.pair(), (1, 2));
        assert_eq!(separation.witness(), &(vec!['a', 'b'], Some("r")));
        assert_eq!(separation.readings(), &(Some(10), Some(11)));
        let named = separator.clone().map(
            |m| m.to_string(),
            |c| c.to_string(),
            |r| Some(r.to_owned()),
            |o| Some(o.to_string()),
        );
        assert_eq!(named.receiver(), Some(&Some("r".to_owned())));
        assert_eq!(named.left_observation(), Some(&Some("10".to_owned())));
    }
}
