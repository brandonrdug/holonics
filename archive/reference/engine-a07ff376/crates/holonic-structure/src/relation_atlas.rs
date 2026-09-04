use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;
use serde::{
    Deserialize, Deserializer, Serialize, Serializer,
    de::{MapAccess, Visitor},
    ser::SerializeMap,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelationAtlasError {
    Extent,
    InvalidSpan,
    Reservation,
}

impl fmt::Display for RelationAtlasError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Extent => formatter.write_str("relation atlas extent is invalid"),
            Self::InvalidSpan => formatter.write_str("relation span is outside its atlas"),
            Self::Reservation => formatter.write_str("relation atlas could not reserve storage"),
        }
    }
}

impl core::error::Error for RelationAtlasError {}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Relation<K, V> {
    key: K,
    value: V,
}

/// One mutable receiver-local relation family used while a morphology is being conditioned.
///
/// Relations remain sorted and unique by key. This owner is intentionally local: it does not
/// imply a global vocabulary, pair table, or semantic graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalRelations<K, V> {
    rows: Vec<Relation<K, V>>,
}

impl<K, V> Default for LocalRelations<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> LocalRelations<K, V> {
    pub const fn new() -> Self {
        Self { rows: Vec::new() }
    }

    pub const fn len(&self) -> usize {
        self.rows.len()
    }

    pub const fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn iter(&self) -> LocalRelationIter<'_, K, V> {
        LocalRelationIter {
            inner: self.rows.iter(),
        }
    }

    pub fn clear(&mut self) {
        self.rows.clear();
    }

    pub fn try_reserve_additional(&mut self, additional: usize) -> Result<(), RelationAtlasError> {
        self.rows
            .try_reserve(additional)
            .map_err(|_| RelationAtlasError::Reservation)
    }
}

impl<K: Ord, V> LocalRelations<K, V> {
    pub fn get(&self, key: &K) -> Option<&V> {
        let at = self.rows.binary_search_by(|row| row.key.cmp(key)).ok()?;
        Some(&self.rows[at].value)
    }

    pub fn contains(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let at = self.rows.binary_search_by(|row| row.key.cmp(key)).ok()?;
        Some(&mut self.rows[at].value)
    }

    pub fn first(&self) -> Option<(&K, &V)> {
        let row = self.rows.first()?;
        Some((&row.key, &row.value))
    }

    pub fn remove(&mut self, key: &K) -> Option<V> {
        let at = self.rows.binary_search_by(|row| row.key.cmp(key)).ok()?;
        Some(self.rows.remove(at).value)
    }

    pub fn try_insert(&mut self, key: K, value: V) -> Result<Option<V>, RelationAtlasError> {
        match self.rows.binary_search_by(|row| row.key.cmp(&key)) {
            Ok(at) => Ok(Some(core::mem::replace(&mut self.rows[at].value, value))),
            Err(at) => {
                self.rows
                    .try_reserve(1)
                    .map_err(|_| RelationAtlasError::Reservation)?;
                self.rows.insert(at, Relation { key, value });
                Ok(None)
            }
        }
    }

    /// Convenience for an already-bounded local relation family. Production laws which must
    /// return physical allocation refusal use [`Self::try_insert`].
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self.rows.binary_search_by(|row| row.key.cmp(&key)) {
            Ok(at) => Some(core::mem::replace(&mut self.rows[at].value, value)),
            Err(at) => {
                self.rows.insert(at, Relation { key, value });
                None
            }
        }
    }
}

pub struct LocalRelationIter<'a, K, V> {
    inner: core::slice::Iter<'a, Relation<K, V>>,
}

impl<'a, K, V> Iterator for LocalRelationIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|row| (&row.key, &row.value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K, V> ExactSizeIterator for LocalRelationIter<'_, K, V> {}

impl<K: Serialize, V: Serialize> Serialize for LocalRelations<K, V> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(Some(self.rows.len()))?;
        for row in &self.rows {
            map.serialize_entry(&row.key, &row.value)?;
        }
        map.end()
    }
}

struct LocalRelationsVisitor<K, V> {
    marker: core::marker::PhantomData<(K, V)>,
}

impl<'de, K, V> Visitor<'de> for LocalRelationsVisitor<K, V>
where
    K: Deserialize<'de> + Ord,
    V: Deserialize<'de>,
{
    type Value = LocalRelations<K, V>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("an exact local relation map")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
        let mut relations = LocalRelations::new();
        while let Some((key, value)) = map.next_entry()? {
            if relations
                .try_insert(key, value)
                .map_err(|_| serde::de::Error::custom("local relation storage refused"))?
                .is_some()
            {
                return Err(serde::de::Error::custom("duplicate local relation key"));
            }
        }
        Ok(relations)
    }
}

impl<'de, K, V> Deserialize<'de> for LocalRelations<K, V>
where
    K: Deserialize<'de> + Ord,
    V: Deserialize<'de>,
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_map(LocalRelationsVisitor {
            marker: core::marker::PhantomData,
        })
    }
}

impl<K, V> IntoIterator for LocalRelations<K, V> {
    type Item = (K, V);
    type IntoIter = LocalRelationsIntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        LocalRelationsIntoIter {
            inner: self.rows.into_iter(),
        }
    }
}

pub struct LocalRelationsIntoIter<K, V> {
    inner: alloc::vec::IntoIter<Relation<K, V>>,
}

impl<K, V> Iterator for LocalRelationsIntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|row| (row.key, row.value))
    }
}

/// Exact range of one receiver's local outgoing relations in a frozen atlas.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RelationSpan {
    start: u64,
    len: u64,
}

impl RelationSpan {
    pub const fn len(self) -> u64 {
        self.len
    }

    pub const fn is_empty(self) -> bool {
        self.len == 0
    }
}

/// Construction owner which appends already-canonical local relation families.
pub struct FrozenRelationBuilder<K, V> {
    rows: Vec<Relation<K, V>>,
}

impl<K, V> Default for FrozenRelationBuilder<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> FrozenRelationBuilder<K, V> {
    pub const fn new() -> Self {
        Self { rows: Vec::new() }
    }

    pub fn try_append(
        &mut self,
        local: &LocalRelations<K, V>,
    ) -> Result<RelationSpan, RelationAtlasError>
    where
        K: Clone,
        V: Clone,
    {
        let start = u64::try_from(self.rows.len()).map_err(|_| RelationAtlasError::Extent)?;
        let len = u64::try_from(local.len()).map_err(|_| RelationAtlasError::Extent)?;
        self.rows
            .try_reserve(local.len())
            .map_err(|_| RelationAtlasError::Reservation)?;
        for (key, value) in local.iter() {
            self.rows.push(Relation {
                key: key.clone(),
                value: value.clone(),
            });
        }
        Ok(RelationSpan { start, len })
    }

    pub fn finish(self) -> FrozenRelationAtlas<K, V> {
        FrozenRelationAtlas {
            rows: self.rows.into_boxed_slice(),
        }
    }
}

/// Immutable, contiguous morphology consulted during continuing propagation.
///
/// Each state retains only a [`RelationSpan`]. A carried current therefore searches its one local
/// family and never consults a global ordered map or reconstructs prior chronology.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrozenRelationAtlas<K, V> {
    rows: Box<[Relation<K, V>]>,
}

impl<K, V> Default for FrozenRelationAtlas<K, V> {
    fn default() -> Self {
        Self {
            rows: Box::default(),
        }
    }
}

impl<K: Ord, V> FrozenRelationAtlas<K, V> {
    pub fn get(&self, span: RelationSpan, key: &K) -> Option<&V> {
        let rows = self.span(span).ok()?;
        let at = rows.binary_search_by(|row| row.key.cmp(key)).ok()?;
        Some(&rows[at].value)
    }
}

impl<K, V> FrozenRelationAtlas<K, V> {
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn iter(
        &self,
        span: RelationSpan,
    ) -> Result<FrozenRelationIter<'_, K, V>, RelationAtlasError> {
        Ok(FrozenRelationIter {
            inner: self.span(span)?.iter(),
        })
    }

    fn span(&self, span: RelationSpan) -> Result<&[Relation<K, V>], RelationAtlasError> {
        let start = usize::try_from(span.start).map_err(|_| RelationAtlasError::InvalidSpan)?;
        let len = usize::try_from(span.len).map_err(|_| RelationAtlasError::InvalidSpan)?;
        let end = start
            .checked_add(len)
            .filter(|end| *end <= self.rows.len())
            .ok_or(RelationAtlasError::InvalidSpan)?;
        Ok(&self.rows[start..end])
    }
}

pub struct FrozenRelationIter<'a, K, V> {
    inner: core::slice::Iter<'a, Relation<K, V>>,
}

impl<'a, K, V> Iterator for FrozenRelationIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|row| (&row.key, &row.value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K, V> ExactSizeIterator for FrozenRelationIter<'_, K, V> {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    #[test]
    fn local_builder_and_frozen_spans_match_ordered_reference() {
        let mut first = LocalRelations::new();
        let mut reference = BTreeMap::new();
        for (key, value) in [(7, 70), (2, 20), (9, 90), (7, 71)] {
            assert_eq!(
                first.try_insert(key, value).unwrap(),
                reference.insert(key, value)
            );
        }
        let mut second = LocalRelations::new();
        second.try_insert(4, 40).unwrap();
        let mut builder = FrozenRelationBuilder::new();
        let first_span = builder.try_append(&first).unwrap();
        let second_span = builder.try_append(&second).unwrap();
        let atlas = builder.finish();
        assert_eq!(atlas.get(first_span, &7), Some(&71));
        assert_eq!(atlas.get(first_span, &4), None);
        assert_eq!(atlas.get(second_span, &4), Some(&40));
        assert_eq!(
            atlas
                .iter(first_span)
                .unwrap()
                .map(|(key, value)| (*key, *value))
                .collect::<Vec<_>>(),
            reference.into_iter().collect::<Vec<_>>()
        );
    }
}
