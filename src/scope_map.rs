//! A generic map type that can have sub-scopes.

use std::{borrow::Borrow, hash::Hash, iter::FromIterator, marker::PhantomData};

use indexmap::IndexMap;

/// An entry in the map of at each scope level. Either there is a value, or we
/// explicitly remember that the entry has been deleted on the current level.
#[derive(Debug)]
enum ScopeEntry<V> {
    Value(V),
    Deleted,
}

/// A ScopeMap is an map type that supports [`ScopeMap::push`] and
/// [`ScopeMap::pop`] operations that increase or decrease a "scope level".
/// Modifications on one scope level can be undone by calling [`ScopeMap::pop`].
///
/// Iteration order of this scope map follows the order of first insertion (or
/// deletion) of a key.
#[derive(Debug)]
pub struct ScopeMap<K, V> {
    scopes: Vec<IndexMap<K, ScopeEntry<V>>>,
}

pub struct ScopeParent<K, V> {
    depth: usize,
    phantom: PhantomData<(K, V)>,
}

impl<K, V> ScopeMap<K, V> {
    /// Create an empty [`ScopeMap`] with one scope level.
    pub fn new() -> Self {
        ScopeMap {
            scopes: vec![IndexMap::new()],
        }
    }

    /// Returns the number of scopes in this scope map.
    pub fn depth(&self) -> usize {
        self.scopes.len()
    }
}

impl<K, V> ScopeMap<K, V>
where
    K: Eq + Hash,
{
    /// Increase the scope level.
    ///
    /// A [`ScopeParent`] object is returned and it is used in the call to
    /// [`ScopeMap::pop`] to check whether the `pop` corresponds to the `push`
    /// that generated this [`ScopeParent`].
    pub fn push(&mut self) -> ScopeParent<K, V> {
        self.scopes.push(IndexMap::new());
        ScopeParent {
            depth: self.scopes.len(),
            phantom: PhantomData,
        }
    }

    /// Decrease the scope level and undo all modifications that happened on
    /// this level.
    ///
    /// The `parent` object is used to assert that the scope level that is
    /// popped here corresponds to the [`ScopeMap::push`] that created the
    /// `parent` object.
    pub fn pop(&mut self, parent: ScopeParent<K, V>) {
        assert_eq!(parent.depth, self.scopes.len());
        self.unchecked_pop();
    }

    /// Like [`ScopeMap::pop`], but doesn't take a [`ScopeParent`] object and
    /// doesn't check the corresponding assertion that the [`ScopeParent`]'s
    /// scope level corresponds to the level that's removed right now.
    ///
    /// Panics if [`ScopeMap::depth`] is one.
    pub fn unchecked_pop(&mut self) {
        assert!(self.scopes.len() > 1);
        self.scopes.pop();
    }

    /// Insert an entry at the current scope level. Can be undone with
    /// [`ScopeMap::pop`].
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let map = self.scopes.last_mut().unwrap();
        let prev = map.insert(key, ScopeEntry::Value(value));
        match prev {
            Some(ScopeEntry::Value(v)) => Some(v),
            _ => None,
        }
    }

    /// Delete the element at the current scope level. This can be undone by
    /// going back to the scope level above.
    ///
    /// If there was a previous element on this scope level, it is returned. If
    /// there is an element at this key at a scope level above, `None` is returned.
    pub fn remove(&mut self, key: K) -> Option<V> {
        let map = self.scopes.last_mut().unwrap();
        let prev = map.insert(key, ScopeEntry::Deleted);
        match prev {
            Some(ScopeEntry::Value(v)) => Some(v),
            _ => None,
        }
    }

    /// Retrieve an element from the map.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        debug_assert!(!self.scopes.is_empty());
        let entry = self
            .scopes
            .iter()
            .rev()
            .flat_map(|map| map.get(key))
            .next()?;
        match entry {
            ScopeEntry::Value(v) => Some(v),
            ScopeEntry::Deleted => None,
        }
    }

    /// Does this map contain the given key?
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.get(key).is_some()
    }

    /// Get an iterator over the entries that have been set on this scope level
    /// only. The order follows the insertion order.
    pub fn local_iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.scopes
            .last()
            .unwrap()
            .iter()
            .flat_map(|(k, v)| match v {
                ScopeEntry::Value(v) => Some((k, v)),
                ScopeEntry::Deleted => None,
            })
    }
}

/// Create a [`ScopeMap`] from an iterator. The order of entries is preserved.
impl<K: Eq + Hash, V> FromIterator<(K, V)> for ScopeMap<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let iter = iter.into_iter().map(|(k, v)| (k, ScopeEntry::Value(v)));
        ScopeMap {
            scopes: vec![IndexMap::from_iter(iter)],
        }
    }
}
