use ref_cast::RefCast;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::{
    fmt,
    ops::{Deref, DerefMut},
    rc::Rc,
};

/// Like [`Rc`], but automatically clones the underlying data when a mutable
/// reference is requested.
#[repr(transparent)]
pub struct Shared<T: ?Sized>(Rc<T>);

impl<T> Shared<T> {
    pub fn new(data: T) -> Self {
        Shared(Rc::new(data))
    }

    pub fn ref_count(this: &Self) -> usize {
        Rc::strong_count(&this.0)
    }

    pub fn as_ptr(this: &Self) -> *const T {
        Rc::as_ptr(&this.0)
    }
}

impl<T: ?Sized> Shared<T> {
    pub fn into_rc(self) -> Rc<T> {
        self.0
    }
}

impl<T: ?Sized> Clone for Shared<T> {
    fn clone(&self) -> Self {
        Shared(self.0.clone())
    }
}

impl<T: ?Sized> Deref for Shared<T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.0.deref()
    }
}

impl<T: Clone> DerefMut for Shared<T> {
    fn deref_mut(&mut self) -> &mut T {
        if cfg!(debug_assertions) {
            let strong_count = Rc::strong_count(&self.0);
            if strong_count > 1 {
                tracing::trace!(strong_count = strong_count, "cloning shared pointer");
            }
        }
        Rc::make_mut(&mut self.0)
    }
}

impl<T: ?Sized> From<Rc<T>> for Shared<T> {
    fn from(v: Rc<T>) -> Shared<T> {
        Shared(v)
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for Shared<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Shared<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

/// [Shared] wrapper that provides pointer-based trait implementations for
/// shared pointers, to store them in sets or maps based on their pointer
/// identity (reference equality).
///
/// Use [RefCast] to efficiently convert between this type and a reference to a
/// [Shared] object.
#[repr(transparent)]
#[derive(RefCast, Clone)]
pub struct RefEqShared<T>(Shared<T>);

impl<T> RefEqShared<T> {
    pub fn new(shared: Shared<T>) -> Self {
        Self(shared)
    }

    pub fn into_shared(self) -> Shared<T> {
        self.0
    }

    pub fn as_shared(&self) -> &Shared<T> {
        &self.0
    }
}

impl<T: fmt::Debug> fmt::Debug for RefEqShared<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&*self.0, f)
    }
}

impl<T> PartialEq for RefEqShared<T> {
    fn eq(&self, other: &Self) -> bool {
        Shared::as_ptr(&self.0) == Shared::as_ptr(&other.0)
    }
}

impl<T> Eq for RefEqShared<T> {}

impl<T> Ord for RefEqShared<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        Shared::as_ptr(&self.0).cmp(&Shared::as_ptr(&other.0))
    }
}

impl<T> PartialOrd for RefEqShared<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(Shared::as_ptr(&self.0).cmp(&Shared::as_ptr(&other.0)))
    }
}

impl<T> Hash for RefEqShared<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Shared::as_ptr(&self.0).hash(state)
    }
}
