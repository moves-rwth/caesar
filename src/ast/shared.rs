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
