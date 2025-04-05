use crate::{Res, ResInner};
use std::{marker::Unsize, ops::CoerceUnsized, rc::Weak};

/// Non-owning version of [Res] similar to [Weak].
pub struct WeakRes<T: ?Sized + 'static>(Weak<ResInner<T>>);

impl<T: 'static> WeakRes<T> {
    /// Constructs a new `WeakRes<T>`, without allocating any memory. Calling
    /// upgrade on the return value always gives `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mutcy::WeakRes;
    ///
    /// let weak: WeakRes<i32> = WeakRes::new();
    /// ```
    pub fn new() -> Self {
        Self(Weak::new())
    }
}

impl<T: ?Sized + 'static> WeakRes<T> {
    pub(crate) fn new_internal(weak: Weak<ResInner<T>>) -> Self {
        Self(weak)
    }

    /// Attempts to upgrade to a strong reference
    pub fn upgrade(&self) -> Option<Res<T>> {
        self.0.upgrade().map(|strong| Res::new_raw(strong))
    }
}

impl<T: ?Sized + 'static> Clone for WeakRes<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<WeakRes<U>> for WeakRes<T> {}

impl<T> Default for WeakRes<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: ?Sized + 'static> From<&Res<T>> for WeakRes<T> {
    fn from(item: &Res<T>) -> WeakRes<T> {
        Res::downgrade(item)
    }
}

impl<T: ?Sized + 'static> From<Res<T>> for WeakRes<T> {
    fn from(item: Res<T>) -> WeakRes<T> {
        Res::downgrade(&item)
    }
}

impl<T: ?Sized + 'static> From<&WeakRes<T>> for WeakRes<T> {
    fn from(item: &WeakRes<T>) -> WeakRes<T> {
        item.clone()
    }
}
