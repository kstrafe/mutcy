use crate::{ASSOC, AssocInner, Associated, Own, UntypedOwn, WeakRes, seal::Sealed};
use std::{cell::UnsafeCell, marker::Unsize, ops::CoerceUnsized, rc::Rc};

/// Associated reference-counted pointer.
///
/// This item's `T` can only be mutably accessed using [via](Res::via).
///
/// # Examples
///
/// ```
/// use mutcy::{Own, Res};
///
/// let own = &mut Own::new();
/// let item = Res::new_in(41, own);
///
/// let mut data: Own<i32> = item.via(own);
/// *data += 1;
/// assert_eq!(*data, 42);
/// ```
pub struct Res<T: ?Sized + 'static>(Rc<ResInner<T>>);

impl<T: 'static> Res<T> {
    /// Create a new `Res` associated to the currently [enter](Own::enter)ed
    /// association.
    ///
    /// # Panics
    ///
    /// This function will panic if not (transitively) called from within
    /// [Own::enter]'s `work` function.
    ///
    /// # Examples
    ///
    /// ```
    /// use mutcy::{Own, Res};
    ///
    /// let mut assoc = Own::new();
    ///
    /// assoc.enter(|x| {
    ///     let item: Res<i32> = Res::new(123);
    /// });
    ///
    /// // PANIC - Thread local context is not present for `Res` to associate with.
    /// // Res::new(123);
    /// ```
    pub fn new(data: T) -> Self {
        ASSOC.with(|assoc| Self::new_in(data, assoc))
    }

    /// Create a new cyclic `Res` associated with the currently
    /// [enter](Own::enter)ed association.
    ///
    /// # Panics
    ///
    /// This function will panic if not (transitively) called from within
    /// [Own::enter]'s `work` function.
    ///
    /// # Examples
    /// ```
    /// use mutcy::{Own, Res, WeakRes};
    ///
    /// let mut assoc = Own::new();
    ///
    /// struct MyItem(i32, WeakRes<Self>);
    ///
    /// assoc.enter(|x| {
    ///     let item: Res<MyItem> = Res::new_cyclic(|weak| MyItem(41, weak.clone()));
    /// });
    /// ```
    pub fn new_cyclic<F>(data_fn: F) -> Self
    where
        F: FnOnce(&WeakRes<T>) -> T,
    {
        ASSOC.with(move |assoc| Self::new_cyclic_in(data_fn, assoc))
    }

    /// Create a new `Res` with the same association as `A`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mutcy::{Own, Res};
    /// let own = &mut Own::new();
    /// let res: Res<i32> = Res::new_in(0, own);
    /// ```
    pub fn new_in<A: Associated>(value: T, assoc: &A) -> Self {
        Self(Rc::new(ResInner::new(assoc.assoc().clone(), value)))
    }

    /// Create a new cyclic `Res` with the same association as `A`.
    ///
    /// `data_fn` is given a reference to a [WeakRes].
    ///
    /// See also [Rc::new_cyclic].
    ///
    /// # Examples
    ///
    /// ```
    /// use mutcy::{Own, Res, WeakRes};
    ///
    /// let assoc = &mut Own::new();
    ///
    /// struct MyItem(i32, WeakRes<Self>);
    /// let item: Res<MyItem> = Res::new_cyclic_in(|weak| MyItem(41, weak.clone()), assoc);
    /// ```
    pub fn new_cyclic_in<F, A>(data_fn: F, assoc: &A) -> Self
    where
        F: FnOnce(&WeakRes<T>) -> T,
        A: Associated,
    {
        let assoc = assoc.assoc().clone();
        Self(Rc::new_cyclic(move |weak| {
            let weak = WeakRes::new_internal(weak.clone());
            ResInner::new(assoc, (data_fn)(&weak))
        }))
    }
}

impl<T: ?Sized + 'static> Res<T> {
    /// Creates a new handle for mutation chaining.
    ///
    /// Equivalent to [`Clone::clone`] but provides clearer semantics when
    /// establishing new mutation chains through [`via`].
    ///
    /// Avoids double-borrow scenarios in method chains:
    ///
    /// # Examples
    ///
    /// ```
    /// # #![feature(arbitrary_self_types)]
    /// # use mutcy::{Mut, Own, Res};
    /// # struct MyType {
    /// #    inner: Res<()>,
    /// # }
    /// impl MyType {
    ///     fn method(self: Mut<Self>) {
    ///         // ERROR: Moving self while while accessing field
    ///         // let inner: Own<()> = self.inner.via(self);
    ///
    ///         // OK
    ///         let inner: Own<()> = self.inner.own().via(self);
    ///     }
    /// }
    /// ```
    ///
    /// [`via`]: Res::via
    pub fn own(&self) -> Self {
        self.clone()
    }

    /// Relinquish a previous `Own` and creates an `Own` of `self`.
    ///
    /// Since references to `T` from `Own<T>` require [Deref](std::ops::Deref)
    /// or [DerefMut](std::ops::DerefMut),
    /// calling this function will relinquish all such borrows on `Own<T>`.
    /// This makes it safe to acquire a mutable reference recursively.
    ///
    /// In effect, there exists only a single accessible `Own<T>` for any
    /// `Res<T>` in the same association. This function checks if the
    /// association matches to prevent multiple `Own<T>` being accessible
    /// within that association..
    ///
    /// # Panics
    ///
    /// Will panic if the arguments' association differ.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![feature(arbitrary_self_types)]
    /// # use mutcy::{Mut, Res};
    /// struct MyType {
    ///     this: Res<Self>,
    ///     value: i32,
    /// }
    ///
    /// impl MyType {
    ///     fn method(self: Mut<Self>) {
    ///         let value_reference: &mut i32 = &mut self.value;
    ///
    ///         // `via` relinquishes `value_reference`, because it has a dependency on
    ///         // `self` that conflicts with `via`.
    ///         self.this.own().via(self);
    ///
    ///         // ERROR: We cannot now use `value_reference`.
    ///         // *value_reference += 1;
    ///
    ///         // We need to reborrow instead.
    ///         let value_reference: &mut i32 = &mut self.value;
    ///     }
    /// }
    /// ```
    pub fn via<'a: 'b, 'b, A: ?Sized + 'static>(self, source: &'a mut Own<A>) -> Own<'b, T> {
        assert!(
            Rc::ptr_eq(self.assoc(), source.assoc()),
            "assoc is not identical"
        );

        Own::new_internal(self)
    }

    pub(crate) fn via_untyped<'a: 'b, 'b>(self, source: &'a mut UntypedOwn) -> Own<'b, T> {
        assert!(
            Rc::ptr_eq(self.assoc(), source.assoc()),
            "assoc is not identical"
        );

        Own::new_internal(self)
    }

    /// Create a weakly referencing version this `Res`.
    ///
    /// See [Rc::downgrade].
    ///
    /// # Examples
    ///
    /// ```
    /// use mutcy::{Own, Res, WeakRes};
    /// let own = &mut Own::new();
    /// let weak: WeakRes<()> = Res::downgrade(&Res::new_in((), own));
    /// ```
    pub fn downgrade(this: &Res<T>) -> WeakRes<T> {
        WeakRes::new_internal(Rc::downgrade(&this.0))
    }

    pub(crate) fn new_raw(data: Rc<ResInner<T>>) -> Self {
        Self(data)
    }

    // SAFETY: Caller must ensure no mutable reference to `T` is live.
    pub(crate) unsafe fn as_ref(&self) -> &T {
        // SAFETY: Function is marked as unsafe. See function comment.
        unsafe { &*self.0.data.get() }
    }

    // SAFETY: Caller must ensure no other reference to `T` is live.
    #[allow(clippy::mut_from_ref)]
    pub(crate) unsafe fn as_mut(&self) -> &mut T {
        // SAFETY: Function is marked as unsafe. See function comment.
        unsafe { &mut *self.0.data.get() }
    }
}

impl<T: 'static> Associated for Res<T> {}

impl<T: ?Sized + 'static> Clone for Res<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<Res<U>> for Res<T> {}

#[allow(private_interfaces)]
impl<T: ?Sized + 'static> Sealed for Res<T> {
    fn assoc(&self) -> &Rc<AssocInner> {
        &self.0.assoc
    }
}

pub struct ResInner<T: ?Sized + 'static> {
    assoc: Rc<AssocInner>,
    data: UnsafeCell<T>,
}

impl<T: 'static> ResInner<T> {
    pub fn new(assoc: Rc<AssocInner>, data: T) -> Self {
        Self {
            assoc,
            data: UnsafeCell::new(data),
        }
    }
}

#[allow(private_interfaces)]
impl<T> Sealed for ResInner<T> {
    fn assoc(&self) -> &Rc<AssocInner> {
        &self.assoc
    }
}
