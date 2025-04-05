use crate::{ASSOC, AssocInner, Associated, Res, ResInner, UntypedOwn, seal::Sealed};
use std::{
    marker::{PhantomData, Unsize},
    ops::{CoerceUnsized, Deref, DerefMut},
    rc::Rc,
};

/// Mutable borrow guard providing access to associated data.
///
/// Implements [`Deref`]/[`DerefMut`] for direct access to the underlying value.
/// While this guard exists, other borrows through the same association are
/// suspended to prevent mutable aliasing.
///
/// A `Own<A>` uses `&mut self` to convert any `Res<B>` into a a `Own<B>`. This
/// allows the transfer of mutability within an association. See also
/// [Res::via].
/// ```
/// use mutcy::{Mut, Own, Res};
///
/// // Create a new root `Own`.
/// let mut root = &mut Own::new();
///
/// // Create a new pointer associated with this root `Own`.
/// let res = Res::new_in(123, root);
///
/// // Transform the `Res` into an `Own`, suspending the root `Own` which relinquishes all existing
/// // borrows on it. The new `res_mut` can then again be used with `via` to relinquish itself and
/// // open up another `Res`.
/// let res_mut: Own<i32> = res.own().via(root);
///
/// // Access the data inside `res` using `res_mut`.
/// assert_eq!(*res_mut, 123);
///
/// // When accessing root again, we relinquish `res_mut`. We are not allowed to use it again.
/// assert_eq!(**root, ());
///
/// // This would fail to compile, because we cannot hold the `res_mut` borrow across the `root` borrow.
/// // assert_eq!(*res_mut, 123);
/// ```
pub struct Own<'a, T: ?Sized + 'static> {
    pub(crate) assoc: PhantomData<&'a ()>,
    pub(crate) data: Res<T>,
}

impl Own<'static, ()> {
    /// Create a new initial `Own` with a new association.
    pub fn new() -> Self {
        Self {
            assoc: PhantomData,
            data: Res::new_raw(Rc::new(ResInner::new(Rc::new(AssocInner), ()))),
        }
    }

    /// Enters the association context to perform mutations.
    ///
    /// Installs a [scoped_thread_local](scoped_tls::scoped_thread_local) that
    /// allows you to call [Res::new] and [new_cyclic](Res::new_cyclic) without
    /// a panic.
    pub fn enter<F: FnOnce(&mut Own<()>) -> R, R>(&mut self, work: F) -> R {
        ASSOC.set(&self.assoc().clone(), || (work)(self))
    }
}

impl<'a, T: ?Sized + 'static> Own<'a, T> {
    pub(crate) fn new_internal(data: Res<T>) -> Self {
        Self {
            assoc: PhantomData,
            data,
        }
    }

    /// Convert into an untyped version of `Own`.
    ///
    /// This is mainly useful for passing to generic functions that need to
    /// [via_untyped](Res::via_untyped)
    /// associated data.
    ///
    /// Crate-visible only because design is unfinished.
    pub(crate) fn untyped(&mut self) -> UntypedOwn {
        UntypedOwn(self.assoc())
    }
}

impl<'a, T: 'static> Associated for Own<'a, T> {}

impl<'a, T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<Own<'a, U>> for Own<'a, T> {}

impl Default for Own<'static, ()> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, T: ?Sized + 'static> Deref for Own<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: The existence and accessibility of this `Own` guarantees that there
        // is no other live reference to this data.
        //
        // Using a different association followed by `Res::via` will result in a panic
        // as documented in `Res::via`. This guarantees that there exists only
        // one accessible `Own<T>` for a set or `Res` associated with an
        // `Assoc`.
        unsafe { self.data.as_ref() }
    }
}

impl<'a, T: ?Sized + 'static> DerefMut for Own<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: The existence and accessibility of this `Own` guarantees that there
        // is no other live reference to this data.
        //
        // Using a different `Assoc` followed by `Res::via` will result in a panic as
        // documented in `Res::via`. This guarantees that there exists only one
        // accessible `Own<T>` for a set or `Res` associated with an `Assoc`.
        unsafe { self.data.as_mut() }
    }
}

#[allow(private_interfaces)]
impl<'a, T: ?Sized + 'static> Sealed for Own<'a, T> {
    fn assoc(&self) -> &Rc<AssocInner> {
        self.data.assoc()
    }
}
