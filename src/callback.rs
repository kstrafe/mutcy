use crate::{Mut, UntypedOwn, WeakRes};
use std::rc::Rc;

type CallbackFn<A, B> = Rc<dyn Fn(&mut UntypedOwn, A) -> Option<B> + 'static>;

/// Weakly referencing callback mechanism.
///
/// # Examples
///
/// ```
/// use mutcy::{Callback, Own, Res};
///
/// let own = &mut Own::new();
/// let item = Res::new_in(0, own);
///
/// let cb = Callback::new(&item, |this, args| {
///     **this += args;
///     123
/// });
///
/// assert_eq!(cb.call(own, 1), Some(123));
///
/// assert_eq!(*item.via(own), 1);
/// ```
#[derive(Clone)]
pub struct Callback<A: 'static, B: 'static>(CallbackFn<A, B>);

impl<A: 'static, B: 'static> Callback<A, B> {
    /// Create a new callback.
    ///
    /// # Note
    /// Callbacks weakly reference their receivers; sending callback objects
    /// around will not cause reference cycles.
    pub fn new<T, O, F>(object: O, handler: F) -> Self
    where
        T: ?Sized + 'static,
        O: Into<WeakRes<T>>,
        F: Fn(Mut<T>, A) -> B + 'static,
    {
        let object = object.into();
        Self(Rc::new(move |assoc: &mut UntypedOwn, args: A| {
            object
                .upgrade()
                .map(|object| (handler)(&mut object.via_untyped(assoc), args))
        }))
    }

    /// Clones the callback to prepare for mutation chaining.
    ///
    /// Equivalent to [`Clone::clone`] but provides clearer semantics when
    /// establishing new mutation chains through [call](Callback::call).
    ///
    /// When an object T contains a callback object, we must clone the callback
    /// first before invoking it. This ensures that when T is dropped, the
    /// callback still lives on the stack.
    ///
    /// This is only needed if called as `self.<get-callback>.call(self,
    /// <args>)`. An `own()` call after `<get-callback>` will be required.
    pub fn own(&self) -> Self {
        Self(self.0.clone())
    }

    /// Invoke the callback.
    ///
    /// Returns None if the object to call has been dropped, otherwise
    /// `Some(B)`.
    pub fn call<'a, 'b, X: ?Sized + 'static>(&self, own: Mut<'a, 'b, X>, args: A) -> Option<B> {
        let untyped = &mut own.untyped();
        (self.0)(untyped, args)
    }
}
