use crate::{Mut, UntypedOwn, WeakRes};
use std::rc::Rc;

type CallbackFn<I, O> = Rc<dyn Fn(&mut UntypedOwn, I) -> Option<O> + 'static>;

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
pub struct Callback<A: 'static, O: 'static>(CallbackFn<A, O>);

impl<I: 'static, O: 'static> Callback<I, O> {
    /// Create a new callback.
    ///
    /// # Note
    /// Callbacks weakly reference their receivers; sending callback objects
    /// around will not cause reference cycles.
    pub fn new<T, R, F>(object: R, handler: F) -> Self
    where
        T: ?Sized + 'static,
        R: Into<WeakRes<T>>,
        F: Fn(Mut<T>, I) -> O + 'static,
    {
        let object = object.into();
        Self(Rc::new(move |assoc: &mut UntypedOwn, args: I| {
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
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(arbitrary_self_types)]
    /// use mutcy::{Callback, Mut, Own, Res};
    ///
    /// let own = &mut Own::new();
    ///
    /// struct Item(Callback<i32, ()>);
    ///
    /// impl Item {
    ///     fn work(self: Mut<Self>) {
    ///         println!("Item::work");
    ///         // Need `own()` call here.
    ///         self.0.own().call(self, 1);
    ///
    ///         // Compile error.
    ///         // self.0.call(self, 1);
    ///     }
    /// }
    ///
    /// let receiver = Res::new_in(1, own);
    /// let cb = Callback::new(&receiver, |this: Mut<i32>, args: i32| {
    ///     println!("Callback: this={} args={}", **this, args);
    /// });
    ///
    /// let sender = Res::new_in(Item(cb), own);
    ///
    /// // This is `Res::own` which has similar semantics. Since `via()` consumes its `self`, if we
    /// // want to keep using `sender` later we must call `own()`.
    /// sender.own().via(own).work();
    /// ```
    pub fn own(&self) -> Self {
        Self(self.0.clone())
    }

    /// Invoke the callback.
    ///
    /// Returns None if the object to call has been dropped, otherwise
    /// `Some(O)`.
    pub fn call<'a, 'b, X: ?Sized + 'static>(&self, own: Mut<'a, 'b, X>, args: I) -> Option<O> {
        let untyped = &mut own.untyped();
        (self.0)(untyped, args)
    }
}
