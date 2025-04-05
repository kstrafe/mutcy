//! # Mutable Cyclic Borrows
//!
//! Safe mutable cyclic borrows using borrow relinquishing.
//!
//! This crate enables objects to mutably reference each
//! other in cycles while adhering to Rust's borrowing rules.
//!
//! Rust does not permit call chains as `A -> B -> A` on objects `A`
//! and `B` using `&mut self` because that mutably aliases `A`
//! which is immediate undefined behavior.
//!
//! `Mutcy` provides an API to work around this constraint by making you
//! relinquish all borrows to `A` when you call `B`. Thus, at the point `B`
//! calls `A` (`B -> A`), there are no live references to `A`. When `B`
//! returns, `A`'s borrow is reacquired.
//!
//! # Rationale
//!
//! Relinquishing borrows allows us to implement [Callback]s and related
//! patterns in our code. Without this crate callbacks are cumbersome to use
//! because we are constrained to [RefCell](std::cell::RefCell), which doesn't
//! allow recursion.
//!
//! Another method is to enqueue work to some executor, but this
//! presents us with a delayed operation and a reordering problem; suppose we
//! have a queue containing work `[A, B]`, if `A` enqueues another operation, we
//! now get `[B, A2]`. A direct function call would run `A2` before `B`. This
//! reordering can give us non-intuitive results. Additionally, reordering is a
//! property of the system as a whole, which removes our ability to perform
//! *local reasoning*; changing code in one place can break it in another.
//!
//! # Note
//!
//! This crate currently requires *nightly* Rust.
//!
//! Note that arbitrary self types `fn name(self: Mut<T>)` are not yet
//! stable. These can be used on nightly using
//! `#![feature(arbitrary_self_types)]`.
//!
//! While it is possible to use this crate without `arbitrary_self_types`, it
//! makes working with this crate impractical.
//!
//! # Example
//!
//! ```
//! #![feature(arbitrary_self_types)]
//! use mutcy::{Mut, Own, Res, WeakRes};
//!
//! // Create a new association for our data. Every `Res` is associated with some root `Own`.
//! let mut assoc = &mut Own::new();
//!
//! // Create two associated objects. See [Res::new] on how to avoid having to pass `assoc`.
//! let a = Res::new_in(
//!     A {
//!         b: WeakRes::new(),
//!         x: 0,
//!     },
//!     assoc,
//! );
//! let b = Res::new_in(B { a: a.clone(), y: 0 }, assoc);
//!
//! // Before we can access `a`, we need to call `own().via(x)`. This relinquishes all existing
//! // borrows acquired via `assoc`'s Deref/DerefMut implementation.
//! a.own().via(assoc).b = Res::downgrade(&b);
//!
//! // Call a method on `A`
//! a.own().via(assoc).call_a(5);
//!
//! // You can store the created `Own` from `via` onto the stack.
//! let mut a_own: Own<A> = a.own().via(assoc);
//!
//! // Note, the following fails to compile because of `a_own`'s dependency on `x`. This prevents
//! // Rust's requirements for references from being violated.
//!
//! // let _: () = **assoc;
//!
//! // error[E0502]: cannot borrow `*assoc` as immutable because it is also borrowed as mutable
//! //   --> src/lib.rs:56:14
//! //    |
//! // 30 | let mut a_own: Own<A> = a.own().via(assoc);
//! //    |                                     ----- mutable borrow occurs here
//! // ...
//! // 35 | let _: () = **assoc;
//! //    |              ^^^^^^ immutable borrow occurs here
//! // ...
//! // 50 | a_own.my_method();
//! //    | ----- mutable borrow later used here
//!
//! // Because this `Own` (`a_own`) still exists.
//! a_own.my_method();
//!
//! struct A {
//!     b: WeakRes<B>,
//!     x: i32,
//! }
//!
//! impl A {
//!     // `Mut` is a type alias to `&mut Own`.
//!     fn call_a(self: Mut<Self>, count: usize) {
//!         // Mutate through &mut Self.
//!         self.x += 1;
//!
//!         println!(">>> A: {}", count);
//!         self.b.upgrade().unwrap().via(self).call_b(count - 1);
//!         println!("<<< A: {}", count);
//!
//!         // Mutate again, this is valid after the call to `b` which has called back into here
//!         // because we reborrow &mut Self here.
//!         self.x -= 1;
//!     }
//!
//!     fn my_method(self: Mut<Self>) {
//!         self.x += 1;
//!     }
//! }
//!
//! impl Drop for A {
//!     fn drop(&mut self) {
//!         println!("A dropped");
//!     }
//! }
//!
//! struct B {
//!     a: Res<A>,
//!     y: u64,
//! }
//!
//! impl B {
//!     fn call_b(self: Mut<Self>, count: usize) {
//!         self.y += 1;
//!
//!         println!(">>> B: {}", count);
//!         let mut a = self.a.own().via(self);
//!         if count > 1 {
//!             a.call_a(count - 1);
//!         }
//!         println!("<<< B: {}", count);
//!
//!         self.y -= 1;
//!     }
//! }
//!
//! impl Drop for B {
//!     fn drop(&mut self) {
//!         println!("B dropped");
//!     }
//! }
//! ```
//!
//! # What is an association?
//!
//! Each pointer type ([Own], [Res]) belongs to an association. This is
//! just a unique number (currently, it is a pointer to non-ZST data that was
//! allocated, guaranteeing uniqueness via the global allocator).
//!
//! When we use [Own::new], we create a new association. `Res` can be
//! associated with this `Own` upon construction. [Res::via] takes `(self, &mut
//! Own)` and returns a `Own` to `self`. This
//! relinquishes access to the input `Own<A>`, and "opens" the `Res<B>`
//! into a dereferencable `Own<B>`. We assert that the associations of the two
//! inputs are equal, otherwise, we panic. This ensures that we can never have
//! more than one dereferencable `Own` simultaneously, which could cause
//! undefined behavior.
//!
//! # Preventing leaks
//!
//! We need to be aware whenever a struct declares an `Option<Res<_>>` (or any
//! other container of `Res`) that needs to be populated from outside after
//! initialization. This indicates that we may have a potential leak, as we can
//! create a reference cycle.
//!
//! To avoid leaks, make a struct take in `Res` during construction only. It is
//! also not leaky to create and store `Res` objects from within the struct.
//! It's mainly the transfer of these to other objects that creates leaks.
//!
//! If you still need to clone a `Res` into some struct, consider
//! [Res::downgrade] to create a [WeakRes].
//!
//! # Drop guarantees
//!
//! The system maintains object validity through the following conditions.
//!
//! - An object `T` will only be dropped when:
//!    1. All [`Res<T>`] pointing to it have been dropped.
//!    2. All [`Own<T>`] pointing to it have been dropped.
//!
//! This prevents dangling references in call chains like:
//! ```text
//! A → B → A // Last A access can remove B from itself, into which we return.
//! ```
//!
//! When the call stack returns into B, it will still exist and be valid,
//! because we have cloned `B` using [Res::own] to the stack.
//!
//! ## Example Scenario
//! ```
//! # use mutcy::{Mut, Res};
//! struct Node {
//!     name: String,
//!     child: Option<Res<Node>>,
//!     parent: Option<Res<Node>>,
//! }
//!
//! fn traverse(node: Mut<Node>) {
//!     if let Some(child) = &node.child {
//!         child.own().via(node).parent = None; // Would invalidate parent
//!         // Without guarantees, this could access freed memory:
//!         println!("Parent data: {:?}", node.name);
//!     }
//! }
//! ```
//!
//! The guarantees ensure:
//! - Original `node` (parent) persists until its first `traverse` call
//!   completes.
//! - `parent = None` only marks the relationship, doesn't drop immediately.
//! - Final `println` safely accesses still-allocated parent.
//!
//! Dropping `T` occurs immediately when all `Res<T>` and `Own<T>` objects
//! for that instance of `T` have been dropped.
//!
//! Deallocation of memory backing that
//! `T` occurs once `T` was dropped and no [WeakRes] instances to that
//! `T` exist.
#![feature(arbitrary_self_types)]
#![feature(coerce_unsized)]
#![feature(unsize)]
pub use crate::callback::Callback;
use std::{
    cell::UnsafeCell,
    convert::From,
    marker::{PhantomData, Unsize},
    ops::{CoerceUnsized, Deref, DerefMut},
    rc::{Rc, Weak},
};

mod callback;

scoped_tls::scoped_thread_local!(static ASSOC: Rc<AssocInner>);

/// Convenience type over [Own] allowing self methods as `self: Mut<Self>`.
///
/// It is possible to write `self: &mut Own<Self>` but it's quite noisy. This
/// type serves as a convenience wrapper for methods such that they can be
/// written as `self: Mut<Self>`.
pub type Mut<'a, 'b, T> = &'a mut Own<'b, T>;

mod seal {
    use crate::AssocInner;
    use std::rc::Rc;

    pub trait Sealed {
        #[allow(private_interfaces)]
        fn assoc_inner(&self) -> &Rc<AssocInner>;
    }
}

/// Sealed trait to allow [Res::new_in] and [Res::new_cyclic_in] to use
/// [Mut], or [Res] as an association source.
pub trait Associated: seal::Sealed {}

#[allow(private_interfaces)]
impl seal::Sealed for Rc<AssocInner> {
    fn assoc_inner(&self) -> &Rc<AssocInner> {
        self
    }
}

#[allow(private_interfaces)]
impl<'a, T: 'static> seal::Sealed for Own<'a, T> {
    fn assoc_inner(&self) -> &Rc<AssocInner> {
        &self.data.0.assoc
    }
}

#[allow(private_interfaces)]
impl<T> seal::Sealed for Res<T> {
    fn assoc_inner(&self) -> &Rc<AssocInner> {
        &self.0.assoc
    }
}

#[doc(hidden)]
impl Associated for Rc<AssocInner> {}
impl<T: 'static> Associated for Res<T> {}
impl<'a, T: 'static> Associated for Own<'a, T> {}

pub(crate) struct AssocInner;

/// Associated reference-counted pointer.
///
/// This item's `T` can only be mutably accessed using [via](Res::via).
///
/// ```
/// use mutcy::{Mut, Own, Res};
///
/// let mut assoc = Own::new();
/// let item = Res::new_in(41, &assoc);
///
/// let value: i32 = assoc.enter(|x| {
///     let mut data = item.via(x);
///     *data += 1;
///     *data
/// });
///
/// assert_eq!(value, 42);
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
    /// use mutcy::{Mut, Own, Res};
    ///
    /// let mut assoc = Own::new();
    ///
    /// assoc.enter(|x| {
    ///     let item = Res::new(123);
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
    /// use mutcy::{Mut, Own, Res, WeakRes};
    ///
    /// let mut assoc = Own::new();
    ///
    /// struct MyItem(i32, WeakRes<Self>);
    ///
    /// assoc.enter(|x| {
    ///     let item = Res::new_cyclic(|weak| MyItem(41, weak.clone()));
    ///
    ///     let mut data = item.via(x);
    ///     data.0 += 1;
    ///
    ///     let data_reborrow = data.1.upgrade().unwrap().own().via(x);
    ///     assert_eq!(data_reborrow.0, 42);
    /// });
    /// ```
    pub fn new_cyclic<F>(data_fn: F) -> Self
    where
        F: FnOnce(&WeakRes<T>) -> T,
    {
        ASSOC.with(move |assoc| Self::new_cyclic_in(data_fn, assoc))
    }

    /// Create a new `Res` with the same association as `A`.
    pub fn new_in<A: Associated>(value: T, assoc: &A) -> Self {
        Self(Rc::new(ResInner::new(assoc.assoc_inner().clone(), value)))
    }

    /// Create a new cyclic `Res` with the same association as `A`.
    ///
    /// `data_fn` is given a reference to a [WeakRes].
    ///
    /// See also [Rc::new_cyclic].
    /// ```
    /// use mutcy::{Mut, Own, Res, WeakRes};
    ///
    /// let assoc = &mut Own::new();
    ///
    /// struct MyItem(i32, WeakRes<Self>);
    /// let item = Res::new_cyclic_in(|weak| MyItem(41, weak.clone()), assoc);
    ///
    /// assoc.enter(|x| {
    ///     let mut data = item.via(x);
    ///     data.0 += 1;
    ///
    ///     let data_reborrow = data.1.upgrade().unwrap().own().via(x);
    ///     assert_eq!(data_reborrow.0, 42);
    /// });
    /// ```
    pub fn new_cyclic_in<F, A>(data_fn: F, assoc: &A) -> Self
    where
        F: FnOnce(&WeakRes<T>) -> T,
        A: Associated,
    {
        let assoc = assoc.assoc_inner().clone();
        Self(Rc::new_cyclic(move |weak| {
            let weak = WeakRes::new_internal(weak.clone());
            ResInner::new(assoc, (data_fn)(&weak))
        }))
    }
}

impl<T: ?Sized + 'static> Res<T> {
    fn new_raw(data: Rc<ResInner<T>>) -> Self {
        Self(data)
    }

    /// Creates a new handle for mutation chaining.
    ///
    /// Equivalent to [`Clone::clone`] but provides clearer semantics when
    /// establishing new mutation chains through [`via`].
    ///
    /// Avoids double-borrow scenarios in method chains:
    /// ```
    /// # #![feature(arbitrary_self_types)]
    /// # use mutcy::{Mut, Res};
    /// # struct MyType {
    /// #    inner: Res<()>,
    /// # }
    /// impl MyType {
    ///     fn method(self: Mut<Self>) {
    ///         // ERROR: Cannot borrow `self` mutably more than once
    ///         // self.inner.via(self);
    ///
    ///         // OK
    ///         let inner = self.inner.own().via(self);
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
    /// Since references to `T` from `Own<T>` require [Deref] or [DerefMut],
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
            Rc::ptr_eq(&self.0.assoc, &source.data.0.assoc),
            "assoc is not identical"
        );

        Own {
            assoc: source.assoc,
            data: self,
        }
    }

    fn via_untyped<'a: 'b, 'b>(self, source: &'a mut UntypedOwn) -> Own<'b, T> {
        assert!(
            Rc::ptr_eq(&self.0.assoc, source.0),
            "assoc is not identical"
        );

        Own {
            assoc: PhantomData,
            data: self,
        }
    }

    /// Create a weakly referencing version this `Res`.
    ///
    /// See [Rc::downgrade].
    pub fn downgrade(this: &Res<T>) -> WeakRes<T> {
        WeakRes::new_internal(Rc::downgrade(&this.0))
    }

    // SAFETY: Caller must ensure no mutable reference to `T` is live.
    unsafe fn as_ref(&self) -> &T {
        // SAFETY: Function is marked as unsafe. See function comment.
        unsafe { &*self.0.data.get() }
    }

    // SAFETY: Caller must ensure no other reference to `T` is live.
    #[allow(clippy::mut_from_ref)]
    unsafe fn as_mut(&self) -> &mut T {
        // SAFETY: Function is marked as unsafe. See function comment.
        unsafe { &mut *self.0.data.get() }
    }
}

impl<T: ?Sized + 'static> Clone for Res<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<Res<U>> for Res<T> {}

struct ResInner<T: ?Sized + 'static> {
    assoc: Rc<AssocInner>,
    data: UnsafeCell<T>,
}

impl<T: 'static> ResInner<T> {
    fn new(assoc: Rc<AssocInner>, data: T) -> Self {
        Self {
            assoc,
            data: UnsafeCell::new(data),
        }
    }
}

/// Non-owning version of [Res] similar to [Weak].
pub struct WeakRes<T: ?Sized + 'static>(Weak<ResInner<T>>);

impl<T: 'static> WeakRes<T> {
    /// Constructs a new `WeakRes<T>`, without allocating any memory. Calling
    /// upgrade on the return value always gives `None`.
    pub fn new() -> Self {
        Self(Weak::new())
    }
}

impl<T: ?Sized + 'static> WeakRes<T> {
    fn new_internal(weak: Weak<ResInner<T>>) -> Self {
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
    assoc: PhantomData<&'a ()>,
    data: Res<T>,
}

impl Own<'static, ()> {
    /// Create a new initial `Own` with a new association.
    pub fn new() -> Self {
        Self {
            assoc: PhantomData,
            data: Res(Rc::new(ResInner::new(Rc::new(AssocInner), ()))),
        }
    }

    /// Enters the association context to perform mutations.
    ///
    /// Installs a [scoped_thread_local](scoped_tls::scoped_thread_local) that
    /// allows you to call [Res::new] and [new_cyclic](Res::new_cyclic) without
    /// a panic.
    pub fn enter<F: FnOnce(&mut Own<()>) -> R, R>(&mut self, work: F) -> R {
        ASSOC.set(&self.data.0.assoc.clone(), || (work)(self))
    }
}

impl<'a, T: ?Sized + 'static> Own<'a, T> {
    /// Convert into an untyped version of `Own`.
    ///
    /// This is mainly useful for passing to generic functions that need to
    /// [via_untyped](Res::via_untyped)
    /// associated data.
    ///
    /// Crate-visible only because design is unfinished.
    pub(crate) fn untyped(&mut self) -> UntypedOwn {
        UntypedOwn(&self.data.0.assoc)
    }
}

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

/// A type-erased version of [Own].
///
/// Useful mainly for passing to generic functions that need to convert [Res]
/// into [Own] without knowing a concrete type. Intended for storing function
/// objects as `Fn(&mut UntypedOwn)`.
pub(crate) struct UntypedOwn<'a>(&'a Rc<AssocInner>);
