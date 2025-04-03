//! # Mutable Cyclic Borrows #
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
//! # Note #
//!
//! This crate currently requires *nightly* Rust.
//!
//! Note that arbitrary self types `fn name(self: &mut Mut<T>)` are not yet
//! stable. These can be used on nightly using
//! `#![feature(arbitrary_self_types)]`.
//!
//! While it is possible to use this crate without `arbitrary_self_types`, it
//! makes working with this crate impractical.
//!
//! # Example #
//!
//! ```
//! #![feature(arbitrary_self_types)]
//! use mutcy::{Assoc, Mut, Res};
//!
//! // Create a new association for our data. Every `Res` is associated with some `Assoc`.
//! let mut assoc = Assoc::new();
//!
//! // Create two associated objects. See [Res::new] on how to avoid having to pass `&assoc`.
//! let a = Res::new_in(A { b: None, x: 0 }, &assoc);
//! let b = Res::new_in(B { a: a.clone(), y: 0 }, &assoc);
//!
//! // Acquire the initial `Mut` which we need to access `Res` objects.
//! let key: &mut Mut<()> = &mut assoc.key();
//!
//! // Before we can mutate `a`, we need to call `mutate().via(x)`. This relinquishes all existing
//! // borrows acquired via `x`'s Deref/DerefMut implementation.
//! a.mutate().via(key).b = Some(b);
//!
//! // Call a method on `A`
//! a.mutate().via(key).call_a(5);
//!
//! // You can store the created `Mut` from `via` onto the stack.
//! let mut a_mut: Mut<A> = a.mutate().via(key);
//!
//! // Note, the following fails to compile because of `a_mut`'s dependency on `x`. This prevents
//! // Rust's requirements for references from being violated.
//!
//! // let _: () = **key;
//!
//! // error[E0502]: cannot borrow `*x` as immutable because it is also borrowed as mutable
//! //   --> src/lib.rs:38:18
//! //    |
//! // 27 |     let mut a_mut: Mut<A> = a.mutate().via(x);
//! //    |                                    - mutable borrow occurs here
//! // ...
//! // 32 |     let _: () = **x;
//! //    |                  ^^ immutable borrow occurs here
//! // ...
//! // 47 |     a_mut.my_method();
//! //    |     ----- mutable borrow later used here
//!
//! // Because this `Mut` (`a_mut`) still exists.
//! a_mut.my_method();
//!
//! struct A {
//!     b: Option<Res<B>>,
//!     x: i32,
//! }
//!
//! impl A {
//!     fn call_a(self: &mut Mut<Self>, count: usize) {
//!         // Mutate through &mut Self.
//!         self.x += 1;
//!
//!         println!(">>> A: {}", count);
//!         self.b
//!             .as_ref()
//!             .unwrap()
//!             .mutate()
//!             .via(self)
//!             .call_b(count - 1);
//!         println!("<<< A: {}", count);
//!
//!         // Mutate again, this is valid after the call to `b` which has called back into here
//!         // because we reborrow &mut Self here.
//!         self.x -= 1;
//!     }
//!
//!     fn remove_b(self: &mut Mut<Self>) {
//!         // This does not drop `B` yet even though it's the only direct `Res<B>` object referring
//!         // to the underlying data.
//!         // The call stack will still refer to this `B` after this call finishes.
//!         // Because `b` was invoked on as `self.b.as_ref().unwrap().mutate().via(self)`, we have
//!         // created a clone of the `Res<B>` at multiple locations on the call stack.
//!         // This ensures that `B` will exist as long as some part of the call stack is still
//!         // using it.
//!         self.b = None;
//!     }
//!
//!     fn my_method(self: &mut Mut<Self>) {
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
//!     fn call_b(self: &mut Mut<Self>, count: usize) {
//!         self.y += 1;
//!
//!         println!(">>> B: {}", count);
//!         let mut a = self.a.mutate().via(self);
//!         if count > 1 {
//!             a.call_a(count - 1);
//!         } else {
//!             a.remove_b();
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
//! # Drop guarantees
//!
//! The system maintains object validity through two invariants:
//!
//! 1. An object `T` will only be dropped when:
//!    - All [`Res<T>`] handles pointing to it have been dropped
//!    - All active [`Mut<T>`] borrow guards to it have been dropped
//!
//! This prevents dangling references in call chains like:
//! ```text
//! A → B → C → B // Last B access can remove C, into which we return. Will stay valid.
//! ```
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
//! fn traverse(node: &mut Mut<Node>) {
//!     if let Some(child) = &node.child {
//!         child.mutate().via(node).parent = None; // Would invalidate parent
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
//! Dropping `T` occurs immediately when all `Res<T>` and `Mut<T>` objects
//! for that instance of `T` have been dropped.
//!
//! Deallocation of memory backing that
//! `T` occurs immediately if `T` was dropped and no [WeakRes] instances to that
//! `T` exist.
#![feature(arbitrary_self_types)]
#![feature(coerce_unsized)]
#![feature(unsize)]
use std::{
    cell::UnsafeCell,
    marker::{PhantomData, Unsize},
    ops::{CoerceUnsized, Deref, DerefMut},
    rc::{Rc, Weak},
};

scoped_tls::scoped_thread_local!(static ASSOC: Rc<AssocInner>);

/// Association of pointers.
pub struct Assoc(Rc<AssocInner>, Res<()>);

impl Assoc {
    /// Create new association.
    pub fn new() -> Self {
        Self::default()
    }

    /// Acquire the key to the association allowing you to perform operations on
    /// [Res].
    ///
    /// The returned key is just a [Mut] to `()`. You can use this object as the
    /// key in [Res::via].
    ///
    /// ```
    /// use mutcy::{Assoc, Res};
    ///
    /// let mut assoc = Assoc::new();
    /// let key = &mut assoc.key();
    ///
    /// // You can use the key, `Assoc`, or another `Res` as an argument to `Res::new_in`.
    /// let resource = Res::new_in(123, key);
    /// *resource.via(key) += 1;
    /// ```
    pub fn key<'a>(&'a mut self) -> Mut<'a, ()> {
        Mut {
            scope: PhantomData,
            data: self.1.clone(),
        }
    }

    /// Enters the association context to perform mutations.
    ///
    /// Grants you the initial [Mut] used to transform [Res] using
    /// [via](Res::via), also installs a
    /// [scoped_thread_local](scoped_tls::scoped_thread_local) that allows
    /// you to call [Res::new] without a panic.
    pub fn enter<F: FnOnce(&mut Mut<()>) -> R, R>(&mut self, work: F) -> R {
        let mut item: Mut<()> = Mut {
            scope: PhantomData,
            data: self.1.clone(),
        };

        ASSOC.set(&self.0, || (work)(&mut item))
    }
}

impl Default for Assoc {
    fn default() -> Self {
        let inner = Rc::new(AssocInner);
        let root = Res::new_in((), &inner);
        Self(inner, root)
    }
}

mod seal {
    use crate::AssocInner;
    use std::rc::Rc;

    pub trait Sealed {
        #[allow(private_interfaces)]
        fn assoc_inner(&self) -> &Rc<AssocInner>;
    }
}

/// Sealed trait to allow [Res::new_in] and [Res::new_cyclic_in] to use [Assoc],
/// [Mut], or [Res] as an association source.
pub trait Associated: seal::Sealed {}

#[allow(private_interfaces)]
impl seal::Sealed for Assoc {
    fn assoc_inner(&self) -> &Rc<AssocInner> {
        &self.0
    }
}

#[allow(private_interfaces)]
impl seal::Sealed for Rc<AssocInner> {
    fn assoc_inner(&self) -> &Rc<AssocInner> {
        self
    }
}

#[allow(private_interfaces)]
impl<'a, T: 'static> seal::Sealed for Mut<'a, T> {
    fn assoc_inner(&self) -> &Rc<AssocInner> {
        &self.data.0.scope
    }
}

#[allow(private_interfaces)]
impl<T> seal::Sealed for Res<T> {
    fn assoc_inner(&self) -> &Rc<AssocInner> {
        &self.0.scope
    }
}

impl Associated for Assoc {}
#[doc(hidden)]
impl Associated for Rc<AssocInner> {}
impl<T: 'static> Associated for Res<T> {}
impl<'a, T: 'static> Associated for Mut<'a, T> {}

pub(crate) struct AssocInner;

/// [Assoc]iated reference-counted handle to data.
///
/// This item's `T` can only be mutably accessed using [via](Res::via).
///
/// `Res` stands for resource.
///
/// ```
/// use mutcy::{Assoc, Res};
///
/// let mut assoc = Assoc::new();
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
    /// Create a new `Res` associated to the currently [enter](Assoc::enter)ed
    /// [Assoc].
    ///
    /// # Panics
    ///
    /// This function will panic if not (transitively) called from within
    /// [Assoc::enter]'s `work` function.
    ///
    /// # Examples
    ///
    /// ```
    /// use mutcy::{Assoc, Res};
    ///
    /// let mut assoc = Assoc::new();
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

    /// Create a new cyclic `Res` associated with the currently [enter](Assoc::enter)ed [Assoc].
    ///
    /// # Panics
    ///
    /// This function will panic if not (transitively) called from within
    /// [Assoc::enter]'s `work` function.
    ///
    /// # Examples
    /// ```
    /// use mutcy::{Assoc, Res, WeakRes};
    ///
    /// let mut assoc = Assoc::new();
    ///
    /// struct MyItem(i32, WeakRes<Self>);
    ///
    /// assoc.enter(|x| {
    ///     let item = Res::new_cyclic(|weak| MyItem(41, weak.clone()));
    ///
    ///     let mut data = item.via(x);
    ///     data.0 += 1;
    ///
    ///     let data_reborrow = data.1.upgrade().unwrap().mutate().via(x);
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
    /// use mutcy::{Assoc, Res, WeakRes};
    ///
    /// let mut assoc = Assoc::new();
    ///
    /// struct MyItem(i32, WeakRes<Self>);
    /// let item = Res::new_cyclic_in(|weak| MyItem(41, weak.clone()), &assoc);
    ///
    /// assoc.enter(|x| {
    ///     let mut data = item.via(x);
    ///     data.0 += 1;
    ///
    ///     let data_reborrow = data.1.upgrade().unwrap().mutate().via(x);
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
            let weak = WeakRes::new(weak.clone());
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
    ///     fn method(self: &mut Mut<Self>) {
    ///         // ERROR: Cannot borrow `self` mutably more than once
    ///         // self.inner.via(self);
    ///
    ///         // OK
    ///         let inner = self.inner.mutate().via(self);
    ///     }
    /// }
    /// ```
    ///
    /// [`via`]: Res::via
    pub fn mutate(&self) -> Self {
        self.clone()
    }

    /// Relinquish a previous `Mut` and creates a `Mut` of `self`.
    ///
    /// Since references to `T` from `Mut<T>` require [Deref] or [DerefMut],
    /// calling this function will relinquish all such borrows on `Mut<T>`.
    /// This makes it safe to acquire a mutable reference recursively.
    ///
    /// In effect, there exists only a single accessible `Mut<T>` for any
    /// `Res<T>` in a single association. This function checks if the
    /// association matches to prevent multiple `Mut<T>` being accessible
    /// for a `Res<T>` in the same [Assoc]. [Assoc::enter] borrows the
    /// association mutably, thus guaranteeing that only one `Mut<T>` can be
    /// live per association.
    ///
    /// # Panics #
    ///
    /// Will panic if the arguments' associated [Assoc]s differ.
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
    ///     fn method(self: &mut Mut<Self>) {
    ///         let value_reference: &mut i32 = &mut self.value;
    ///
    ///         // `via` relinquishes `value_reference`, because it has a dependency on
    ///         // `self` that conflicts with `via`.
    ///         self.this.mutate().via(self);
    ///
    ///         // ERROR: We cannot now use `value_reference`.
    ///         // *value_reference += 1;
    ///
    ///         // We need to reborrow instead.
    ///         let value_reference: &mut i32 = &mut self.value;
    ///     }
    /// }
    /// ```
    pub fn via<'a: 'b, 'b, A: 'static>(self, source: &'a mut Mut<A>) -> Mut<'b, T> {
        assert!(
            Rc::ptr_eq(&self.0.scope, &source.data.0.scope),
            "assoc is not identical"
        );

        Mut {
            scope: source.scope,
            data: self,
        }
    }

    /// Create a weakly referencing version this `Res`.
    ///
    /// See [Rc::downgrade].
    pub fn downgrade(this: &Res<T>) -> WeakRes<T> {
        WeakRes::new(Rc::downgrade(&this.0))
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
    scope: Rc<AssocInner>,
    data: UnsafeCell<T>,
}

impl<T: 'static> ResInner<T> {
    fn new(scope: Rc<AssocInner>, data: T) -> Self {
        Self {
            scope,
            data: UnsafeCell::new(data),
        }
    }
}

/// Non-owning version of [Res] similar to [Weak].
pub struct WeakRes<T: ?Sized + 'static>(Weak<ResInner<T>>);

impl<T: ?Sized + 'static> WeakRes<T> {
    fn new(weak: Weak<ResInner<T>>) -> Self {
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

/// Mutable borrow guard providing access to associated data.
///
/// Implements [`Deref`]/[`DerefMut`] for direct access to the underlying value.
/// While this guard exists, other borrows through the same association are
/// suspended to prevent mutable aliasing.
pub struct Mut<'a, T: ?Sized + 'static> {
    scope: PhantomData<&'a ()>,
    data: Res<T>,
}

impl<'a, T: ?Sized + 'static> Deref for Mut<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: The existence and accessibility of this `Mut` guarantees that there
        // is no other live reference to this data.
        //
        // Using a different `Assoc` followed by `Res::via` will result in a panic as
        // documented in `Res::via`. This guarantees that there exists only one
        // accessible `Mut<T>` for a set or `Res` associated with an `Assoc`.
        unsafe { self.data.as_ref() }
    }
}

impl<'a, T: ?Sized + 'static> DerefMut for Mut<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: The existence and accessibility of this `Mut` guarantees that there
        // is no other live reference to this data.
        //
        // Using a different `Assoc` followed by `Res::via` will result in a panic as
        // documented in `Res::via`. This guarantees that there exists only one
        // accessible `Mut<T>` for a set or `Res` associated with an `Assoc`.
        unsafe { self.data.as_mut() }
    }
}
