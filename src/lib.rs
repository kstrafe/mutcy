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
pub(crate) use self::{associnner::AssocInner, res::ResInner, seal::Sealed};
pub use self::{callback::Callback, own::Own, res::Res, weakres::WeakRes};
use std::rc::Rc;

mod associnner;
mod callback;
mod own;
mod res;
mod seal;
mod weakres;

scoped_tls::scoped_thread_local!(static ASSOC: Rc<AssocInner>);

/// Convenience type over [Own] allowing self methods as `self: Mut<Self>`.
///
/// It is possible to write `self: &mut Own<Self>` but it's quite noisy. This
/// type serves as a convenience wrapper for methods such that they can be
/// written as `self: Mut<Self>`.
///
/// # Examples
///
/// ```
/// #![feature(arbitrary_self_types)]
/// use mutcy::Mut;
///
/// struct X(i32);
///
/// impl X {
///     fn my_method(self: Mut<X>) {
///         self.0 += 1;
///     }
/// }
/// ```
pub type Mut<'a, 'b, T> = &'a mut Own<'b, T>;

/// Sealed trait to allow [Res::new_in] and [Res::new_cyclic_in] to use
/// [Mut], or [Res] as an association source.
pub trait Associated: Sealed {}

/// A type-erased version of [Own].
///
/// Useful mainly for passing to generic functions that need to convert [Res]
/// into [Own] without knowing a concrete type. Intended for storing function
/// objects as `Fn(&mut UntypedOwn)`.
pub(crate) struct UntypedOwn<'a>(&'a Rc<AssocInner>);

#[allow(private_interfaces)]
impl<'a> Sealed for UntypedOwn<'a> {
    fn assoc(&self) -> &Rc<AssocInner> {
        self.0
    }
}
