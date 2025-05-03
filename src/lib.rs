//! # Zero-Cost Mutable Cyclic Borrows #
//!
//! A `RefCell`-like dynamic borrowing system that permits recursive borrowing
//! with zero runtime overhead.
//!
//! This crate implements [KeyCell] of which only a single instance can be
//! mutably borrowed at a time using a [Key]. Simultaneous immutable borrows
//! are permitted.
//!
//! `Key` is a ZST, and only a single instance can exist per thread. The only
//! dynamic check this library performs is upon calling [Key::acquire] to ensure
//! that there exists no other instance in the same thread. This ensures that we
//! can only mutably borrow one `KeyCell` per thread.
//!
//! Once we have a mutable borrow of a `KeyCell` we can relinquish this borrow
//! temporarily using [Key::split_rw] to get
//! `&mut Key`, and borrow other `KeyCell`s. This is what allows us to implement
//! recursive calls with mutable access.
//!
//! # Comparison to `RefCell` #
//!
//! Unlike `RefCell`, borrows on [KeyCell]s will never fail. They also don't
//! need to perform any runtime checks. All borrow checking is performed at
//! compile time.
//!
//! 1. Borrowing is zero-cost.
//! 2. Borrowing will never fail or panic.
//! 3. Only a single `KeyCell` can be mutably borrowed per thread.
//!
//! # Alternatives #
//!
//! The core idea in this crate relies on acquiring mutable borrows through a
//! unique object (the [Key]). The same idea is implemented in a few other
//! crates.
//!
//! - [ghost-cell](https://crates.io/crates/ghost-cell)
//! - [qcell](https://crates.io/crates/qcell)
//! - [token-cell](https://crates.io/crates/token-cell)
//! - [frankencell](https://crates.io/crates/frankencell)
//!
//! # Examples #
//!
//! This crate uses [ro](KeyCell::ro) and
//! [rw](KeyCell::rw) instead of `borrow` and `borrow_mut` to access data.
//!
//! ```
//! use mutcy::{Key, KeyCell, Rw};
//!
//! let mut key = Key::acquire();
//!
//! let kc1 = KeyCell::new(0i32, ());
//! let kc2 = KeyCell::new(String::new(), ());
//!
//! *kc2.rw(&mut key) += "Hello";
//! *kc1.rw(&mut key) += 1;
//! *kc2.rw(&mut key) += "World";
//!
//! let item1 = kc1.ro(&key);
//! let item2 = kc1.ro(&key);
//!
//! println!("{} - {}", *item1, *item2);
//! ```
//!
//! With this library it's possible to define methods that take [Rw] and
//! transfer mutability to other [KeyCell]s when needed. The compile-time borrow
//! checker ensures that no mutable aliasing occurs.
//!
//! In the following example we show how a struct can accept a `self:
//! Rw<Self>` and relinquish its own borrows to access some other
//! `KeyCell`.
//!
//! ```
//! #![feature(arbitrary_self_types)]
//! use mutcy::{Key, KeyCell, Meta, Rw};
//! use std::rc::Rc;
//!
//! struct MyStruct {
//!     value: i32,
//! }
//!
//! impl MyStruct {
//!     fn my_function(self: Rw<Self>) {
//!         self.value += 1;
//!
//!         // This relinquishes any borrows to `self`.
//!         let (this, key) = Key::split_rw(self);
//!
//!         // We can now access any other KeyCell using `key`.
//!         let mut string = this.meta().other.rw(key);
//!         *string += "Hello world";
//!
//!         self.value += 1;
//!     }
//! }
//!
//! struct MyStructMeta {
//!     other: Rc<KeyCell<String>>,
//! }
//!
//! impl Meta for MyStruct {
//!     type Data = MyStructMeta;
//! }
//!
//! let mut key = Key::acquire();
//!
//! let other = Rc::new(KeyCell::new(String::new(), ()));
//!
//! let my_struct = KeyCell::new(
//!     MyStruct { value: 0 },
//!     MyStructMeta {
//!         other: other.clone(),
//!     },
//! );
//!
//! my_struct.rw(&mut key).my_function();
//!
//! println!("{}", *other.ro(&key));
//! println!("{}", my_struct.ro(&key).value);
//! ```
//!
//! # Metadata #
//!
//! [KeyCell::new] takes two arguments, the primary data to wrap, and metadata.
//! Metadata can always be accessed immutably as it does not require a [Key].
//!
//! This allows us to reference and access other [KeyCell]s without having to
//! clone an `Rc<KeyCell<_>>` out of the initial item.
//!
//! For more details see [Meta].
#![feature(arbitrary_self_types)]
#![deny(
    missing_docs,
    rustdoc::broken_intra_doc_links,
    unused_imports,
    unused_qualifications
)]

pub use self::{callback::Callback, meta::Meta, signal::Signal};
use std::{
    cell::{Cell, UnsafeCell},
    marker::PhantomData,
    ops::{Deref, DerefMut},
    rc::{Rc, Weak},
};

mod callback;
mod meta;
mod signal;

thread_local! {
    static KEY: Cell<bool> = const { Cell::new(true) }
}

/// Immutable reference to [RoGuard].
///
/// Convenience wrapper that allows the creation of methods that take `Ro`
/// without specifying lifetimes.
///
/// # Examples #
///
/// ```
/// #![feature(arbitrary_self_types)]
/// use mutcy::{Meta, Ro};
///
/// struct X;
///
/// impl Meta for X {
///     type Data = ();
/// }
///
/// impl X {
///     fn my_function(self: Ro<Self>) {
///         // ...
///     }
/// }
/// ```
pub type Ro<'a, 'b, T> = &'a RoGuard<'b, T>;

/// Mutable reference to [RwGuard].
///
/// Convenience wrapper that allows the creation of methods that take `Rw`
/// without specifying lifetimes.
///
/// # Examples #
///
/// ```
/// #![feature(arbitrary_self_types)]
/// use mutcy::{Meta, Rw};
///
/// struct X;
///
/// impl Meta for X {
///     type Data = ();
/// }
///
/// impl X {
///     fn my_function(self: Rw<Self>) {
///         // ...
///     }
/// }
/// ```
pub type Rw<'a, 'b, T> = &'a mut RwGuard<'b, T>;

/// A per-thread unique key used to access data inside [KeyCell]s.
///
/// This type enforces the existence of only a single instance of itself per
/// thread. By doing so it guards against mutable aliasing when borrowing from
/// `KeyCell`.
pub struct Key(PhantomData<*mut ()>);

impl Key {
    /// Acquire the thread-local Key.
    ///
    /// # Panics #
    ///
    /// Panics if an instance already exists for the current thread. Calling
    /// acquire after dropping the key will not panic.
    ///
    /// # Examples #
    ///
    /// ```
    /// use mutcy::Key;
    ///
    /// let key = Key::acquire();
    /// ```
    pub fn acquire() -> Self {
        KEY.with(|key| {
            assert!(key.get());
            key.set(false);
        });

        Key(PhantomData)
    }

    /// Split an [Ro] into its consitutuent [KeyCell] and immutable [Key].
    ///
    /// Similar to [split_rw](Key::split_rw). Unlike `split_rw`, the `Ro`
    /// remains accessible because multiple simultaneous immutable borrows
    /// are allowed.
    ///
    /// # Examples #
    ///
    /// ```
    /// use mutcy::{Key, KeyCell, Ro};
    ///
    /// fn function(kc1: Ro<i32>, kc2: &KeyCell<i32>) {
    ///     let (_, key) = Key::split_ro(kc1);
    ///     println!("{}", **kc1);
    ///     println!("{}", *kc2.ro(key));
    /// }
    ///
    /// let kc1 = KeyCell::new(0, ());
    /// let kc2 = KeyCell::new(10, ());
    ///
    /// let mut key = Key::acquire();
    ///
    /// let mut kc1_borrow = kc1.ro(&mut key);
    ///
    /// function(&kc1_borrow, &kc2);
    /// ```
    pub fn split_ro<'a: 'b, 'b, T: Meta>(item: &'b RoGuard<'a, T>) -> (&'b KeyCell<T>, &'b Key) {
        RoGuard::split(item)
    }

    /// Split an [Rw] into its consitutuent [KeyCell] and mutable [Key].
    ///
    /// Whenever we want to borrow another item while already holding a `Rw`
    /// we need to unborrow. This function unborrows, granting you access to
    /// the key that was used to borrow the initial `KeyCell`.
    ///
    /// # Examples #
    ///
    /// ```
    /// use mutcy::{Key, KeyCell, Rw};
    ///
    /// fn function(kc1: Rw<i32>, kc2: &KeyCell<i32>) {
    ///     **kc1 += 1; // kc1 = 1
    ///
    ///     let (kc1_ref, key) = Key::split_rw(kc1);
    ///
    ///     let mut kc2_mut = kc2.rw(key);
    ///     *kc2_mut += 1;
    ///
    ///     // Relinquish the split.
    ///     **kc1 += 1; // kc1 = 2;
    ///
    ///     // Compile error.
    ///     // *kc2_mut += 1;
    /// }
    ///
    /// let kc1 = KeyCell::new(0, ());
    /// let kc2 = KeyCell::new(10, ());
    ///
    /// let mut key = Key::acquire();
    ///
    /// let mut kc1_borrow = kc1.rw(&mut key);
    ///
    /// function(&mut kc1_borrow, &kc2);
    /// ```
    pub fn split_rw<'a: 'b, 'b, T: Meta>(
        item: &'b mut RwGuard<'a, T>,
    ) -> (&'b KeyCell<T>, &'b mut Key) {
        RwGuard::split(item)
    }
}

impl Drop for Key {
    /// Drops the key. Once the key is dropped, the next [acquire](Key::acquire)
    /// will not panic.
    fn drop(&mut self) {
        KEY.with(|key| {
            key.set(true);
        });
    }
}

/// A `RefCell`-like wrapper that can only be accessed via
/// [Key].
pub struct KeyCell<T: Meta>(UnsafeCell<T>, T::Data);

impl<T: Meta> KeyCell<T> {
    /// Creates a new `KeyCell` from an object and its associated
    /// [metadata](Meta).
    ///
    /// # Examples #
    ///
    /// ```
    /// use mutcy::KeyCell;
    ///
    /// let kc = KeyCell::new(123, ());
    /// ```
    pub fn new(item: T, meta: T::Data) -> Self {
        Self(UnsafeCell::new(item), meta)
    }

    /// Immutably borrows the wrapped value.
    ///
    /// Requires a `&Key` to ensure no mutable borrow exists.
    ///
    /// # Examples #
    ///
    /// ```
    /// use mutcy::{Key, KeyCell};
    ///
    /// let key = Key::acquire();
    /// let kc = KeyCell::new(123, ());
    ///
    /// let borrowed1 = kc.ro(&key);
    /// let borrowed2 = kc.ro(&key);
    /// ```
    pub fn ro<'a>(&'a self, key: &'a Key) -> RoGuard<'a, T> {
        RoGuard(self, key)
    }

    /// Mutably borrows the wrapped value.
    ///
    /// Requires a `&mut Key` that ensures that no other borrows exist
    /// simultaneously.
    ///
    /// # Examples #
    ///
    /// ```
    /// use mutcy::{Key, KeyCell};
    ///
    /// let mut key = Key::acquire();
    /// let kc = KeyCell::new(123, ());
    ///
    /// let borrowed1 = kc.rw(&mut key);
    ///
    /// let borrowed2 = kc.ro(&key);
    ///
    /// // This does not compile.
    /// // let _ = *borrowed1;
    /// ```
    pub fn rw<'a>(&'a self, key: &'a mut Key) -> RwGuard<'a, T> {
        RwGuard(self, key)
    }

    /// Acquire metadata. See [Meta].
    ///
    /// # Examples #
    ///
    /// ```
    /// use mutcy::{KeyCell, Meta};
    /// struct A;
    ///
    /// impl Meta for A {
    ///     type Data = i32;
    /// }
    ///
    /// let kc = KeyCell::new(A, 123);
    ///
    /// assert_eq!(*kc.meta(), 123);
    /// ```
    pub fn meta(&self) -> &T::Data {
        &self.1
    }

    /// Acquire mutable reference to metadata. See [Meta].
    ///
    /// # Examples #
    ///
    /// ```
    /// use mutcy::{KeyCell, Meta};
    /// struct A;
    ///
    /// impl Meta for A {
    ///     type Data = i32;
    /// }
    ///
    /// let mut kc = KeyCell::new(A, 123);
    ///
    /// *kc.meta_mut() = 100;
    /// assert_eq!(*kc.meta(), 100);
    /// ```
    pub fn meta_mut(&mut self) -> &mut T::Data {
        &mut self.1
    }
}

/// Wraps an immutably borrowed reference to a value in a `KeyCell`.
///
/// See [KeyCell::ro].
pub struct RoGuard<'a, T: Meta>(&'a KeyCell<T>, &'a Key);

impl<'a, T: Meta> RoGuard<'a, T> {
    fn split(this: &Self) -> (&KeyCell<T>, &Key) {
        (this.0, this.1)
    }
}

impl<'a, T: Meta> Deref for RoGuard<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.0.0.get() }
    }
}

/// Wraps a mutably borrowed reference to a value in a `KeyCell`.
///
/// See [KeyCell::rw].
pub struct RwGuard<'a, T: Meta>(&'a KeyCell<T>, &'a mut Key);

impl<'a, T: Meta> RwGuard<'a, T> {
    fn split(this: &mut Self) -> (&KeyCell<T>, &mut Key) {
        (this.0, this.1)
    }
}

impl<'a, T: Meta> Deref for RwGuard<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.0.0.get() }
    }
}

impl<'a, T: Meta> DerefMut for RwGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.0.0.get() }
    }
}

/// Converts [Rc](std::rc::Rc) or [Weak](std::rc::Weak) into a `Weak`.
///
/// Used to make the API take either an `Rc` or a `Weak`.
pub trait IntoWeak<T: Meta> {
    /// Perform the conversion.
    fn into(&self) -> Weak<KeyCell<T>>;
}

impl<T: Meta> IntoWeak<T> for Rc<KeyCell<T>> {
    fn into(&self) -> Weak<KeyCell<T>> {
        Rc::downgrade(self)
    }
}

impl<T: Meta> IntoWeak<T> for Weak<KeyCell<T>> {
    fn into(&self) -> Weak<KeyCell<T>> {
        self.clone()
    }
}
