//! # Zero-Cost Mutable Cyclic Borrows #
//!
//! A `RefCell`-like dynamic borrowing system that permits recursive borrowing
//! with zero runtime overhead.
//!
//! This crate implements [KeyCell] of which only a single instance can be
//! mutably borrowed at a time using a [Key]. Simultaneous immutable borrows
//! are permitted.
//!
//! [Key] is a ZST, and only a single instance can exist per thread. The only
//! dynamic check this library performs is upon calling [Key::acquire] to ensure
//! that there exists no other instance.
//!
//! # Comparison to `RefCell` #
//!
//! Unlike `RefCell`, borrows on [KeyCell]s will never fail. They also don't
//! need to perform any runtime checks. All borrow checking is performed at
//! compile time.
//!
//! 1. Borrowing is zero-cost.
//! 2. Borrowing will never fail or panic.
//! 3. Only a single [KeyCell] can be mutably borrowed per thread.
//!
//! # Examples #
//!
//! This crate uses [borrow](KeyCell::borrow) and
//! [borrow_mut](KeyCell::borrow_mut) to access data.
//!
//! ```
//! use mutcy::{Key, KeyCell, KeyMut};
//!
//! let mut key = Key::acquire();
//!
//! let kc1 = KeyCell::new(0i32, ());
//! let kc2 = KeyCell::new(String::new(), ());
//!
//! *kc2.borrow_mut(&mut key) += "Hello";
//! *kc1.borrow_mut(&mut key) += 1;
//! *kc2.borrow_mut(&mut key) += "World";
//!
//! let item1 = kc1.borrow(&key);
//! let item2 = kc1.borrow(&key);
//!
//! println!("{} - {}", *item1, *item2);
//! ```
//!
//! With this library it's possible to define methods that take [KeyMut] and
//! transfer mutability to other [KeyCell]s when needed. The compile-time borrow
//! checker ensures that no mutable aliasing occurs.
//!
//! In the following example we show how a struct can accept a `self:
//! KeyMut<Self>` and relinquish its own borrows to access some other
//! `KeyCell`.
//!
//! ```
//! #![feature(arbitrary_self_types)]
//! use mutcy::{Key, KeyCell, KeyMut, Meta};
//! use std::rc::Rc;
//!
//! struct MyStruct {
//!     value: i32,
//! }
//!
//! impl MyStruct {
//!     fn my_function(self: KeyMut<Self>) {
//!         self.value += 1;
//!
//!         // This relinquishes any borrows to `self`.
//!         let (this, key) = Key::split(self);
//!
//!         // We can now access any other KeyCell using `key`.
//!         let mut string = this.meta().other.borrow_mut(key);
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
//! my_struct.borrow_mut(&mut key).my_function();
//!
//! println!("{}", *other.borrow(&key));
//! println!("{}", my_struct.borrow(&key).value);
//! ```
//!
//! For more information on metadata see [Meta].
pub use self::meta::Meta;
use std::{
    cell::{Cell, UnsafeCell},
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

mod meta;

thread_local! {
    static KEY: Cell<bool> = const { Cell::new(true) }
}

/// Reference to [KeyCellRef].
pub type KeyRef<'a, T> = &'a KeyCellRef<'a, T>;

/// Mutable reference to [KeyCellMut].
pub type KeyMut<'a, T> = &'a mut KeyCellMut<'a, T>;

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

    /// Split a [KeyMut] into its consitutuent [KeyCell] and [Key].
    ///
    /// Whenever we want to borrow another item while already holding a `KeyMut`
    /// we need to unborrow. This function unborrows, granting you access to
    /// the key that was used to borrow the initial `KeyCell`.
    ///
    /// # Examples #
    ///
    /// ```
    /// use mutcy::{Key, KeyCell, KeyMut};
    ///
    /// fn function(kc1: KeyMut<i32>, kc2: &KeyCell<i32>) {
    ///     **kc1 += 1; // kc1 = 1
    ///
    ///     let (kc1_ref, key) = Key::split(kc1);
    ///
    ///     let mut kc2_mut = kc2.borrow_mut(key);
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
    /// let mut kc1_borrow = kc1.borrow_mut(&mut key);
    ///
    /// function(&mut kc1_borrow, &kc2);
    /// ```
    pub fn split<'a: 'b, 'b, T: Meta>(
        item: &'b mut KeyCellMut<'a, T>,
    ) -> (&'b KeyCell<T>, &'b mut Key) {
        KeyCellMut::split(item)
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
    pub fn new(item: T, attached: T::Data) -> Self {
        Self(UnsafeCell::new(item), attached)
    }

    /// Immutably borrows the wrapped value.
    ///
    /// # Examples #
    ///
    /// ```
    /// use mutcy::{Key, KeyCell};
    ///
    /// let key = Key::acquire();
    /// let kc = KeyCell::new(123, ());
    ///
    /// let borrowed1 = kc.borrow(&key);
    /// let borrowed2 = kc.borrow(&key);
    /// ```
    pub fn borrow<'a>(&'a self, _key: &'a Key) -> KeyCellRef<'a, T> {
        KeyCellRef(self)
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
    /// let borrowed1 = kc.borrow_mut(&mut key);
    ///
    /// let borrowed2 = kc.borrow(&key);
    ///
    /// // This does not compile.
    /// // let _ = *borrowed1;
    /// ```
    pub fn borrow_mut<'a>(&'a self, key: &'a mut Key) -> KeyCellMut<'a, T> {
        KeyCellMut(self, key)
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
/// See [KeyCell::borrow].
pub struct KeyCellRef<'a, T: Meta>(&'a KeyCell<T>);

impl<'a, T: Meta> Deref for KeyCellRef<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.0.0.get() }
    }
}

/// Wraps a mutably borrowed reference to a value in a `KeyCell`.
///
/// See [KeyCell::borrow_mut].
pub struct KeyCellMut<'a, T: Meta>(&'a KeyCell<T>, &'a mut Key);

impl<'a, T: Meta> KeyCellMut<'a, T> {
    fn split(this: &mut Self) -> (&KeyCell<T>, &mut Key) {
        (this.0, this.1)
    }
}

impl<'a, T: Meta> Deref for KeyCellMut<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.0.0.get() }
    }
}

impl<'a, T: Meta> DerefMut for KeyCellMut<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.0.0.get() }
    }
}
