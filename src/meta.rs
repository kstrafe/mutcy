use std::{
    collections::VecDeque,
    rc::{Rc, Weak},
};

/// Defines constant metadata to be stored alongside the primary item in a
/// [KeyCell](crate::KeyCell).
///
/// # Purpose #
///
/// Metadata is constant data associated with a particular `KeyCell`. Its
/// primary purpose is to provide references to other `KeyCell`s. If these other
/// `KeyCell`s were instead stored inside the original `KeyCell`, then any
/// access to those would require us to clone them out before use.
///
/// # Examples #
///
/// The following example shows how we will need to clone out `other` because
/// there is no way to access it after we have split `this` into a `&KeyCell<_>`
/// and a `&mut Key`.
///
/// ```
/// use mutcy::{Key, KeyCell, KeyMut};
/// use std::rc::Rc;
///
/// struct A {
///     other: Rc<KeyCell<i32>>,
/// }
/// # impl mutcy::Meta for A { type Data = (); }
///
/// fn function(this: KeyMut<A>) {
///     // We require this clone...
///     let other = this.other.clone();
///     // because we can no longer access `this`...
///     let (_this, key) = Key::split(this);
///     // to increment `other`.
///     *other.borrow_mut(key) += 1;
/// }
/// ```
///
/// Metadata solves the issue of requiring clones.
///
/// ```
/// use mutcy::{Key, KeyCell, KeyMut, Meta};
/// use std::rc::Rc;
///
/// struct A {
///     // ...
/// }
///
/// impl Meta for A {
///     type Data = Rc<KeyCell<i32>>;
/// }
///
/// fn function(this: KeyMut<A>) {
///     // We don't need to clone anything before splitting...
///     let (input, key) = Key::split(this);
///     // because we can now access the `KeyCell` metadata via `meta`.
///     *input.meta().borrow_mut(key) += 1;
/// }
/// ```
pub trait Meta {
    type Data;
}

macro_rules! impl_attached_common {
    ($($ty:ty),* $(,)?) => {
        $(
            impl Meta for $ty {
                type Data = ();
            }
        )*
    };
}

impl_attached_common! {
    &str,
    (),
    String,
    bool,
    char,
    f32, f64,
    i8, i16, i32, i64, i128,
    isize,
    u8, u16, u32, u64, u128,
    usize,
}

macro_rules! impl_attached_common_generic {
    ($($ty:ident<$($generic:ident),*>),* $(,)?) => {
        $(
            impl<$($generic),*> Meta for $ty<$($generic),*> {
                type Data = ();
            }
        )*
    };
}

impl_attached_common_generic! {
    Box<T>,
    Rc<T>,
    Vec<T>,
    VecDeque<T>,
    Weak<T>,
}

macro_rules! impl_attached_tuples {
    ($(($($generic:ident),*)),* $(,)?) => {
        $(
            impl<$($generic),*> Meta for ($($generic),*,) {
                type Data = ();
            }
        )*
    };
}

impl_attached_tuples! {
    (A),
    (A, B),
    (A, B, C),
    (A, B, C, D),
    (A, B, C, D, E),
    (A, B, C, D, E, F),
}
