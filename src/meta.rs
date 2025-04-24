use std::{
    collections::VecDeque,
    rc::{Rc, Weak},
};

/// Defines metadata to be stored alongside the primary item in a
/// [KeyCell](crate::KeyCell).
///
/// # Purpose #
///
/// Metadata is data associated with a particular `KeyCell`. Its
/// primary purpose is to provide references to other `KeyCell`s. If these other
/// `KeyCell`s were instead stored inside the original `KeyCell`, then any
/// access to those would require us to clone them out before use.
///
/// The key constraint on metadata is that it is immutable so long as KeyCell
/// is immutable (e.g. `Rc<KeyCell<_>>`), so it's not possible to mutate
/// metadata. Interior mutability could be used (`RefCell`), but then panics may
/// occur.
///
/// # Examples #
///
/// The following example shows how we will need to clone out `other` because
/// there is no way to access it after we have split `this` into a `&KeyCell<_>`
/// and a `&mut Key`.
///
/// ```
/// use mutcy::{Key, KeyCell, Rw};
/// use std::rc::Rc;
///
/// struct A {
///     other: Rc<KeyCell<i32>>,
/// }
/// # impl mutcy::Meta for A { type Data = (); }
///
/// fn function(this: Rw<A>) {
///     // We require this clone...
///     let other = this.other.clone();
///     // because we can no longer access `this.other`...
///     let (_this, key): (&KeyCell<_>, &mut Key) = Key::split_rw(this);
///     // to increment `other`.
///     *other.rw(key) += 1;
/// }
/// ```
///
/// Metadata solves the issue of requiring clones.
///
/// ```
/// use mutcy::{Key, KeyCell, Meta, Rw};
/// use std::rc::Rc;
///
/// struct A {}
///
/// impl Meta for A {
///     type Data = Rc<KeyCell<i32>>;
/// }
///
/// fn function(this: Rw<A>) {
///     // We don't need to clone anything before splitting...
///     let (input, key) = Key::split_rw(this);
///     // because we can now access the `KeyCell` metadata via `meta`.
///     *input.meta().rw(key) += 1;
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
