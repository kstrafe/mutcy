use crate::{IntoWeak, Key, Meta, Rw};
use std::rc::Rc;

#[cfg(test)]
mod tests;

type Handler<I, O> = Rc<dyn Fn(&mut Key, I) -> Option<O>>;

/// Callback defined on a [KeyCell](crate::KeyCell).
///
/// Holds a weak reference to a `KeyCell` together with a callback function.
///
/// # Examples #
///
/// ```
/// use mutcy::{Callback, Key, KeyCell, Rw};
/// use std::rc::Rc;
///
/// let item = Rc::new(KeyCell::new(0, ()));
/// let cb = Callback::new(&item, |item: Rw<i32>, arg: &str| {
///     println!("Argument: {}", arg);
///     **item += 1;
/// });
///
/// let key = &mut Key::acquire();
/// cb.call(key, "a string");
/// ```
pub struct Callback<I, O>(Handler<I, O>);

impl<I, O> Callback<I, O> {
    /// Create a new callback.
    pub fn new<W, T, F>(receiver: &W, handler: F) -> Self
    where
        W: IntoWeak<T>,
        T: Meta + 'static,
        F: Fn(Rw<T>, I) -> O + 'static,
    {
        let receiver = receiver.into();
        Self(Rc::new(move |key, input| {
            receiver.upgrade().map(|x| (handler)(&mut x.rw(key), input))
        }))
    }

    /// Invoke the callback.
    ///
    /// # Returns #
    ///
    /// Returns `None` if the `Weak<KeyCell<_>>` has no strong references.
    pub fn call(&self, key: &mut Key, input: I) -> Option<O> {
        (self.0)(key, input)
    }
}
