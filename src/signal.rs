use super::{IntoWeak, Key, KeyCell, Meta, Rw};
use std::{
    any::Any,
    borrow::Cow,
    rc::{Rc, Weak},
};

#[cfg(test)]
mod tests;

type Handler<T> = dyn Fn(&mut Key, &T) -> bool;

struct Receiver<T> {
    handler: Rc<Handler<T>>,
    name: Cow<'static, str>,
    target: Weak<dyn Any>,
}

/// Holds weak references to [KeyCell]s on which callbacks can be run.
///
/// # Examples #
///
/// ```
/// use mutcy::{Key, KeyCell, Signal};
/// use std::rc::Rc;
///
/// let key = &mut Key::acquire();
///
/// let signal = Signal::new();
/// let item = Rc::new(KeyCell::new(1, ()));
///
/// signal.connect(key, &item, "a", |this, event| {
///     **this *= event;
/// });
///
/// assert_eq!(1, *item.ro(key));
///
/// signal.emit(key, 2);
/// assert_eq!(2, *item.ro(key));
///
/// signal.emit(key, 2);
/// assert_eq!(4, *item.ro(key));
///
/// signal.emit(key, 3);
/// assert_eq!(12, *item.ro(key));
/// ```
pub struct Signal<T>(Rc<KeyCell<SignalInternal<T>>>);

impl<T> Signal<T> {
    /// Creates a new `Signal`.
    pub fn new() -> Self {
        Signal(Rc::new(KeyCell::new(SignalInternal::new(), ())))
    }

    /// Connects a receiver to this signal.
    ///
    /// Each receiver has a unique identifier: `name`. Handlers are invoked
    /// according to lexicographic order; "a" runs before "b".
    ///
    /// Handlers are removed automatically if the receiver has no strong
    /// references left.
    ///
    /// # Note #
    ///
    /// Holding a `Signal` instance inside `handler` may cause a reference
    /// cycle. If the `Signal` is instead held inside `receiver`, no
    /// reference cycle will be possible.
    ///
    /// Also note that this function requires the receiver to have a strong
    /// reference. This is to prevent cases such as [Rc::new_cyclic]
    /// connecting a weak followed by an [emit](Signal::emit) causing the
    /// not-yet constructed `Rc` from being removed.
    ///
    /// # Panics #
    ///
    /// Panics if `name` already exists or there are no strong references to the
    /// receiver.
    ///
    /// # Examples #
    ///
    /// ```
    /// use mutcy::{Key, KeyCell, Rw, Signal};
    /// use std::rc::Rc;
    ///
    /// let key = &mut Key::acquire();
    ///
    /// let signal = Signal::new();
    /// let item = Rc::new(KeyCell::new(1, ()));
    ///
    /// signal.connect(key, &item, "a", |this, event| {
    ///     **this *= event;
    /// });
    /// ```
    pub fn connect<R, I, C, F>(&self, key: &mut Key, receiver: &I, name: C, handler: F)
    where
        R: Meta + 'static,
        I: IntoWeak<R>,
        C: Into<Cow<'static, str>>,
        F: Fn(Rw<R>, &T) + 'static,
    {
        self.0.rw(key).connect(receiver, name, handler);
    }

    /// Emits a value to all receivers.
    ///
    /// Since [KeyCell] permits recursive borrowing, it is possible to call
    /// [Signal::emit] recursively. If that happens, the most deeply nested
    /// `emit` call invalidates the preceding emit call. Once the call stack
    /// returns to the preceding `emit` call, we immediately return from it. We
    /// do this because we can assume that subsequent emits have more
    /// up-to-date information to emit.
    ///
    /// This allows us to add a receiver that modifies the data and re-emits.
    pub fn emit(&self, key: &mut Key, item: T) {
        self.0.rw(key).emit(item);
    }

    /// Disconnects a handler.
    ///
    /// If `order` does not exist in this signal, then no operation happens.
    pub fn disconnect<C>(&self, key: &mut Key, order: C)
    where
        C: Into<Cow<'static, str>>,
    {
        self.0.rw(key).disconnect(order);
    }
}

impl<T> Clone for Signal<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T> Default for Signal<T> {
    fn default() -> Self {
        Self::new()
    }
}

struct SignalInternal<T> {
    receivers: Vec<Receiver<T>>,
    index: usize,
    depth: usize,
    top: usize,
}

impl<T> SignalInternal<T> {
    pub fn new() -> Self {
        Self {
            receivers: Vec::new(),
            index: 0,
            depth: 0,
            top: 0,
        }
    }

    pub fn connect<R, I, C, F>(self: Rw<Self>, receiver: &I, name: C, handler: F)
    where
        R: Meta + 'static,
        I: IntoWeak<R>,
        C: Into<Cow<'static, str>>,
        F: Fn(Rw<R>, &T) + 'static,
    {
        let name = name.into();
        let receiver = receiver.into();
        let target: Weak<_> = receiver.clone();

        assert!(
            Weak::strong_count(&target) > 0,
            "Signal::connect: object must have a strong reference"
        );

        let handler: Rc<Handler<T>> = Rc::new(move |key, item| {
            if let Some(receiver) = receiver.upgrade() {
                (handler)(&mut receiver.rw(key), item);
                false
            } else {
                true
            }
        });

        match self.receivers.binary_search_by(|x| x.name.cmp(&name)) {
            Ok(idx) => {
                if Weak::strong_count(&self.receivers[idx].target) == 0 {
                    self.receivers[idx] = Receiver {
                        handler,
                        name,
                        target,
                    };
                } else {
                    panic!("Signal::connect name already exists: {:?}", name);
                }
            }
            Err(idx) => {
                self.receivers.insert(
                    idx,
                    Receiver {
                        handler,
                        name,
                        target,
                    },
                );

                if idx < self.index {
                    self.index -= 1;
                }
            }
        };
    }

    pub fn emit(self: Rw<Self>, item: T) {
        self.top = self.depth;
        let top = self.top;
        self.depth += 1;
        self.index = 0;

        struct DeferDec<'a, 'b, T>(Rw<'a, 'b, SignalInternal<T>>);

        impl<T> Drop for DeferDec<'_, '_, T> {
            fn drop(&mut self) {
                self.0.depth -= 1;
            }
        }

        let this = DeferDec(self);

        while let Some(receiver) = this.0.receivers.get(this.0.index) {
            let receiver = receiver.handler.clone();
            this.0.index += 1;

            let (_, key) = Key::split_rw(this.0);

            if (receiver)(key, &item) {
                this.0.index -= 1;
                let index = this.0.index;
                this.0.receivers.remove(index);
            }

            if this.0.top > top {
                break;
            }
        }

        drop(this);
    }

    pub fn disconnect<C>(self: Rw<Self>, name: C)
    where
        C: Into<Cow<'static, str>>,
    {
        let name = name.into();
        let idx = match self.receivers.binary_search_by(|x| x.name.cmp(&name)) {
            Ok(idx) => idx,
            Err(_) => return,
        };

        self.receivers.remove(idx);

        if idx < self.index {
            self.index -= 1;
        }
    }
}

impl<T> Meta for SignalInternal<T> {
    type Data = ();
}
