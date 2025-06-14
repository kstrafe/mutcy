use self::fractional_index::{FractionalIndex, FractionalIndexType};
use super::{IntoWeak, Key, KeyCell, Meta, Rw};
use std::rc::{Rc, Weak};

mod fractional_index;
#[cfg(test)]
mod tests;

type Handler<T> = dyn Fn(&mut Key, &T) -> bool;

struct Receiver<T> {
    handler: Rc<Handler<T>>,
    relative_index: FractionalIndexType,
    id: u64,
}

trait Disconnectable {
    fn disconnect(&self, key: &mut Key, id: u64);
}

impl<T> Disconnectable for KeyCell<SignalInner<T>> {
    fn disconnect(&self, key: &mut Key, id: u64) {
        self.rw(key).disconnect(id);
    }
}

/// References a connection created via [Signal::connect].
pub struct Connection {
    inner: Rc<dyn Disconnectable>,
    id: u64,
}

impl Connection {
    /// Disconnect this connection.
    pub fn disconnect(self, key: &mut Key) {
        self.inner.disconnect(key, self.id);
    }
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
/// signal.connect(key, &item, |this, event| {
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
///
/// # Connection Ordering #
///
/// [connect](Signal::connect)ions are invoked upon a call to
/// [emit](Signal::emit). The order of these invocations corresponds
/// to the order in which [connect](Signal::connect) was called.
///
/// Using [before](Signal::before) or [after](Signal::after) allows different
/// ordering using fractional indexing.
///
/// ```
/// use mutcy::{Key, KeyCell, Rw, Signal};
/// use std::rc::Rc;
///
/// let key = &mut Key::acquire();
///
/// let signal = Signal::new();
/// let item = Rc::new(KeyCell::new(0, ()));
///
/// signal.before().unwrap().connect(key, &item, |this, event| {
///     **this *= event;
/// });
/// ```
pub struct Signal<T> {
    inner: Rc<KeyCell<SignalInner<T>>>,
    index: FractionalIndex,
}

impl<T: 'static> Signal<T> {
    /// Creates a new `Signal`.
    pub fn new() -> Self {
        Signal {
            inner: Rc::new(KeyCell::new(SignalInner::new(), ())),
            index: FractionalIndex::new(),
        }
    }

    /// Connects a receiver to this signal.
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
    /// # Ordering #
    ///
    /// Handlers are invoked in the same order in which they were `connect`ed.
    /// To specify a different ordering, see [Signal::before] and
    /// [Signal::after].
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
    /// signal.connect(key, &item, |this, event| {
    ///     **this *= event;
    /// });
    /// ```
    pub fn connect<R, I, F>(&self, key: &mut Key, receiver: &I, handler: F) -> Connection
    where
        R: Meta + 'static,
        I: IntoWeak<R>,
        F: Fn(Rw<R>, &T) + 'static,
    {
        let id = self
            .inner
            .rw(key)
            .connect(receiver, self.index.value(), handler);

        Connection {
            inner: self.inner.clone(),
            id,
        }
    }

    /// Creates a [Signal] to which connections will be invoked before the
    /// current signal.
    ///
    /// Normally, connections are invoked by the order in which their respective
    /// [connect](Signal::connect)s
    /// were called.
    ///
    /// # Examples #
    ///
    /// ```
    /// use mutcy::{Key, KeyCell, Rw, Signal};
    /// use std::{cell::RefCell, rc::Rc};
    ///
    /// let key = &mut Key::acquire();
    ///
    /// let signal = Signal::new();
    /// let shared = Rc::new(RefCell::new(Vec::new()));
    ///
    /// let item = Rc::new(KeyCell::new(1, ()));
    ///
    /// let shared_clone = shared.clone();
    /// signal.connect(key, &item, move |this, event| {
    ///     shared_clone.borrow_mut().push(1);
    ///     println!("This runs after");
    /// });
    ///
    /// let shared_clone = shared.clone();
    /// signal
    ///     .before()
    ///     .unwrap()
    ///     .connect(key, &item, move |this, event| {
    ///         shared_clone.borrow_mut().push(0);
    ///         println!("This runs before");
    ///     });
    ///
    /// signal.emit(key, ());
    /// assert_eq!(&*shared.borrow(), &[0, 1]);
    /// ```
    pub fn before(&self) -> Option<Self> {
        self.index.left().map(|index| Self {
            inner: self.inner.clone(),
            index,
        })
    }

    /// Creates a [Signal] to which connections will be invoked after the
    /// current signal.
    ///
    /// Normally, connections are invoked by the order in which their respective
    /// [connect](Signal::connect)s
    /// were called.
    ///
    /// # Examples #
    ///
    /// ```
    /// use mutcy::{Key, KeyCell, Rw, Signal};
    /// use std::{cell::RefCell, rc::Rc};
    ///
    /// let key = &mut Key::acquire();
    ///
    /// let signal = Signal::new();
    /// let shared = Rc::new(RefCell::new(Vec::new()));
    ///
    /// let item = Rc::new(KeyCell::new(1, ()));
    ///
    /// let shared_clone = shared.clone();
    /// signal
    ///     .after()
    ///     .unwrap()
    ///     .connect(key, &item, move |this, event| {
    ///         shared_clone.borrow_mut().push(1);
    ///         println!("This runs after");
    ///     });
    ///
    /// let shared_clone = shared.clone();
    /// signal.connect(key, &item, move |this, event| {
    ///     shared_clone.borrow_mut().push(0);
    ///     println!("This runs before");
    /// });
    ///
    /// signal.emit(key, ());
    /// assert_eq!(&*shared.borrow(), &[0, 1]);
    /// ```
    pub fn after(&self) -> Option<Self> {
        self.index.right().map(|index| Self {
            inner: self.inner.clone(),
            index,
        })
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
        self.inner.rw(key).emit(item);
    }
}

impl<T> Clone for Signal<T> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            index: self.index,
        }
    }
}

impl<T: 'static> Default for Signal<T> {
    fn default() -> Self {
        Self::new()
    }
}

struct SignalInner<T> {
    receivers: Vec<Receiver<T>>,
    index: usize,
    depth: usize,
    top: usize,
    idgen: u64,
}

impl<T> SignalInner<T> {
    pub fn new() -> Self {
        Self {
            receivers: Vec::new(),
            index: 0,
            depth: 0,
            top: 0,
            idgen: 0,
        }
    }

    pub fn connect<R, I, F>(
        self: Rw<Self>,
        receiver: &I,
        order: FractionalIndexType,
        handler: F,
    ) -> u64
    where
        R: Meta + 'static,
        I: IntoWeak<R>,
        F: Fn(Rw<R>, &T) + 'static,
    {
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

        let id = self.idgen;
        self.idgen += 1;

        match self
            .receivers
            .binary_search_by(|x| x.relative_index.cmp(&order))
        {
            Ok(idx) => {
                self.receivers.insert(
                    idx + 1,
                    Receiver {
                        handler,
                        relative_index: order,
                        id,
                    },
                );
            }
            Err(idx) => {
                self.receivers.insert(
                    idx,
                    Receiver {
                        handler,
                        relative_index: order,
                        id,
                    },
                );

                if idx < self.index {
                    self.index -= 1;
                }
            }
        };

        id
    }

    pub fn emit(self: Rw<Self>, item: T) {
        self.top = self.depth;
        let top = self.top;
        self.depth += 1;
        self.index = 0;

        struct DeferDec<'a, 'b, T>(Rw<'a, 'b, SignalInner<T>>);

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

    fn disconnect(self: Rw<Self>, id: u64) {
        let Some(idx) = self.receivers.iter().position(|x| x.id == id) else {
            return;
        };

        self.receivers.remove(idx);

        if idx < self.index {
            self.index -= 1;
        }
    }
}

impl<T> Meta for SignalInner<T> {
    type Data = ();
}
