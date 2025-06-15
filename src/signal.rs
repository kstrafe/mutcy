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
    fn disconnect(&self, key: &mut Key, id: u64, relative_index: FractionalIndexType);
}

impl<T: 'static> Disconnectable for KeyCell<SignalInner<T>> {
    fn disconnect(&self, key: &mut Key, id: u64, relative_index: FractionalIndexType) {
        self.rw(key).disconnect(id, relative_index);
    }
}

/// References a connection created via [Signal::connect].
pub struct Connection {
    inner: Rc<dyn Disconnectable>,
    relative_index: FractionalIndexType,
    id: u64,
}

impl Connection {
    /// Disconnect this connection.
    ///
    /// Does nothing if the connection is already removed. This can happen if we
    /// destroy the receiver object and run [emit](Signal::emit).
    ///
    /// # Time Complexity #
    ///
    /// Takes `O(connection_count)` time. All connections that come after this
    /// connection need to be shifted by one position. In the worst case if
    /// disconnecting the first connection, all other connections must be
    /// shifted.
    pub fn disconnect(self, key: &mut Key) {
        self.inner.disconnect(key, self.id, self.relative_index);
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
/// [Connect](Signal::connect)ions are invoked upon a call to
/// [emit](Signal::emit). The order of these invocations corresponds
/// to the order in which `connect` was called.
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
/// signal.before(key).connect(key, &item, |this, event| {
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

    /// Creates a cloned `Signal` whose connections are invoked **before** the
    /// parent signal's connections.
    ///
    /// By default, connections are invoked in the order they were created via
    /// [`connect`](Signal::connect). This method creates a priority tier -
    /// all connections made to the cloned signal will execute *before* any
    /// connections on the parent signal.
    ///
    /// ## Invocation Order
    /// - Parent signal: Base priority
    /// - `before(key)` clones: Higher priority (executed first)
    /// - `after(key)` clones: Lower priority (executed last)
    ///
    /// ## Ordering Notes ##
    /// - `signal.before(key).after(key)` creates a middle priority tier between
    ///   the parent and `before` clone.
    /// - Subsequent calls to `before(key)`/`after(key)` on clones maintain
    ///   their relative ordering.
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
    /// signal.before(key).connect(key, &item, move |this, event| {
    ///     shared_clone.borrow_mut().push(0);
    ///     println!("This runs before");
    /// });
    ///
    /// signal.emit(key, ());
    /// assert_eq!(&*shared.borrow(), &[0, 1]);
    /// ```
    pub fn before(&self, key: &mut Key) -> Self {
        if let Some(index) = self.index.left() {
            Self {
                inner: self.inner.clone(),
                index,
            }
        } else {
            self.subsignal(key)
        }
    }

    /// Creates a cloned `Signal` whose connections are invoked **after** the
    /// parent signal's connections.
    ///
    /// By default, connections are invoked in the order they were created via
    /// [`connect`](Signal::connect). This method creates a priority tier -
    /// all connections made to the cloned signal will execute *after* any
    /// connections on the parent signal.
    ///
    /// ## Invocation Order
    /// - Parent signal: Base priority
    /// - `before(key)` clones: Higher priority (executed first)
    /// - `after(key)` clones: Lower priority (executed last)
    ///
    /// ## Ordering Notes ##
    /// - `signal.after(key).before(key)` creates a middle priority tier between
    ///   the parent and `after` clone.
    /// - Subsequent calls to `before(key)`/`after(key)` on clones maintain
    ///   their relative ordering.
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
    /// signal.after(key).connect(key, &item, move |this, event| {
    ///     shared_clone.borrow_mut().push(1);
    ///     println!("This runs after");
    /// });
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
    pub fn after(&self, key: &mut Key) -> Self {
        if let Some(index) = self.index.right() {
            Self {
                inner: self.inner.clone(),
                index,
            }
        } else {
            self.subsignal(key)
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
    /// # Panics #
    ///
    /// Panics if the receiver has no strong
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
            relative_index: self.index.value(),
            id,
        }
    }

    /// Creates a new subsignal.
    ///
    /// Creates a new [Signal] object and connects it to this (parent) signal.
    /// Any [emit](Signal::emit) run on the
    /// parent signal is forwarded to the subsignal.
    ///
    /// The main purpose of a subsignal is to group together a set of slots for
    /// two reasons.
    ///
    /// 1. To group connections together.
    /// 2. To enable fast [disconnect](Connection)ion.
    ///
    /// # Performance #
    /// Subsignals are an extra indirection step making them about 3-4x slower
    /// than a non-subsignal connection.
    ///
    /// # Examples #
    ///
    /// ## Example: Grouping ##
    ///
    /// In the following example we group together a set of connections. Note
    /// that because `subsignal_1` is created before `subsignal_2`, that any
    /// [emit](Signal::emit) will invoke `subsignal_1` before `subsignal_2`;
    /// this is the same ordering that [connect](Signal::connect) uses.
    ///
    /// ```
    /// use mutcy::{Key, KeyCell, Rw, Signal};
    /// use std::rc::Rc;
    ///
    /// let key = &mut Key::acquire();
    ///
    /// let signal = Signal::new();
    /// let subsignal_1 = signal.subsignal(key);
    /// let subsignal_2 = signal.subsignal(key);
    ///
    /// let item = Rc::new(KeyCell::new(String::new(), ()));
    ///
    /// subsignal_1.connect(key, &item, |this, event| {
    ///     **this += "a";
    /// });
    ///
    /// subsignal_2.connect(key, &item, |this, event| {
    ///     **this += "c";
    /// });
    ///
    /// subsignal_1.connect(key, &item, |this, event| {
    ///     **this += "b";
    /// });
    ///
    /// signal.emit(key, ());
    ///
    /// assert_eq!(*item.ro(key), "abc");
    /// ```
    ///
    /// ## Example: Fast disconnection ##
    ///
    /// [Connection::disconnect] is an `O(N)` operation. As such, frequently
    /// connecting and disconnecting a connection in a significantly
    /// populated [Signal] would lead to slowdowns.
    ///
    /// To remedy this, we can use a subsignal to hold the frequently changing
    /// set of connections, given that this set might be significantly
    /// smaller.
    ///
    /// ```
    /// use mutcy::{Key, KeyCell, Rw, Signal};
    /// use std::rc::Rc;
    ///
    /// let key = &mut Key::acquire();
    ///
    /// let signal: Signal<()> = Signal::new();
    ///
    /// // Without the `subsignal(key)` call here, the last loop in
    /// // this example runs much slower.
    /// let frequently_changing = signal.before(key).subsignal(key);
    ///
    /// let item = Rc::new(KeyCell::new(String::new(), ()));
    ///
    /// for _ in 0..1_000_000 {
    ///     signal.connect(key, &item, |_, _| {});
    /// }
    ///
    /// for _ in 0..1_000_000 {
    ///     // This is fast because the subsignal contains at most 1 element.
    ///     let conn = frequently_changing.connect(key, &item, |_, _| {});
    ///     conn.disconnect(key);
    /// }
    /// ```
    pub fn subsignal(&self, key: &mut Key) -> Self {
        let index = self.index;
        let inner = self.inner.rw(key).subsignal(index.value());

        Self {
            inner,
            index: FractionalIndex::new(),
        }
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

impl<T: 'static> SignalInner<T> {
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

        let idx = self
            .receivers
            .partition_point(|x| x.relative_index <= order);

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

        id
    }

    pub fn subsignal(self: Rw<Self>, order: FractionalIndexType) -> Rc<KeyCell<Self>> {
        let signal = Rc::new(KeyCell::new(Self::new(), ()));

        let receiver = signal.clone();

        let handler: Rc<Handler<T>> = Rc::new(move |key, item| {
            let strong = Rc::strong_count(&receiver);
            let mut receiver = receiver.rw(key);

            if strong == 1 && receiver.len() == 0 {
                return true;
            }

            receiver.emit_ref(item);
            false
        });

        let id = self.idgen;
        self.idgen += 1;

        let idx = self
            .receivers
            .partition_point(|x| x.relative_index <= order);

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

        signal
    }

    pub fn emit(self: Rw<Self>, item: T) {
        self.emit_ref(&item);
    }

    pub fn emit_ref(self: Rw<Self>, item: &T) {
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

            if (receiver)(key, item) {
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

    fn disconnect(self: Rw<Self>, id: u64, relative_index: FractionalIndexType) {
        let left = self
            .receivers
            .partition_point(|x| x.relative_index < relative_index);
        let right = self
            .receivers
            .partition_point(|x| x.relative_index <= relative_index);

        let idx = self.receivers[left..right].partition_point(|x| x.id < id);

        if idx + left >= self.receivers.len() {
            return;
        }

        if self.receivers[idx + left].id != id {
            return;
        }

        self.receivers.remove(idx + left);

        if idx + left < self.index {
            self.index -= 1;
        }
    }

    fn len(self: Rw<Self>) -> usize {
        self.receivers.len()
    }
}

impl<T> Meta for SignalInner<T> {
    type Data = ();
}
