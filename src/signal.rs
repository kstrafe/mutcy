use self::{
    fractional_index::{FractionalIndex, FractionalIndexType},
    inner::{Action, SignalInner},
};
use super::{IntoWeak, Key, KeyCell, Meta, Rw};
use std::{borrow::Borrow, rc::Rc};

mod fractional_index;
mod inner;
#[cfg(test)]
mod tests;

type Handler<T> = dyn Fn(&mut Key, &T) -> Action;

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
            self.subsignal_at(key, self.index.value() - 1)
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
            self.subsignal_at(key, self.index.value() + 1)
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
        let receiver = receiver.into();
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
    /// parent signal is forwarded to the subsignal at this particular order as
    /// specified by previous [before](Signal::before)/
    /// [after](Signal::after) calls.
    ///
    /// The main purpose of a subsignal is to group together a set of slots for
    /// two reasons.
    ///
    /// 1. Cluster connections into a single priority group.
    /// 2. To enable fast [disconnect](Connection)ion.
    ///
    /// # Performance #
    /// Subsignals are an extra indirection step making them about 3-4x slower
    /// than a non-subsignal connection.
    ///
    /// # Examples #
    ///
    /// ## Example: Clustering into  single priority group ##
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
    /// // Even though this is connected later, it's connected to subsignal_1, which is ordered
    /// // before subsignal_2, so this will run before any connection to subsignal_2.
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
    /// connecting and disconnecting a connection to a significantly
    /// populated [Signal] would lead to slowdowns.
    ///
    /// To remedy this, we can use a subsignal to hold the frequently changing
    /// set of connections.
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
    /// for _ in 0..1_000 {
    ///     signal.connect(key, &item, |_, _| {});
    /// }
    ///
    /// for _ in 0..1_000 {
    ///     // This is fast because the subsignal contains at most 1 element.
    ///     let conn = frequently_changing.connect(key, &item, |_, _| {});
    ///     conn.disconnect(key);
    /// }
    /// ```
    pub fn subsignal(&self, key: &mut Key) -> Self {
        let index = self.index.value();
        let inner = self.inner.rw(key).subsignal(index);

        Self {
            inner,
            index: FractionalIndex::new(),
        }
    }

    fn subsignal_at(&self, key: &mut Key, index: FractionalIndexType) -> Self {
        debug_assert!(index % 2 == 1);

        if let Some(subsignal) = self.inner.rw(key).preexisting_subsignal(index) {
            return subsignal;
        }

        let inner = self.inner.rw(key).subsignal(index);

        let subsignal = Self {
            inner,
            index: FractionalIndex::new(),
        };

        self.inner
            .rw(key)
            .register_subsignal(subsignal.clone(), index);

        subsignal
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
    /// This allows us to add a receiver that effectively modifies the data and
    /// re-emits.
    ///
    /// # Examples #
    ///
    /// ## Plain emitting ##
    ///
    /// ```
    /// use mutcy::{Key, KeyCell, Signal};
    /// use std::rc::Rc;
    ///
    /// let key = &mut Key::acquire();
    /// let signal = Signal::new();
    /// let receiver = Rc::new(KeyCell::new(String::new(), ()));
    ///
    /// signal.connect(key, &receiver, |this, value| {
    ///     **this += &format!("Number: {}\n", value);
    /// });
    ///
    /// // Both call-by-moving and by-reference work.
    /// signal.emit(key, 123);
    /// signal.emit(key, &456);
    ///
    /// assert_eq!(*receiver.ro(key), "Number: 123\nNumber: 456\n");
    /// ```
    ///
    /// ## Nested emits ##
    ///
    /// A signal handler can call `emit` on the same signal that invoked the
    /// handler. In those cases, the outermost `emit` will return early upon
    /// the signal handler returning. The nested `emit` call will run all
    /// receivers as if it were calling it as the outer `emit`. From any
    /// call to `emit`, we are thus guaranteed that all receivers are called.
    ///
    /// In the example here, the outer emit will effectively observe that
    /// receivers are called with the argument `0` until `b` is reached.
    /// After that, the emit resets to `1` and all receivers
    /// are again executed with this new argument. `C(0)` is never executed.
    ///
    /// ```
    /// use mutcy::{Key, KeyCell, Meta, Signal};
    /// use std::{cell::RefCell, rc::Rc};
    ///
    /// let key = &mut Key::acquire();
    /// let signal = Signal::new();
    ///
    /// let record = Rc::new(RefCell::new(String::new()));
    ///
    /// struct X {
    ///     record: Rc<RefCell<String>>,
    /// }
    ///
    /// impl Meta for X {
    ///     type Data = Signal<i32>;
    /// }
    ///
    /// let receiver = Rc::new(KeyCell::new(
    ///     X {
    ///         record: record.clone(),
    ///     },
    ///     signal.clone(),
    /// ));
    ///
    /// signal.connect(key, &receiver, |this, value| {
    ///     *this.record.borrow_mut() += &format!("A({}) ", value);
    /// });
    ///
    /// signal.connect(key, &receiver, |this, value| {
    ///     *this.record.borrow_mut() += &format!("B({}) ", value);
    ///     if *value == 0 {
    ///         *this.record.borrow_mut() += &format!("RE-EMIT({}) ", value + 1);
    ///         let (cell, key) = Key::split_rw(this);
    ///         cell.meta().emit(key, value + 1);
    ///     }
    /// });
    ///
    /// signal.connect(key, &receiver, |this, value| {
    ///     *this.record.borrow_mut() += &format!("C({}) ", value);
    /// });
    ///
    /// signal.emit(key, 0);
    ///
    /// assert_eq!(*record.borrow(), "A(0) B(0) RE-EMIT(1) A(1) B(1) C(1) ");
    /// ```
    pub fn emit<B>(&self, key: &mut Key, item: B)
    where
        B: Borrow<T>,
    {
        self.inner.rw(key).emit(item.borrow());
    }

    #[cfg(test)]
    const fn test_ordering_depth() -> u32 {
        FractionalIndexType::BITS - 1
    }

    /// Get the amount of subscribers.
    #[cfg(test)]
    pub fn test_subscriber_count(&self, key: &mut Key) -> usize {
        self.inner.ro(key).len()
    }

    #[cfg(test)]
    fn test_ordering_subsignal_count(&self, key: &mut Key) -> usize {
        self.inner.ro(key).ordering_subsignals()
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

impl<T: 'static> Eq for Signal<T> {}

/// Compares two signals. Equal when the underlying signal object is the same,
/// and their order values are the same.
///
/// # Examples #
///
/// ```
/// use mutcy::{Key, Signal};
///
/// let key = &mut Key::acquire();
///
/// let signal = Signal::<()>::new();
///
/// // Equal cases.
/// assert!(signal == signal);
/// assert!(signal.clone() == signal);
/// assert!(signal.before(key) == signal.before(key));
/// assert!(signal.after(key) == signal.after(key));
/// assert!(signal.after(key) == signal.after(key));
///
/// // Unequal cases.
/// assert!(signal.before(key) != signal);
/// assert!(signal.after(key) != signal);
/// assert!(signal != signal.subsignal(key));
///
/// // Note that subsignals append a new signal object to the current order, so these are not
/// // equal.
/// assert!(signal.subsignal(key) != signal.subsignal(key));
/// ```
impl<T: 'static> PartialEq for Signal<T> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.inner, &other.inner) && self.index.value() == other.index.value()
    }
}
