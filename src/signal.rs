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

impl<T> Disconnectable for KeyCell<SignalInner<T>> {
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
/// signal.before().connect(key, &item, |this, event| {
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
    /// - `before()` clones: Higher priority (executed first)
    /// - `after()` clones: Lower priority (executed last)
    ///
    /// ## Panics ##
    ///
    /// Panics if the priority space is exhausted (after 127 nested
    /// `before`/`after` calls).
    ///
    /// ## Ordering Notes ##
    /// - `signal.before().after()` creates a middle priority tier between the
    ///   parent and `before` clone.
    /// - Subsequent calls to `before()`/`after()` on clones maintain their
    ///   relative ordering.
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
    /// signal.before().connect(key, &item, move |this, event| {
    ///     shared_clone.borrow_mut().push(0);
    ///     println!("This runs before");
    /// });
    ///
    /// signal.emit(key, ());
    /// assert_eq!(&*shared.borrow(), &[0, 1]);
    /// ```
    pub fn before(&self) -> Self {
        let index = self.index.left().expect("fractional index exhausted");

        Self {
            inner: self.inner.clone(),
            index,
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
    /// - `before()` clones: Higher priority (executed first)
    /// - `after()` clones: Lower priority (executed last)
    ///
    /// ## Panics ##
    ///
    /// Panics if the priority space is exhausted (after 127 nested
    /// `before`/`after` calls).
    ///
    /// ## Ordering Notes ##
    /// - `signal.after().before()` creates a middle priority tier between the
    ///   parent and `after` clone.
    /// - Subsequent calls to `before()`/`after()` on clones maintain their
    ///   relative ordering.
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
    /// signal.after().connect(key, &item, move |this, event| {
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
    pub fn after(&self) -> Self {
        let index = self.index.right().expect("fractional index exhausted");

        Self {
            inner: self.inner.clone(),
            index,
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
            relative_index: self.index.value(),
            id,
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

    /// Returns the relative order of this signal.
    ///
    /// Note that comparisons of orders only gives meaningful information for
    /// the same underlying signal - that is - signals cloned using `before`
    /// or `after`. Two distinct signals have unrelated orderings.
    ///
    /// See [before](Signal::before) and [after](Signal::after) for more
    /// details.
    ///
    /// # Example #
    ///
    /// ```
    /// use mutcy::Signal;
    ///
    /// let signal: Signal<()> = Signal::new();
    ///
    /// assert_eq!(170141183460469231731687303715884105727, signal.order());
    ///
    /// assert_eq!(
    ///     85070591730234615865843651857942052863,
    ///     signal.before().order()
    /// );
    /// assert_eq!(
    ///     127605887595351923798765477786913079295,
    ///     signal.before().after().order()
    /// );
    ///
    /// assert_eq!(
    ///     255211775190703847597530955573826158591,
    ///     signal.after().order()
    /// );
    /// assert_eq!(
    ///     212676479325586539664609129644855132159,
    ///     signal.after().before().order()
    /// );
    ///
    /// let max_before = {
    ///     let mut max_before = signal.before();
    ///     for _ in 0..126 {
    ///         max_before = max_before.before();
    ///     }
    ///     max_before
    /// };
    ///
    /// assert_eq!(max_before.order(), 0);
    ///
    /// let max_after = {
    ///     let mut max_after = signal.after();
    ///     for _ in 0..126 {
    ///         max_after = max_after.after();
    ///     }
    ///     max_after
    /// };
    ///
    /// assert_eq!(max_after.order(), u128::MAX - 1);
    /// ```
    pub fn order(&self) -> FractionalIndexType {
        self.index.value()
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
}

impl<T> Meta for SignalInner<T> {
    type Data = ();
}
