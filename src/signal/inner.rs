use super::{FractionalIndexType, Handler, Receiver, Signal};
use crate::{Key, KeyCell, Meta, Rw};
use std::{
    collections::HashMap,
    rc::{Rc, Weak},
};

pub enum Action {
    Continue,
    Remove,
    RemoveSignal(FractionalIndexType),
}

pub struct SignalInner<T> {
    receivers: Vec<Receiver<T>>,
    index: usize,
    depth: usize,
    top: usize,
    idgen: u64,
    subsignals: HashMap<FractionalIndexType, Signal<T>>,
}

impl<T: 'static> SignalInner<T> {
    pub fn new() -> Self {
        Self {
            receivers: Vec::new(),
            index: 0,
            depth: 0,
            top: 0,
            idgen: 0,
            subsignals: HashMap::new(),
        }
    }

    pub fn connect<R, F>(
        self: Rw<Self>,
        receiver: Weak<KeyCell<R>>,
        order: FractionalIndexType,
        handler: F,
    ) -> u64
    where
        R: Meta + 'static,
        F: Fn(Rw<R>, &T) + 'static,
    {
        debug_assert!(order % 2 == 0 && order != 0);
        assert!(
            Weak::strong_count(&receiver) > 0,
            "Signal::connect: object must have a strong reference"
        );

        let handler: Rc<Handler<T>> = Rc::new(move |key, item| {
            if let Some(receiver) = receiver.upgrade() {
                (handler)(&mut receiver.rw(key), item);
                Action::Continue
            } else {
                Action::Remove
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
                return Action::Remove;
            }

            if strong == 2 && receiver.len() == 0 && order % 2 == 1 {
                return Action::RemoveSignal(order);
            }

            receiver.emit(item);
            Action::Continue
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

    pub fn emit(self: Rw<Self>, item: &T) {
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

            match (receiver)(key, item) {
                Action::Remove => {
                    this.0.index -= 1;
                    let index = this.0.index;
                    this.0.receivers.remove(index);
                }
                Action::Continue => {}
                Action::RemoveSignal(position) => {
                    this.0.index -= 1;
                    let index = this.0.index;
                    this.0.receivers.remove(index);
                    this.0.subsignals.remove(&position);
                }
            }

            if this.0.top > top {
                break;
            }
        }

        drop(this);
    }

    pub fn disconnect(self: Rw<Self>, id: u64, relative_index: FractionalIndexType) {
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

    pub fn len(&self) -> usize {
        self.receivers.len()
    }

    pub fn register_subsignal(self: Rw<Self>, signal: Signal<T>, index: FractionalIndexType) {
        self.subsignals.insert(index, signal);
    }

    pub fn preexisting_subsignal(self: Rw<Self>, index: FractionalIndexType) -> Option<Signal<T>> {
        self.subsignals.get(&index).cloned()
    }

    #[cfg(test)]
    pub fn ordering_subsignals(&self) -> usize {
        self.subsignals.len()
    }
}

impl<T> Meta for SignalInner<T> {
    type Data = ();
}
