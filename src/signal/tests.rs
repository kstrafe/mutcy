use super::{Connection, Key, KeyCell, Meta, Rw, Signal};
use quickcheck::{Arbitrary, Gen};
use quickcheck_macros::quickcheck;
use std::{
    cell::{Cell, RefCell},
    cmp::Ordering,
    rc::{Rc, Weak},
};

const DEPTH: u32 = Signal::<()>::test_ordering_depth();

#[test]
fn emit_and_receive() {
    let mut key = Key::acquire();
    let key = &mut key;

    let signal = Signal::new();
    let receiver = Rc::new(KeyCell::new(0, ()));

    {
        signal.connect(key, &receiver, |this, event| {
            **this += event;
        });

        signal.emit(key, 1);
    }
    assert_eq!(1, *receiver.ro(&key));

    signal.emit(key, 1);
    assert_eq!(2, *receiver.ro(&key));

    drop(receiver);

    signal.emit(key, 1);
}

#[test]
fn order() {
    use std::cell::RefCell;

    let mut key = Key::acquire();
    let signal = Signal::<()>::new();

    let recorder = Rc::new(RefCell::new(Vec::new()));

    struct Announcer {
        name: &'static str,
        recorder: Rc<RefCell<Vec<&'static str>>>,
    }

    impl Announcer {
        fn new(name: &'static str, recorder: Rc<RefCell<Vec<&'static str>>>) -> KeyCell<Self> {
            KeyCell::new(Self { name, recorder }, ())
        }

        fn handle(self: Rw<Self>, _: &()) {
            self.recorder.borrow_mut().push(self.name);
        }
    }

    impl Meta for Announcer {
        type Data = ();
    }

    {
        let key = &mut key;

        let receiver = Rc::new(Announcer::new("b", recorder.clone()));
        signal.connect(key, &receiver, Announcer::handle);

        let receiver = Rc::new(Announcer::new("c", recorder.clone()));
        signal.after(key).connect(key, &receiver, Announcer::handle);

        let receiver = Rc::new(Announcer::new("a", recorder.clone()));
        signal
            .before(key)
            .connect(key, &receiver, Announcer::handle);

        signal.emit(key, ());
    }

    assert_eq!(*recorder.borrow(), &["a", "b", "c"]);
}

#[test]
fn drop_connect() {
    let mut key = Key::acquire();
    let signal = Signal::<()>::new();

    {
        let key = &mut key;

        let receiver = Rc::new(KeyCell::new(0, ()));
        signal.connect(key, &receiver, |_, _| {});

        drop(receiver);

        let receiver = Rc::new(KeyCell::new(0, ()));
        signal.connect(key, &receiver, |_, _| {});
    }
}

#[test]
fn connect_during_emit_after_index() {
    let mut key = Key::acquire();
    let signal = Signal::new();

    struct SelfConnector {
        current: u16,
        recorder: Rc<RefCell<Vec<u16>>>,
    }

    struct SelfConnectorMeta {
        this: Weak<KeyCell<SelfConnector>>,
        signal: Signal<()>,
    }

    impl SelfConnector {
        fn handle(self: Rw<Self>, _: &()) {
            self.current += 1;
            let index = self.current;
            self.recorder.borrow_mut().push(index);

            if index < 10 {
                let (this, key) = Key::split_rw(self);
                this.meta()
                    .signal
                    .connect(key, &this.meta().this, Self::handle);
            }
        }
    }

    impl Meta for SelfConnector {
        type Data = SelfConnectorMeta;
    }

    let recorder = Rc::new(RefCell::new(Vec::new()));

    let sc: Rc<KeyCell<_>> = Rc::new_cyclic(|weak: &Weak<KeyCell<_>>| {
        KeyCell::new(
            SelfConnector {
                current: 0,
                recorder: recorder.clone(),
            },
            SelfConnectorMeta {
                this: weak.clone(),
                signal: signal.clone(),
            },
        )
    });

    signal.connect(&mut key, &sc, SelfConnector::handle);
    signal.emit(&mut key, ());

    assert_eq!(&*recorder.borrow(), &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
}

#[test]
#[should_panic(expected = "Signal::connect: object must have a strong reference")]
fn weak_without_strong_panics() {
    let key = &mut Key::acquire();
    let signal = Signal::new();

    Rc::new_cyclic(|weak| {
        signal.connect(key, weak, |_, _: &()| {});
        KeyCell::new(0, ())
    });
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct FractionalOrderDecisions {
    decisions: Vec<bool>,
}

impl Arbitrary for FractionalOrderDecisions {
    fn arbitrary(g: &mut Gen) -> Self {
        fn list() -> [usize; (DEPTH as usize) * 2] {
            let mut array = [0; (DEPTH as usize) * 2];
            for idx in 0..array.len() {
                array[idx] = idx;
            }
            array
        }

        let count = *g.choose(&list()).unwrap();

        let mut decisions = Vec::with_capacity(count);
        for _ in 0..count {
            decisions.push(*g.choose(&[false, true]).unwrap());
        }

        Self { decisions }
    }
}

impl Ord for FractionalOrderDecisions {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl PartialOrd for FractionalOrderDecisions {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let lhs = self
            .decisions
            .iter()
            .cloned()
            .map(|x| Some(x))
            .chain([None::<bool>].into_iter().cycle());

        let rhs = other
            .decisions
            .iter()
            .cloned()
            .map(|x| Some(x))
            .chain([None::<bool>].into_iter().cycle());

        for (lhs, rhs) in lhs.zip(rhs) {
            if lhs.is_some() && rhs.is_some() {
                let ordering = lhs.unwrap().cmp(&rhs.unwrap());
                if let Ordering::Equal = ordering {
                    continue;
                }

                return Some(ordering);
            }

            if lhs.is_none() && rhs.is_some() {
                if rhs.unwrap() {
                    return Some(Ordering::Less);
                } else {
                    return Some(Ordering::Greater);
                }
            }

            if lhs.is_some() && rhs.is_none() {
                if lhs.unwrap() {
                    return Some(Ordering::Greater);
                } else {
                    return Some(Ordering::Less);
                }
            }

            return Some(Ordering::Equal);
        }

        panic!("no ordering reached")
    }
}

#[quickcheck]
fn different_ordering_has_different_fractional_order(
    x: FractionalOrderDecisions,
    y: FractionalOrderDecisions,
) {
    let key = &mut Key::acquire();

    let signal: Signal<()> = Signal::new();

    let mut signal_x = signal.clone();
    for decision in &x.decisions {
        if *decision {
            signal_x = signal_x.after(key);
        } else {
            signal_x = signal_x.before(key);
        }
    }

    let mut signal_y = signal.clone();
    for decision in &y.decisions {
        if *decision {
            signal_y = signal_y.after(key);
        } else {
            signal_y = signal_y.before(key);
        }
    }

    if x == y {
        assert!(signal_x == signal_y);
    } else {
        assert!(signal_x != signal_y);
    }

    let receiver = Rc::new(KeyCell::new(String::new(), ()));
    signal_x.connect(key, &receiver, |this, _| {
        **this += "x";
    });

    signal_y.connect(key, &receiver, |this, _| {
        **this += "y";
    });

    signal.emit(key, ());

    if x <= y {
        assert_eq!(*receiver.ro(key), "xy");
    } else {
        assert_eq!(*receiver.ro(key), "yx");
    }
}

#[quickcheck]
fn same_order_refers_to_same_signal_object(order: FractionalOrderDecisions) {
    let key = &mut Key::acquire();
    let signal: Signal<()> = Signal::new();

    let mut signal_x = signal.clone();
    for decision in &order.decisions {
        if *decision {
            signal_x = signal_x.after(key);
        } else {
            signal_x = signal_x.before(key);
        }
    }

    let mut signal_y = signal.clone();
    for decision in &order.decisions {
        if *decision {
            signal_y = signal_y.after(key);
        } else {
            signal_y = signal_y.before(key);
        }
    }

    assert!(signal_x == signal_y);
}

#[test]
fn signal_disconnect() {
    let key = &mut Key::acquire();
    let signal: Signal<()> = Signal::new();

    let receiver = Rc::new(KeyCell::new(String::new(), ()));

    let a = signal.connect(key, &receiver, |this, _| {
        **this += "a";
    });

    let b = signal.connect(key, &receiver, |this, _| {
        **this += "b";
    });

    let c = signal.connect(key, &receiver, |this, _| {
        **this += "c";
    });

    signal.emit(key, ());
    assert_eq!(*receiver.ro(key), "abc");

    b.disconnect(key);

    receiver.rw(key).clear();
    signal.emit(key, ());
    assert_eq!(*receiver.ro(key), "ac");

    a.disconnect(key);

    receiver.rw(key).clear();
    signal.emit(key, ());
    assert_eq!(*receiver.ro(key), "c");

    c.disconnect(key);

    receiver.rw(key).clear();
    signal.emit(key, ());
    assert_eq!(*receiver.ro(key), "");
}

#[test]
fn signal_disconnect_dropped_item() {
    let key = &mut Key::acquire();
    let signal: Signal<()> = Signal::new();

    let number = Rc::new(Cell::new(0));
    let receiver = Rc::new(KeyCell::new(number.clone(), ()));

    let a = signal.connect(key, &receiver, |this, _| {
        this.set(this.get() + 1);
    });

    assert_eq!(number.get(), 0);

    signal.emit(key, ());
    assert_eq!(number.get(), 1);

    drop(receiver);

    signal.emit(key, ());
    assert_eq!(number.get(), 1);

    a.disconnect(key);

    signal.emit(key, ());
    assert_eq!(number.get(), 1);
}

#[test]
fn disconnect_while_emitting() {
    let key = &mut Key::acquire();
    let signal: Signal<()> = Signal::new();

    struct Receiver {
        value: String,
    }

    impl Meta for Receiver {
        type Data = Signal<()>;
    }

    let receiver = Rc::new(KeyCell::new(
        Receiver {
            value: String::new(),
        },
        signal.clone(),
    ));

    let connection = signal.after(key).connect(key, &receiver, move |this, _| {
        this.value += "2";
    });

    let connection = RefCell::new(Some(connection));
    signal.connect(key, &receiver, move |this, _| {
        if this.value == "" {
            this.value += "1";
            let (rhis, key) = Key::split_rw(this);
            rhis.meta().emit(key, ());

            if let Some(connection) = connection.borrow_mut().take() {
                connection.disconnect(key);
            }

            rhis.meta().emit(key, ());
        }
    });

    signal.emit(key, ());
    assert_eq!(&receiver.ro(key).value, "12");

    signal.emit(key, ());
    assert_eq!(&receiver.ro(key).value, "12");
}

#[test]
fn disconnect_self_while_emitting() {
    let key = &mut Key::acquire();
    let signal: Signal<RefCell<Option<Connection>>> = Signal::new();

    let receiver = Rc::new(KeyCell::new(String::new(), ()));

    signal.connect(key, &receiver, move |this, _| {
        **this += "a";
    });

    let connection = signal.connect(key, &receiver, move |this, connection| {
        let (_, key) = Key::split_rw(this);
        connection.borrow_mut().take().unwrap().disconnect(key);
        **this += "b";
    });

    signal.connect(key, &receiver, move |this, _| {
        **this += "c";
    });

    signal.emit(key, RefCell::new(Some(connection)));
    assert_eq!(*receiver.ro(key), "abc");

    signal.emit(key, RefCell::new(None));
    assert_eq!(*receiver.ro(key), "abcac");
}

#[test]
fn ordering_recursion() {
    let key = &mut Key::acquire();
    let signal: Signal<()> = Signal::new();
    let receiver = Rc::new(KeyCell::new(String::new(), ()));

    signal
        .before(key)
        .after(key)
        .after(key)
        .connect(key, &receiver, |this, _| {
            **this += "c";
        });

    signal
        .before(key)
        .before(key)
        .connect(key, &receiver, |this, _| {
            **this += "a";
        });

    signal
        .after(key)
        .before(key)
        .before(key)
        .connect(key, &receiver, |this, _| {
            **this += "d";
        });

    signal
        .before(key)
        .after(key)
        .connect(key, &receiver, |this, _| {
            **this += "b";
        });

    signal.emit(key, ());
    assert_eq!(*receiver.ro(key), "abcd");
}

#[test]
fn subsignal() {
    let key = &mut Key::acquire();
    let signal: Signal<()> = Signal::new();
    let subsignal = signal.before(key).subsignal(key);

    let receiver = Rc::new(KeyCell::new(String::new(), ()));

    signal.connect(key, &receiver, |this, _| {
        **this += "b";
    });

    subsignal.connect(key, &receiver, |this, _| {
        **this += "a";
    });

    signal.emit(key, ());
    assert_eq!(*receiver.ro(key), "ab");
}

#[test]
fn ordering_subsignal_reuses_before() {
    let key = &mut Key::acquire();
    let signal: Signal<()> = Signal::new();

    let mut subsignal_1 = signal.before(key);
    for _ in 0..DEPTH {
        subsignal_1 = subsignal_1.before(key);
    }

    let mut subsignal_2 = signal.before(key);
    for _ in 0..DEPTH {
        subsignal_2 = subsignal_2.before(key);
    }

    assert!(subsignal_1 == subsignal_2);

    let receiver = Rc::new(KeyCell::new(String::new(), ()));

    subsignal_2.connect(key, &receiver, |this, _| {
        **this += "a";
    });

    subsignal_1.connect(key, &receiver, |this, _| {
        **this += "b";
    });

    signal.emit(key, ());
    assert_eq!(*receiver.ro(key), "ab");
}

#[test]
fn ordering_subsignal_reuses_after() {
    let key = &mut Key::acquire();
    let signal: Signal<()> = Signal::new();

    let mut subsignal_1 = signal.after(key);
    for _ in 0..DEPTH {
        subsignal_1 = subsignal_1.after(key);
    }

    let mut subsignal_2 = signal.after(key);
    for _ in 0..DEPTH {
        subsignal_2 = subsignal_2.after(key);
    }

    assert!(subsignal_1 == subsignal_2);

    let receiver = Rc::new(KeyCell::new(String::new(), ()));

    subsignal_2.connect(key, &receiver, |this, _| {
        **this += "a";
    });

    subsignal_1.connect(key, &receiver, |this, _| {
        **this += "b";
    });

    signal.emit(key, ());
    assert_eq!(*receiver.ro(key), "ab");
}

#[test]
fn emit_using_reference() {
    let key = &mut Key::acquire();
    let signal: Signal<()> = Signal::new();
    signal.emit(key, &());
}

#[test]
fn subsignals_from_ordering_autoremoved() {
    let key = &mut Key::acquire();
    let signal: Signal<()> = Signal::new();

    assert_eq!(signal.test_ordering_subsignal_count(key), 0);
    assert_eq!(signal.test_subscriber_count(key), 0);

    let mut before = signal.before(key);
    for _ in 0..DEPTH - 2 {
        before = before.before(key);
        assert_eq!(signal.test_ordering_subsignal_count(key), 0);
        assert_eq!(signal.test_subscriber_count(key), 0);
    }

    before = before.before(key);
    assert_eq!(signal.test_ordering_subsignal_count(key), 1);
    assert_eq!(signal.test_subscriber_count(key), 1);

    signal.emit(key, &());
    assert_eq!(signal.test_ordering_subsignal_count(key), 1);
    assert_eq!(signal.test_subscriber_count(key), 1);

    drop(before);
    assert_eq!(signal.test_ordering_subsignal_count(key), 1);
    assert_eq!(signal.test_subscriber_count(key), 1);

    signal.emit(key, &());
    assert_eq!(signal.test_ordering_subsignal_count(key), 0);
    assert_eq!(signal.test_subscriber_count(key), 0);

    let subsignal = signal.subsignal(key);
    assert_eq!(signal.test_ordering_subsignal_count(key), 0);
    assert_eq!(signal.test_subscriber_count(key), 1);
    assert_eq!(subsignal.test_ordering_subsignal_count(key), 0);
    assert_eq!(subsignal.test_subscriber_count(key), 0);

    let connection = subsignal.connect(key, &Rc::new(KeyCell::new(0, ())), |_, _| {});
    assert_eq!(signal.test_ordering_subsignal_count(key), 0);
    assert_eq!(signal.test_subscriber_count(key), 1);
    assert_eq!(subsignal.test_ordering_subsignal_count(key), 0);
    assert_eq!(subsignal.test_subscriber_count(key), 1);

    drop(subsignal);
    assert_eq!(signal.test_ordering_subsignal_count(key), 0);
    assert_eq!(signal.test_subscriber_count(key), 1);

    signal.emit(key, &());
    assert_eq!(signal.test_ordering_subsignal_count(key), 0);
    assert_eq!(signal.test_subscriber_count(key), 1);

    connection.disconnect(key);
    assert_eq!(signal.test_ordering_subsignal_count(key), 0);
    assert_eq!(signal.test_subscriber_count(key), 1);

    signal.emit(key, &());
    assert_eq!(signal.test_ordering_subsignal_count(key), 0);
    assert_eq!(signal.test_subscriber_count(key), 0);
}
