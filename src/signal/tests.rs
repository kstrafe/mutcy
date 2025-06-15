use super::*;
use quickcheck::{Arbitrary, Gen};
use quickcheck_macros::quickcheck;
use std::cell::{Cell, RefCell};

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
        signal.after().connect(key, &receiver, Announcer::handle);

        let receiver = Rc::new(Announcer::new("a", recorder.clone()));
        signal.before().connect(key, &receiver, Announcer::handle);

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

#[test]
fn signal_ordering_limit() {
    let signal: Signal<()> = Signal::new();
    let mut signal_before = signal.before();
    for _ in 0..126 {
        signal_before = signal_before.before();
    }
}

#[test]
fn signal_ordering_limit_exceeded() {
    fn verify_exhausted(signal: &Signal<()>) {
        use std::panic::AssertUnwindSafe;

        let Err(msg) = std::panic::catch_unwind(AssertUnwindSafe(|| {
            let _ = signal.before();
        })) else {
            panic!("Fractional index not exhausted");
        };

        assert_eq!(
            *msg.downcast::<String>().unwrap(),
            "fractional index exhausted"
        );

        let Err(msg) = std::panic::catch_unwind(AssertUnwindSafe(|| {
            let _ = signal.after();
        })) else {
            panic!("Fractional index not exhausted");
        };

        assert_eq!(
            *msg.downcast::<String>().unwrap(),
            "fractional index exhausted"
        );
    }

    let signal: Signal<()> = Signal::new();
    let mut signal_before = signal.before();
    for _ in 0..126 {
        signal_before = signal_before.before();
    }

    let mut signal_after = signal.after();
    for _ in 0..126 {
        signal_after = signal_after.after();
    }

    verify_exhausted(&signal_before);
    verify_exhausted(&signal_after);
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct FractionalOrderDecisions {
    decisions: Vec<bool>,
}

impl Arbitrary for FractionalOrderDecisions {
    fn arbitrary(g: &mut Gen) -> Self {
        let count = *g.choose(&(0..=127).collect::<Vec<_>>()).unwrap();

        let mut decisions = Vec::with_capacity(count);
        for _ in 0..count {
            decisions.push(*g.choose(&[false, true]).unwrap());
        }

        Self { decisions }
    }
}

#[quickcheck]
fn different_ordering_has_different_fractional_order(
    x: FractionalOrderDecisions,
    y: FractionalOrderDecisions,
) {
    if x == y {
        return;
    }

    let signal: Signal<()> = Signal::new();

    let mut signal_x = signal.clone();
    for decision in &x.decisions {
        if *decision {
            signal_x = signal_x.before();
        } else {
            signal_x = signal_x.after();
        }
    }

    let mut signal_y = signal.clone();
    for decision in &y.decisions {
        if *decision {
            signal_y = signal_y.before();
        } else {
            signal_y = signal_y.after();
        }
    }

    assert!(signal_x.order() != signal_y.order());
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

    let connection = signal.after().connect(key, &receiver, move |this, _| {
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
        .before()
        .after()
        .after()
        .connect(key, &receiver, |this, _| {
            **this += "c";
        });

    signal.before().before().connect(key, &receiver, |this, _| {
        **this += "a";
    });

    signal
        .after()
        .before()
        .before()
        .connect(key, &receiver, |this, _| {
            **this += "d";
        });

    signal.before().after().connect(key, &receiver, |this, _| {
        **this += "b";
    });

    signal.emit(key, ());
    assert_eq!(*receiver.ro(key), "abcd");
}
