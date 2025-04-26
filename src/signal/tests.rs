use super::*;
use std::cell::RefCell;

#[test]
fn emit_and_receive() {
    let mut key = Key::acquire();
    let key = &mut key;

    let signal = Signal::new();
    let receiver = Rc::new(KeyCell::new(0, ()));

    {
        signal.connect(key, &receiver, "", |this, event| {
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
        signal.connect(key, &receiver, "b", Announcer::handle);

        let receiver = Rc::new(Announcer::new("c", recorder.clone()));
        signal.connect(key, &receiver, "c", Announcer::handle);

        let receiver = Rc::new(Announcer::new("a", recorder.clone()));
        signal.connect(key, &receiver, "a", Announcer::handle);

        signal.emit(key, ());
    }

    assert_eq!(*recorder.borrow(), &["a", "b", "c"]);
}

#[test]
#[should_panic(expected = "Signal::connect name already exists: \"name\"")]
fn dual_connect_different_object() {
    let mut key = Key::acquire();
    let signal = Signal::<()>::new();

    {
        let key = &mut key;

        let receiver = Rc::new(KeyCell::new(0, ()));
        signal.connect(key, &receiver, "name", |_, _| {});

        let receiver = Rc::new(KeyCell::new(0, ()));
        signal.connect(key, &receiver, "name", |_, _| {});
    }
}

#[test]
#[should_panic(expected = "Signal::connect name already exists: \"name\"")]
fn dual_connect_same_object() {
    let mut key = Key::acquire();
    let signal = Signal::<()>::new();

    {
        let key = &mut key;

        let receiver = Rc::new(KeyCell::new(0, ()));
        signal.connect(key, &receiver, "name", |_, _| {});
        signal.connect(key, &receiver, "name", |_, _| {});
    }
}

#[test]
fn drop_connect() {
    let mut key = Key::acquire();
    let signal = Signal::<()>::new();

    {
        let key = &mut key;

        let receiver = Rc::new(KeyCell::new(0, ()));
        signal.connect(key, &receiver, "name", |_, _| {});

        drop(receiver);

        let receiver = Rc::new(KeyCell::new(0, ()));
        signal.connect(key, &receiver, "name", |_, _| {});
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
                this.meta().signal.connect(
                    key,
                    &this.meta().this,
                    format!("{}", index),
                    Self::handle,
                );
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

    signal.connect(&mut key, &sc, "0", SelfConnector::handle);
    signal.emit(&mut key, ());

    assert_eq!(&*recorder.borrow(), &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
}

#[test]
#[should_panic(expected = "Signal::connect: object must have a strong reference")]
fn weak_without_strong_panics() {
    let key = &mut Key::acquire();
    let signal = Signal::new();

    Rc::new_cyclic(|weak| {
        signal.connect(key, weak, "", |_, _: &()| {});
        KeyCell::new(0, ())
    });
}
