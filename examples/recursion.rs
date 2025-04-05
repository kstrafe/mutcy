#![feature(arbitrary_self_types)]
use mutcy::*;
use std::rc::{Rc, Weak};

fn main() {
    let mut key = Key::acquire();

    struct A {
        b: Weak<KeyCell<B>>,
    }

    impl Meta for A {
        type Data = ();
    }

    impl A {
        fn work_a(self: KeyMut<Self>, value: i32) {
            println!("A: {}", value);

            if value < 10 {
                let b = self.b.upgrade().unwrap();
                let (_, key) = Key::split(self);
                b.borrow_mut(key).work_b(value + 1);
            }
        }
    }

    struct B {}

    impl Meta for B {
        type Data = Rc<KeyCell<A>>;
    }

    impl B {
        fn work_b(self: KeyMut<Self>, value: i32) {
            println!("B: {}", value);

            let (this, key) = Key::split(self);
            this.meta().borrow_mut(key).work_a(value + 1);
        }
    }

    let a = Rc::new(KeyCell::new(A { b: Weak::new() }, ()));
    let b = Rc::new(KeyCell::new(B {}, a.clone()));
    a.borrow_mut(&mut key).b = Rc::downgrade(&b);

    a.borrow_mut(&mut key).work_a(0);
}
