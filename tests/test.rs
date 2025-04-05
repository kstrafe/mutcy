#![feature(arbitrary_self_types)]
use mutcy::{Callback, Mut, Own, Res, WeakRes};

#[test]
#[should_panic(expected = "assoc is not identical")]
fn different_assocs() {
    let assoc1 = Own::new();
    let mut assoc2 = Own::new();

    let item = Res::new_in((), &assoc1);
    drop(assoc1);

    assoc2.enter(|x| {
        item.via(x);
    });
}

#[test]
fn deferred_destruction() {
    struct A {
        this: Option<Res<A>>,
        destroyed: bool,
    }

    impl A {
        fn recur(self: Mut<Self>, count: usize) {
            if count == 0 {
                self.this = None;
            } else {
                self.this.as_ref().unwrap().own().via(self).recur(count - 1)
            }
        }
    }

    impl Drop for A {
        fn drop(&mut self) {
            self.destroyed = true;
        }
    }

    let mut assoc = Own::new();

    let a = Res::new_in(
        A {
            this: None,
            destroyed: false,
        },
        &assoc,
    );

    assoc.enter(|x| {
        let mut a_mut = a.own().via(x);
        a_mut.this = Some(a);
        a_mut.recur(10);
    });
}

#[test]
fn unsize_array_res() {
    let key = &mut Own::new();

    let array: Res<[u8]> = Res::new_in([0u8; 1024], key);
    array.via(key)[1023] = 123;
}

#[test]
fn unsize_array_weakres() {
    let key = &mut Own::new();

    let array: Res<[u8; 1024]> = Res::new_in([0u8; 1024], key);
    let weak: WeakRes<[u8; 1024]> = Res::downgrade(&array);
    let weak: WeakRes<[u8]> = weak;

    let array = weak.upgrade().unwrap();
    array.via(key)[1023] = 123;
}

#[test]
fn callback_from_strong() {
    let own = &mut Own::new();
    let item = Res::new_in(123, own);

    let cb = Callback::new(&item, |this, args| **this + args);

    assert_eq!(cb.own().call(own, 1), Some(124));
    drop(item);
    assert_eq!(cb.own().call(own, 1), None);
}

#[test]
fn callback_from_weak() {
    let own = &mut Own::new();
    let item = Res::new_in(123, own);

    let weak = Res::downgrade(&item);

    let cb = Callback::new(&weak, |this, args| **this + args);

    assert_eq!(cb.own().call(own, 1), Some(124));
    drop(item);
    assert_eq!(cb.own().call(own, 1), None);
}

#[test]
#[should_panic(expected = "assoc is not identical")]
fn callback_different_assocs() {
    let own1 = &mut Own::new();
    let own2 = &mut Own::new();

    let item = Res::new_in(123, own1);

    let cb = Callback::new(&item, |_, _| {});

    cb.call(own2, ());
}
