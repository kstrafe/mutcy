#![feature(arbitrary_self_types)]
use mutcy::{Assoc, Mut, Res, WeakRes};

#[test]
#[should_panic(expected = "assoc is not identical")]
fn different_assocs() {
    let assoc1 = Assoc::new();
    let mut assoc2 = Assoc::new();

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
        fn recur(self: &mut Mut<Self>, count: usize) {
            if count == 0 {
                self.this = None;
            } else {
                self.this
                    .as_ref()
                    .unwrap()
                    .mutate()
                    .via(self)
                    .recur(count - 1)
            }
        }
    }

    impl Drop for A {
        fn drop(&mut self) {
            self.destroyed = true;
        }
    }

    let mut assoc = Assoc::new();

    let a = Res::new_in(
        A {
            this: None,
            destroyed: false,
        },
        &assoc,
    );

    assoc.enter(|x| {
        let mut a_mut = a.mutate().via(x);
        a_mut.this = Some(a);
        a_mut.recur(10);
    });
}

#[test]
fn unsize_array_res() {
    let mut assoc = Assoc::new();
    let key = &mut assoc.key();

    let array: Res<[u8]> = Res::new_in([0u8; 1024], key);
    array.via(key)[1023] = 123;
}

#[test]
fn unsize_array_weakres() {
    let mut assoc = Assoc::new();
    let key = &mut assoc.key();

    let array: Res<[u8; 1024]> = Res::new_in([0u8; 1024], key);
    let weak: WeakRes<[u8; 1024]> = Res::downgrade(&array);
    let weak: WeakRes<[u8]> = weak;

    let array = weak.upgrade().unwrap();
    array.via(key)[1023] = 123;
}
