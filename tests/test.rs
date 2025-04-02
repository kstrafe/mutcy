#![feature(arbitrary_self_types)]
use mutcy::{Assoc, Mut, Res};

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
