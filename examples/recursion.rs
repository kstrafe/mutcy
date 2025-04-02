#![feature(arbitrary_self_types)]
use mutcy::{Assoc, Mut, Res};

fn main() {
    struct A {
        b: Option<Res<B>>,
    }

    impl A {
        fn subtract_and_call(self: &mut Mut<Self>, count: usize) {
            println!("--> A: {}", count);
            self.b
                .as_ref()
                .unwrap()
                .mutate()
                .via(self)
                .subtract_and_call(count - 1);
            println!("<-- A: Unwinding {}", count);
        }

        fn remove_b(self: &mut Mut<Self>) {
            self.b = None;
        }
    }

    impl Drop for A {
        fn drop(&mut self) {
            println!("A dropped");
        }
    }

    struct B {
        a: Res<A>,
    }

    impl B {
        fn subtract_and_call(self: &mut Mut<Self>, count: usize) {
            println!("--> B: {}", count);
            let mut a = self.a.mutate().via(self);
            if count > 1 {
                a.subtract_and_call(count - 1);
            } else {
                a.remove_b();
            }
            println!("<-- B: Unwinding {}", count);
        }
    }

    impl Drop for B {
        fn drop(&mut self) {
            println!("B dropped");
        }
    }

    let mut assoc = Assoc::default();

    let a = Res::new_in(A { b: None }, &assoc);
    let b = Res::new_in(B { a: a.clone() }, &assoc);

    assoc.enter(move |x| {
        let mut ax = a.mutate().via(x);
        ax.b = Some(b.clone());
        ax.subtract_and_call(10);
    });
}
