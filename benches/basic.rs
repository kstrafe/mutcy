#![feature(arbitrary_self_types)]
use criterion::{Criterion, black_box, criterion_group, criterion_main};
use mutcy::*;

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("enter-scope", |bench| {
        let mut assoc = Own::new();
        bench.iter(|| {
            assoc.enter(black_box(|_: Mut<()>| {}));
        });
    });

    c.bench_function("recursive-ping-pong", |bench| {
        struct A {
            b: Option<Res<B>>,
        }

        impl A {
            fn subtract_and_call(self: Mut<Self>, count: usize) {
                self.b
                    .as_ref()
                    .unwrap()
                    .own()
                    .via(self)
                    .subtract_and_call(count - 1);
            }
        }

        struct B {
            a: Res<A>,
        }

        impl B {
            fn subtract_and_call(self: Mut<Self>, count: usize) {
                if count > 1 {
                    black_box(self.a.own())
                        .via(self)
                        .subtract_and_call(count - 1);
                }
            }
        }

        let mut assoc = Own::new();

        assoc.enter(|key| {
            let a = Res::new(A { b: None });
            let b = Res::new(B { a: a.clone() });

            a.own().via(key).b = Some(b.clone());
            let mut ax = a.via(key);

            bench.iter(|| {
                ax.subtract_and_call(black_box(1000));
            });

            ax.b = None;
        });
    });

    c.bench_function("callback", |bench| {
        let own = &mut Own::new();
        let item = Res::new_in(123, own);
        let cb = Callback::new(&item, |this, arg| **this + arg);

        bench.iter(|| {
            assert_eq!(Some(124), cb.call(black_box(own), black_box(1)));
        });
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
