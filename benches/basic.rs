#![feature(arbitrary_self_types)]
use criterion::{Criterion, black_box, criterion_group, criterion_main};
use mutcy::*;

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("enter-scope", |bench| {
        let mut assoc = Assoc::new();
        bench.iter(|| {
            assoc.enter(black_box(|_: &mut Mut<()>| {}));
        });
    });

    c.bench_function("recursive-ping-pong", |bench| {
        struct A {
            b: Option<Res<B>>,
        }

        impl A {
            fn subtract_and_call(self: &mut Mut<Self>, count: usize) {
                self.b
                    .as_ref()
                    .unwrap()
                    .mutate()
                    .via(self)
                    .subtract_and_call(black_box(count - 1));
            }
        }

        struct B {
            a: Res<A>,
        }

        impl B {
            fn subtract_and_call(self: &mut Mut<Self>, count: usize) {
                if count > 1 {
                    black_box(self.a.mutate())
                        .via(self)
                        .subtract_and_call(count - 1);
                }
            }
        }

        let mut assoc = Assoc::new();

        assoc.enter(|key| {
            let a = Res::new(A { b: None });
            let b = Res::new(B { a: a.clone() });

            a.mutate().via(key).b = Some(b.clone());
            let mut ax = a.via(key);

            bench.iter(|| {
                ax.subtract_and_call(black_box(1000));
            });

            ax.b = None;
        });
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
