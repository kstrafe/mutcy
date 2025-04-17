use criterion::{Criterion, black_box, criterion_group, criterion_main};
use mutcy::*;

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("count-1M-native", |bench| {
        let mut x = 0;
        bench.iter(|| {
            x = 0;
            for _ in 0..1_000_000 {
                x += black_box(1);
            }
        });
    });

    c.bench_function("count-1M-keycell", |bench| {
        let mut key = Key::acquire();

        let x = KeyCell::new(0usize, ());

        bench.iter(|| {
            *x.borrow_mut(&mut key) = 0;
            for _ in 0..1_000_000 {
                *x.borrow_mut(&mut key) += black_box(1);
            }
        });
    });

    c.bench_function("recursion-native", |bench| {
        fn ping_pong(a: &mut i32, b: &mut i32) {
            if *a > 0 {
                *a -= black_box(1);
                *b += black_box(1);

                ping_pong(a, b);
            }
        }

        bench.iter(|| {
            let mut a = 1000;
            let mut b = 0;
            ping_pong(&mut a, &mut b);
        });
    });

    c.bench_function("recursion-keycell", |bench| {
        fn ping_pong(a: KeyMut<i32>, b: &KeyCell<i32>) {
            if **a > 0 {
                **a -= black_box(1);

                let (_, key) = Key::split(a);
                *b.borrow_mut(key) += black_box(1);

                ping_pong(a, b);
            }
        }

        let mut key = Key::acquire();

        bench.iter(|| {
            let a = KeyCell::new(1000, ());
            let b = KeyCell::new(0, ());
            ping_pong(&mut a.borrow_mut(&mut key), &b);
        });
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
