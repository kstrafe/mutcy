use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};
use mutcy::*;

fn criterion_benchmark(c: &mut Criterion) {
    {
        let mut group = c.benchmark_group("count");
        const COUNT: u64 = 1_000_000;
        group.throughput(Throughput::Elements(COUNT));

        group.bench_function("native", |bench| {
            let mut x = 0;
            bench.iter(|| {
                x = 0;
                for _ in 0..COUNT {
                    x += black_box(1);
                }
            });
        });

        group.bench_function("keycell", |bench| {
            let mut key = Key::acquire();

            let x = KeyCell::new(0usize, ());

            bench.iter(|| {
                *x.borrow_mut(&mut key) = 0;
                for _ in 0..COUNT {
                    *x.borrow_mut(&mut key) += black_box(1);
                }
            });
        });

        group.finish();
    }

    {
        let mut group = c.benchmark_group("recursion");
        const COUNT: u64 = 1000;
        group.throughput(Throughput::Elements(COUNT));

        group.bench_function("native", |bench| {
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

        group.bench_function("keycell", |bench| {
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

        group.finish();
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
