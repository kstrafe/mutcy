use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};
use mutcy::*;
use std::{
    rc::Rc,
    time::{Duration, Instant},
};

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
                *x.rw(&mut key) = 0;
                for _ in 0..COUNT {
                    *x.rw(&mut key) += black_box(1);
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
            fn ping_pong(a: Rw<i32>, b: &KeyCell<i32>) {
                if **a > 0 {
                    **a -= black_box(1);

                    let (_, key) = Key::split_rw(a);
                    *b.rw(key) += black_box(1);

                    ping_pong(a, b);
                }
            }

            let mut key = Key::acquire();

            bench.iter(|| {
                let a = KeyCell::new(1000, ());
                let b = KeyCell::new(0, ());
                ping_pong(&mut a.rw(&mut key), &b);
            });
        });

        group.finish();
    }

    {
        let mut group = c.benchmark_group("signal");
        const COUNT: u64 = 1000;
        group.throughput(Throughput::Elements(COUNT));

        group.bench_function("empty", |bench| {
            let mut key = Key::acquire();
            let signal = Signal::new();
            bench.iter(|| {
                for _ in 0..COUNT {
                    signal.emit(&mut key, ());
                }
            });
        });

        group.bench_function("receivers", |bench| {
            let mut key = Key::acquire();
            let signal = Signal::new();

            let mut receivers = Vec::new();

            for idx in 0..COUNT {
                let receiver = Rc::new(KeyCell::new(idx, ()));

                signal.connect(&mut key, &receiver, |this, _: &()| {
                    **this += black_box(1);
                });

                receivers.push(receiver);
            }

            bench.iter(|| {
                black_box(&signal).emit(&mut key, ());
            });
        });

        group.finish();
    }

    {
        let mut group = c.benchmark_group("callback");
        const COUNT: u64 = 1000;
        group.throughput(Throughput::Elements(COUNT));

        group.bench_function("empty", |bench| {
            let mut key = Key::acquire();
            let receiver = Rc::new(KeyCell::new(0, ()));
            let callback = Callback::new(&receiver, |_, _: ()| {});

            bench.iter(|| {
                for _ in 0..COUNT {
                    callback.call(&mut key, ());
                }
            });
        });
    }

    {
        let mut group = c.benchmark_group("disconnection");
        const COUNT: u64 = 1_000_000;
        group.bench_function("needle", |bench| {
            let mut key = Key::acquire();
            let signal: Signal<()> = Signal::new();
            let receiver = Rc::new(KeyCell::new(0, ()));

            for _ in 0..COUNT {
                signal.before().connect(&mut key, &receiver, |_, _| {});
            }

            bench.iter_custom(|iters| {
                let mut elapsed = Duration::new(0, 0);

                for _ in 0..iters {
                    let connection = signal.connect(&mut key, &receiver, |_, _| {});
                    let start = Instant::now();
                    connection.disconnect(&mut key);
                    elapsed += start.elapsed()
                }

                elapsed
            });
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
