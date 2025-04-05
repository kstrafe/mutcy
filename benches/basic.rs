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
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
