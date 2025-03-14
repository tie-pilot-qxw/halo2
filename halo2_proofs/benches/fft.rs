#[macro_use]
extern crate criterion;

use crate::arithmetic::best_fft;
use group::ff::Field;
use halo2_proofs::*;
use halo2curves::pasta::Fp;

use criterion::{BenchmarkId, Criterion};
use rand_core::{OsRng, SeedableRng};
use rand_xorshift::XorShiftRng; // Faster than OsRng
use rayon::iter::{IntoParallelIterator, ParallelIterator};

fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("fft");
    for k in 3..=24 {
        let omega = Fp::random(OsRng); // More realistic to use the same omega
        group.bench_function(BenchmarkId::new("k", k), |b| {
            let mut a = (0..(1 << k)).into_par_iter().map(|_| Fp::random(XorShiftRng::from_rng(OsRng).unwrap())).collect::<Vec<_>>(); // parallel data generation
            b.iter(|| {
                best_fft(&mut a, omega, k as u32);
            });
        }).sample_size(10);
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
