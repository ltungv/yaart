use std::{collections::BTreeMap, ops::Range};

use criterion::{criterion_group, criterion_main, Criterion};
use rand::{
    distr::{Alphanumeric, Distribution, StandardUniform},
    seq::SliceRandom,
    Rng, SeedableRng,
};
use yaart::ART;

fn get_samples<T>(
    seed: u64,
    prefix_count: usize,
    prefix_sizes: Range<usize>,
    suffix_count: usize,
    suffix_size: usize,
) -> Vec<(String, T)>
where
    StandardUniform: Distribution<T> + Distribution<u64>,
{
    let random_string = |seed: u64, size: usize| {
        rand::rngs::StdRng::seed_from_u64(seed)
            .sample_iter(Alphanumeric)
            .map(char::from)
            .take(size)
            .collect::<String>()
    };
    let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
    let mut keys = Vec::new();
    for prefix_size in prefix_sizes {
        let mut prefixes = Vec::default();
        for _ in 0..prefix_count {
            prefixes.push(random_string(rng.random(), prefix_size));
        }
        for suffix_index in 0..suffix_count {
            let mut key = String::new();
            for prefix in prefixes.iter().take(suffix_index % prefix_count) {
                key.push_str(prefix);
            }
            key.push_str(&random_string(rng.random(), suffix_size));
            keys.push((key, rng.random()));
        }
    }
    keys.shuffle(&mut rng);
    keys
}

pub fn insert(c: &mut Criterion) {
    let samples = get_samples::<u32>(rand::random(), 32, 10..11, 256, 8);
    c.bench_function("btree (insert)", |b| {
        b.iter_batched(
            || &samples,
            |samples| {
                let mut btree = BTreeMap::new();
                for (k, v) in samples.iter() {
                    btree.insert(k.clone(), *v);
                }
            },
            criterion::BatchSize::LargeInput,
        )
    });
    c.bench_function("radix8 (insert)", |b| {
        b.iter_batched(
            || &samples,
            |samples| {
                let mut radix = ART::<_, _, 8>::default();
                for (k, v) in samples.iter() {
                    radix.insert(k.clone(), *v);
                }
            },
            criterion::BatchSize::LargeInput,
        )
    });
    c.bench_function("radix10 (insert)", |b| {
        b.iter_batched(
            || &samples,
            |samples| {
                let mut radix = ART::<_, _, 10>::default();
                for (k, v) in samples.iter() {
                    radix.insert(k.clone(), *v);
                }
            },
            criterion::BatchSize::LargeInput,
        )
    });
    c.bench_function("radix12 (insert)", |b| {
        b.iter_batched(
            || &samples,
            |samples| {
                let mut radix = ART::<_, _, 12>::default();
                for (k, v) in samples.iter() {
                    radix.insert(k.clone(), *v);
                }
            },
            criterion::BatchSize::LargeInput,
        )
    });
}

pub fn search(c: &mut Criterion) {
    let samples = get_samples::<u32>(rand::random(), 32, 2..18, 256, 8);
    c.bench_function("btree (search)", |b| {
        b.iter_batched(
            || {
                let mut btree = BTreeMap::new();
                for (k, v) in samples.iter() {
                    btree.insert(k.clone(), *v);
                }
                (&samples, btree)
            },
            |(samples, tree)| {
                for (k, v) in samples {
                    assert_eq!(tree.get(k), Some(v))
                }
            },
            criterion::BatchSize::LargeInput,
        )
    });
    c.bench_function("radix8 (search)", |b| {
        b.iter_batched(
            || {
                let mut radix = ART::<_, _, 8>::default();
                for (k, v) in samples.iter() {
                    radix.insert(k.clone(), *v);
                }
                (&samples, radix)
            },
            |(samples, tree)| {
                for (k, v) in samples {
                    assert_eq!(tree.search(k), Some(v))
                }
            },
            criterion::BatchSize::LargeInput,
        )
    });
    c.bench_function("radix10 (search)", |b| {
        b.iter_batched(
            || {
                let mut radix = ART::<_, _, 10>::default();
                for (k, v) in samples.iter() {
                    radix.insert(k.clone(), *v);
                }
                (&samples, radix)
            },
            |(samples, tree)| {
                for (k, v) in samples {
                    assert_eq!(tree.search(k), Some(v))
                }
            },
            criterion::BatchSize::LargeInput,
        )
    });
    c.bench_function("radix12 (search)", |b| {
        b.iter_batched(
            || {
                let mut radix = ART::<_, _, 12>::default();
                for (k, v) in samples.iter() {
                    radix.insert(k.clone(), *v);
                }
                (&samples, radix)
            },
            |(samples, tree)| {
                for (k, v) in samples {
                    assert_eq!(tree.search(k), Some(v))
                }
            },
            criterion::BatchSize::LargeInput,
        )
    });
}

criterion_group!(benches, insert, search);
criterion_main!(benches);
