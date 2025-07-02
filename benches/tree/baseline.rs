use std::collections::BTreeMap;

use criterion::{criterion_group, Criterion};
use yaart::RadixTreeMap;

use crate::common::get_samples;

fn btree_insert(samples: Vec<String>) -> BTreeMap<String, usize> {
    let mut btree = BTreeMap::new();
    for (idx, word) in samples.into_iter().enumerate() {
        btree.insert(word, idx);
    }
    btree
}

fn radix_insert(samples: Vec<String>) -> RadixTreeMap<String, usize> {
    let mut radix = RadixTreeMap::new();
    for (idx, word) in samples.into_iter().enumerate() {
        radix.insert(word, idx);
    }
    radix
}

pub fn bench(c: &mut Criterion) {
    let samples = get_samples(rand::random(), 32, 2..18, 256, 8);
    let nbytes = samples.iter().map(|s| s.len() as u64).sum();
    {
        let mut group = c.benchmark_group("baseline/get");
        group.throughput(criterion::Throughput::Bytes(nbytes));
        group.bench_function("btree", |b| {
            b.iter_batched(
                || {
                    let btree = btree_insert(samples.clone());
                    (&samples, btree)
                },
                |(samples, tree)| {
                    for (idx, word) in samples.iter().enumerate() {
                        assert_eq!(tree.get(word), Some(&idx));
                    }
                },
                criterion::BatchSize::SmallInput,
            )
        });
        group.bench_function("radix", |b| {
            b.iter_batched(
                || {
                    let radix = radix_insert(samples.clone());
                    (&samples, radix)
                },
                |(samples, tree)| {
                    for (idx, word) in samples.iter().enumerate() {
                        assert_eq!(tree.get(word), Some(&idx));
                    }
                },
                criterion::BatchSize::SmallInput,
            )
        });
    }
    {
        let mut group = c.benchmark_group("baseline/insert");
        group.throughput(criterion::Throughput::Bytes(nbytes));
        group.bench_function("btree", |b| {
            b.iter_batched(
                || samples.clone(),
                btree_insert,
                criterion::BatchSize::SmallInput,
            )
        });
        group.bench_function("radix", |b| {
            b.iter_batched(
                || samples.clone(),
                radix_insert,
                criterion::BatchSize::SmallInput,
            )
        });
    }
}

criterion_group!(bench_baseline_group, bench);
