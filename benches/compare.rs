use std::{collections::BTreeMap, rc::Rc};

use criterion::{criterion_group, criterion_main, Criterion};
use rand::{distr::Alphanumeric, seq::SliceRandom, Rng};
use yaart::ART;

fn get_samples(
    prefix_sizes: std::ops::Range<usize>,
    suffix_count: usize,
    suffix_size: usize,
) -> Vec<(Rc<str>, u32)> {
    let random_string = |size: usize| {
        rand::rng()
            .sample_iter(Alphanumeric)
            .map(char::from)
            .take(size)
            .collect::<String>()
    };
    let mut rng = rand::rng();
    let mut keys = Vec::new();
    for prefix_size in prefix_sizes {
        let prefix1: String = random_string(prefix_size);
        let prefix2: String = random_string(prefix_size);
        let prefix3: String = random_string(prefix_size);
        for suffix_index in 0..suffix_count {
            let mut key = String::new();
            match suffix_index % 3 {
                0 => key.push_str(&prefix1),
                1 => {
                    key.push_str(&prefix1);
                    key.push_str(&prefix2);
                }
                _ => {
                    key.push_str(&prefix1);
                    key.push_str(&prefix2);
                    key.push_str(&prefix3);
                }
            }
            key.push_str(&random_string(suffix_size));
            keys.push((Rc::from(key), rng.random()));
        }
    }
    keys.shuffle(&mut rng);
    keys
}

pub fn compare(c: &mut Criterion) {
    c.bench_function("radix", |b| {
        b.iter_batched(
            || get_samples(3..24, 32, 4),
            |samples| {
                let mut radix = ART::<_, _, 10>::default();
                for (k, v) in samples.iter() {
                    radix.insert(k.clone(), *v);
                }
            },
            criterion::BatchSize::LargeInput,
        )
    });
    c.bench_function("btree", |b| {
        b.iter_batched(
            || get_samples(3..24, 32, 4),
            |samples| {
                let mut btree = BTreeMap::new();
                for (k, v) in samples.iter() {
                    btree.insert(k.clone(), *v);
                }
            },
            criterion::BatchSize::LargeInput,
        )
    });
}

criterion_group!(benches, compare);
criterion_main!(benches);
