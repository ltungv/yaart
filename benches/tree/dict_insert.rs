use criterion::{criterion_group, Criterion};
use rand::{
    rngs::StdRng,
    seq::{IndexedRandom, SliceRandom},
    SeedableRng,
};
use yaart::RadixTreeMap;

fn insert(words: Vec<String>) -> RadixTreeMap<String, usize> {
    let mut art = RadixTreeMap::new();
    for (idx, word) in words.into_iter().enumerate() {
        art.insert(word, idx);
    }
    art
}

fn bench(c: &mut Criterion) {
    let mut rng = StdRng::seed_from_u64(69420);
    let mut words: Vec<_> = include_str!("../data/medium-dict.txt").lines().map(String::from).collect();
    let bytes = words.iter().map(String::len).sum::<usize>();

    words.dedup();
    words.sort();

    let mut rev_words = words.clone();
    rev_words.reverse();

    let mut rand_words = words.clone();
    rand_words.shuffle(&mut rng);

    let mut part_words: Vec<_> = words.choose_multiple(&mut rng, 50_000).cloned().collect();
    part_words.sort();

    let mut rev_part_words = part_words.clone();
    rev_part_words.reverse();

    let mut rand_part_words = part_words.clone();
    rand_part_words.shuffle(&mut rng);

    let part_bytes: usize = part_words.iter().map(|w| w.len()).sum();
    {
        let mut group = c.benchmark_group("dict/words/full");
        group.throughput(criterion::Throughput::Bytes(bytes as u64));
        group.bench_function("insert/asc", |b| b.iter_batched(|| words.clone(), insert, criterion::BatchSize::SmallInput));
        group.bench_function("insert/desc", |b| b.iter_batched(|| rev_words.clone(), insert, criterion::BatchSize::SmallInput));
        group
            .bench_function("insert/rand", |b| b.iter_batched(|| rand_words.clone(), insert, criterion::BatchSize::SmallInput));
    }
    {
        let mut group = c.benchmark_group("dict/words/part");
        group.throughput(criterion::Throughput::Bytes(part_bytes as u64));
        group.bench_function("insert/asc", |b| b.iter_batched(|| part_words.clone(), insert, criterion::BatchSize::SmallInput));
        group.bench_function("insert/desc", |b| {
            b.iter_batched(|| rev_part_words.clone(), insert, criterion::BatchSize::SmallInput)
        });
        group.bench_function("insert/rand", |b| {
            b.iter_batched(|| rand_part_words.clone(), insert, criterion::BatchSize::SmallInput)
        });
    }
}

criterion_group!(bench_dict_insert_group, bench);
