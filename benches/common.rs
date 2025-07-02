use std::ops::Range;

use rand::{
    distr::{Alphanumeric, Distribution, StandardUniform},
    seq::SliceRandom,
    Rng, SeedableRng,
};

pub fn get_samples(
    seed: u64,
    prefix_count: usize,
    prefix_sizes: Range<usize>,
    suffix_count: usize,
    suffix_size: usize,
) -> Vec<String>
where
    StandardUniform: Distribution<u64>,
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
            keys.push(key);
        }
    }
    keys.shuffle(&mut rng);
    keys
}
