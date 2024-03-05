use std::{collections::HashMap, ops::Range};

use rand::{distributions::Alphanumeric, seq::SliceRandom, Rng};
use yaart::ART;

fn get_key_samples(
    prefix_sizes: Range<usize>,
    suffix_count: usize,
    suffix_size: usize,
) -> Vec<String> {
    let mut keys = Vec::new();
    for prefix_len in prefix_sizes {
        let prefix1: String = rand::thread_rng()
            .sample_iter(Alphanumeric)
            .map(char::from)
            .take(prefix_len)
            .collect();
        let prefix2: String = rand::thread_rng()
            .sample_iter(Alphanumeric)
            .map(char::from)
            .take(prefix_len)
            .collect();
        let prefix3: String = rand::thread_rng()
            .sample_iter(Alphanumeric)
            .map(char::from)
            .take(prefix_len)
            .collect();

        for _ in 0..suffix_count {
            let mut prefix = String::new();
            match suffix_count % 3 {
                0 => prefix.push_str(&prefix1),
                1 => {
                    prefix.push_str(&prefix1);
                    prefix.push_str(&prefix2);
                }
                _ => {
                    prefix.push_str(&prefix1);
                    prefix.push_str(&prefix2);
                    prefix.push_str(&prefix3);
                }
            }

            let suffix: String = rand::thread_rng()
                .sample_iter(Alphanumeric)
                .map(char::from)
                .take(suffix_size)
                .collect();

            keys.push(prefix + &suffix);
        }
    }
    let mut rng = rand::thread_rng();
    keys.shuffle(&mut rng);
    keys
}

fn main() {
    let keys = get_key_samples(0..8, 1024, 16);
    let mut rng = rand::thread_rng();
    let mut tree = ART::<_, _, 10>::default();
    let mut hash = HashMap::new();

    for key in keys {
        let v: u32 = rng.gen();
        tree.insert(key.clone(), v);
        hash.insert(key.clone(), v);
    }

    println!("================================");
    println!("{:?}", tree);
}
