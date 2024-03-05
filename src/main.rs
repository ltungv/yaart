use std::{collections::HashMap, ops::Range};

use rand::{distributions::Alphanumeric, seq::SliceRandom, Rng};
use yaart::ART;

fn get_key_samples(
    prefix_sizes: Range<usize>,
    suffix_count: usize,
    suffix_size: usize,
) -> Vec<String> {
    let random_string = |size: usize| {
        rand::thread_rng()
            .sample_iter(Alphanumeric)
            .map(char::from)
            .take(size)
            .collect::<String>()
    };
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
            keys.push(key);
        }
    }
    let mut rng = rand::thread_rng();
    keys.shuffle(&mut rng);
    keys
}

fn main() {
    let keys = get_key_samples(3..5, 32, 4);
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
