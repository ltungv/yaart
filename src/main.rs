use std::{
    collections::BTreeMap,
    fs::File,
    io::{BufRead, BufReader},
    time::Instant,
};

use yaart::RadixTreeMap;

fn main() {
    let path = std::env::args().nth(1).unwrap();
    let file = File::open(path).unwrap();
    let reader = BufReader::new(file);

    let mut words = Vec::new();
    for line in reader.lines() {
        let Ok(line) = line else {
            continue;
        };
        for word in line.split_whitespace() {
            words.push(word.to_string())
        }
    }

    let mut m = RadixTreeMap::<String, usize, 4>::new();
    {
        let start = Instant::now();
        assert!(m.is_empty());
        for (i, w) in words.clone().into_iter().enumerate() {
            assert!(m.insert(w, i).is_none());
        }
        println!("INSERT (ART) {:?}", start.elapsed());
    };
    {
        let start = Instant::now();
        assert_eq!(m.len(), words.len());
        for (i, w) in words.iter().enumerate() {
            assert_eq!(m.get(w), Some(&i));
        }
        println!("LOOKUP (ART) {:?}", start.elapsed());
    }

    let mut b = BTreeMap::new();
    {
        let start = Instant::now();
        assert!(b.is_empty());
        for (i, w) in words.clone().into_iter().enumerate() {
            assert!(b.insert(w, i).is_none());
        }
        println!("INSERT (BTREE) {:?}", start.elapsed());
    };
    {
        let start = Instant::now();
        assert_eq!(b.len(), words.len());
        for (i, w) in words.iter().enumerate() {
            assert_eq!(b.get(w), Some(&i));
        }
        println!("LOOKUP (BTREE) {:?}", start.elapsed());
    }
}
