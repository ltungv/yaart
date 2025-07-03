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

    let mut radix = RadixTreeMap::<String, usize, 4>::new();
    {
        let start = Instant::now();
        assert!(radix.is_empty());
        for (i, w) in words.clone().into_iter().enumerate() {
            assert!(radix.insert(w, i).is_none());
        }
        println!("INSERT (ART) {:?}", start.elapsed());
    };
    {
        let start = Instant::now();
        assert_eq!(radix.len(), words.len());
        for (i, w) in words.iter().enumerate() {
            assert_eq!(radix.get(w), Some(&i));
        }
        println!("SEARCH (ART) {:?}", start.elapsed());
    }
    {
        let start = Instant::now();
        for (i, w) in words.iter().enumerate() {
            assert_eq!(radix.remove(w), Some(i));
        }
        assert!(radix.is_empty());
        println!("DELETE (ART) {:?}", start.elapsed());
    }

    let mut btree = BTreeMap::new();
    {
        let start = Instant::now();
        assert!(btree.is_empty());
        for (i, w) in words.clone().into_iter().enumerate() {
            assert!(btree.insert(w, i).is_none());
        }
        println!("INSERT (BTREE) {:?}", start.elapsed());
    };
    {
        let start = Instant::now();
        assert_eq!(btree.len(), words.len());
        for (i, w) in words.iter().enumerate() {
            assert_eq!(btree.get(w), Some(&i));
        }
        println!("SEARCH (BTREE) {:?}", start.elapsed());
    }
    {
        let start = Instant::now();
        for (i, w) in words.iter().enumerate() {
            assert_eq!(btree.remove(w), Some(i));
        }
        assert!(btree.is_empty());
        println!("DELETE (BTREE) {:?}", start.elapsed());
    }
}
