mod tree;

use criterion::criterion_main;

criterion_main!(tree::baseline::bench_baseline_group, tree::dict_insert::bench_dict_insert_group);
