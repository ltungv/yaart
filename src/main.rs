use yaart::Tree;

fn main() {
    let mut tree = Tree::<String, String>::default();
    tree.insert("hello".to_string(), "world".to_string());
    tree.insert("world".to_string(), "hello".to_string());
    print!("{:?}", tree);
}
