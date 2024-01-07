use yaart::Tree;

fn main() {
    let mut tree = Tree::default();
    tree.insert("and".to_string(), ());
    tree.insert("ant".to_string(), ());
    tree.insert("any".to_string(), ());
    tree.insert("are".to_string(), ());
    tree.insert("art".to_string(), ());
    println!("{:?}", tree);
}
