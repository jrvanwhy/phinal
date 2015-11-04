extern crate phinal;

pub fn main() {
	println!("{:?}", phinal::PhiIter::new().take(20).collect::<Vec<_>>());
}
