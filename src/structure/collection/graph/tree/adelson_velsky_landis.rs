//! Implementation of [`AdelsonVelskyLandis`].

use super::Rooted;
use super::Tree;
use super::Graph;
use super::Collection;

pub struct AdelsonVelskyLandis<T> {
    root: Option<Node<T>>,
}

struct Node<T> {
    data: T,

    height: usize,

    left: Option<Box<Node<T>>>,
    right: Option<Box<Node<T>>>,
}

#[cfg(test)]
#[allow(
    clippy::undocumented_unsafe_blocks,
    clippy::unwrap_used,
    clippy::expect_used
)]
mod test {
    use super::*;

    mod method {
        use super::*;

        mod insert {
            use super::*;

            #[test]
            fn inserts_root_node_when_empty() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                instance.insert(12345);

                assert!(instance.root.is_some());
                assert_eq!(instance.root.unwrap().data, 12345);
            }

        }
    }
}
