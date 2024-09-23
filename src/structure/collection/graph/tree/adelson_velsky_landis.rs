//! Implementation of [`AdelsonVelskyLandis`].

use super::Collection;
use super::Graph;
use super::Rooted;
use super::Tree;

pub struct AdelsonVelsoLandis<T> {
    root: Option<Box<Node<T>>>,
}

impl<T> AdelsonVelsoLandis<T> {
    pub fn insert(&mut self, element: T) -> Result<&mut T, T> {
        let new = Box::new(Node {
            data: element,
            height: 0,
            left: None,
            right: None,
        });

        if self.root.is_none() {
            return Ok(&mut self.root.insert(new).data);
        }

        Err(new.data)
    }
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
    clippy::expect_used,
    clippy::assertions_on_result_states
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

                assert!(instance.insert(12345).is_ok());

                assert!(instance.root.is_some());
                assert_eq!(instance.root.unwrap().data, 12345);
            }

        }
    }
}
