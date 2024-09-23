//! Implementations of [`Tree`].

pub mod rooted;
pub use rooted::Rooted;

pub mod adelson_velsky_landis;
pub use adelson_velsky_landis::AdelsonVelsoLandis;

use super::Graph;
use super::Collection;

pub trait Tree : Graph {
    #[must_use]
    fn leaves(&self) -> impl Iterator<Item = &Self::Node>;

    #[must_use]
    fn breadth(&self) -> usize {
        self.leaves().count()
    }

    #[must_use]
    fn height(&self) -> usize;
}

pub trait Node : super::Node {
    #[must_use]
    fn is_leaf(&self) -> bool;

    #[must_use]
    fn is_branch(&self) -> bool;
}
