//! Implementations of [`Binary`].

pub mod adelson_velsky_landis;

pub use adelson_velsky_landis::AdelsonVelskyLandis;

use super::Tree;
use super::Graph;
use super::Collection;

pub trait Binary : Tree {}
