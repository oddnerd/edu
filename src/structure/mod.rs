//! Logical relationships between data.
//!
//! Contained within are [traits][trait] which describe associated behaviour,
//! and [structs][struct] which relate variables. These types exist to
//! [encapsulate][encapsulate] (group together) [methods][method] (functions)
//! that act upon [objects][object] (instances of some cohesive _thing_).
//!
//! See also: [Wikipedia][wikipedia].
//!
//! [trait]: https://doc.rust-lang.org/reference/items/traits.html
//! [struct]: https://doc.rust-lang.org/reference/items/structs.html
//! [encapsulate]: https://en.wikipedia.org/wiki/Encapsulation_(computer_programming)
//! [method]: https://en.wikipedia.org/wiki/Method_(computer_programming)
//! [object]: https://en.wikipedia.org/wiki/Object_(computer_science)
//! [wikipedia]: https://en.wikipedia.org/wiki/Data_structure

pub mod collection;

pub use collection::Collection;
