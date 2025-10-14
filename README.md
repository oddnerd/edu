# edu

This repository contains development artifacts for the `edu` library, an
educational reference alternative standard library for the Rust programming
language.

This project exists to accomplish two goals:

1. To organize a collections of high-quality, trustworthy educational reference
   implementations for myself and others;
2. To act as a portfolio piece to exhibit my software engineering
   craftsmanship.

Notably, this explicitly does _not_ include being a drop-in replacement
for the `std` crate. In fact, most implementations still base their interfaces
around `core` types such as `Default` and `FromIterator`. It does,
nevertheless, reimplement most types to exhibit how I believe one ought to look
in optimal conditions when not bound to consumers. This repository is not
merely reformatting existing implementations available online; the code here
is hand-written from scratch without the use of any artificial intelligence
providing implementation truly worthy of reference.

## Building

This project relies solely upon Rust, no other applications or libraries.

To build a release binary, run `cargo build --release`. This will enable
optimizations and strip the binary.

To run the test suite and prove correctness, run `cargo test --tests`. This
will compile a development build and automatically run all unit and integration
tests.

To verify all documentation examples both compile and have the expected runtime
behaviour, run `cargo test --doc`. This will compile a development build and
automatically run all example snippets as separate binaries.

## Contributing

This project is intended the be a lone adventure. Nevertheless, there exists
extensive [documentation](CONTRIBUTING.md) about my development process to
further highlight the skills I can bring to a development team.
