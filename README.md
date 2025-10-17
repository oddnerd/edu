# edu

This repository contains development artifacts for the `edu` library, a
collection of implementations in the Rust programming language for education
reference.

This project exists to accomplish two goals:

1. To organize a collection of high-quality reference implementations for
   myself and others;
2. To act as a portfolio piece to exhibit my software engineering
   craftsmanship.

This repository is not merely reformatting existing implementations available
online; the code here is hand-written from scratch without the use of any
artificial intelligence providing implementations truly worthy of reference.

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
