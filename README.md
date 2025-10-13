# edu

This repository contains development artifacts for the `edu` library, a collection of various implementations of core computer science utilities written in the Rust language.

This project exists to accomplish two goals:

1. To organize a collections of high-quality, trustworthy educational reference implementations for myself and others;
2. To act as a portfolio piece to exhibit my software engineering craftsmanship.

## Code Quality

The code contained is not merely a translation into Rust of listings found online---it is hand-written optimizing for clarity sufficient for being an education reference. Moreover, thanks to the wonders of modern compilers, the lower-complexity that makes this code easy to read also makes it easier to automagically optimize.

Rust's standardized Clippy static analysis tool is used offensively to restrict compilation to only code worthy of it. The vast majority of lints offered have been enabled, and the vast majority of those have been upgraded from warnings to compilation errors.

## Testing

Unlike other online references which one merely hopes are correct, this repository is extensively tested providing certainty about what behaviour the code exhibits under various preconditions. No framework is used, behaviour-driven-development (BDD) style tests (given/when/then) are transparently implemented inside source code modules using Rust's standardized integration. Tests are parameterized when applicable via for-loops.

## Documentation

Although it is not expected for this library to be depended upon, consumer-facing documentation is required via Clippy for all public interfaces. These contain not only a brief description intended for tooltip is text-editor tooling, but also detailed explanation, memory and runtime performance notes including asymptotic complexity, and a runnable example that is automatically tested via Rust's Cargo build system.

## Project Management

The development of this project has been methodical therefore enabling potential reviewers ease with organization. Commit messages have been standardized based on the [Angular](https://github.com/angular/angular/blob/main/contributing-docs/commit-message-guidelines.md) guidelines, alongside issues and pull-requests being templatized.
