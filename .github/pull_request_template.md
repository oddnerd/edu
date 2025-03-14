### Description

Closes #

### Checklist

#### Documentation

- [ ] Public **and** private symbols described?
- [ ] Performance considerations for all subroutines?
  - [ ] Time complexity?
  - [ ] Memory complexity?
- [ ] Examples for public interfaces?
  - [ ] `cargo test --doc` passes?
- [ ] `cargo doc --document-private-items` passes?

#### Testing

- [ ] All post-conditions tested?
- [ ] Dedicated tests for edge-cases?
- [ ] Naming consistent with the existing codebase?
- [ ] Organized into a module hierarchy?
- [ ] `cargo test --tests` passes?
- [ ] `MIRIFLAGS="-Zmiri-disable-stacked-borrows" cargo +nightly miri test` passes?
- [ ] Reviewed coverage report via `cargo tarpaulin --fail-immediately --ignored --offline --line --out lcov --engine ptrace`?

#### Style

- [ ] Considered [exception safety](https://doc.rust-lang.org/nomicon/exception-safety.html)?
- [ ] `cargo check` passes?
- [ ] `cargo clippy` passes?
- [ ] `cargo fmt` passes?

#### Chores

- [ ] Bumped version?
- [ ] Link to new features in readme?
- [ ] Rebased branch for clean commit history?
