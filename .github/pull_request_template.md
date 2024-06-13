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
- [ ] Naming consistent with existing body?
- [ ] Organized into a module hierarchy?
- [ ] `cargo test --tests` passes?
- [ ] `MIRIFLAGS="-Zmiri-disable-stacked-borrows" cargo +nightly miri test` passes?

#### Style

- [ ] Considered [exception safety](https://doc.rust-lang.org/nomicon/exception-safety.html)?
- [ ] `cargo check` passes?
- [ ] `cargo clippy` passes?
- [ ] `cargo fmt` passes?

#### Chores

- [ ] Bumped version?
- [ ] Added link to readme?
- [ ] Rebased branch for clean commit history?
