### Description

Closes #<issue>

### Checklist

#### Testing

- [ ] `cargo test --tests`
- [ ] `cargo +nightly miri test`
- [ ] `cargo tarpaulin --fail-immediately --ignored --offline --line --out lcov --engine ptrace`

#### Documentation

- [ ] `cargo test --doc`
- [ ] `cargo doc --document-private-items`

#### Style

- [ ] `cargo check`
- [ ] `cargo clippy`
- [ ] `cargo fmt`

#### Chores

- [ ] Bumped version?
