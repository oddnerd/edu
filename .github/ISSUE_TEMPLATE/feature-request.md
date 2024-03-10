---
name: Feature request
about: Suggest an idea
title: ''
labels: 'type: feat'
assignees: oddnerd

---

### What

Explain what should be possible but currently is not.

### Why

Justify why such a feature is worth pursuing. Consider alternatives if available elaborating why existing solutions are insufficient.

### How

Outline how the proposed solution ought to be implemented. Attempt to preempt development hurdles and edge cases which require consideration.

---

### Post-Implementation/Pre-Merge Tracker

#### Documentation

- [ ] Unsafe blocks have a 'Safety' section?
- [ ] All public interfaces are documented?
- [ ] And said documentation includes examples?
- [ ] And said examples do, in fact, pass?

#### Testing

- [ ] All public interfaces have their post-conditions tested?
- [ ] And said tests have highest possible code coverage?
- [ ] And dedicated tests exist for aforementioned edge cases?
- [ ] And said tests do, in fact, pass?

#### Style

- [ ] Considered [exception safety](https://doc.rust-lang.org/nomicon/exception-safety.html)?
- [ ] No compiler warnings?
- [ ] No Clippy suggestions?
- [ ] Ran formatter?
- [ ] Bumped version?
- [ ] Rebased branch for clean commit history?
