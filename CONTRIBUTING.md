# Contributing

1. Create Issue Ticket

This repository configures GitHub to limit issues to select templates:

- Additions which add new functionality.
- Alterations which modify how existing functionality is implemented.
- Corrections which alter the behaviour of existing implementations.

From there a branch is created and tracked for the ticket.

2. Design API

To exhibit Behaviour Driven Design (BDD), place oneself in the perspective
of a consumer of the Application Programming Interface (API) being designed
and thenceforth write Rustdoc documentation for those endpoints in the
following convention:

```
<brief description>

<detailed description>

# Safety
<optionally any conditions necessary to many calling this safe>

# Panic
<optionally any conditions upon which this panics>

# Performance
<both time and memory complexity>

# Examples
<executable Rust program>
```

3. Test

Follow Test Driven Development (TDD) by first implementing an exhaustive test
suite using the 'given/when/then' style of BDD. Mocks are available in the
crate root.

4. Develop

The pride of this repository is code quality! In the
[build configuration](Cargo.toml), all[^1] warnings available have been
enabled, and all[^1] warnings have been upgraded to errors. This project
also uses static analysis via Clippy and dynamic analysis via Miri passing
all[^1] checks.

[^1]: Technically not all lints are enabled as some are contradictory and
      cannot be simultaneously enabled alongside a handful which for, stylistic
      reasons, remain suppressed.

5. Commit

This project uses a standardized commit message style enforced via template
based upon the [Angular guidelines](https://github.com/angular/angular/blob/main/contributing-docs/commit-message-guidelines.md).

6. Pull-Request

There is a final checklist to ensure all above conditions are met, and then
changes are merged into the main branch following Continuous Development (CD)
practices.
