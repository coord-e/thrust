# CLAUDE.md

Everything about the project itself is documented for humans, starting from `README.md`;
read it, the Development section in particular, rather than looking for it here. This file
records only what is easy to get wrong.

## Adding test cases

UI tests live in `tests/ui/`.

Add a test as a pair of files sharing one name: `tests/ui/pass/<name>.rs` headed by
`//@check-pass`, and `tests/ui/fail/<name>.rs` headed by `//@error-in-other-file: Unsat`.
The `fail` file is the `pass` file with the verified property broken as narrowly as
possible, so that the pair pins down both directions of the check.

## Panics on unsupported input

Thrust is under active development, and it is fine for an unsupported or unexpected
construct to reach a `panic!`, an `unimplemented!`, or a failing `unwrap`. Reporting one as
a proper diagnostic instead is fine too. What is not wanted is working around an existing
ICE path: validation passes, `Result` plumbing, or extra layers of processing added only to
keep from reaching it.

## Running the tests on claude.ai/code

Neither prerequisite of `cargo test` is set up in the session container. Install Z3 at the
version `.github/actions/setup-z3` pins for CI, and start a Docker daemon with `dockerd &`.
The daemon dies from time to time, so restart it whenever the tests that need it fail.
