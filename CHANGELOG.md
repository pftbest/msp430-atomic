# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

## [v0.1.5] - 2022-12-10

_As of `v0.1.5`, this crate is deprecated in favor of [`portable-atomic`](https://github.com/taiki-e/portable-atomic)
`v0.3.16` or later_. Only bugfix/patch releases will be made going forward.

- Add `#[repr(C, align(N))]` to atomic types for parity with types provided
  in `libcore`.
- Fix compilation on non-MSP430 targets by using atomic types in `libcore`.
- Update README.md with information comparing this crate to the similar
  use-case [`portable-atomic`](https://github.com/taiki-e/portable-atomic) and
  [`atomic-polyfill`](https://github.com/embassy-rs/atomic-polyfill).

## [v0.1.4] - 2022-01-27

- Use Rust's inline `asm` macro instead of `llvm_asm`; the latter was [removed](https://github.com/rust-lang/rust/pull/92816)
  from `rustc`.

## [v0.1.3] - 2021-05-17

- Remove `const_fn` feature gate, as it was removed from `rustc` after `v1.53.0`.

## [v0.1.2] - 2020-06-09

- Use `llvm_asm` instead of `asm`

## [v0.1.1] - 2019-12-16

- Expose AtomicOperations trait for public use

- Add atomic_clear() that uses bic instruction

- Make ASM functions always inline

## v0.1.0 - 2017-09-08

Initial release

[Unreleased]: https://github.com/pftbest/msp430-atomic/compare/v0.1.5...HEAD
[v0.1.5]: https://github.com/pftbest/msp430-atomic/compare/v0.1.4...v0.1.5
[v0.1.4]: https://github.com/pftbest/msp430-atomic/compare/v0.1.3...v0.1.4
[v0.1.3]: https://github.com/pftbest/msp430-atomic/compare/v0.1.2...v0.1.3
[v0.1.2]: https://github.com/pftbest/msp430-atomic/compare/v0.1.1...v0.1.2
[v0.1.1]: https://github.com/pftbest/msp430-atomic/compare/v0.1.0...v0.1.1
