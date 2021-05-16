# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

- Remove `const_fn` feature gate, as it was removed from `rustc` after `v1.53.0`.

## v0.1.2 - 2020-06-09

- Use llvm_asm instead of asm

## v0.1.1 - 2019-12-16

- Expose AtomicOperations trait for public use

- Add atomic_clear() that uses bic instruction

- Make ASM functions always inline

## v0.1.0 - 2017-09-08

Initial release

[Unreleased]: https://github.com/pftbest/msp430-atomic/compare/v0.1.2...HEAD
[v0.1.2]: https://github.com/pftbest/msp430-atomic/compare/v0.1.1...v0.1.2
