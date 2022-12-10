# `msp430-atomic`

> Atomic operations for MSP430 microcontrollers

**Deprecated**: This crate's functionality is a strict subset of [`portable-atomic`](https://github.com/taiki-e/portable-atomic)
as of `v0.3.16`. Use `portable-atomic` `v0.3.16` or greater going forward.

## Relationship to `portable-atomic`

`msp430-atomic` uses inline `asm` to implement atomic opertions without
needing to disable interrupts. On MSP430, loads and stores of types
up to 16-bits are _single instruction_ operations. These are atomic because
the current MSP430 instruction will run to completion before an interrupt
is serviced. Adding, subtracting, and logical operations on these types are
atomic in the same way, and `msp430-atomic` provides inline assembly for these
as well (`add`, `sub`, etc).

However, the standard APIs for atomic adds, subtracts, and logical operations
are also expected to return the old value before the operation (`fetch_{add,sub,etc.}`).
MSP430 has no single instructions to also return the old value while
simultaneously updating a memory location. [Compare-And-Swap (CAS)](https://en.wikipedia.org/wiki/Compare-and-swap)
or [Load-Link/Store Conditional](https://en.wikipedia.org/wiki/Load-link/store-conditional)
instructions can be used to implement these `fetch_` instructions, but MSP430
has no such instructions either. Consequently, `msp430-atomic` does not provide
`fetch_{add,sub,etc.}`.

In contrast, `portable-atomic` provides load and stores using inline asm, 
and implements `fetch_{add,sub,etc.}` by disabling interrupts. As of [`v0.3.16`](https://github.com/taiki-e/portable-atomic/blob/main/CHANGELOG.md#0316---2022-12-09),
`portable-atomic` provides `add`, `sub`, etc. primitives which mirror the
public API of this crate (and don't disable interrupts).

## Relationship to [`atomic-polyfill`](https://github.com/embassy-rs/atomic-polyfill)

`atomic-polyfill` uses the [`critical-section`](https://github.com/rust-embedded/critical-section)
crate to implement _all_ atomic operations. For msp430, the `critical-section`
implementation usually means disabling interrupts. As of this writing
(11-06-2022), no optimizations that avoid disabling interrupts are provided
in `atomic-polyfill`.

# License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or
  http://www.apache.org/licenses/LICENSE-2.0)

- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
