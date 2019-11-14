// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at http://rust-lang.org/COPYRIGHT.
//
// Copyright 2017 Vadzim Dambrouski, initial port to MSP430.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Atomic types
//!
//! Atomic types provide primitive shared-memory communication between
//! threads, and are the building blocks of other concurrent
//! types.
//!
//! This module defines atomic versions of a select number of primitive
//! types, including [`AtomicBool`], [`AtomicIsize`], and [`AtomicUsize`].
//! Atomic types present operations that, when used correctly, synchronize
//! updates between threads.
//!
//! [`AtomicBool`]: struct.AtomicBool.html
//! [`AtomicIsize`]: struct.AtomicIsize.html
//! [`AtomicUsize`]: struct.AtomicUsize.html
//!
//! MSP430 note: All atomic operations in this crate have `SeqCst`
//! memory [ordering].
//!
//! [ordering]: https://doc.rust-lang.org/std/sync/atomic/enum.Ordering.html
//!
//! Atomic variables are safe to share between threads (they implement [`Sync`])
//! but they do not themselves provide the mechanism for sharing and follow the
//! [threading model](https://doc.rust-lang.org/std/thread/#the-threading-model)
//! of rust.
//!
//! [`Sync`]: https://doc.rust-lang.org/std/marker/trait.Sync.html
//!
//! Most atomic types may be stored in static variables, initialized using
//! the provided static initializers like [`ATOMIC_BOOL_INIT`]. Atomic statics
//! are often used for lazy global initialization.
//!
//! [`ATOMIC_BOOL_INIT`]: constant.ATOMIC_BOOL_INIT.html
//!
//! # Examples
//!
//! A simple spinlock:
//!
//! ```
//! use msp430_atomic::{AtomicUsize, ATOMIC_USIZE_INIT};
//! use std::thread;
//!
//! // Initialize SPINLOCK to 0
//! static SPINLOCK: AtomicUsize = ATOMIC_USIZE_INIT;
//!
//! fn main() {
//!     let thread = thread::spawn(move|| {
//!         SPINLOCK.store(1);
//!     });
//!
//!     // Wait for the other thread to release the lock
//!     while SPINLOCK.load() == 0 {}
//!
//!     if let Err(panic) = thread.join() {
//!         println!("Thread had an error: {:?}", panic);
//!     }
//! }
//! ```

#![no_std]
#![feature(asm)]
#![feature(const_fn)]
#![cfg_attr(not(target_arch = "msp430"), feature(core_intrinsics))]

use core::cell::UnsafeCell;
use core::fmt;

/// A boolean type which can be safely shared between threads.
///
/// This type has the same in-memory representation as a `bool`.
pub struct AtomicBool {
    v: UnsafeCell<u8>,
}

impl Default for AtomicBool {
    /// Creates an `AtomicBool` initialized to `false`.
    fn default() -> Self {
        Self::new(false)
    }
}

// Send is implicitly implemented for AtomicBool.
unsafe impl Sync for AtomicBool {}

/// A raw pointer type which can be safely shared between threads.
///
/// This type has the same in-memory representation as a `*mut T`.
pub struct AtomicPtr<T> {
    p: UnsafeCell<*mut T>,
}

impl<T> Default for AtomicPtr<T> {
    /// Creates a null `AtomicPtr<T>`.
    fn default() -> AtomicPtr<T> {
        AtomicPtr::new(core::ptr::null_mut())
    }
}

unsafe impl<T> Send for AtomicPtr<T> {}
unsafe impl<T> Sync for AtomicPtr<T> {}

/// An [`AtomicBool`] initialized to `false`.
///
/// [`AtomicBool`]: struct.AtomicBool.html
pub const ATOMIC_BOOL_INIT: AtomicBool = AtomicBool::new(false);

impl AtomicBool {
    /// Creates a new `AtomicBool`.
    ///
    /// # Examples
    ///
    /// ```
    /// use msp430_atomic::AtomicBool;
    ///
    /// let atomic_true  = AtomicBool::new(true);
    /// let atomic_false = AtomicBool::new(false);
    /// ```
    #[inline]
    pub const fn new(v: bool) -> AtomicBool {
        AtomicBool {
            v: UnsafeCell::new(v as u8),
        }
    }

    /// Returns a mutable reference to the underlying `bool`.
    ///
    /// This is safe because the mutable reference guarantees that no other threads are
    /// concurrently accessing the atomic data.
    ///
    /// # Examples
    ///
    /// ```
    /// use msp430_atomic::AtomicBool;
    ///
    /// let mut some_bool = AtomicBool::new(true);
    /// assert_eq!(*some_bool.get_mut(), true);
    /// *some_bool.get_mut() = false;
    /// assert_eq!(some_bool.load(), false);
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut bool {
        unsafe { &mut *(self.v.get() as *mut bool) }
    }

    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing `self` by value guarantees that no other threads are
    /// concurrently accessing the atomic data.
    ///
    /// # Examples
    ///
    /// ```
    /// use msp430_atomic::AtomicBool;
    ///
    /// let some_bool = AtomicBool::new(true);
    /// assert_eq!(some_bool.into_inner(), true);
    /// ```
    #[inline]
    pub fn into_inner(self) -> bool {
        self.v.into_inner() != 0
    }

    /// Loads a value from the bool.
    ///
    /// # Examples
    ///
    /// ```
    /// use msp430_atomic::AtomicBool;
    ///
    /// let some_bool = AtomicBool::new(true);
    ///
    /// assert_eq!(some_bool.load(), true);
    /// ```
    #[inline]
    pub fn load(&self) -> bool {
        unsafe { u8::atomic_load(self.v.get()) != 0 }
    }

    /// Stores a value into the bool.
    ///
    /// # Examples
    ///
    /// ```
    /// use msp430_atomic::AtomicBool;
    ///
    /// let some_bool = AtomicBool::new(true);
    ///
    /// some_bool.store(false);
    /// assert_eq!(some_bool.load(), false);
    /// ```
    #[inline]
    pub fn store(&self, val: bool) {
        unsafe {
            u8::atomic_store(self.v.get(), val as u8);
        }
    }

    /// Logical "and" with a boolean value.
    ///
    /// Performs a logical "and" operation on the current value and the argument `val`, and sets
    /// the new value to the result.
    ///
    /// # Examples
    ///
    /// ```
    /// use msp430_atomic::AtomicBool;
    ///
    /// let foo = AtomicBool::new(true);
    /// foo.and(false);
    /// assert_eq!(foo.load(), false);
    ///
    /// let foo = AtomicBool::new(true);
    /// foo.and(true);
    /// assert_eq!(foo.load(), true);
    ///
    /// let foo = AtomicBool::new(false);
    /// foo.and(false);
    /// assert_eq!(foo.load(), false);
    /// ```
    #[inline]
    pub fn and(&self, val: bool) {
        unsafe { u8::atomic_and(self.v.get(), val as u8) }
    }

    /// Logical "nand" with a boolean value.
    ///
    /// Performs a logical "nand" operation on the current value and the argument `val`, and sets
    /// the new value to the result.
    ///
    /// # Examples
    ///
    /// ```
    /// use msp430_atomic::AtomicBool;
    ///
    /// let foo = AtomicBool::new(true);
    /// foo.nand(false);
    /// assert_eq!(foo.load(), true);
    ///
    /// let foo = AtomicBool::new(true);
    /// foo.nand(true);
    /// assert_eq!(foo.load() as usize, 0);
    /// assert_eq!(foo.load(), false);
    ///
    /// let foo = AtomicBool::new(false);
    /// foo.nand(false);
    /// assert_eq!(foo.load(), true);
    /// ```
    #[inline]
    pub fn nand(&self, val: bool) {
        // We can't use atomic_nand here because it can result in a bool with
        // an invalid value. This happens because the atomic operation is done
        // with an 8-bit integer internally, which would set the upper 7 bits.
        // So we just use xor or swap instead.
        if val {
            // !(x & true) == !x
            // We must invert the bool.
            self.xor(true)
        } else {
            // !(x & false) == true
            // We must set the bool to true.
            self.store(true)
        }
    }

    /// Logical "or" with a boolean value.
    ///
    /// Performs a logical "or" operation on the current value and the argument `val`, and sets the
    /// new value to the result.
    ///
    /// # Examples
    ///
    /// ```
    /// use msp430_atomic::AtomicBool;
    ///
    /// let foo = AtomicBool::new(true);
    /// foo.or(false);
    /// assert_eq!(foo.load(), true);
    ///
    /// let foo = AtomicBool::new(true);
    /// foo.or(true);
    /// assert_eq!(foo.load(), true);
    ///
    /// let foo = AtomicBool::new(false);
    /// foo.or(false);
    /// assert_eq!(foo.load(), false);
    /// ```
    #[inline]
    pub fn or(&self, val: bool) {
        unsafe { u8::atomic_or(self.v.get(), val as u8) }
    }

    /// Logical "xor" with a boolean value.
    ///
    /// Performs a logical "xor" operation on the current value and the argument `val`, and sets
    /// the new value to the result.
    ///
    /// # Examples
    ///
    /// ```
    /// use msp430_atomic::AtomicBool;
    ///
    /// let foo = AtomicBool::new(true);
    /// foo.xor(false);
    /// assert_eq!(foo.load(), true);
    ///
    /// let foo = AtomicBool::new(true);
    /// foo.xor(true);
    /// assert_eq!(foo.load(), false);
    ///
    /// let foo = AtomicBool::new(false);
    /// foo.xor(false);
    /// assert_eq!(foo.load(), false);
    /// ```
    #[inline]
    pub fn xor(&self, val: bool) {
        unsafe { u8::atomic_xor(self.v.get(), val as u8) }
    }
}

impl<T> AtomicPtr<T> {
    /// Creates a new `AtomicPtr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use msp430_atomic::AtomicPtr;
    ///
    /// let ptr = &mut 5;
    /// let atomic_ptr  = AtomicPtr::new(ptr);
    /// ```
    #[inline]
    pub const fn new(p: *mut T) -> AtomicPtr<T> {
        AtomicPtr {
            p: UnsafeCell::new(p),
        }
    }

    /// Returns a mutable reference to the underlying pointer.
    ///
    /// This is safe because the mutable reference guarantees that no other threads are
    /// concurrently accessing the atomic data.
    ///
    /// # Examples
    ///
    /// ```
    /// use msp430_atomic::AtomicPtr;
    ///
    /// let mut atomic_ptr = AtomicPtr::new(&mut 10);
    /// *atomic_ptr.get_mut() = &mut 5;
    /// assert_eq!(unsafe { *atomic_ptr.load() }, 5);
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut *mut T {
        unsafe { &mut *self.p.get() }
    }

    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing `self` by value guarantees that no other threads are
    /// concurrently accessing the atomic data.
    ///
    /// # Examples
    ///
    /// ```
    /// use msp430_atomic::AtomicPtr;
    ///
    /// let atomic_ptr = AtomicPtr::new(&mut 5);
    /// assert_eq!(unsafe { *atomic_ptr.into_inner() }, 5);
    /// ```
    #[inline]
    pub fn into_inner(self) -> *mut T {
        self.p.into_inner()
    }

    /// Loads a value from the pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use msp430_atomic::AtomicPtr;
    ///
    /// let ptr = &mut 5;
    /// let some_ptr  = AtomicPtr::new(ptr);
    ///
    /// let value = some_ptr.load();
    /// ```
    #[inline]
    pub fn load(&self) -> *mut T {
        unsafe { usize::atomic_load(self.p.get() as *mut usize) as *mut T }
    }

    /// Stores a value into the pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use msp430_atomic::AtomicPtr;
    ///
    /// let ptr = &mut 5;
    /// let some_ptr  = AtomicPtr::new(ptr);
    ///
    /// let other_ptr = &mut 10;
    ///
    /// some_ptr.store(other_ptr);
    /// ```
    #[inline]
    pub fn store(&self, ptr: *mut T) {
        unsafe {
            usize::atomic_store(self.p.get() as *mut usize, ptr as usize);
        }
    }
}

macro_rules! atomic_int {
    ($int_type:ident $atomic_type:ident $atomic_init:ident $asm_suffix:expr) => {
        /// An integer type which can be safely shared between threads.
        ///
        /// This type has the same in-memory representation as the underlying integer type.
        pub struct $atomic_type {
            v: UnsafeCell<$int_type>,
        }

        /// An atomic integer initialized to `0`.
        pub const $atomic_init: $atomic_type = $atomic_type::new(0);

        impl Default for $atomic_type {
            fn default() -> Self {
                Self::new(Default::default())
            }
        }

        impl fmt::Debug for $atomic_type {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.debug_tuple(stringify!($atomic_type))
                 .field(&self.load())
                 .finish()
            }
        }

        // Send is implicitly implemented.
        unsafe impl Sync for $atomic_type {}

        impl $atomic_type {
            /// Creates a new atomic integer.
            ///
            /// # Examples
            ///
            /// ```
            /// use msp430_atomic::AtomicIsize;
            ///
            /// let atomic_forty_two  = AtomicIsize::new(42);
            /// ```
            #[inline]
            pub const fn new(v: $int_type) -> Self {
                $atomic_type {v: UnsafeCell::new(v)}
            }

            /// Returns a mutable reference to the underlying integer.
            ///
            /// This is safe because the mutable reference guarantees that no other threads are
            /// concurrently accessing the atomic data.
            ///
            /// # Examples
            ///
            /// ```
            /// use msp430_atomic::AtomicIsize;
            ///
            /// let mut some_isize = AtomicIsize::new(10);
            /// assert_eq!(*some_isize.get_mut(), 10);
            /// *some_isize.get_mut() = 5;
            /// assert_eq!(some_isize.load(), 5);
            /// ```
            #[inline]
            pub fn get_mut(&mut self) -> &mut $int_type {
                unsafe { &mut *self.v.get() }
            }

            /// Consumes the atomic and returns the contained value.
            ///
            /// This is safe because passing `self` by value guarantees that no other threads are
            /// concurrently accessing the atomic data.
            ///
            /// # Examples
            ///
            /// ```
            /// use msp430_atomic::AtomicIsize;
            ///
            /// let some_isize = AtomicIsize::new(5);
            /// assert_eq!(some_isize.into_inner(), 5);
            /// ```
            #[inline]
            pub fn into_inner(self) -> $int_type {
                 self.v.into_inner()
            }

            /// Loads a value from the atomic integer.
            ///
            /// # Examples
            ///
            /// ```
            /// use msp430_atomic::AtomicIsize;
            ///
            /// let some_isize = AtomicIsize::new(5);
            ///
            /// assert_eq!(some_isize.load(), 5);
            /// ```
            #[inline]
            pub fn load(&self) -> $int_type {
                unsafe { $int_type::atomic_load(self.v.get()) }
            }

            /// Stores a value into the atomic integer.
            ///
            /// # Examples
            ///
            /// ```
            /// use msp430_atomic::AtomicIsize;
            ///
            /// let some_isize = AtomicIsize::new(5);
            ///
            /// some_isize.store(10);
            /// assert_eq!(some_isize.load(), 10);
            /// ```
            #[inline]
            pub fn store(&self, val: $int_type) {
                unsafe { $int_type::atomic_store(self.v.get(), val); }
            }

            /// Adds to the current value, returning the previous value.
            ///
            /// This operation wraps around on overflow.
            ///
            /// # Examples
            ///
            /// ```
            /// use msp430_atomic::AtomicIsize;
            ///
            /// let foo = AtomicIsize::new(0);
            /// foo.add(10);
            /// assert_eq!(foo.load(), 10);
            /// ```
            #[inline]
            pub fn add(&self, val: $int_type) {
                unsafe { $int_type::atomic_add(self.v.get(), val) }
            }

            /// Subtracts from the current value, returning the previous value.
            ///
            /// This operation wraps around on overflow.
            ///
            /// # Examples
            ///
            /// ```
            /// use msp430_atomic::AtomicIsize;
            ///
            /// let foo = AtomicIsize::new(0);
            /// foo.sub(10);
            /// assert_eq!(foo.load(), -10);
            /// ```
            #[inline]
            pub fn sub(&self, val: $int_type) {
                unsafe { $int_type::atomic_sub(self.v.get(), val) }
            }

            /// Bitwise "and" with the current value.
            ///
            /// Performs a bitwise "and" operation on the current value and the argument `val`, and
            /// sets the new value to the result.
            ///
            /// # Examples
            ///
            /// ```
            /// use msp430_atomic::AtomicIsize;
            ///
            /// let foo = AtomicIsize::new(0b101101);
            /// foo.and(0b110011);
            /// assert_eq!(foo.load(), 0b100001);
            #[inline]
            pub fn and(&self, val: $int_type) {
                unsafe { $int_type::atomic_and(self.v.get(), val) }
            }

            /// Bitwise "or" with the current value.
            ///
            /// Performs a bitwise "or" operation on the current value and the argument `val`, and
            /// sets the new value to the result.
            ///
            /// # Examples
            ///
            /// ```
            /// use msp430_atomic::AtomicIsize;
            ///
            /// let foo = AtomicIsize::new(0b101101);
            /// foo.or(0b110011);
            /// assert_eq!(foo.load(), 0b111111);
            #[inline]
            pub fn or(&self, val: $int_type) {
                unsafe { $int_type::atomic_or(self.v.get(), val) }
            }

            /// Bitwise "xor" with the current value.
            ///
            /// Performs a bitwise "xor" operation on the current value and the argument `val`, and
            /// sets the new value to the result.
            ///
            /// # Examples
            ///
            /// ```
            /// use msp430_atomic::AtomicIsize;
            ///
            /// let foo = AtomicIsize::new(0b101101);
            /// foo.xor(0b110011);
            /// assert_eq!(foo.load(), 0b011110);
            #[inline]
            pub fn xor(&self, val: $int_type) {
                unsafe { $int_type::atomic_xor(self.v.get(), val) }
            }
        }

        #[cfg(target_arch = "msp430")]
        impl AtomicOperations for $int_type {
            #[inline]
            unsafe fn atomic_store(dst: *mut Self, val: Self) {
                asm!(concat!("mov", $asm_suffix, " $1, $0")
                    :: "*m"(dst), "ir"(val) : "memory" : "volatile");
            }

            #[inline]
            unsafe fn atomic_load(dst: *const Self) -> Self {
                let out;
                asm!(concat!("mov", $asm_suffix, " $1, $0")
                    : "=r"(out) : "*m"(dst) : "memory" : "volatile");
                out
            }

            #[inline]
            unsafe fn atomic_add(dst: *mut Self, val: Self) {
                asm!(concat!("add", $asm_suffix, " $1, $0")
                    :: "*m"(dst), "ir"(val) : "memory" : "volatile");
            }

            #[inline]
            unsafe fn atomic_sub(dst: *mut Self, val: Self) {
                asm!(concat!("sub", $asm_suffix, " $1, $0")
                    :: "*m"(dst), "ir"(val) : "memory" : "volatile");
            }

            #[inline]
            unsafe fn atomic_and(dst: *mut Self, val: Self) {
                asm!(concat!("and", $asm_suffix, " $1, $0")
                    :: "*m"(dst), "ir"(val) : "memory" : "volatile");
            }

            #[inline]
            unsafe fn atomic_or(dst: *mut Self, val: Self) {
                asm!(concat!("bis", $asm_suffix, " $1, $0")
                    :: "*m"(dst), "ir"(val) : "memory" : "volatile");
            }

            #[inline]
            unsafe fn atomic_xor(dst: *mut Self, val: Self) {
                asm!(concat!("xor", $asm_suffix, " $1, $0")
                    :: "*m"(dst), "ir"(val) : "memory" : "volatile");
            }
        }

        #[cfg(not(target_arch = "msp430"))]
        impl AtomicOperations for $int_type {
            #[inline]
            unsafe fn atomic_store(dst: *mut Self, val: Self) {
                ::core::intrinsics::atomic_store(dst, val);
            }

            #[inline]
            unsafe fn atomic_load(dst: *const Self) -> Self {
                ::core::intrinsics::atomic_load(dst)
            }

            #[inline]
            unsafe fn atomic_add(dst: *mut Self, val: Self) {
                ::core::intrinsics::atomic_xadd(dst, val);
            }

            #[inline]
            unsafe fn atomic_sub(dst: *mut Self, val: Self) {
                ::core::intrinsics::atomic_xsub(dst, val);
            }

            #[inline]
            unsafe fn atomic_and(dst: *mut Self, val: Self) {
                ::core::intrinsics::atomic_and(dst, val);
            }

            #[inline]
            unsafe fn atomic_or(dst: *mut Self, val: Self) {
                ::core::intrinsics::atomic_or(dst, val);
            }

            #[inline]
            unsafe fn atomic_xor(dst: *mut Self, val: Self) {
                ::core::intrinsics::atomic_xor(dst, val);
            }
        }
    }
}

atomic_int! {
    i8 AtomicI8 ATOMIC_I8_INIT ".b"
}

atomic_int! {
    u8 AtomicU8 ATOMIC_U8_INIT ".b"
}

atomic_int! {
    i16 AtomicI16 ATOMIC_I16_INIT ".w"
}

atomic_int! {
    u16 AtomicU16 ATOMIC_U16_INIT ".w"
}

atomic_int! {
    isize AtomicIsize ATOMIC_ISIZE_INIT ".w"
}

atomic_int! {
    usize AtomicUsize ATOMIC_USIZE_INIT ".w"
}

/// Atomic arithmetic and bitwise operations implemented for numerical types. Each operation is
/// implemented with a single assembly instruction.
pub trait AtomicOperations {
    /// Store value into destination pointee.
    unsafe fn atomic_store(dst: *mut Self, val: Self);
    /// Read value from destination pointee.
    unsafe fn atomic_load(dst: *const Self) -> Self;
    /// Add value to destination pointee. Result may wrap around.
    unsafe fn atomic_add(dst: *mut Self, val: Self);
    /// Subtract value from destination pointee. Result may wrap around.
    unsafe fn atomic_sub(dst: *mut Self, val: Self);
    /// Clear all bits in destination pointee that are zeroed in value.
    unsafe fn atomic_and(dst: *mut Self, val: Self);
    /// Set all bits in destination pointee that are set in value.
    unsafe fn atomic_or(dst: *mut Self, val: Self);
    /// Toggle all bits in destination pointee that are set in value.
    unsafe fn atomic_xor(dst: *mut Self, val: Self);
}

impl fmt::Debug for AtomicBool {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("AtomicBool").field(&self.load()).finish()
    }
}

impl<T> fmt::Debug for AtomicPtr<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("AtomicPtr").field(&self.load()).finish()
    }
}
