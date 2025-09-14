use crate::kernel::{Bit, InstrVal, RegId, RegVal};

/// A simple macro to do try-like stuff in const contexts.
/// This exists because Rust currently does not allow `?` in
/// const-contexts. Note, that unlike `?`, it doesn't call `.into()`.
#[macro_export]
macro_rules! c_try {
    ($e:expr) => {
        match $e {
            Ok(x) => x,
            Err(e) => return Err(e),
        }
    };
}

#[macro_export]
macro_rules! instr {
    ($name:ident $($arg:tt),*) => {
        $crate::kernel::shortcodes::$name($(
            $crate::instr!(@operand $arg)
        ),*)
    };
    (@operand $reg:ident) => {
        $crate::kernel::RegId::$reg
    };
    (@operand $l:literal) => {
        $crate::util::bit($l)
    };
    (@operand {$e:expr}) => { $e };
}

#[macro_export]
macro_rules! program {
    ($($name:ident $($arg:tt),*;)+) => (
        [$(
            $crate::instr!($name $($arg),*)
        ),+]
    );
}

/// Shortcut function that panics if `v` is not a valid reg index.
#[allow(dead_code)]
pub fn reg_x(x: InstrVal) -> RegId {
    RegId::new(x).expect("Bad register value")
}

/// Shortcut function that panics if `v` is not a valid Bit<N> value.
#[allow(dead_code)]
pub fn bit<const WIDTH: usize>(v: RegVal) -> Bit<{ WIDTH }> {
    Bit::new(v).expect("bad bit value")
}
