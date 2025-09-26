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

/// Shortcut function that panics if `v` is not a valid reg index.
pub const fn reg_x(x: InstrVal) -> RegId {
    RegId::new(x).expect("Bad register value")
}

/// Shortcut function that panics if `v` is not a valid Bit<N> value.
pub const fn bit<const WIDTH: usize>(v: RegVal) -> Bit<{ WIDTH }> {
    Bit::new(v).expect("bad bit value")
}
