use super::{ArrayAndTupleError, ForceCollect, ForceFromIterator, TryCollect, TryFromIterator};
use std::collections::*;

mod binary_heap_wrapper;
mod from_mem_debug;
/// All the tests in the `crate::test::test_try_collect` must be mirrored here
mod test_force_collect;
mod test_try_collect;
use binary_heap_wrapper::BHWrapper;
use from_mem_debug::TryIntoMemDebug;

/// A simple wrapper on bool, that can be built with `TryFrom<bool>`,
/// which only succeeds if the bool one is converting is `true`.
///
/// Its purpose is to test `try_collect`.
#[derive(Clone, Copy, Debug)]
struct True(bool);

impl TryFrom<bool> for True {
    type Error = bool;
    fn try_from(value: bool) -> Result<Self, Self::Error> {
        if value {
            Ok(Self(value))
        } else {
            Err(value)
        }
    }
}

/// We ensure that force_collect is a default feature.
#[test]
fn test_default_feature() {
    #[cfg(not(feature = "force_collect"))]
    panic!("force_collect is not a default feature. It should be!");
}
