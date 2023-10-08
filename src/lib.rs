#[cfg(feature = "force_collect")]
mod force_implementations;
mod helper_functions;
#[cfg(test)]
mod test;
mod trait_definitions;
mod try_implementations;

use helper_functions::{array_transmute, maybe_uninit_array_orderly_cleanup};
#[cfg(feature = "force_collect")]
pub use trait_definitions::{ForceCollect, ForceFromIterator};
pub use trait_definitions::{TryCollect, TryFromIterator};
pub use try_implementations::{ArrayAndTupleError, NoItems};
