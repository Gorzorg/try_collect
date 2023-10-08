/// A trait which implements a fallible version of [`FromIterator`].
///
/// The reasons for failure may be arbitrary.
/// The crate provides implementations for standard library collections,
/// arrays, and homogeneous tuples.
///
/// All those implementations can implicitly mutate the item type to match the
/// one needed in the target collection by applying [`TryInto::try_into`] to
/// the items produced by the iterator.
///
/// The implementations provided for arrays and tuples additionally can
/// fail if the iterator yields an inadequate amount of items.
pub trait TryFromIterator<Item>: Sized {
    type Error;
    fn try_from_iter<T>(iter: T) -> Result<Self, Self::Error>
    where
        T: IntoIterator<Item = Item>;
}

/// #Concept
///
///  A trait which implements a fallible version of collect.
///
/// This should not to be confused with [`Iterator::try_collect`],
/// which tries building a collection with an iterator of elements which
/// implement Try (e.g. [`Option`], [`Result`]).
///
/// Indeed, this fallible version of collect is also allowed to fail for
/// other reasons, such as condition that depend on the iterator, and not
/// on the single items.
///
/// One example of such conditions is trying to collect into fixed-size,
/// or bounded-size collections, e.g. arrays. In those cases,
/// [`TryCollect::try_collect`] may also fail due to an incorrect length of
/// the iterator.
///
/// #Definition
///
/// This trait is blanket-implemented, in the same way [`Iterator::collect`]
/// is, i.e. it is just syntactic sugar for a call to a method implemented
/// in another trait, in this case [`TryFromIterator`].
pub trait TryCollect: IntoIterator {
    fn try_collect<T: TryFromIterator<Self::Item>>(self) -> Result<T, T::Error>;
}

#[cfg(feature = "force_collect")]
pub use force_traits::*;

#[cfg(feature = "force_collect")]
pub mod force_traits {
    use crate::TryFromIterator;

    pub trait ForceFromIterator<Item>: TryFromIterator<Item> {
        fn f_from_iter<T>(iter: T, error_msg: &str) -> Self
        where
            T: IntoIterator<Item = Item>,
        {
            // We avoid using `Self::try_from_iter(iter).unwrap()`
            // or similar things because it would require
            // `Self::Error : Debug`
            match Self::try_from_iter(iter) {
                Ok(value) => value,
                Err(_) => panic!("{}", error_msg),
            }
        }
    }

    pub trait ForceCollect: IntoIterator {
        fn f_collect<T: ForceFromIterator<Self::Item>>(self, error_msg: &str) -> T;
    }
}
