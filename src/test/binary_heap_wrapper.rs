//! [`std::collections::BinaryHeap`] does not implement `PartialEq`
//! so we wrap it into a struct that provides `PartialEq` for
//! usability in `assert_eq!`

use super::*;

/// Binary heap does not implement `PartialEq`, so we need this wrapper
/// to test it together with the other std collections.
#[derive(Debug)]
pub(super) struct BHWrapper<Item> {
    heap: BinaryHeap<Item>,
}

impl<Item: Clone + Ord> PartialEq for BHWrapper<Item> {
    fn eq(&self, other: &Self) -> bool {
        BTreeSet::from_iter(self.heap.clone().into_iter())
            == BTreeSet::from_iter(other.heap.clone().into_iter())
    }
}

impl<I: Ord> FromIterator<I> for BHWrapper<I> {
    fn from_iter<T: IntoIterator<Item = I>>(iter: T) -> Self {
        Self {
            heap: iter.into_iter().collect(),
        }
    }
}

impl<I, J> TryFromIterator<J> for BHWrapper<I>
where
    BinaryHeap<I>: TryFromIterator<J>,
{
    type Error = <BinaryHeap<I> as TryFromIterator<J>>::Error;
    fn try_from_iter<T>(iter: T) -> Result<Self, Self::Error>
    where
        T: IntoIterator<Item = J>,
    {
        Ok(Self {
            heap: iter.into_iter().try_collect()?,
        })
    }
}

impl<I, J> ForceFromIterator<J> for BHWrapper<I>
where
    BinaryHeap<I>: ForceFromIterator<J>,
{
    fn f_from_iter<T>(iter: T, error_msg: &str) -> Self
    where
        T: IntoIterator<Item = J>,
    {
        Self {
            heap: iter.into_iter().f_collect(error_msg),
        }
    }
}

impl<Item> Eq for BHWrapper<Item> where BHWrapper<Item>: PartialEq {}
