use super::{ignore_first, TryCollect, TryFromIterator};
use std::{collections::*, fmt::Debug};

// Blanket implementation for `TryCollect`.
impl<X: IntoIterator> TryCollect for X {
    fn try_collect<T: TryFromIterator<Self::Item>>(self) -> Result<T, T::Error> {
        TryFromIterator::try_from_iter(self.into_iter())
    }
}

/// This macro allows to implement `TryFromIterator` for collection types
/// without copy-pasting a lot of boilerplate code.
macro_rules! implement_collection {
    (
        [$($generics: tt)*]
        $target_type: ty,
        $iter_item_type: ty,
        $error_type: ty,
        $for_loop_body: expr
    ) => {
        impl<$($generics)*> TryFromIterator<$iter_item_type> for $target_type {
            type Error = $error_type;
            #[inline]
            fn try_from_iter<T>(iter: T) -> Result<Self, Self::Error>
            where
                T: IntoIterator<Item = $iter_item_type>,
            {
                // Forwarding the implementation to `Iterator::try_fold`
                // for better efficiency
                iter.into_iter().try_fold(Self::default(), $for_loop_body)
            }
        }
    };
}

implement_collection!(
    [IntoV: TryInto<V>, V] Vec<V>, IntoV, IntoV::Error,
    |mut v, item| {v.push(item.try_into()?); Ok(v)}
);

implement_collection!(
    [IntoV: TryInto<V>, V] VecDeque<V>, IntoV, IntoV::Error,
    |mut v, item| {v.push_back(item.try_into()?); Ok(v)}
);

implement_collection!(
    [IntoV: TryInto<V>, V] LinkedList<V>, IntoV, IntoV::Error,
    |mut v, item| {v.push_back(item.try_into()?); Ok(v)}
);

implement_collection!(
    [IntoV: TryInto<V>, V: Ord] BinaryHeap<V>, IntoV, IntoV::Error,
    |mut v, item| {v.push(item.try_into()?); Ok(v)}
);

implement_collection!(
    [IntoK: TryInto<K>, K: Ord] BTreeSet<K>, IntoK, IntoK::Error,
    |mut v, item| {v.insert(item.try_into()?); Ok(v)}
);

implement_collection!(
    [IntoK: TryInto<K>, IntoV: TryInto<V>, K: Ord, V] BTreeMap<K, V>, (IntoK, IntoV),
    (Option<IntoK::Error>, Option<IntoV::Error>),
    |mut v, (into_k, into_v)| {
        v.insert(
            into_k.try_into().map_err(|x| (Some(x), None))?,
            into_v.try_into().map_err(|x| (None, Some(x)))?,
        );
        Ok(v)
    }
);

implement_collection!(
    [IntoK: TryInto<K>, K: std::hash::Hash + Eq] HashSet<K>, IntoK, IntoK::Error,
    |mut v, item| {v.insert(item.try_into()?); Ok(v)}
);

implement_collection!(
    [IntoK: TryInto<K>, IntoV: TryInto<V>, K: std::hash::Hash + Eq, V] HashMap<K, V>, (IntoK, IntoV),
    (Option<IntoK::Error>, Option<IntoV::Error>),
    |mut v, (into_k, into_v)| {
        v.insert(
            into_k.try_into().map_err(|x| (Some(x), None))?,
            into_v.try_into().map_err(|x| (None, Some(x)))?,
        );
        Ok(v)
    }
);

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ArrayAndTupleError<E> {
    TryFromError(E),
    NotEnoughItems,
    TooManyItems,
}

impl<E> ArrayAndTupleError<E> {
    /// Analogous to the `expect` function that is implemented for
    /// `Option` and `Result`.
    ///
    /// Panics if `self` is not an instance of the `TryFromError`
    /// variant.
    ///
    /// Otherwise, the error data in `self` is returned.
    pub fn expect_try_from_error<STR: std::fmt::Display>(self, message: impl FnOnce() -> STR) -> E {
        match self {
            Self::TryFromError(err) => err,
            _ => panic!("{}", message()),
        }
    }

    /// Returns `true` if `self` is an instance of the `TryFromError` variant,
    /// returns `false` otherwise
    pub fn is_try_from_error(&self) -> bool {
        match &self {
            &Self::TryFromError(_) => true,
            _ => false,
        }
    }

    /// Returns `true` if `self` is an instance of the
    /// `NotEnoughItems` variant, returns `false` otherwise
    pub fn not_enough_items(&self) -> bool {
        match &self {
            &Self::NotEnoughItems => true,
            _ => false,
        }
    }

    /// Returns `true` if `self` is an instance of the
    /// `TooManyItems` variant, returns `false` otherwise
    pub fn too_many_items(&self) -> bool {
        match &self {
            &Self::TooManyItems => true,
            _ => false,
        }
    }
}

impl<IntoV: TryInto<V>, V, const N: usize> TryFromIterator<IntoV> for [V; N] {
    type Error = ArrayAndTupleError<<IntoV as TryInto<V>>::Error>;
    fn try_from_iter<T>(iter: T) -> Result<Self, Self::Error>
    where
        T: IntoIterator<Item = IntoV>,
    {
        use super::{array_transmute, maybe_uninit_array_orderly_cleanup};
        use core::mem::MaybeUninit;

        // We build the array directly inside of the `Ok` result, so that
        // we don't have to copy the data over when we need to return.
        let mut out = Result::<[MaybeUninit<V>; N], Self::Error>::Ok(unsafe {
            // We are initializing an array that contains uninitialized memory.
            // It is our responsability to ensure that, if the array gets dropped,
            // only its inizialized elements get dropped.
            MaybeUninit::uninit().assume_init()
        });

        // We are building out in place, in order to avoid useless copies.
        // This requires us to match the value contained in out,
        // which we know for sure to be Ok(...)
        if let Ok(ref mut array) = out {
            let mut iter = iter.into_iter();
            for index in 0..N {
                // We attempt converting and adding the next element to the array
                //
                // If the iterator yields no element, or if the conversion fails,
                // We have to drop the elements that have already been initialized,
                // and we return an error.
                //
                // We already initialized the elements up to `out[0..index]`
                // therefore, before returning an error, we have to drop those,
                // in case their drop is necessary to preserve some invariants.
                if let Some(t) = iter.next() {
                    match t.try_into() {
                        Ok(e) => {
                            array[index].write(e);
                            continue;
                        }
                        Err(e) => {
                            maybe_uninit_array_orderly_cleanup(array, index);
                            return Err(ArrayAndTupleError::TryFromError(e));
                        }
                    }
                }
                maybe_uninit_array_orderly_cleanup(array, index);
                return Err(ArrayAndTupleError::NotEnoughItems);
            }

            // If the iterator contains too many elements for the array, then we
            // orderly drop the entire array, since it has been completely
            // initialized already, and we return an error.
            if iter.next().is_some() {
                maybe_uninit_array_orderly_cleanup(array, N);
                return Err(ArrayAndTupleError::TooManyItems);
            }
        }

        unsafe {
            // We transmute the value inside of `Ok(...)` instead of the
            // entire `out` value, so that, in case the compiler ever tries
            // applying niche optimizations to `Result<[T; N], E>`,
            // we don't get undefined behavior.
            // This precaution is necessary because `MaybeUninit` prevents
            // niche optimizations on enclosing types, since every memory
            // content is valid for its uninit variant.
            out.map(|array| array_transmute(array))
        }
    }
}

// Implementing traits for tuples in full generality is to this day (Aug 2023)
// impossible in Rust.
//
// We therefore use a macro to implement `TryFromIterator` for
// tuples up to a specified length.

// The implementation for `()` is somewhat different from other tuples,
// so we write it here explicitly. For the other implementations,
// we use a macro to do the job.

/// This enum cannot have instances.
/// Its purpose is to be used in the implementation of
/// `TryFromIterator` for the empty tuple.
///
/// The fact that this enum has no instances makes it easier for the
/// compiler to notice that `ArrayAndTupleError<NoItems>::TryFromError`
/// will never exist, because we will not need to call `.try_into()`
/// on anything for empty tuples.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum NoItems {}

impl<I> TryFromIterator<I> for () {
    type Error = ArrayAndTupleError<NoItems>;
    #[inline]
    fn try_from_iter<T>(iter: T) -> Result<Self, Self::Error>
    where
        T: IntoIterator<Item = I>,
    {
        match iter.into_iter().next() {
            None => Ok(()),
            _ => Err(ArrayAndTupleError::TooManyItems),
        }
    }
}

/// Calling this macro with `n` literal tokens causes it to
/// implement the `TryFromIterator` trait for tuples of
/// length from `1` up to `n`.
macro_rules! impl_try_from_iterator_for_tuples {
    () => {};
	(
        $discard_first_counter_token: literal
        $($counter: literal)*
    ) => {
        impl<IntoI: TryInto<I>, I> TryFromIterator<IntoI> for (I, $(ignore_first!($counter I),)*) {
            type Error = ArrayAndTupleError<<IntoI as TryInto<I>>::Error>;
            #[inline]
			fn try_from_iter<T>(iter: T) -> Result<Self, Self::Error>
            where
				T: IntoIterator<Item = IntoI>
            {
                let mut iter = iter.into_iter();
                let ret = Ok((
                    // We fetch an item from `iter`,
                    // if `None` is returned, or if the returned item
                    // does not convert to `I` successfully,
                    // then we return an error.
                    //
                    // We repeat this `len($counter) + 1` times
                    match iter.next() {
                        Some(e) => e.try_into().map_err(|err| ArrayAndTupleError::TryFromError(err))?,
                        None => return Err(ArrayAndTupleError::NotEnoughItems),
                    },
                    $(
                        ignore_first!(
                            $counter
                            match iter.next() {
                                Some(e) => e.try_into().map_err(|err| ArrayAndTupleError::TryFromError(err))?,
                                None => return Err(ArrayAndTupleError::NotEnoughItems),
                            }
                        ),
                    )*
                ));
                if iter.next().is_some() {
                    return Err(ArrayAndTupleError::TooManyItems)
                }
                ret
            }
        }

        impl_try_from_iterator_for_tuples!($($counter)*);
    };
}

impl_try_from_iterator_for_tuples!(
     1  2  3  4  5  6  7  8  9 10
    11 12 13 14 15 16 17 18 19 20
    21 22 23 24 25 26 27 28 29 30
    31 32
);
