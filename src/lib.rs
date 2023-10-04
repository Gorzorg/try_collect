use std::{collections::*, fmt::Debug};

#[cfg(test)]
mod test;

///A trait which implements a fallible version of FromIterator.
pub trait TryFromIterator<A>: Sized {
    type Error;
    fn try_from_iter<T>(iter: T) -> Result<Self, Self::Error>
    where
        T: IntoIterator<Item = A>;
}

///A trait which implements a fallible version of collect. Not to be confused with the standard
/// try_collect, which attempts at building a collection with an iterator of elements which
/// implement Try (e.g. Option, Result).
///
/// This trait is created having bounded-size collections in mind. Those collections do not
/// implement collect, because they cannot implement the FromIterator trait.
pub trait TryCollect: IntoIterator {
    fn try_collect<T: TryFromIterator<Self::Item>>(self) -> Result<T, T::Error>;
}

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
                iter.into_iter().try_fold(Self::default(), $for_loop_body)
            }
        }
    };
}

implement_collection!(
    [IntoV: TryInto<V>, V] Vec<V>, IntoV, <IntoV as TryInto<V>>::Error,
    |mut v, item| {v.push(item.try_into()?); Ok(v)}
);

implement_collection!(
    [IntoV: TryInto<V>, V] VecDeque<V>, IntoV, <IntoV as TryInto<V>>::Error,
    |mut v, item| {v.push_back(item.try_into()?); Ok(v)}
);

implement_collection!(
    [IntoV: TryInto<V>, V] LinkedList<V>, IntoV, <IntoV as TryInto<V>>::Error,
    |mut v, item| {v.push_back(item.try_into()?); Ok(v)}
);

implement_collection!(
    [IntoV: TryInto<V>, V: Ord] BinaryHeap<V>, IntoV, <IntoV as TryInto<V>>::Error,
    |mut v, item| {v.push(item.try_into()?); Ok(v)}
);

implement_collection!(
    [IntoK: TryInto<K>, K: Ord] BTreeSet<K>, IntoK, <IntoK as TryInto<K>>::Error,
    |mut v, item| {v.insert(item.try_into()?); Ok(v)}
);

implement_collection!(
    [IntoK: TryInto<K>, IntoV: TryInto<V>, K: Ord, V] BTreeMap<K, V>, (IntoK, IntoV),
    (Option<<IntoK as TryInto<K>>::Error>, Option<<IntoV as TryInto<V>>::Error>),
    |mut v, (into_k, into_v)| {
        v.insert(
            into_k.try_into().map_err(|x| (Some(x), None))?,
            into_v.try_into().map_err(|x| (None, Some(x)))?,
        );
        Ok(v)
    }
);

implement_collection!(
    [IntoK: TryInto<K>, K: std::hash::Hash + Eq] HashSet<K>, IntoK, <IntoK as TryInto<K>>::Error,
    |mut v, item| {v.insert(item.try_into()?); Ok(v)}
);

implement_collection!(
    [IntoK: TryInto<K>, IntoV: TryInto<V>, K: std::hash::Hash + Eq, V] HashMap<K, V>, (IntoK, IntoV),
    (Option<<IntoK as TryInto<K>>::Error>, Option<<IntoV as TryInto<V>>::Error>),
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

impl<IntoV: TryInto<V>, V, const N: usize> TryFromIterator<IntoV> for [V; N] {
    type Error = ArrayAndTupleError<<IntoV as TryInto<V>>::Error>;
    fn try_from_iter<T>(iter: T) -> Result<Self, Self::Error>
    where
        T: IntoIterator<Item = IntoV>,
    {
        use core::mem::MaybeUninit;

        // We build the array directly inside of the `Ok` result, so that
        // we don't have to copy the data over when we need to return.
        let mut out = Result::<[MaybeUninit<V>; N], Self::Error>::Ok(unsafe {
            // We are initializing an array that contains uninitialized memory.
            // It is our responsability to ensure that, if the array gets dropped,
            // only its inizialized elements get dropped.
            MaybeUninit::uninit().assume_init()
        });

        #[inline]
        fn maybe_uninit_array_orderly_cleanup<I, const M: usize>(
            array: &mut [MaybeUninit<I>; M],
            initialized_up_to: usize,
        ) {
            for drop_index in 0..initialized_up_to {
                unsafe { array[drop_index].assume_init_drop() }
            }
        }

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
            // We perform a custom transmutation on the `out` value.
            // This is needed because, at present day (Aug 2023),
            // `core::mem::transmute` cannot handle generic types correctly.
            // For example, even trying to apply `transmute::<T, T>` would
            // fail with a generic `T`, let alone trying to execute
            // `transmute::<[MaybeUninit<V>; N], [V; N]>`.

            // Safety: `out` has been completely initialized,
            // and `[MaybeUninit<V>; N]` has memory layout equal to `[V; N]`
            // so copying the memory of `out` to `cast_out` is safe.
            //
            // Also, we apply `core::mem::forget` to `out`, so that
            // `out` can go out of scope without altering any of the
            // data that `out` manages, since `drop` is not called on
            // `out` this way.
            // It follows that `cast_out` becomes the owner of all
            // the resources managed by `out`.
            //
            // Another note on safety, is that we are casting the
            // value inside the `Ok` variant, and not the `Result` itself,
            // because, even if `V` and `MaybeUninit<V>` have the same
            // memory layout, the compiler might in some cases perform
            // some memory layout optimizations on `Result<V, E>` and not on
            // `Result<MaybeUninit<V>, E>`,
            // called niche optimization, which would result in
            // `Result<V, E>` and `Result<MaybeUninit<V>, E>`
            // having different memory layouts, which would in turn
            // make the cast undefined behavior.

            // Efficiency: while `core::ptr::read` tecnically requires
            // the memory to be copied, one can assume that every
            // non-zero level of optimization while building the program
            // will optimize the copy away.
            // (A possible exception is in presence of niche optimization,
            // but i did not test what happens exactly in those cases.)
            //
            // This is technically not guaranteed, but for practical purposes,
            // one can assume that this is equivalent to using
            // `core::mem::transmute::<[MaybeUninit<V>; N], [V; N]>`
            out.map(|array| {
                let cast = core::ptr::read(&array as *const _ as *const _);
                core::mem::forget(array);
                cast
            })
        }
    }
}

/// We use this macro to be able to use sequences of tokens
/// as repetition counters.
///
/// For example, one can have a sequence
/// of tokens `$($counter: tt)*` in another macro, and
/// might want to repeat some expression `e` a number of times
/// that corresponds to the length of `$counter`.
///
/// In that scenario, one can invoke
/// ```text
/// $(
///     ignore_first!(
///         $counter
///         e
///     )
/// )*
/// ```
///
/// that will expand to
/// `e e e e ... e` where the sequence is as long as `$counter`.
macro_rules! ignore_first {
	($unused: tt $($whatever: tt)*) => {
		$($whatever)*
	};
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
