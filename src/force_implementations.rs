//! Even though ForceFromIterator provides a blanket implementation,
//! for performance reasons, one may want to implement the
//! methods defined in ForceFromIterator manually.
//!
//! Also, the implementation of `ForceCollect::f_collect` must be
//! coherent with the implementation of `ForceFromIterator::f_from_iter`,
//! so we provide a blanket implementation that covers every situation
//! in which one can implement `ForceCollect`

use super::{ignore_first, ForceCollect, ForceFromIterator};
use std::collections::*;

impl<X: IntoIterator> ForceCollect for X {
    #[inline]
    fn f_collect<T: ForceFromIterator<Self::Item>>(self, error_msg: &str) -> T {
        T::f_from_iter(self, error_msg)
    }
}

/// This macro allows to implement `ForceFromIterator` for collection types
/// without copy-pasting a lot of boilerplate code.
macro_rules! implement_collection {
    (
        $error_msg: ident
        [$($generics: tt)*]
        $target_type: ty,
        $iter_item_type: ty,
        $for_loop_body: expr
    ) => {
        impl<$($generics)*> ForceFromIterator<$iter_item_type> for $target_type {
            #[inline]
            fn f_from_iter<T>(iter: T, $error_msg: &str) -> Self
            where
                T: IntoIterator<Item = $iter_item_type>,
            {
                // Forwarding the implementation to `Iterator::fold`
                // for better efficiency
                iter.into_iter().fold(Self::default(), $for_loop_body)
            }
        }
    };
}

/// calls try_into, and panics if the conversion fails.
/// This helper function is used to reduce typing required for implementations
/// of `ForceFromIterator` in this module.
#[inline]
fn f_into<I: TryInto<J>, J>(item: I, error_msg: &str) -> J {
    match item.try_into() {
        Ok(x) => x,
        _ => panic!("{}", error_msg),
    }
}

implement_collection!(
    error_msg // we have to provide this identifier due to macro hygiene
    [IntoV: TryInto<V>, V] Vec<V>, IntoV,
        move |mut v, item| {v.push(f_into(item, error_msg)); v}
);

implement_collection!(
    error_msg // we have to provide this identifier due to macro hygiene
    [IntoV: TryInto<V>, V] VecDeque<V>, IntoV,
        move |mut v, item| {v.push_back(f_into(item, error_msg)); v}
);

implement_collection!(
    error_msg // we have to provide this identifier due to macro hygiene
    [IntoV: TryInto<V>, V] LinkedList<V>, IntoV,
    |mut v, item| {v.push_back(f_into(item, error_msg)); v}
);

implement_collection!(
    error_msg // we have to provide this identifier due to macro hygiene
    [IntoV: TryInto<V>, V: Ord] BinaryHeap<V>, IntoV,
    |mut v, item| {v.push(f_into(item, error_msg)); v}
);

implement_collection!(
    error_msg // we have to provide this identifier due to macro hygiene
    [IntoK: TryInto<K>, K: Ord] BTreeSet<K>, IntoK,
    |mut v, item| {v.insert(f_into(item, error_msg)); v}
);

implement_collection!(
    error_msg // we have to provide this identifier due to macro hygiene
    [IntoK: TryInto<K>, IntoV: TryInto<V>, K: Ord, V] BTreeMap<K, V>, (IntoK, IntoV),
    |mut v, (into_k, into_v)| {
        v.insert(
            f_into(into_k, error_msg),
            f_into(into_v, error_msg),
        );
        v
    }
);

implement_collection!(
    error_msg // we have to provide this identifier due to macro hygiene
    [IntoK: TryInto<K>, K: std::hash::Hash + Eq] HashSet<K>, IntoK,
    |mut v, item| {v.insert(f_into(item, error_msg)); v}
);

implement_collection!(
    error_msg // we have to provide this identifier due to macro hygiene
    [IntoK: TryInto<K>, IntoV: TryInto<V>, K: std::hash::Hash + Eq, V] HashMap<K, V>, (IntoK, IntoV),
    |mut v, (into_k, into_v)| {
        v.insert(
            f_into(into_k, error_msg),
            f_into(into_v, error_msg),
        );
        v
    }
);

impl<IntoV: TryInto<V>, V, const N: usize> ForceFromIterator<IntoV> for [V; N] {
    fn f_from_iter<T>(iter: T, error_msg: &str) -> Self
    where
        T: IntoIterator<Item = IntoV>,
    {
        use super::{array_transmute, maybe_uninit_array_orderly_cleanup};
        use core::mem::MaybeUninit;

        // We build the array directly inside of the `Ok` result, so that
        // we don't have to copy the data over when we need to return.
        let mut array: [MaybeUninit<V>; N] = unsafe {
            // We are initializing an array that contains uninitialized memory.
            // It is our responsability to ensure that, if the array gets dropped,
            // only its inizialized elements get dropped.
            MaybeUninit::uninit().assume_init()
        };

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
                    Err(_) => {
                        maybe_uninit_array_orderly_cleanup(&mut array, index);
                        panic!("{}", error_msg);
                    }
                }
            }
            maybe_uninit_array_orderly_cleanup(&mut array, index);
            panic!("{}", error_msg);
        }

        // If the iterator contains too many elements for the array, then we
        // orderly drop the entire array, since it has been completely
        // initialized already, and we return an error.
        if iter.next().is_some() {
            maybe_uninit_array_orderly_cleanup(&mut array, N);
            panic!("{}", error_msg);
        }

        unsafe { array_transmute(array) }
    }
}

impl<I> ForceFromIterator<I> for () {
    #[inline]
    fn f_from_iter<T>(iter: T, error_msg: &str) -> Self
    where
        T: IntoIterator<Item = I>,
    {
        match iter.into_iter().next() {
            None => (),
            _ => panic!("{}", error_msg),
        }
    }
}

/// Calling this macro with `n` literal tokens causes it to
/// implement the `ForceFromIterator` trait for tuples of
/// length from `1` up to `n`.
macro_rules! impl_force_from_iterator_for_tuples {
    () => {};
	(
        $discard_first_counter_token: literal
        $($counter: literal)*
    ) => {
        impl<IntoI: TryInto<I>, I> ForceFromIterator<IntoI> for (I, $(ignore_first!($counter I),)*) {
            #[inline]
			fn f_from_iter<T>(iter: T, error_msg: &str) -> Self
            where
				T: IntoIterator<Item = IntoI>
            {
                let mut iter = iter.into_iter();
                let ret = (
                    // We fetch an item from `iter`,
                    // if `None` is returned, or if the returned item
                    // does not convert to `I` successfully,
                    // then we return an error.
                    //
                    // We repeat this `len($counter) + 1` times
                    match iter.next() {
                        Some(x) => match x.try_into() {
                            Ok(y) => y,
                            _ => panic!("{}", error_msg),
                        },
                        _ => panic!("{}", error_msg),
                    },
                    $(
                        ignore_first!(
                            $counter
                            match iter.next() {
                                Some(x) => match x.try_into() {
                                    Ok(y) => y,
                                    _ => panic!("{}", error_msg),
                                },
                                _ => panic!("{}", error_msg),
                            }
                        ),
                    )*
                );
                if iter.next().is_some() {
                    panic!("{}", error_msg)
                }
                ret
            }
        }

        impl_force_from_iterator_for_tuples!($($counter)*);
    };
}

impl_force_from_iterator_for_tuples!(
     1  2  3  4  5  6  7  8  9 10
    11 12 13 14 15 16 17 18 19 20
    21 22 23 24 25 26 27 28 29 30
    31 32
);
