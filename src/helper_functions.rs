use std::mem::MaybeUninit;

/// This function is roughly equivalent to a special case of
/// [`transmute`][`core::mem::transmute`].
///
/// This custom implementation is needed because, at present day (Aug 2023),
/// [`transmute`][`core::mem::transmute`] cannot handle generic types.
/// For example, even trying though
/// [`transmute::<T, T>`][`core::mem::transmute`] would
/// be sound with a generic `T`, the compiler cannot understand it yet,
/// and similarly it cannot understand the soundness of
/// [`transmute::<[MaybeUninit<T>; N], [T; N]>`][`core::mem::transmute`].
///
/// ## Undefined Behavior:
///
/// The caller of this function has to make sure that all the elements of the
/// array are properly initialized. Failing to do so is undefined behavior.
///
/// ## Soundness:
///
/// The memory layout of [`MaybeUninit<T>`][`core::mem::MaybeUninit`] is the
/// same as the memory layout of `T`, and this implies that the memory layout
/// of `[MaybeUninit<T>; N]` is the same as the memory layout of `[T; N]`.
/// This ensures that no alignment errors occur while performing the cast.
///
/// Also, the memory of the initialized variant of
/// [`MaybeUninit<T>`][`core::mem::MaybeUninit`] contains the exact same data
/// of a valid instance of `T`, so reinterpreting the data does not raise any
/// logical errors.
///
/// As a first operation, we wrap `maybe_uninit_array` into a
/// [`ManuallyDrop<[MaybeUninit<T>; N]>`][`core::mem::ManuallyDrop`],
/// for which we will not call the destructor.
///
/// Since we cannot apply [`transmute`][`core::mem::transmute`] directly,
/// we use [`core::ptr::read`] to make a copy of the memory of
/// `maybe_uninit_array`, we interpret the
/// copied memory as a `[T; N]`, and we return that object.
///
/// If the input contains properly initialized items, the output also does.
/// Moreover, even if `T` is not [`Copy`], since the input is never used,
/// and never dropped, after the copy with [`read`][`core::ptr::read`].
///
/// ## Efficiency:
///
/// [`read`][`core::ptr::read`] tecnically requires
/// the memory to be copied, but one can assume that every
/// non-zero level of optimization while building the program
/// will optimize the copy away in almost all cases.
pub(crate) unsafe fn array_transmute<T, const N: usize>(
    maybe_uninit_array: [MaybeUninit<T>; N],
) -> [T; N] {
    let maybe_uninit_array = core::mem::ManuallyDrop::new(maybe_uninit_array);
    unsafe { core::ptr::read(maybe_uninit_array.as_ptr() as *const _) }
}

/// A function that drops the first `initialized_up_to` items of an array
/// that contains [`MaybeUninit`][`core::mem::MaybeUninit`] items.
#[inline]
pub(crate) fn maybe_uninit_array_orderly_cleanup<I, const M: usize>(
    array: &mut [MaybeUninit<I>; M],
    initialized_up_to: usize,
) {
    for drop_index in 0..initialized_up_to {
        unsafe { array[drop_index].assume_init_drop() }
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
#[macro_export]
macro_rules! ignore_first {
	($unused: tt $($whatever: tt)*) => {
		$($whatever)*
	};
}
