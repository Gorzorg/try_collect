use super::*;

/// The array implementation of try_collect relies on a lot of unsafe code.
/// It has to be toroughly tested for memory unsoundness.
///
/// Since we are testing the functionality on `MemDebug` objects,
/// if the test does not panic, we are guaranteed that no uninitialized, or
/// already dropped memory, is ever read in the test.
///
/// Here, we test if `try_collect` succeeds only if the number
/// of elements being collected is equal to the length of the array.
#[test]
fn test_try_collect_on_array() {
    use memory_debug_tools::MemDebug;

    let tag = MemDebug::create_tag();

    let source: Vec<MemDebug<usize>> = (0..840).map(|i| MemDebug::new(i, [])).collect();

    for i in 0..840 {
        let truncated_source: Vec<_> = source[0..i].iter().map(|item| item.clone()).collect();
        let ids: BTreeSet<_> = truncated_source.iter().map(|item| item.id()).collect();

        assert!(MemDebug::add_tag_to_group(ids.iter(), tag).is_ok());
        let maybe_array: Result<[MemDebug<_>; 420], _> = truncated_source.try_collect();

        if i == 420 {
            let array = maybe_array.expect("the length matches, so try collect should succeed");
            // We assert that exactly the right `MemDebug` instances are tagged
            // i.e. the ones that were in `truncated_source`
            assert_eq!(*MemDebug::get_tag(tag), ids);
            // We assert that the array was copied in the correct order.
            for (idx, item) in array.iter().enumerate() {
                assert_eq!(idx, **item);
            }
        } else {
            assert_eq!(
                maybe_array.expect_err("wrong iterator item count"),
                if i < 420 {
                    ArrayAndTupleError::NotEnoughItems
                } else {
                    ArrayAndTupleError::TooManyItems
                }
            );
            // We assert that no instances of `MemDebug` are tagged.
            // If the assert succeeds, that means that no memory leak
            // has occurred.
            assert!(MemDebug::get_tag(tag).is_empty());
        }
    }
}

/// The array implementation of try_collect relies on a lot of unsafe code.
/// It has to be toroughly tested for memory unsoundness.
///
/// Since we are testing the functionality on `MemDebug` objects,
/// if the test does not panic, we are guaranteed that no uninitialized, or
/// already dropped memory, is ever read in the test.
///
/// Here, we test that `try_collect` succeeds only if all items in the
/// iterator can convert successfully.
#[test]
fn test_try_collect_on_array_conversion_error() {
    use memory_debug_tools::MemDebug;

    let tag = MemDebug::create_tag();

    // We now test the behavior of `try_collect` when item conversion fails.

    let source: Vec<MemDebug<bool>> = (0..840)
        .map(|i| MemDebug::new(if i == 420 { false } else { true }, []))
        .collect();

    for offset in 0..420 {
        // We clone the a subslice of the source material, and we
        // wrap the cloned values in `TryIntoMemDebug`, which
        // will be used later to perform `try_collect` on an array.
        let source: Vec<_> = source[offset..offset + 420]
            .iter()
            .map(|item| TryIntoMemDebug(item.clone()))
            .collect();

        let ids: BTreeSet<_> = source.iter().map(|item| item.0.id()).collect();

        // The id of the `TryIndoMemDebug` instance that will fail to convert.
        let bad_id = if offset == 0 {
            None
        } else {
            Some(source[420 - offset].0.id())
        };

        assert!(MemDebug::add_tag_to_group(ids.iter(), tag).is_ok());

        let maybe_array: Result<[MemDebug<True>; 420], _> = source.try_collect();

        if offset == 0 {
            assert_eq!(*MemDebug::get_tag(tag), ids);
            assert!(maybe_array
                .expect("all items before 420 contain true")
                .iter()
                .all(|e| (**e).0));
        } else {
            let bad_id = bad_id.unwrap();
            assert_eq!(*MemDebug::get_tag(tag), BTreeSet::from_iter([bad_id]));
            // Since `MemDebug` instances cannot be copied, we cannot use
            // assert_eq directly here.
            match maybe_array.expect_err("item 420 should fail to convert") {
                ArrayAndTupleError::TryFromError(mem_dbg) => {
                    assert_eq!((mem_dbg.id(), *mem_dbg), (bad_id, false))
                }
                _ => panic!("Wrong error variant"),
            }
        }
    }
}

// Apparently there is no way to directly declare a
// `core::num::TryFromIntError` instance, so we make one out of thin air,
// since it is a zero-sized type.
//
// We will use this value in `assert_eq!` statements.
const TRY_FROM_INT_ERR: core::num::TryFromIntError =
    unsafe { *core::ptr::NonNull::<core::num::TryFromIntError>::dangling().as_ref() };

/// Test the try-collect functionality for tuples.
/// The tuple implementation is written with a macro, so
/// a test is particularly important to ensure that the implementation
/// does what is specified.
#[test]
fn test_try_collect_on_tuple() {
    // We first test the implementation for the empty tuple.
    assert_eq!(
        <()>::try_from_iter(vec![0; 3]),
        Err(ArrayAndTupleError::TooManyItems)
    );

    assert_eq!(<()>::try_from_iter(vec![0; 0]), Ok(()));

    // Then we test non-empty tuples.
    // It would be much nicer to write the test with macros, but that would
    // risk introducing even more potential for errors, hence the copy-paste

    //we declare shorthands for the error kinds we will encounter:
    fn too_many<T, E>() -> Result<T, ArrayAndTupleError<E>> {
        Err(ArrayAndTupleError::TooManyItems)
    }
    fn not_enough<T, E>() -> Result<T, ArrayAndTupleError<E>> {
        Err(ArrayAndTupleError::NotEnoughItems)
    }
    fn try_from_err<T>() -> Result<T, ArrayAndTupleError<core::num::TryFromIntError>> {
        Err(ArrayAndTupleError::TryFromError(TRY_FROM_INT_ERR))
    }

    assert_eq!(vec![0; 3].try_collect::<(u8,)>(), too_many(),);
    assert_eq!(vec![0; 3].try_collect::<(u8, u8)>(), too_many(),);
    assert_eq!(vec![42; 3].try_collect::<(u8, u8, u8)>(), Ok((42, 42, 42)));
    assert_eq!(vec![0; 3].try_collect::<(u8, u8, u8, u8)>(), not_enough(),);
    assert_eq!(
        vec![0; 3].try_collect::<(u8, u8, u8, u8, u8)>(),
        not_enough(),
    );

    type U8_3 = (u8, u8, u8);

    assert_eq!([420, 42, 42].try_collect::<U8_3>(), try_from_err(),);
    assert_eq!([42, 420, 42].try_collect::<U8_3>(), try_from_err(),);
    assert_eq!([42, 42, 420].try_collect::<U8_3>(), try_from_err(),);
    assert_eq!([420].try_collect::<U8_3>(), try_from_err(),);
    assert_eq!([42, 420].try_collect::<U8_3>(), try_from_err(),);
    assert_eq!([42, 42, 420, 42].try_collect::<U8_3>(), try_from_err(),);
    assert_eq!([42, 42, 42, 420].try_collect::<U8_3>(), too_many(),);
}

/// This test is instead aimed at testing the more straightforward
/// implementations of try_collect on adjustable-size collections.
/// The only thing we have to take into account here are conversion errors
#[test]
fn test_try_collect_on_std_collections() {
    macro_rules! test_collections {
        ($valid_iter: expr, $invalid_iter: expr, $item_conversion: expr, $error: expr, $($collection: ty),+ $(,)?) => {
            let v = $valid_iter;
            let w = $invalid_iter;
            $(
                // We test a valid collection input
                assert_eq!(
                    TryCollect::try_collect::<$collection>(v.clone().into_iter()),
                    Ok(Iterator::collect::<$collection>(
                        v.clone().into_iter()
                            .map($item_conversion)
                    ))
                );
                assert_eq!(
                    TryCollect::try_collect::<$collection>(w.clone().into_iter()),
                    Err($error)
                );
            )+
        };
    }

    test_collections!(
        [42_u16, 42, 16, 28, 64, 65, 42],
        [42_u16, 420, 42], // TryInto::<u8>::try_into(420_u16) fails.
        |item: u16| -> u8 { item.try_into().unwrap() },
        TRY_FROM_INT_ERR,
        Vec<u8>,
        VecDeque<u8>,
        LinkedList<u8>,
        BHWrapper<u8>, // Eq not implemented for `BinaryHeap`, so we wrap it.
        BTreeSet<u8>,
        HashSet<u8>,
    );

    // We test maps twice. Once, we make the conversion of a key fail,
    // and the second time we make the conversion of a value fail.
    //
    // Notice that we also test that `try_collect` behaves well when there
    // are repeated keys.

    let tuple_try_into = |(k, v): (u16, u16)| (k as u8, v as u8);

    test_collections!(
        [(42_u16, 42_u16), (12, 42), (64, 42), (0, 42), (64, 21)],
        [(42_u16, 42_u16), (420, 42), (12, 42)],// key conversion fail
        tuple_try_into,
        (Some(TRY_FROM_INT_ERR), None),
        BTreeMap<u8, u8>,
        HashMap<u8, u8>,
    );

    test_collections!(
        [],
        [(42_u16, 42_u16), (42, 420), (12, 42)],// value conversion fail
        tuple_try_into,
        (None, Some(TRY_FROM_INT_ERR)),
        BTreeMap<u8, u8>,
        HashMap<u8, u8>,
    );
}
