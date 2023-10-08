use super::*;

/// The array implementation of `f_collect` relies on a lot of unsafe code.
/// It has to be toroughly tested for memory unsoundness.
///
/// Since we are testing the functionality on `MemDebug` objects,
/// if the test succeeds, we are guaranteed that no uninitialized, or
/// already dropped memory, is ever read in the test.
///
/// Here, we test if `f_collect` succeeds only if the number
/// of elements being collected is equal to the length of the array,
/// and that it panics in the correct way otherwise.
#[test]
fn test_force_collect_on_array() {
    use memory_debug_tools::MemDebug;

    let tag = MemDebug::create_tag();

    let source: Vec<MemDebug<usize>> = (0..840).map(|i| MemDebug::new(i, [])).collect();

    for i in 0..840 {
        let truncated_source: Vec<_> = source[0..i].iter().map(|item| item.clone()).collect();
        let ids: BTreeSet<_> = truncated_source.iter().map(|item| item.id()).collect();

        assert!(MemDebug::add_tag_to_group(ids.iter(), tag).is_ok());

        fn array_gen(iter: Vec<MemDebug<usize>>, error_msg: &str) -> [MemDebug<usize>; 420] {
            iter.f_collect(error_msg)
        }

        // Differently from the `TryCollect` version of this test, here we have
        // to catch potential panics. In order to do so, we spawn threads, and
        // then we join them, to see if a panic occurred.
        let maybe_array = std::thread::spawn(move || {
            array_gen(
                truncated_source,
                if i < 420 {
                    "not enough items"
                } else {
                    "too many items"
                },
            )
        })
        .join();

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
                maybe_array
                    .expect_err("wrong iterator item count")
                    .downcast_ref::<String>()
                    .expect("error should be a string"),
                if i < 420 {
                    &"not enough items"
                } else {
                    &"too many items"
                }
            );
            // We assert that no instances of `MemDebug` are tagged.
            // If the assert succeeds, that means that no memory leak
            // has occurred.
            assert!(MemDebug::get_tag(tag).is_empty());
        }
    }
}

/// The array implementation of `f_collect` relies on a lot of unsafe code.
/// It has to be toroughly tested for memory unsoundness.
///
/// Since we are testing the functionality on `MemDebug` objects,
/// if the test does not panic, we are guaranteed that no uninitialized, or
/// already dropped memory, is ever read in the test.
///
/// Here, we test that `f_collect` succeeds only if all items in the
/// iterator can convert successfully.
#[test]
fn test_force_collect_on_array_conversion_error() {
    use memory_debug_tools::MemDebug;

    let tag = MemDebug::create_tag();

    // We now test the behavior of `f_collect` when item conversion fails.

    let source: Vec<MemDebug<bool>> = (0..840)
        .map(|i| MemDebug::new(if i == 420 { false } else { true }, []))
        .collect();

    for offset in 0..420 {
        // We clone the a subslice of the source material, and we
        // wrap the cloned values in `TryIntoMemDebug`, which
        // will be used later to perform `f_collect` on an array.
        let source: Vec<_> = source[offset..offset + 420]
            .iter()
            .map(|item| TryIntoMemDebug(item.clone()))
            .collect();

        let ids: BTreeSet<_> = source.iter().map(|item| item.0.id()).collect();

        assert!(MemDebug::add_tag_to_group(ids.iter(), tag).is_ok());

        // We spawn a new thread so that if `f_collect` triggers a panic
        // we can detect it.
        let maybe_array: Result<[MemDebug<True>; 420], _> =
            std::thread::spawn(move || source.f_collect("bad item")).join();

        if offset == 0 {
            assert_eq!(*MemDebug::get_tag(tag), ids);
            assert!(maybe_array
                .expect("all items before 420 contain true")
                .iter()
                .all(|e| (**e).0));
        } else {
            assert!(MemDebug::get_tag(tag).is_empty());

            assert_eq!(
                maybe_array
                    .expect_err("item 420 should fail to convert")
                    .downcast_ref::<String>()
                    .expect("the error object is a string"),
                &"bad item"
            );
        }
    }
}

/// Test the `f_collect` functionality for tuples.
/// The tuple implementation is written with a macro, so
/// a test is particularly important to ensure that the implementation
/// does what is specified.
#[test]
fn test_try_collect_on_tuple() {
    // We first test the implementation for the empty tuple.
    // We spawn a new thread to be able to detect the panic.
    assert_eq!(
        std::thread::spawn(move || <()>::f_from_iter(vec![0; 3], "too many items"))
            .join()
            .expect_err("the vec is not empty")
            .downcast_ref::<String>()
            .expect("The panic arg was a string"),
        &"too many items"
    );

    assert_eq!(
        <()>::f_from_iter(vec![0; 0], "Empty vector, this should not fail"),
        ()
    );

    // Then we test non-empty tuples.
    // It would be much nicer to write the test with macros, but that would
    // risk introducing even more potential for errors, hence the copy-paste

    /// In order to detect panics, we spawn new threads and execute `f_collect` there
    fn f_collect<
        I: IntoIterator + Send + 'static,
        J: ForceFromIterator<I::Item> + 'static + Send,
    >(
        c: I,
        error_msg: &str,
    ) -> std::thread::Result<J> {
        let error_msg = String::from(error_msg);
        std::thread::spawn(move || c.f_collect(&error_msg)).join()
    }

    /// To make the code less redundant, we use a standard way to unpack the error from
    /// the panicked `f_collect` into a tuple.
    fn f_collect_assert_err<
        I: IntoIterator + Send + 'static,
        J: ForceFromIterator<I::Item> + Send + core::fmt::Debug + 'static,
    >(
        c: I,
        error_msg: &str,
    ) {
        assert_eq!(
            f_collect::<I, J>(c, error_msg)
                .expect_err("expected thread panic")
                .downcast_ref::<String>()
                .expect("Panic arg should be string"),
            error_msg
        );
    }

    let too_many = "too many items";
    let not_enough = "not enough items";
    let bad_item = "item failed to convert";

    f_collect_assert_err::<_, (u8,)>(vec![0; 3], too_many);
    f_collect_assert_err::<_, (u8, u8)>(vec![0; 3], too_many);
    assert_eq!(
        f_collect::<_, (u8, u8, u8)>(vec![42; 3], "this does not fail")
            .expect("this does not fail"),
        (42, 42, 42)
    );
    f_collect_assert_err::<_, (u8, u8, u8, u8)>(vec![0; 3], not_enough);
    f_collect_assert_err::<_, (u8, u8, u8, u8, u8)>(vec![0; 3], not_enough);

    type U8_3 = (u8, u8, u8);

    f_collect_assert_err::<_, U8_3>([420, 42, 42], bad_item);
    f_collect_assert_err::<_, U8_3>([42, 420, 42], bad_item);
    f_collect_assert_err::<_, U8_3>([42, 42, 420], bad_item);
    f_collect_assert_err::<_, U8_3>([420], bad_item);
    f_collect_assert_err::<_, U8_3>([42, 420], bad_item);
    f_collect_assert_err::<_, U8_3>([42, 42, 420, 42], bad_item);
    f_collect_assert_err::<_, U8_3>([42, 42, 42, 420], too_many);
}

/// This test is instead aimed at testing the more straightforward
/// implementations of `f_collect` on adjustable-size collections.
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
                    ForceCollect::f_collect::<$collection>(v.clone().into_iter(), "this does not fail"),
                    Iterator::collect::<$collection>(
                        v.clone().into_iter()
                            .map($item_conversion)
                    )
                );

                assert_eq!(
                    // We spawn a new thread to be able to detect the panic.
                    std::thread::spawn(
                        move || ForceCollect::f_collect::<$collection>(
                            w.clone().into_iter(),
                            $error
                    )).join()
                        .expect_err("this iterator should generate an error")
                        .downcast_ref::<String>()
                        .expect("The panic arg should be a string"),
                    $error
                );
            )+
        };
    }

    test_collections!(
        [42_u16, 42, 16, 28, 64, 65, 42],
        [42_u16, 420, 42], // TryInto::<u8>::try_into(420_u16) fails.
        |item: u16| -> u8 { item.try_into().unwrap() },
        "TRY_FROM_INT_ERR",
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
    // Notice that we also test that `f_collect` behaves well when there
    // are repeated keys.

    let tuple_try_into = |(k, v): (u16, u16)| (k as u8, v as u8);

    test_collections!(
        [(42_u16, 42_u16), (12, 42), (64, 42), (0, 42), (64, 21)],
        [(42_u16, 42_u16), (420, 42), (12, 42)],// key conversion fail
        tuple_try_into,
        "TRY_FROM_INT_ERR",
        BTreeMap<u8, u8>,
        HashMap<u8, u8>,
    );

    test_collections!(
        [],
        [(42_u16, 42_u16), (42, 420), (12, 42)],// value conversion fail
        tuple_try_into,
        "TRY_FROM_INT_ERR",
        BTreeMap<u8, u8>,
        HashMap<u8, u8>,
    );
}
