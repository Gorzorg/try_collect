use memory_debug_tools::MemDebug;

/// In order to make some tests on the implementation of try_collect,
/// we need to keep track of `MemDebug` objects while their inner data
/// undergoes a `try_into` transformation.
/// For this purpose, we declare a wrapper that allows exactly that.
///
/// It implements
///
/// ```ignore
/// impl<D: TryInto<E>, E> TryInto<MemDebug<E>> for TryIntoMemDebug<D>
/// ```
///
/// in a way that preserves the continuity of the underlying `MemDebug`
/// instance. More precisely, this means that the `Ok` output of
/// `try_into` will be a `MemDebug` instance with the same `id` as the
/// one that was used as input.
pub struct TryIntoMemDebug<Data>(pub MemDebug<Data>);

impl<Data> From<MemDebug<Data>> for TryIntoMemDebug<Data> {
    fn from(value: MemDebug<Data>) -> Self {
        Self(value)
    }
}

impl<Data: TryInto<OtherData>, OtherData> TryInto<MemDebug<OtherData>> for TryIntoMemDebug<Data> {
    type Error = MemDebug<<Data as TryInto<OtherData>>::Error>;
    fn try_into(self) -> Result<MemDebug<OtherData>, Self::Error> {
        let (id, data) = unsafe { self.0.into_raw_parts() };
        match data.try_into() {
            Ok(data) => Ok(unsafe { MemDebug::from_raw_parts(id, data) }),
            Err(err) => Err(unsafe { MemDebug::from_raw_parts(id, err) }),
        }
    }
}
