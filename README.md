# Content

This crate defines the traits `TryFromIterator`, `TryCollect`, `ForceFromIterator`, and `ForceCollect`,  and implements them for arrays, homogeneous tuples, and the collections in the standard library.

## `TryFromIterator` and `TryCollect`


`TryFromIterator` provides the function `try_from_iter`, that generalizes the functionality provided by
`FromIterator::from_iter`.  
`TryCollect` provides the function `try_collect`, that does with `TryFromIterator` the same `Iterator::collect` does with `FromIterator`, i.e.

```rust
fn try_collect<T: TryFromIterator<Self::Item>>(self) -> Result<T, T::Error> {
    TryFromIterator::try_from_iter(self.into_iter())
}
```

The generalization provided by the traits defined here resides in the fact that `try_from_iter` is like `FromIterator::from_iter`, but it is allowed to fail, and this allows a more flexible implementation.  
For example, the following code is valid:

```rust
let v = vec!["a", "b", "c"];
let w : [&str; 3] = v
    .clone()
    .try_collect()
    .unwrap_or(["hello", "hi", "howdy"]);

let z: [&str; 2] = v
    .try_collect()
    .unwrap_or(["hello", "hi"]);

assert_eq!(w, ["a", "b", "c"]);
assert_eq!(z, ["hello", "hi"]);
```

and there is no equivalent way to do the same in a concise way when `v` is not known in advance, or if the lengths of `w` and `z` are above `32`, using only the standard library.

Another flexibility that the implementations of `TryFromIterator` provide is that they can automatically convert the items yielded by the iterator via `TryInto` to match the items of the collection one is trying to collect into.  
For example, the following code is valid:

```rust
let v : [u16; 3] = [42, 42, 42];
let w: Vec<u8> = v.clone().try_collect();

let z: Vec<u8> = v
    .into_iter()
    .try_fold(vec![], |mut vec, item| {
        vec.push(item.try_into()?);
        Ok(vec)
    });

// more explicit construction for z:
// let mut z = Ok(Vec::<u8>::new());
// for item in v {
//     match item.try_into() {
//         Ok(item) => z.as_mut().unwrap().push(item),
//         Err(e) => {
//             z = Err(e);
//             break
//         }
//     }
// }

assert_eq!(w, z);

let a : [u16; 3] = [42, 420, 42]; // 420 does not fit in u8
let b: Vec<u8> = a.try_collect();

assert!(b.is_err());
```

## `ForceFromIterator` and `ForceCollect`

Those traits are the panicky versions of `TryFromIterator` and `TryCollect`.

The idea of those traits is to provide a shorthand, and possibly more optimized, way of performing

```rust
iterator.try_collect::<SomeType>().expect("error msg")
```

and as such, they should be used with the due caution.

`ForceFromIterator::f_from_iter` is the panicky version of `TryFromIterator::try_from_iter`.

it is defined as sub-trait of `ForceFromIterator`, as follows:

```rust
trait ForceFromIterator<Item> : TryFromIterator<Item> {
    fn f_from_iter<I: IntoIterator<Item = Item>>(iter: I, error_msg: &str) -> Self {
        Self::try_from_iter().expect(error_msg)
    }
}
```

***Pay attention to the fact that this blanket implementation is overwriteable, and that a custom type may implement it in other ways.***

We do however encourage the users of this trait to only make implementations that are (*almost*)equivalent to

```rust
Self::try_from_iter().expect(error_msg)
```

and only improve the efficiency of the implementation, as we do for example in the implementations brovided in this crate.

`ForceCollect`, similarly to `TryCollect`, is defined as a sub-trait of `IntoIterator`, as follows:

```rust
trait ForceCollect: IntoIterator {
    fn f_collect<T: ForceFromIterator<Self::Item>>(self, error_msg: &str) -> T;
}

impl<X: IntoIterator> ForceCollect for X {
    fn f_collect<T: ForceFromIterator<Self::Item>>(self, error_msg: &str) -> T {
        T::f_from_iter(self, error_msg)
    }
}
```

Notice that this blanket implementation is not overwriteable, and it is forced to be coherent with whatever `ForceFromIterator` does.

We remind again that, due to the overwriteability of the implementtion of `ForceFromIterator::f_from_iter`, it is technically not guaranteed, although it is strongly encouraged, that

```rust
iterator.try_collect::<SomeType>().expect("error msg")
```

and

```rust
iterator.f_collect::<SomeType>("error msg")
```

resolve in the same way.