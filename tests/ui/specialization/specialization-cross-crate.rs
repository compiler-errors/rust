//@ run-pass

//@ aux-build:specialization_cross_crate.rs

#![feature(specialization)] //~ WARN the feature `specialization` is incomplete

extern crate specialization_cross_crate;

use specialization_cross_crate::*;

struct NotClone;

#[derive(Clone)]
struct MarkedAndClone;
impl MyMarker for MarkedAndClone {}

struct MyType<T>(#[allow(dead_code)] T);
impl<T> Foo for MyType<T> {
    default fn foo(&self) -> &'static str {
        "generic MyType"
    }
}

impl Foo for MyType<u8> {
    fn foo(&self) -> &'static str {
        "MyType<u8>"
    }
}

struct MyOtherType;
impl Foo for MyOtherType {}

fn  main() {
    assert_eq!(NotClone.foo(), "generic");
    assert_eq!(0u8.foo(), "generic Clone");
    assert_eq!(vec![NotClone].foo(), "generic");
    assert_eq!(vec![0u8].foo(), "generic Vec");
    assert_eq!(vec![0i32].foo(), "Vec<i32>");
    assert_eq!(0i32.foo(), "i32");
    assert_eq!(String::new().foo(), "String");
    assert_eq!(((), 0).foo(), "generic pair");
    assert_eq!(((), ()).foo(), "generic uniform pair");
    assert_eq!((0u8, 0u32).foo(), "(u8, u32)");
    assert_eq!((0u8, 0u8).foo(), "(u8, u8)");
    assert_eq!(MarkedAndClone.foo(), "generic Clone + MyMarker");

    assert_eq!(MyType(()).foo(), "generic MyType");
    assert_eq!(MyType(0u8).foo(), "MyType<u8>");
    assert_eq!(MyOtherType.foo(), "generic");
}
