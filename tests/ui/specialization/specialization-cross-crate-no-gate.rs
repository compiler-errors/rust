//@ run-pass

// Test that specialization works even if only the upstream crate enables it

//@ aux-build:specialization_cross_crate.rs

extern crate specialization_cross_crate;

use specialization_cross_crate::*;

fn  main() {
    assert_eq!(0u8.foo(), "generic Clone");
    assert_eq!(vec![0u8].foo(), "generic Vec");
    assert_eq!(vec![0i32].foo(), "Vec<i32>");
    assert_eq!(0i32.foo(), "i32");
    assert_eq!(String::new().foo(), "String");
    assert_eq!(((), 0).foo(), "generic pair");
    assert_eq!(((), ()).foo(), "generic uniform pair");
    assert_eq!((0u8, 0u32).foo(), "(u8, u32)");
    assert_eq!((0u8, 0u8).foo(), "(u8, u8)");
}
