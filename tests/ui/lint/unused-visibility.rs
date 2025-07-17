//@ run-rustfix

#![deny(unused_visibility)]

pub const _: i32 = 0;
//~^ ERROR unnecessary visibility marker on unnamed const

pub(crate) const _: i32 = 1;
//~^ ERROR unnecessary visibility marker on unnamed const

pub(in self) const _: i32 = 2;
//~^ ERROR unnecessary visibility marker on unnamed const

#[allow(unused_visibility)]
fn scoped() {
    pub const _: i32 = 5;
}

// Obviously this shouldn't lint.
const _: i32 = 3;

// Nor should we lint on a named const.
pub const NAMED: i32 = 4;

fn main() {}
