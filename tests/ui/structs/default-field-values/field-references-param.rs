// Make sure we don't ICE when a field default references a generic parameter via inference.

#![feature(default_field_values)]

struct W<const X: usize>;

impl<const X: usize> W<X> {
    const fn new() -> Self { W }
}

struct Z<const X: usize> {
    x: W<X> = W::new(),
    //~^ ERROR default value for field cannot depend on generic parameters
}

fn main() {}
