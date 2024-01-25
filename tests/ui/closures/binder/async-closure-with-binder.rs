// edition:2021
#![feature(closure_lifetime_binder)]
#![feature(async_closure)]
fn main() {
    for<'a> async || -> () {};
}
