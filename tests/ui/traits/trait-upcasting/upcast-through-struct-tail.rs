// revisions: current next
//[next] compile-flags: -Ztrait-solver=next
// check-pass

struct Wrapper<T: ?Sized>(T);

trait A: B {}
trait B {}

fn test<'a>(x: Box<Wrapper<dyn A + 'a>>) -> Box<Wrapper<dyn B + 'a>> {
    x
}

fn main() {}
