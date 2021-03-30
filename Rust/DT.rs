trait Level {
    fn to_nat(&self) -> i32;
}

struct L0;
impl Level for L0 {
    fn to_nat(&self) -> i32 {
        0
    }
}
struct L1;
impl Level for L1 {
    fn to_nat(&self) -> i32 {
        1
    }
}
struct L2;
impl Level for L2 {
    fn to_nat(&self) -> i32 {
        2
    }
}

struct Type<T> where
  T : Level
{
    level: T,
}

struct Equality<T> {
    a1: T,
    a2: T,
}

trait PI<T> {
    fn acc(a2 : T, e: Equality<T>) -> dyn Level;
}

fn J<A, B>(_a1: A, b: B, a2: A, p: Equality<A>) -> B where
    A : Level,
    B : PI<A>
{
    move |a, p| { L0{} }
}
