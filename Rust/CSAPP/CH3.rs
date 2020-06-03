fn decode2(x: i64, y: i64, z: i64) -> i64 {
    ((y - z) << 63 >> 63) ^ ((y - z) * x)
}

fn loop1(x: i64, n: i32) -> i64 {
    let mut res:i64 = 0;
    while { let mut mask:i64 = 1; res = res | (x & mask); mask = mask << n; mask == 0 } {}
    res
}

fn cread_alt(_xp: &i64) -> i64 {
    // (!xp) ? 0 : *xp
    // As you see, this can't be true in Rust
    114514
}

enum ModeT {
    ModeA, ModeB, ModeC, ModeD, ModeE
}

fn switch3(p1: &mut i64, p2: &mut i64, action: ModeT) -> i64{
    match action {
        ModeT::ModeA => {let t2 = *p2; *p2 = *p1; t2},
        ModeT::ModeB => {let t = *p2 + *p1; *p1 = t; t},
        ModeT::ModeC => {*p1 = 59; *p2},
        ModeT::ModeD => {*p1 = *p2; 27},
        ModeT::ModeE => 27,
        _      => 12, // In fact never reachable.
    }
}

fn switch_prob(x: i64, n: i64) -> i64{
    match n {
        60 | 62 => 8 * x,
        63 => x >> 3,
        64 => (x << 4 - x) + 75,
        65 => (x * x) + 75,
        _  => x + 75,
    }
}

#[derive(Copy, Clone)]
union Ele<'a> {
    a: E1<'a>,
    b: E2<'a>
}

#[derive(Copy, Clone)]
struct E1<'a> {
    p: &'a i64,
    y: i64
}

#[derive(Copy, Clone)]
struct E2<'a> {
    x: i64,
    next: &'a Ele<'a>
}

fn proc(up: &mut Ele) {
    unsafe {
        (*up).b.x = *((*((*up).b.next)).a.p) -  (*((*up).b.next)).a.y; // Fuck Rust!!!!
    }
}

/*
    find_range:
        vxorps %xmm1, %xmm1, %xmm1
        vusomiss %xmm0, %xmm1
        jp .L5
        movl $0, $eax
        ja .L3
        movl $1, $eax
        je .L3
        movl $1, $eax
        ret
        .L5:
            movl $3, $eax
        .L3:
            rep; ret

*/

/*
    find_range:
        xorq $rax, %rax
        movq $1, $r8
        movq $2, $r9
        movq $3, $r10
        vxorps %xmm1, %xmm1, %xmm1
        vusomiss %xmm0, %xmm1
        cmoveq $r8 $rax
        cmovbq $r9 $rax
        cmovpq $r10 $rax

*/

fn main() {
    let mut a: i64 = 6;
    let mut b: i64 = 4;
    println!("{}", switch3(&mut a, &mut b, ModeT::ModeB));
}