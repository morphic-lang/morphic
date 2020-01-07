extern "C" {
    fn dummy(i: *mut i32);
}

fn main() {
    let mut i = 0;
    unsafe { dummy(&mut i) };
}
