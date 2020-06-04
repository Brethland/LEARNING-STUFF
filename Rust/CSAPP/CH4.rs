/*   
  movq REG, -8(%rsp)
  subq $8, %rsp

  addq $8, %rsp
  movq 8(%rsp), REG
*/

fn bubble_sort(array: &mut [i64], cnt: isize) {
    let array = array.as_mut_ptr();
    for last in 0..(cnt - 1) {
        for i in 0..(cnt - last - 1) {
            unsafe {
                if *(array.wrapping_offset(i + 1)) < *(array.wrapping_offset(i)) {
                    *(array.wrapping_offset(i + 1)) = *(array.wrapping_offset(i + 1)) ^ *(array.wrapping_offset(i));
                    *(array.wrapping_offset(i))     = *(array.wrapping_offset(i)) ^ *(array.wrapping_offset(i + 1));
                    *(array.wrapping_offset(i + 1)) = *(array.wrapping_offset(i + 1)) ^ *(array.wrapping_offset(i));
                }
            }
        }
    }
}

fn main() {

}