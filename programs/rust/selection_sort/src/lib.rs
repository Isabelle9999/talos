mod exports;

/// In-place selection sort on a mutable slice of u32.
/// Finds the minimum in the unsorted portion and swaps it to the front.
/// Uses swap as a subroutine.
pub fn selection_sort(arr: &mut [u32]) {
    let n = arr.len();
    for i in 0..n {
        let mut min_idx = i;
        for j in (i + 1)..n {
            if arr[j] < arr[min_idx] {
                min_idx = j;
            }
        }
        arr.swap(i, min_idx);
    }
}