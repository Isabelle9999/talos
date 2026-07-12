mod exports;

/// In-place insertion sort on a mutable slice of u32.
///
/// Stable, O(n²) comparison sort. Maintains the invariant that
/// `arr[0..i]` is sorted after each outer iteration.
pub fn insertion_sort(arr: &mut [u32]) {
    let mut i = 1;
    while i < arr.len() {
        let key = arr[i];
        let mut j = i;
        while j > 0 && arr[j - 1] > key {
            arr[j] = arr[j - 1];
            j -= 1;
        }
        arr[j] = key;
        i += 1;
    }
}