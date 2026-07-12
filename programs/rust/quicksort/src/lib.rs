mod exports;

/// In-place quicksort on a mutable slice of u32.
/// Uses Lomuto partition scheme with last element as pivot.
pub fn quicksort(arr: &mut [u32]) {
    if arr.len() <= 1 {
        return;
    }
    let pivot_idx = partition(arr);
    quicksort(&mut arr[..pivot_idx]);
    quicksort(&mut arr[pivot_idx + 1..]);
}

/// Lomuto partition: elements < pivot go left, pivot ends at its final position.
/// Returns the index where the pivot was placed.
fn partition(arr: &mut [u32]) -> usize {
    let pivot = arr[arr.len() - 1];
    let mut i = 0;
    for j in 0..arr.len() - 1 {
        if arr[j] <= pivot {
            arr.swap(i, j);
            i += 1;
        }
    }
    arr.swap(i, arr.len() - 1);
    i
}