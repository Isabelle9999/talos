/// Wasm-exported entry point for `quicksort`.
///
/// Receives the array as a `(pointer, length)` pair.
/// The caller must guarantee that `[array_ptr, array_ptr + length * 4)`
/// is a valid, aligned `u32` region.
#[unsafe(no_mangle)]
pub extern "C" fn quicksort(array_ptr: *mut u32, length: usize) {
    let arr = unsafe { core::slice::from_raw_parts_mut(array_ptr, length) };
    crate::quicksort(arr);
}