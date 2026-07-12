import Project.InsertionSort.Program
import CodeLib.SepLogic.WasmHeap

/-!
# Specification for `insertion_sort`

Entry point: func2 (funcIdx 2), params: (array_ptr : i32, length : i32)
Chain: func2 → func1 (slice setup) → func0 (sort loop)

func0 structure:
  - outer loop: i from 1 to len-1
  - inner loop: j from i downward, shift arr[j-1] right while arr[j-1] > key
  - after inner loop: arr[j] = key
  - bounds checks call func54 (panic) on out-of-range

Postcondition: the array is sorted and a permutation of the input.
-/
namespace Project.InsertionSort

open Wasm Wasm.SepLogic

variable [inst : WasmHeapGS]

/-- Insertion sort correctness: given an array of u32 values at `ptr`,
    calling insertion_sort produces a sorted permutation in-place.

    pre:  arrayAt ptr xs  (own the array with contents xs)
    post: ∃ ys, arrayAt ptr ys ∧ ys.Pairwise (· ≤ ·) ∧ ys.Perm xs -/
def insertion_sort_spec (ptr : UInt32) (xs : List UInt32) : Prop :=
  wp_wasm_prop «module» { mem := default, .. } -- initial store
    (func2Def.toLocals [.i32 ptr, .i32 (UInt32.ofNat xs.length)])
    func2Def.body {}
    (fun st' _ =>
      ∃ ys : List UInt32,
        wordsAt st'.mem ptr ys.length = ys ∧
        ys.Pairwise (· ≤ ·) ∧
        ys.Perm xs)

end Project.InsertionSort
