import Project.InsertionSort.Program
import CodeLib.SepLogic.WasmHeap

/-!
# Specification for `insertion_sort`

Entry point: func2 (funcIdx 2), params: (array_ptr : i32, length : i32)
func2 → func1 (slice setup) → func0 (sort loop)

Postcondition: the array is sorted and a permutation of the input.
-/
namespace Project.InsertionSort.Spec
open Wasm

-- TODO: prove using iris-lean pipeline (arrayAt, wp_wasm_prop, wasm_heap_adequacy)
-- Spec: ∀ ptr n xs, xs.length = n.toNat →
--   arrayAt ptr xs ⊢ wp_wasm_prop ... (fun st' _ =>
--     ∃ ys, arrayAt ptr ys ∧ ys.Pairwise (· ≤ ·) ∧ ys.Perm xs)

end Project.InsertionSort.Spec
