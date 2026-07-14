import Project.SelectionSort.Program
import CodeLib.SepLogic.WasmHeap

/-!
# Specification for `selection_sort`

Entry point: func8 (funcIdx 8), params: (ptr : i32, len : i32)
Chain: func8 → func7 (slice setup) → func0 (sort with find-min + swap)

Selection sort: for each position i, finds the minimum in arr[i..n],
swaps it to position i. Uses arr.swap internally.

Postcondition: the array is sorted and a permutation of the input.
-/
namespace Project.SelectionSort

open Wasm Wasm.SepLogic

def wordsAt (m : Mem) (base : UInt32) (n : Nat) : List UInt32 :=
  (List.range n).map (fun i => m.read32 (base + 4 * UInt32.ofNat i))

def SelectionSortSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr len : UInt32) (xs : List UInt32),
    xs.length = len.toNat →
    ptr.toNat + 4 * xs.length ≤ st.mem.pages * 65536 →
    st.globals.globals[0]? = some (.i32 (1048576 : UInt32)) →
    wordsAt st.mem ptr xs.length = xs →
    TerminatesWith env «module» 8 st [.i32 len, .i32 ptr]
      (fun st' _ =>
        ∃ ys : List UInt32,
          wordsAt st'.mem ptr ys.length = ys ∧
          ys.Pairwise (· ≤ ·) ∧
          ys.Perm xs)

end Project.SelectionSort
