import Project.InsertionSort.Program
import CodeLib.SepLogic.WasmHeap

/-!
# Specification for `insertion_sort`

Entry point: func2 (funcIdx 2), params: (ptr : i32, len : i32)
Chain: func2 → func1 (slice setup) → func0 (sort loop)

func0 structure:
  - outer loop: i from 1 to len-1
  - inner loop: j from i downward, shift arr[j-1] right while arr[j-1] > key
  - after inner loop: arr[j] = key
  - bounds checks call func54 (panic) on out-of-range; unreachable on valid input

Postcondition: the array is sorted and a permutation of the input.
-/
namespace Project.InsertionSort

open Wasm Wasm.SepLogic

variable [inst : WasmHeapGS]

/-- The `n` consecutive little-endian `u32` words stored in memory `m`
starting at byte address `base`. Element `i` lives at `base + 4 * i`. -/
def wordsAt (m : Mem) (base : UInt32) (n : Nat) : List UInt32 :=
  (List.range n).map (fun i => m.read32 (base + 4 * UInt32.ofNat i))

/-- Insertion sort correctness: given an array of u32 values at `ptr` with `len`
    elements, calling the module's entry point (func2) sorts the array in place.

    Preconditions:
    - `xs` is the initial array content (length = len)
    - array is within memory bounds
    - global0 holds the shadow stack pointer (1048576 = 0x100000)

    Postcondition: the array is a sorted permutation of the original. -/
def InsertionSortSpec : Prop :=
  ∀ (st : Store Unit) (ptr len : UInt32) (xs : List UInt32),
    xs.length = len.toNat →
    ptr.toNat + 4 * xs.length ≤ st.mem.pages * 65536 →
    (1048576 : Nat) ≤ st.mem.pages * 65536 →
    st.globals.globals[0]? = some (.i32 (1048576 : UInt32)) →
    wordsAt st.mem ptr xs.length = xs →
    ptr.toNat + 4 * xs.length ≤ 1048544 →
    TerminatesWith {} «module» 2 st [.i32 len, .i32 ptr]
      (fun st' _ =>
        ∃ ys : List UInt32,
          wordsAt st'.mem ptr ys.length = ys ∧
          ys.Pairwise (· ≤ ·) ∧
          ys.Perm xs)

end Project.InsertionSort
