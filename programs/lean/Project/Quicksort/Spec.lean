import Project.Quicksort.Program
import CodeLib.SepLogic.WasmHeap

/-!
# Specification for `quicksort`

Entry point: func12 (funcIdx 12), params: (ptr : i32, len : i32)
Chain: func12 → func8 (slice setup) → func11 (quicksort recursive)
func11 calls partition internally, recurses on left and right halves.

Lomuto partition: last element as pivot, elements ≤ pivot go left.
After partition, pivot is at its final sorted position.
Recursion on [0..pivot_idx) and [pivot_idx+1..len).

Postcondition: the array is sorted and a permutation of the input.
-/
namespace Project.Quicksort

open Wasm Wasm.SepLogic

variable [inst : WasmHeapGS]

/-- The `n` consecutive u32 words in memory at byte address `base`. -/
def wordsAt (m : Mem) (base : UInt32) (n : Nat) : List UInt32 :=
  (List.range n).map (fun i => m.read32 (base + 4 * UInt32.ofNat i))

/-- Quicksort correctness: calling func12 sorts the array in place.

    Postcondition: sorted permutation of input.
    Same spec shape as insertion sort and merge sort. -/
def QuicksortSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr len : UInt32) (xs : List UInt32),
    xs.length = len.toNat →
    ptr.toNat + 4 * xs.length ≤ st.mem.pages * 65536 →
    (1048576 : Nat) ≤ st.mem.pages * 65536 →
    st.globals.globals[0]? = some (.i32 (1048576 : UInt32)) →
    wordsAt st.mem ptr xs.length = xs →
    TerminatesWith env «module» 12 st [.i32 len, .i32 ptr]
      (fun st' _ =>
        ∃ ys : List UInt32,
          wordsAt st'.mem ptr ys.length = ys ∧
          ys.Pairwise (· ≤ ·) ∧
          ys.Perm xs)

end Project.Quicksort
