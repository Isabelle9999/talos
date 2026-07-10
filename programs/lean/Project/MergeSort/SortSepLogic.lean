import Project.MergeSort.MergeFull
import Project.MergeSort.Spec
import CodeLib.SepLogic.Adequacy

namespace Wasm.SepLogic.MergeSort

open Wasm Project.MergeSort Project.MergeSort.Spec

variable [WasmHeapGS]

/-
call graph (imports = [], .call N = funcN):
  func33 (export "merge_sort", params: i32 i32) →
    func15 (slice-header init, straight-line) →
    func1  (sort with pre-allocated scratch) →
      func2  → func20 (vec init, allocator deferred)
      func0  (field copy, straight-line)
      func3  (recursive sort) →
        func5  (slice split, allocator deferred)
        func3  (left half, recursive)
        func3  (right half, recursive)
        func6  (merge, proven by func6_terminates)
        func7  → func13 (copy-back, deferred)
      func4  → func8, func9 (dealloc, allocator deferred)
-/

-- func15: straight-line, stores v1 at ptr, v2 at ptr+4
-- provable via ⟨7, by simp [exec, execOne.eq_def]⟩; deferred
private theorem func15_terminates
    (st : Store Unit) (ptr v1 v2 v3 : UInt32)
    (hb : ptr.toNat + 8 ≤ st.mem.pages * 65536) :
    TerminatesWith {} «module» 15 st
      [.i32 v3, .i32 v2, .i32 v1, .i32 ptr]
      (fun st' _ => st'.mem.read32 ptr = v1 ∧ st'.mem.read32 (ptr + 4) = v2) := by
  sorry

-- func3: recursive sort; terminates by induction on src_n
-- allocator verification deferred (func5)
private theorem func3_terminates
    (st : Store Unit) (src_ptr src_n dst_ptr dst_n : UInt32) :
    TerminatesWith {} «module» 3 st
      [.i32 dst_n, .i32 dst_ptr, .i32 src_n, .i32 src_ptr]
      (fun _ _ => True) := by
  sorry -- allocator verification deferred (func5)

-- func1: sort with scratch; defers to func3
-- allocator verification deferred (func2, func4)
private theorem func1_terminates
    (st : Store Unit) (data_ptr len : UInt32) :
    TerminatesWith {} «module» 1 st
      [.i32 len, .i32 data_ptr]
      (fun _ _ => True) := by
  sorry -- allocator verification deferred (func2, func4)

-- content correctness deferred: requires Pairwise/Perm derivation from func3 correctness
-- env bridge deferred: «module».imports = [], so run is env-independent
-- func33: preamble → wp_wasm_prop_call func15_terminates → wp_wasm_prop_call func1_terminates
theorem merge_sort_correct : MergeSortSpec := by
  intro env st dataPtr len hdHi hpristine hmargin
  sorry

end Wasm.SepLogic.MergeSort
