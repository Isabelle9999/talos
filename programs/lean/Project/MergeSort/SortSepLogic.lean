import Project.MergeSort.MergeFull
import Project.MergeSort.Spec
import CodeLib.SepLogic.Adequacy

namespace Wasm.SepLogic.MergeSort

open Wasm Project.MergeSort Project.MergeSort.Spec Project.MergeSort.Framing

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
private theorem func15_terminates
    (st : Store Unit) (ptr v1 v2 v3 : UInt32)
    (hb : ptr.toNat + 8 ≤ st.mem.pages * 65536) :
    TerminatesWith {} «module» 15 st
      [.i32 v3, .i32 v2, .i32 v1, .i32 ptr]
      (fun st' _ => st'.mem.read32 ptr = v1 ∧ st'.mem.read32 (ptr + 4) = v2) := by
  have hb4 : ¬(ptr.toNat + (4 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
    have : (4 : UInt32).toNat = 4 := rfl; omega
  have hb0 : ¬(ptr.toNat + (0 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
    have : (0 : UInt32).toNat = 0 := rfl; omega
  have hdisj : ptr.toNat + 4 ≤ (ptr + 4 : UInt32).toNat
      ∨ (ptr + 4 : UInt32).toNat + 4 ≤ ptr.toNat := by
    simp only [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]
    omega
  have hz : ptr + (0 : UInt32) = ptr := UInt32.add_zero ptr
  apply TerminatesWith.of_run 1 []
      { st with mem := (st.mem.write32 (ptr + 4) v2).write32 ptr v1 }
  · rw [run_eq (show «module».imports[15]? = none from rfl)]
    conv_lhs =>
      simp only [
        show «module».funcs[15 - «module».imports.length]? = some func15Def from rfl,
        func15Def, func15,
        Function.numParams, Function.toLocals, List.map,
        List.take, List.reverse, List.reverseAux, List.drop,
        List.length_cons, List.length_nil,
        exec, execOne.eq_def,
        Locals.get,
        show (0 : Nat) < 4 from by omega,
        show (1 : Nat) < 4 from by omega,
        show (2 : Nat) < 4 from by omega,
        List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
        Mem.write32_pages,
        if_neg hb4, if_neg hb0, hz,
        ite_true, ite_false,
        List.nil_append]
  · constructor
    · exact Mem.read32_write32_same _ _ _
    · rw [Mem.read32_write32_of_disjoint _ _ _ _ hdisj]
      exact Mem.read32_write32_same _ _ _

-- func3: recursive merge sort; strong induction on src_n.toNat
-- allocator calls (func5, func7) deferred as sorry
private theorem func3_terminates
    (st : Store Unit) (src_ptr src_n dst_ptr dst_n : UInt32) :
    TerminatesWith {} «module» 3 st
      [.i32 dst_n, .i32 dst_ptr, .i32 src_n, .i32 src_ptr]
      (fun _ _ => True) := by
  -- thread src_n.toNat into a suffices so strong_induction_on can quantify over it
  suffices key : ∀ (n : Nat) (st : Store Unit) (src_ptr src_n dst_ptr dst_n : UInt32),
      src_n.toNat = n →
      TerminatesWith {} «module» 3 st
        [.i32 dst_n, .i32 dst_ptr, .i32 src_n, .i32 src_ptr]
        (fun _ _ => True) from
    key _ st src_ptr src_n dst_ptr dst_n rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro st src_ptr src_n dst_ptr dst_n hn
    by_cases hbase : src_n.toNat ≤ 1
    · -- base: leU fires br_if, block exits without calling func5/func3/func6
      sorry -- straight-line: preamble + block exits via leU + br_if
    · -- recursive: mid = src_n >>> 1
      -- left-sort size  (src_n >>> 1).toNat  < n  → IH applies
      -- right-sort size (src_n - src_n>>>1).toNat < n → IH applies
      -- merge via func6_terminates; func5/func7 allocator deferred per spec
      sorry -- allocator verification deferred per spec (func5, func7)

-- func1: sort with pre-allocated scratch; delegates to func3
-- allocator calls (func2, func4) deferred
private theorem func1_terminates
    (st : Store Unit) (data_ptr len : UInt32) :
    TerminatesWith {} «module» 1 st
      [.i32 len, .i32 data_ptr]
      (fun _ _ => True) := by
  sorry -- allocator verification deferred (func2, func4)

-- content correctness deferred: requires Pairwise/Perm derivation from func3 correctness
-- env bridge: «module».imports = [], so run is env-independent
-- func33: preamble → wp_wasm_prop_call func15_terminates → wp_wasm_prop_call func1_terminates
theorem merge_sort_correct : MergeSortSpec := by
  intro env st dataPtr len hdHi hpristine hmargin
  sorry

end Wasm.SepLogic.MergeSort
