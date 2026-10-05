import CodeLib.Examples.UInt32Array
import CodeLib.RustStd.MemArray.SmallStep
import Interpreter.Wasm.Decoder.ProofEval
import Mathlib.Data.List.Sort

kernel_decoder
attribute [local irreducible] Wasm.Decoder.Wat.decode

/-!
# Quicksort

A handwritten Wasm implementation of Lomuto partition quicksort.
-/

namespace Wasm.Examples.Quicksort

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic
open Wasm.SmallStep
open Wasm.Examples.UInt32Array

def swapAt (base a b tmp : Nat) : Program :=
  loadAt base a ++ [.localSet tmp] ++
  storeAt base a (loadAt base b) ++
  storeAt base b [.localGet tmp]

-- partition: arr=local0, lo=local1, hi=local2
-- pivot=local3, i=local4, j=local5, hiMinusOne=local6, tmp=local7

def partitionInit : Program :=
  [.localGet 2, .const 1, .sub, .localSet 6] ++
  loadAt 0 6 ++ [.localSet 3] ++
  [.localGet 1, .localSet 4,
   .localGet 1, .localSet 5]

def partitionScanCondition : Program := lessLocal 5 6

def partitionScanStep : Program :=
  [.localGet 3] ++ loadAt 0 5 ++ [.ltU,
   .iff 0 0 [] (swapAt 0 4 5 7 ++ increment 4)] ++
  increment 5

def partitionPlacePivot : Program :=
  swapAt 0 4 6 7 ++ [.localGet 4]

def partitionBody : Program :=
  partitionInit ++
  whileDo partitionScanCondition partitionScanStep ++
  partitionPlacePivot ++
  [.ret]

def partitionFunction : Function :=
  { params := [.i32, .i32, .i32]
    locals := [.i32, .i32, .i32, .i32, .i32]
    results := [.i32]
    body := partitionBody }

-- quicksort: arr=local0, lo=local1, hi=local2, pivotIdx=local3

def quicksortBaseCheck : Program :=
  [.localGet 2, .localGet 1, .sub, .const 2, .ltU,
   .iff 0 0 [.ret] []]

def quicksortPartitionCall (partitionIndex : Nat) : Program :=
  [.localGet 0, .localGet 1, .localGet 2, .call partitionIndex, .localSet 3]

def quicksortLeftCall (quicksortIndex : Nat) : Program :=
  [.localGet 0, .localGet 1, .localGet 3, .call quicksortIndex]

def quicksortRightCall (quicksortIndex : Nat) : Program :=
  [.localGet 0, .localGet 3, .const 1, .add, .localGet 2, .call quicksortIndex]

def quicksortBody (partitionIndex quicksortIndex : Nat) : Program :=
  quicksortBaseCheck ++
  quicksortPartitionCall partitionIndex ++
  quicksortLeftCall quicksortIndex ++
  quicksortRightCall quicksortIndex ++
  [.ret]

def quicksortFunction (partitionIndex quicksortIndex : Nat) : Function :=
  { params := [.i32, .i32, .i32]
    locals := [.i32]
    body := quicksortBody partitionIndex quicksortIndex }

def quicksortModule : Module :=
  { funcs := [partitionFunction, quicksortFunction 0 1]
    memory := some { pagesMin := 1 } }

/-! ## Public specification -/

def Sorted (values : List UInt32) : Prop :=
  values.Pairwise (· ≤ ·)

def SortedPermutation (input output : List UInt32) : Prop :=
  Sorted output ∧ List.Perm input output

abbrev segment (values : List UInt32) (start stop : Nat) :=
  (values.drop start).take (stop - start)

def arrayByteRange (base : UInt32) (length : Nat) : Nat × Nat :=
  (base.toNat, base.toNat + 4 * length)

def ValidQuicksortLayout (arr : UInt32) (length : Nat) : Prop :=
  arr.toNat + 4 * length ≤ UInt32.size

def PartitionRange (input output : List UInt32) (lo hi pivotIndex : Nat) : Prop :=
  lo ≤ pivotIndex ∧ pivotIndex < hi ∧ hi ≤ input.length ∧
  output.length = input.length ∧
  output.take lo = input.take lo ∧
  output.drop hi = input.drop hi ∧
  List.Perm (segment input lo hi) (segment output lo hi) ∧
  (∀ x ∈ segment output lo pivotIndex, x ≤ output[pivotIndex]!) ∧
  (∀ x ∈ segment output (pivotIndex + 1) hi, x > output[pivotIndex]!)

def quicksortPre [WasmHeapGS α]
    (arr : UInt32) (values : List UInt32) (lo hi : Nat) : IProp (WasmHeapGF α) :=
  iprop% arrayAt 0 arr values ∗
    ⌜lo ≤ hi ∧ hi ≤ values.length ∧ ValidQuicksortLayout arr values.length⌝

def quicksortPost [WasmHeapGS α]
    (arr : UInt32) (input : List UInt32) (lo hi : Nat) : IProp (WasmHeapGF α) :=
  iprop% ∃ output : List UInt32,
    ⌜output.length = input.length ∧
     output.take lo = input.take lo ∧
     output.drop hi = input.drop hi ∧
     Sorted (segment output lo hi) ∧
     List.Perm (segment input lo hi) (segment output lo hi)⌝ ∗
    arrayAt 0 arr output

/-! ## Executable regressions -/

abbrev writeWordArray := Mem.writeWords32

abbrev readWordArray := Mem.readWords32

def quicksortExampleStore (arr : UInt32) (input : List UInt32) : Store Unit :=
  let initial := quicksortModule.initialStore (α := Unit)
  { initial with mem := writeWordArray initial.mem arr input }

def quicksortArguments (arr : UInt32) (length : Nat) (stack : List Value) : List Value :=
  .i32 (UInt32.ofNat length) :: .i32 0 :: .i32 arr :: stack

private def runQuicksortModule (m : Module) (fuel : Nat) (arr : UInt32)
    (input : List UInt32) : Option (List UInt32) :=
  match SmallStep.initConfig
      { module := m, host := {} } 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length []) with
  | .error _ => none
  | .ok config =>
      match (SmallStep.runSteps fuel config).result with
      | .success _ store =>
          some (readWordArray store.wasm.mem arr input.length)
      | _ => none

def runQuicksortExample (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) := runQuicksortModule quicksortModule fuel arr input

theorem quicksort_exec_empty :
    runQuicksortExample 100 0 [] = some [] := by decide +kernel

theorem quicksort_exec_singleton :
    runQuicksortExample 200 0 [42] = some [42] := by decide +kernel

theorem quicksort_exec_five :
    runQuicksortExample 15000 0 [5, 1, 4, 2, 3] = some [1, 2, 3, 4, 5] := by decide +kernel

theorem quicksort_exec_duplicates :
    runQuicksortExample 18000 0 [4, 1, 4, 2, 1, 3] = some [1, 1, 2, 3, 4, 4] := by decide +kernel

theorem quicksort_exec_sorted :
    runQuicksortExample 10000 0 [1, 2, 3, 4] = some [1, 2, 3, 4] := by decide +kernel

/-! ## TerminatesWith witnesses -/

private def configDefault : Config Unit :=
  { expr := .done []
    store :=
      { runtime := { instances := #[{ module := default, host := {} }], entry := ⟨0⟩ }
        wasm := { globals := default, mem := default, host := () } } }

private def quicksortExampleConfig (arr : UInt32) (input : List UInt32) : Config Unit :=
  (SmallStep.initConfig
      { module := quicksortModule, host := {} } 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length [])).toOption.getD configDefault

theorem quicksort_terminates_empty :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [])
        (fun _ store => readWordArray store.wasm.mem 0 0 = []) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 100)
      (fun _ store => readWordArray store.wasm.mem 0 0 == [])
  · decide +kernel
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

theorem quicksort_terminates_singleton :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [42])
        (fun _ store => readWordArray store.wasm.mem 0 1 = [42]) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 200)
      (fun _ store => readWordArray store.wasm.mem 0 1 == [42])
  · decide +kernel
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

theorem quicksort_terminates_five :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [5, 1, 4, 2, 3])
        (fun _ store => readWordArray store.wasm.mem 0 5 = [1, 2, 3, 4, 5]) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 15000)
      (fun _ store => readWordArray store.wasm.mem 0 5 == [1, 2, 3, 4, 5])
  · decide +kernel
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

theorem quicksort_terminates_duplicates :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [4, 1, 4, 2, 1, 3])
        (fun _ store => readWordArray store.wasm.mem 0 6 = [1, 1, 2, 3, 4, 4]) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 18000)
      (fun _ store => readWordArray store.wasm.mem 0 6 == [1, 1, 2, 3, 4, 4])
  · decide +kernel
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

theorem quicksort_terminates_sorted :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [1, 2, 3, 4])
        (fun _ store => readWordArray store.wasm.mem 0 4 = [1, 2, 3, 4]) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 10000)
      (fun _ store => readWordArray store.wasm.mem 0 4 == [1, 2, 3, 4])
  · decide +kernel
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

/-! ## Differential check -/

def runQuicksortLegacy (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) :=
  match Wasm.run fuel quicksortModule 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length []) with
  | .Success _ store => some (readWordArray store.mem arr input.length)
  | _ => none

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem quicksort_small_large_agree :
    runQuicksortExample 15000 0 [5, 1, 4, 2, 3] =
    runQuicksortLegacy 5000 0 [5, 1, 4, 2, 3] := by
  have hsmall : runQuicksortLegacy 64 0 [5, 1, 4, 2, 3] =
      some [1, 2, 3, 4, 5] := by cbv
  rw [quicksort_exec_five]
  unfold runQuicksortLegacy at hsmall ⊢
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hsmall ⊢
  have hne : Wasm.run 64 quicksortModule 1
      (quicksortExampleStore 0 [5, 1, 4, 2, 3])
      (quicksortArguments 0 5 []) ≠ .OutOfFuel := by
    intro h
    simp [h] at hsmall
  rw [Wasm.run_fuel_mono (show 64 ≤ 5000 by decide) hne]
  exact hsmall.symm

/-! ## Mutation tests -/

private def partitionFunctionMutated1 : Function :=
  { params := [.i32, .i32, .i32]
    locals := [.i32, .i32, .i32, .i32, .i32]
    results := [.i32]
    body :=
      partitionInit ++
      whileDo partitionScanCondition
        ([.localGet 3] ++ loadAt 0 5 ++ [.geU,
          .iff 0 0 [] (swapAt 0 4 5 7 ++ increment 4)] ++
         increment 5) ++
      partitionPlacePivot ++
      [.ret] }

private def quicksortModuleMutated1 : Module :=
  { funcs := [partitionFunctionMutated1, quicksortFunction 0 1]
    memory := some { pagesMin := 1 } }

def runQuicksortMutated1 (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) :=
  match SmallStep.initConfig
      { module := quicksortModuleMutated1, host := {} } 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length []) with
  | .error _ => none
  | .ok config =>
      match (SmallStep.runSteps fuel config).result with
      | .success _ store => some (readWordArray store.wasm.mem arr input.length)
      | _ => none

theorem quicksort_mutation_comparison :
    runQuicksortMutated1 15000 0 [5, 1, 4, 2, 3] ≠ some [1, 2, 3, 4, 5] := by decide +kernel

private def partitionFunctionMutated2 : Function :=
  { params := [.i32, .i32, .i32]
    locals := [.i32, .i32, .i32, .i32, .i32]
    results := [.i32]
    body :=
      partitionInit ++
      whileDo partitionScanCondition partitionScanStep ++
      swapAt 0 5 6 7 ++ [.localGet 4] ++
      [.ret] }

private def quicksortModuleMutated2 : Module :=
  { funcs := [partitionFunctionMutated2, quicksortFunction 0 1]
    memory := some { pagesMin := 1 } }

def runQuicksortMutated2 (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) :=
  match SmallStep.initConfig
      { module := quicksortModuleMutated2, host := {} } 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length []) with
  | .error _ => none
  | .ok config =>
      match (SmallStep.runSteps fuel config).result with
      | .success _ store => some (readWordArray store.wasm.mem arr input.length)
      | _ => none

theorem quicksort_mutation_index :
    runQuicksortMutated2 15000 0 [5, 1, 4, 2, 3] ≠ some [1, 2, 3, 4, 5] := by decide +kernel

private def quicksortFunctionMutated3 : Function :=
  { params := [.i32, .i32, .i32]
    locals := [.i32]
    body :=
      [.localGet 2, .localGet 1, .sub, .const 3, .ltU,
       .iff 0 0 [.ret] []] ++
      quicksortPartitionCall 0 ++
      quicksortLeftCall 1 ++
      quicksortRightCall 1 ++
      [.ret] }

private def quicksortModuleMutated3 : Module :=
  { funcs := [partitionFunction, quicksortFunctionMutated3]
    memory := some { pagesMin := 1 } }

def runQuicksortMutated3 (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) :=
  match SmallStep.initConfig
      { module := quicksortModuleMutated3, host := {} } 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length []) with
  | .error _ => none
  | .ok config =>
      match (SmallStep.runSteps fuel config).result with
      | .success _ store => some (readWordArray store.wasm.mem arr input.length)
      | _ => none

theorem quicksort_mutation_bound :
    runQuicksortMutated3 15000 0 [5, 1, 4, 2, 3] ≠ some [1, 2, 3, 4, 5] := by decide +kernel

private def partitionFunctionMutated4 : Function :=
  { params := [.i32, .i32, .i32]
    locals := [.i32, .i32, .i32, .i32, .i32]
    results := [.i32]
    body :=
      partitionInit ++
      whileDo partitionScanCondition
        ([.localGet 3] ++ loadAt 0 5 ++ [.ltU,
          .iff 0 0 [] (storeAt 0 4 [.const 0] ++ increment 4)] ++
         increment 5) ++
      partitionPlacePivot ++
      [.ret] }

private def quicksortModuleMutated4 : Module :=
  { funcs := [partitionFunctionMutated4, quicksortFunction 0 1]
    memory := some { pagesMin := 1 } }

def runQuicksortMutated4 (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) :=
  match SmallStep.initConfig
      { module := quicksortModuleMutated4, host := {} } 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length []) with
  | .error _ => none
  | .ok config =>
      match (SmallStep.runSteps fuel config).result with
      | .success _ store => some (readWordArray store.wasm.mem arr input.length)
      | _ => none

theorem quicksort_mutation_store :
    runQuicksortMutated4 15000 0 [5, 1, 4, 2, 3] ≠ some [1, 2, 3, 4, 5] := by decide +kernel

/-! ## Oracle agreement -/

theorem quicksort_oracle_empty :
    runQuicksortExample 100 0 [] =
    some (List.mergeSort []) := by decide +kernel

theorem quicksort_oracle_singleton :
    runQuicksortExample 200 0 [42] =
    some (List.mergeSort [42]) := by decide +kernel

theorem quicksort_oracle_five :
    runQuicksortExample 15000 0 [5, 1, 4, 2, 3] =
    some (List.mergeSort [5, 1, 4, 2, 3]) := by
  rw [quicksort_exec_five]
  cbv

theorem quicksort_oracle_duplicates :
    runQuicksortExample 18000 0 [4, 1, 4, 2, 1, 3] =
    some (List.mergeSort [4, 1, 4, 2, 1, 3]) := by
  rw [quicksort_exec_duplicates]
  cbv

theorem quicksort_oracle_sorted :
    runQuicksortExample 10000 0 [1, 2, 3, 4] =
    some (List.mergeSort [1, 2, 3, 4]) := by
  rw [quicksort_exec_sorted]
  cbv

/-! ## Adequacy infrastructure -/

def quicksortHeap (arr : UInt32) (input : List UInt32) :
    WasmHeapMap (Option UInt8) :=
  heap32Aux ∅ arr input

def quicksortConfig (arr : UInt32) (input : List UInt32) : Config Unit :=
  let initial := quicksortModule.initialStore (α := Unit)
  { expr := .running
      ⟨⟨[], [], [.i32 (UInt32.ofNat input.length), .i32 0, .i32 arr]⟩,
        [.call 1], 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := quicksortModule, host := {} }], entry := ⟨0⟩ }
        wasm := { initial with mem := writeWordArray initial.mem arr input } } }

theorem quicksortHeap_agrees (arr : UInt32) (input : List UInt32)
    (hfit : arr.toNat + 4 * input.length ≤ UInt32.size) :
    heapAgreesWithMem (quicksortHeap arr input)
      (storeResolve (quicksortConfig arr input).store) := by
  unfold quicksortHeap
  have h := heap32Aux_agrees ∅ (quicksortModule.initialStore (α := Unit)).mem
    arr input
    (by intro key value hget; simp [get?_empty] at hget)
    hfit
  have heq := singleMemoryResolve_eq_storeResolve (quicksortConfig arr input).store
    (writeWordArray (quicksortModule.initialStore (α := Unit)).mem arr input) rfl
    (show (quicksortModule.initialStore (α := Unit)).extraMems = [] from by decide +kernel)
  rw [heq] at h; exact h

theorem quicksortHeap_inBounds (arr : UInt32) (input : List UInt32)
    (hfit : arr.toNat + 4 * input.length ≤ UInt32.size)
    (hmem : arr.toNat + 4 * input.length ≤ 65536) :
    heapAddressesInBounds (quicksortHeap arr input)
      (storeResolve (quicksortConfig arr input).store) := by
  unfold quicksortHeap
  have h := heap32Aux_inBounds ∅ (quicksortModule.initialStore (α := Unit)).mem
    arr input
    (by intro key hget; simp [get?_empty] at hget)
    hfit
    (by have hpages : (quicksortModule.initialStore (α := Unit)).mem.pages = 1 := by decide
        simp only [hpages]; exact hmem)
  have heq := singleMemoryResolve_eq_storeResolve (quicksortConfig arr input).store
    (writeWordArray (quicksortModule.initialStore (α := Unit)).mem arr input) rfl
    (show (quicksortModule.initialStore (α := Unit)).extraMems = [] from by decide +kernel)
  rw [heq] at h; exact h

theorem quicksortHeap_pointsTo [WasmHeapGS α]
    (arr : UInt32) (input : List UInt32)
    (hfit : arr.toNat + 4 * input.length < UInt32.size) :
    ([∗map] address ↦ value ∈ quicksortHeap arr input,
        pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap) address (DFrac.own 1) value) ⊢
      arrayAt 0 arr input := by
  unfold quicksortHeap
  iintro Hheap
  ihave ⟨Harray, _Hemp⟩ := heap32Aux_pointsTo ∅ arr input
    (fun a b hget => by simp [get?_empty] at hget) hfit $$ Hheap
  iexact Harray

/-! ## WAT decoder agreement -/

private def quicksortWat : String := include_str "quicksort.wat"

private def moduleOfDecoded (result : Except String Module) : Module :=
  match result with
  | .ok m => m
  | .error _ => default

private def quicksortModuleDecoded : Module :=
  moduleOfDecoded (Wasm.Decoder.Wat.decode quicksortWat)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem quicksort_decode_eq :
    Wasm.Decoder.Wat.decode quicksortWat = .ok quicksortModule := by cbv

def runQuicksortDecoded (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) := runQuicksortModule quicksortModuleDecoded fuel arr input

set_option maxRecDepth 100000 in
private theorem quicksortModuleDecoded_eq : quicksortModuleDecoded = quicksortModule :=
  congrArg moduleOfDecoded quicksort_decode_eq

set_option maxRecDepth 100000 in
private theorem runQuicksortDecoded_eq (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    runQuicksortDecoded fuel arr input = runQuicksortExample fuel arr input :=
  congrArg (fun m => runQuicksortModule m fuel arr input) quicksortModuleDecoded_eq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem quicksort_decoded_agrees :
    runQuicksortDecoded 15000 0 [5, 1, 4, 2, 3] =
      runQuicksortExample 15000 0 [5, 1, 4, 2, 3] ∧
    runQuicksortDecoded 15000 0 [] = runQuicksortExample 15000 0 [] ∧
    runQuicksortDecoded 15000 0 [7] = runQuicksortExample 15000 0 [7] ∧
    runQuicksortDecoded 15000 0 [4, 3, 2, 1] =
      runQuicksortExample 15000 0 [4, 3, 2, 1] ∧
    runQuicksortDecoded 20 0 [3, 2, 1] =
      runQuicksortExample 20 0 [3, 2, 1] := by
  exact ⟨runQuicksortDecoded_eq .., runQuicksortDecoded_eq ..,
    runQuicksortDecoded_eq .., runQuicksortDecoded_eq .., runQuicksortDecoded_eq ..⟩

end Wasm.Examples.Quicksort
