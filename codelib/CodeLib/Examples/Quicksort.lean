import CodeLib.SepLogic.SmallStepAdequacy
import Mathlib.Data.List.Sort

/-!
# Quicksort

A handwritten Wasm implementation of Lomuto partition quicksort.
-/

namespace Wasm.Examples.Quicksort

open Wasm
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open Wasm.SmallStep

def increment (index : Nat) : Program :=
  [.localGet index, .const 1, .add, .localSet index]

def address (base index : Nat) : Program :=
  [.localGet base, .localGet index, .const 4, .mul, .add]

def loadAt (base index : Nat) : Program :=
  address base index ++ [.load32 0]

def storeAt (base index : Nat) (value : Program) : Program :=
  address base index ++ value ++ [.store32 0]

def whileLoopCode (condition body : Program) : Program :=
  condition ++ [.eqz, .br_if 1] ++ body ++ [.br 0]

def whileDo (condition body : Program) : Program :=
  [.block 0 0 [.loop 0 0 (whileLoopCode condition body)]]

def lessLocal (lhs rhs : Nat) : Program :=
  [.localGet lhs, .localGet rhs, .ltU]

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

def segment (values : List UInt32) (start stop : Nat) : List UInt32 :=
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

def quicksortPre [WasmHeapGS]
    (arr : UInt32) (values : List UInt32) (lo hi : Nat) : IProp WasmHeapGF :=
  iprop% arrayAt arr values ∗
    ⌜lo ≤ hi ∧ hi ≤ values.length ∧ ValidQuicksortLayout arr values.length⌝

def quicksortPost [WasmHeapGS]
    (arr : UInt32) (input : List UInt32) (lo hi : Nat) : IProp WasmHeapGF :=
  iprop% ∃ output : List UInt32,
    ⌜output.length = input.length ∧
     output.take lo = input.take lo ∧
     output.drop hi = input.drop hi ∧
     Sorted (segment output lo hi) ∧
     List.Perm (segment input lo hi) (segment output lo hi)⌝ ∗
    arrayAt arr output

/-! ## Executable regressions -/

def writeWordArray : Mem → UInt32 → List UInt32 → Mem
  | memory, _, [] => memory
  | memory, address, value :: values =>
      writeWordArray (memory.write32 address value) (address + 4) values

def readWordArray : Mem → UInt32 → Nat → List UInt32
  | _, _, 0 => []
  | memory, address, count + 1 =>
      memory.read32 address ::
        readWordArray memory (address + 4) count

def quicksortExampleStore (arr : UInt32) (input : List UInt32) : Store Unit :=
  let initial := quicksortModule.initialStore (α := Unit)
  { initial with mem := writeWordArray initial.mem arr input }

def quicksortArguments (arr : UInt32) (length : Nat) (stack : List Value) : List Value :=
  .i32 (UInt32.ofNat length) :: .i32 0 :: .i32 arr :: stack

def runQuicksortExample (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) :=
  match SmallStep.initConfig
      { module := quicksortModule, host := {} } 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length []) with
  | .error _ => none
  | .ok config =>
      match (SmallStep.runSteps fuel config).result with
      | .success _ store =>
          some (readWordArray store.wasm.mem arr input.length)
      | _ => none

theorem quicksort_exec_empty :
    runQuicksortExample 100 0 [] = some [] := by native_decide

theorem quicksort_exec_singleton :
    runQuicksortExample 200 0 [42] = some [42] := by native_decide

theorem quicksort_exec_five :
    runQuicksortExample 15000 0 [5, 1, 4, 2, 3] = some [1, 2, 3, 4, 5] := by
  native_decide

theorem quicksort_exec_duplicates :
    runQuicksortExample 18000 0 [4, 1, 4, 2, 1, 3] = some [1, 1, 2, 3, 4, 4] := by
  native_decide

theorem quicksort_exec_sorted :
    runQuicksortExample 10000 0 [1, 2, 3, 4] = some [1, 2, 3, 4] := by native_decide

/-! ## TerminatesWith witnesses -/

private def configDefault : Config Unit :=
  { expr := .done []
    store :=
      { runtime := { module := default, host := {} }
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
  · native_decide
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

theorem quicksort_terminates_singleton :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [42])
        (fun _ store => readWordArray store.wasm.mem 0 1 = [42]) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 200)
      (fun _ store => readWordArray store.wasm.mem 0 1 == [42])
  · native_decide
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

theorem quicksort_terminates_five :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [5, 1, 4, 2, 3])
        (fun _ store => readWordArray store.wasm.mem 0 5 = [1, 2, 3, 4, 5]) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 15000)
      (fun _ store => readWordArray store.wasm.mem 0 5 == [1, 2, 3, 4, 5])
  · native_decide
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

theorem quicksort_terminates_duplicates :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [4, 1, 4, 2, 1, 3])
        (fun _ store => readWordArray store.wasm.mem 0 6 = [1, 1, 2, 3, 4, 4]) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 18000)
      (fun _ store => readWordArray store.wasm.mem 0 6 == [1, 1, 2, 3, 4, 4])
  · native_decide
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

theorem quicksort_terminates_sorted :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [1, 2, 3, 4])
        (fun _ store => readWordArray store.wasm.mem 0 4 = [1, 2, 3, 4]) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 10000)
      (fun _ store => readWordArray store.wasm.mem 0 4 == [1, 2, 3, 4])
  · native_decide
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

/-! ## Differential check -/

-- Wasm.run (big-step, Interpreter.Wasm.Semantics) is imported transitively
-- through SmallStep.lean. Result.Success carries the final store.
def runQuicksortLegacy (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) :=
  match Wasm.run fuel quicksortModule 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length []) with
  | .Success _ store => some (readWordArray store.mem arr input.length)
  | _ => none

theorem quicksort_small_large_agree :
    runQuicksortExample 15000 0 [5, 1, 4, 2, 3] =
    runQuicksortLegacy 5000 0 [5, 1, 4, 2, 3] := by native_decide

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
    runQuicksortMutated1 15000 0 [5, 1, 4, 2, 3] ≠ some [1, 2, 3, 4, 5] := by
  native_decide

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
    runQuicksortMutated2 15000 0 [5, 1, 4, 2, 3] ≠ some [1, 2, 3, 4, 5] := by
  native_decide

/-! ## Oracle agreement -/

theorem quicksort_oracle_empty :
    runQuicksortExample 100 0 [] =
    some (List.mergeSort []) := by native_decide

theorem quicksort_oracle_singleton :
    runQuicksortExample 200 0 [42] =
    some (List.mergeSort [42]) := by native_decide

theorem quicksort_oracle_five :
    runQuicksortExample 15000 0 [5, 1, 4, 2, 3] =
    some (List.mergeSort [5, 1, 4, 2, 3]) := by native_decide

theorem quicksort_oracle_duplicates :
    runQuicksortExample 18000 0 [4, 1, 4, 2, 1, 3] =
    some (List.mergeSort [4, 1, 4, 2, 1, 3]) := by native_decide

theorem quicksort_oracle_sorted :
    runQuicksortExample 10000 0 [1, 2, 3, 4] =
    some (List.mergeSort [1, 2, 3, 4]) := by native_decide

end Wasm.Examples.Quicksort
