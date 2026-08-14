import Project.SwapElements.SmallStepSpec
import Project.SwapElementsOpt3.SmallStepEquivalence

namespace Project.SwapElementsOpt3.Equivalence

open Iris Iris.BI
open Wasm Wasm.SepLogic

def SwapOptEquiv : Prop :=
  ∀ (wasm : Store Unit) (ptr len i j : UInt32)
    (oldSpillPtr oldSpillLen : UInt32)
    (oldScratch oldA oldB : UInt64)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value),
    i < len → j < len →
    ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ wasm.mem.pages * 65536 →
    ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ wasm.mem.pages * 65536 →
    wasm.mem.pages ≤ 65536 →
    heapAgreesWithMem σ wasm.mem →
    heapAddressesInBounds σ wasm.mem →
    globalHeapAgrees globalσ wasm.globals →
    (∀ [WasmHeapGS Unit],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      pointsTo_u64 1048552 oldScratch ∗
      pointsTo_u32 1048568 oldSpillPtr ∗
      pointsTo_u32 1048572 oldSpillLen ∗
      pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 ((j <<< (3 % 32)) + ptr) oldB) →
    (∀ [WasmGlobalGS Unit],
      ([∗map] index ↦ value ∈ globalσ,
        globalPointsTo index value) ⊢
      globalPointsTo 0 (.i32 1048576)) →
    SmallStep.ObservationallyEquivOn
      (Project.SwapElements.SwapSepLogic.func4ConfigFromStore wasm ptr len i j)
      (SmallStepEquivalence.opt3ConfigFromStore wasm ptr len i j)
      (fun store =>
        (store.wasm.mem.read64 ((i <<< (3 % 32)) + ptr),
         store.wasm.mem.read64 ((j <<< (3 % 32)) + ptr)))

theorem swap_opt_equiv : SwapOptEquiv := by
  intro wasm ptr len i j oldSpillPtr oldSpillLen oldScratch oldA oldB
    σ globalσ hi hj hboundI hboundJ hpages hagree hinBounds hglobals
    hresources hglobalOwn
  have hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296 := by
    have := Nat.mul_le_mul_right 65536 hpages; omega
  have hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296 := by
    have := Nat.mul_le_mul_right 65536 hpages; omega
  have hresources' : ∀ [WasmHeapGS Unit],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 ((j <<< (3 % 32)) + ptr) oldB :=
    fun [WasmHeapGS Unit] => hresources.trans (by iintro ⟨_, _, _, HA, HB⟩; iframe)
  apply SmallStep.ObservationallyEquivOn.of_common_outcome (o := (oldB, oldA))
  · refine (Project.SwapElements.SmallStepSpec.swap_elements_distinct_terminates_correct
      wasm ptr len i j oldSpillPtr oldSpillLen oldScratch oldA oldB
      σ globalσ hi hj hroomI hroomJ hagree hinBounds hglobals
      hresources hglobalOwn).mono ?_
    rintro values store ⟨hv, hA, hB⟩
    exact ⟨hv, Prod.ext hA hB⟩
  · refine (SmallStepEquivalence.opt3_func0_distinct_store_terminatesWith
      wasm ptr len i j oldA oldB σ globalσ hi hj hboundI hboundJ hroomI hroomJ
      hagree hinBounds hglobals hresources').mono ?_
    rintro values store ⟨hv, hA, hB⟩
    exact ⟨hv, Prod.ext hA hB⟩

end Project.SwapElementsOpt3.Equivalence
