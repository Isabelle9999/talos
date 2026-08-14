import CodeLib.SepLogic.SmallStepAdequacy

namespace Wasm.SmallStep

open Iris Iris.BI Iris.ProgramLogic OFE COFE Iris.Algebra
  Language.Notation Std Wasm.SepLogic

def sharedMemFn : Function where
  params  := [.i32]
  locals  := []
  results := []
  body    := [.const 0, .localGet 0, .store8 0, .ret]

def readBackFn : Function where
  params  := [.i32]
  locals  := []
  results := [.i32]
  body    := [.localGet 0, .call 0, .const 0, .load8U 0, .ret]

def sharedMemModule : Module where
  imports := []
  funcs   := [sharedMemFn, readBackFn]

def sharedMemRuntime : RuntimeEnv Unit :=
  { instances := #[{ module := sharedMemModule, host := HostEnv.empty }]
    entry     := ⟨0⟩ }

def sharedMemConfig (v : UInt8) : Config Unit :=
  { expr := .running
      { locals          := { params := [.i32 v.toUInt32], locals := [], values := [] }
        code            := [.localGet 0, .call 0, .const 0, .load8U 0, .ret]
        resultArity     := 1
        callerRemainder := []
        control         := []
        calls           := [] }
    store :=
      { runtime := sharedMemRuntime
        wasm    :=
          { globals := { globals := [] }
            mem     := Mem.empty 1
            host    := () } } }

def sharedMemHeap : WasmHeapMap (Option UInt8) :=
  insert ∅ (⟨0, 0⟩ : MemoryKey) (some (0 : UInt8))

@[simp] private theorem RuntimeEnv.currentModule_sharedMem :
    sharedMemRuntime.currentModule = sharedMemModule := rfl

@[simp] private theorem RuntimeEnv.entry_sharedMem :
    sharedMemRuntime.entry = ⟨0⟩ := rfl

private theorem sharedMemHeap_agrees (v : UInt8) :
    heapAgreesWithMem sharedMemHeap (storeResolve (sharedMemConfig v).store) := by
  intro key value hget
  simp only [sharedMemHeap] at hget
  by_cases h : key = ⟨0, 0⟩
  · subst h
    simp only [get?_insert_eq rfl, Option.some.injEq] at hget
    subst hget
    exact ⟨Mem.empty 1,
      by simp [storeResolve, sharedMemConfig, sharedMemRuntime],
      by simp [Mem.read8, Mem.empty]⟩
  · rw [get?_insert_ne (Ne.symm h), get?_empty] at hget
    contradiction

private theorem sharedMemHeap_inBounds (v : UInt8) :
    heapAddressesInBounds sharedMemHeap (storeResolve (sharedMemConfig v).store) := by
  intro key hne
  simp only [sharedMemHeap] at hne
  by_cases h : key = ⟨0, 0⟩
  · subst h
    refine ⟨Mem.empty 1, by simp [storeResolve, sharedMemConfig, sharedMemRuntime], ?_⟩
    simp [Mem.empty]
  · rw [get?_insert_ne (Ne.symm h), get?_empty] at hne
    simp at hne

private theorem sharedMemHeap_pointsTo [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ sharedMemHeap,
      pointsTo (GF := WasmHeapGF.{0} α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo (GF := WasmHeapGF.{0} α) (H := WasmHeapMap)
        ⟨0, 0⟩ (DFrac.own 1) (some 0) := by
  unfold sharedMemHeap
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : MemoryKey))).to_eq]
  rw [BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]

theorem sharedMem_partiallyMeets (v : UInt8) :
    PartiallyMeets (sharedMemConfig v)
      (fun values _ => values = [.i32 v.toUInt32]) := by
  apply wasm_smallStep_heap_runtime_instance_partiallyMeets
      (α := Unit) (σ := sharedMemHeap)
      (φ := fun values => values = [.i32 v.toUInt32])
  · exact sharedMemHeap_agrees v
  · exact sharedMemHeap_inBounds v
  · simp only [sharedMemConfig]; decide
  · intro gs
    simp only [sharedMemConfig, RuntimeEnv.currentModule_sharedMem,
               RuntimeEnv.entry_sharedMem]
    iintro ⟨Hpoints, Hruntime⟩
    ihave Hpt := sharedMemHeap_pointsTo $$ Hpoints
    iapply wp_localGet rfl
    inext
    iapply wp_call sharedMemModule 0 sharedMemFn
        (by simp [sharedMemModule]) rfl ⟨0⟩
        $$ Hruntime
    inext
    iintro Hruntime'
    simp only [sharedMemFn, Function.toLocals, Function.numParams, List.map_nil]
    iapply wp_const
    inext
    iapply wp_localGet rfl
    inext
    ihave HptLater :
        ▷ pointsTo (GF := WasmHeapGF.{0} Unit) (H := WasmHeapMap)
          ⟨0, 0 + 0⟩ (DFrac.own 1) (some 0) $$ [Hpt]
    · inext
      rw [UInt32.add_zero]
      iexact Hpt
    iapply wp_store8 (0 : UInt8) rfl $$ HptLater
    inext
    iintro Hpt'
    iapply wp_returnFromCallExplicit $$ Hruntime'
    inext
    iapply wp_const
    inext
    ihave HptLater2 :
        ▷ pointsTo (GF := WasmHeapGF.{0} Unit) (H := WasmHeapMap)
          ⟨0, 0 + 0⟩ (DFrac.own 1) (some v.toUInt32.toUInt8) $$ [Hpt']
    · inext
      iexact Hpt'
    iapply wp_load8U v.toUInt32.toUInt8 rfl $$ HptLater2
    inext
    iintro _Hpt_back
    iapply wp_returnFromFunction
    inext
    iapply wp_value'
    ipureintro
    simp [List.take]

theorem sharedMem_terminates :
    TerminatesWith (sharedMemConfig 0) (fun _ _ => True) :=
  runSteps_checked_terminates (fuel := 100)
    (fun _ _ => true)
    (by native_decide)
    (fun _ _ _ => trivial)

end Wasm.SmallStep
