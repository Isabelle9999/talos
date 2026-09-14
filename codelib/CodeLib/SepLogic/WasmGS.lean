import CodeLib.SepLogic.SmallStepState

/-!
# Abstract ghost-functor instance context for the Wasm small-step layer

Mirrors the HeapLang pattern in iris-lean:
- `WasmGpreS` collects pre-allocation ElemG obligations (for adequacy).
- `WasmGS` is parameterised over any `BundledGFunctors` and carries the
  same ghost-state components as `WasmSmallStepGS`, each decomposed to its
  raw `ElemG` / `GhostMapG` obligation over the abstract `GF`.
- `instWasmGS_of_WasmSmallStepGS` bridges the concrete world: every existing
  user of `[WasmSmallStepGS hlc α]` automatically gets `[WasmGS hlc (WasmHeapGF α) α]`
  without any change to their code.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Std
open Wasm.SepLogic

/-! ## Pre-allocation obligations (for adequacy) -/

/-- Ghost-functor pre-S class for Wasm, mirroring `HeapLangGpreS`. -/
class WasmGpreS (hlc : outParam HasLC) (GF : BundledGFunctors) (α : outParam Type)
    extends InvGpreS GF where
  heap_pre : genHeapPreS MemoryKey (Option UInt8) GF WasmHeapMap

attribute [reducible, instance] WasmGpreS.heap_pre

/-- `WasmHeapGF α` satisfies `WasmGpreS` without any existing allocation.
Mirrors `instHeapLangGS_HeapLangS` in iris-lean. -/
instance instWasmGpreS_WasmHeapGF : WasmGpreS HasLC.hasLC (WasmHeapGF α) α where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    exists 3
  heap_pre := inferInstance

/-! ## Abstract ghost-state class -/

/-- Abstract ghost-state context for the Wasm small-step layer, parameterised
over an arbitrary `BundledGFunctors`.  `invGS` is intentionally not a global
instance to avoid diamonds with `IrisGS_gen`. -/
class WasmGS (hlc : outParam HasLC) (GF : BundledGFunctors) (α : outParam Type) where
  -- not an instance on purpose to avoid diamonds with IrisGS_gen
  [invGS : InvGS_gen hlc GF]
  heap            : genHeapGS MemoryKey (Option UInt8) GF WasmHeapMap
  heapFrontierElem : ElemG GF
      (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat)))))
  heapFrontierName : GName
  memoryPagesElem : ElemG GF MonoNatRF
  memoryPagesName : GName
  globalGS        : GhostMapG GF GlobalKey Value WasmGlobalMap
  globalName      : GName
  dataSegmentGS   : GhostMapG GF DataSegmentKey (Option (List UInt8)) WasmDataSegmentMap
  dataSegmentName : GName
  tableGS         : GhostMapG GF TableKey TableInst WasmTableMap
  tableName       : GName
  elementSegmentGS : GhostMapG GF ElementSegmentKey (Option (List (Option Nat)))
      WasmElementSegmentMap
  elementSegmentName : GName
  exceptionGS     : GhostMapG GF Nat (Nat × List Value) WasmExceptionMap
  exceptionName   : GName
  runtimeModuleGS : GhostMapG GF Nat Module WasmRuntimeModuleMap
  runtimeName     : GName
  tagTableElem    : ElemG GF (constOF (Agree (DiscreteO (List Nat))))
  tagTableName    : GName
  hostEnvGS       : GhostMapG GF Nat (HostEnv α) WasmHostEnvMap
  hostEnvName     : GName
  hostStateElem   : ElemG GF
      (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO α)))))
  hostStateName   : GName
  instanceElem    : ElemG GF
      (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat)))))
  instanceName    : GName
  runtimeInstancesElem : ElemG GF
      (constOF (Agree (DiscreteO (Array (ModuleInstance α)))))
  runtimeInstancesName : GName

attribute [reducible, instance] WasmGS.heap
attribute [reducible, instance] WasmGS.heapFrontierElem
attribute [reducible, instance] WasmGS.memoryPagesElem
attribute [reducible, instance] WasmGS.globalGS
attribute [reducible, instance] WasmGS.dataSegmentGS
attribute [reducible, instance] WasmGS.tableGS
attribute [reducible, instance] WasmGS.elementSegmentGS
attribute [reducible, instance] WasmGS.exceptionGS
attribute [reducible, instance] WasmGS.runtimeModuleGS
attribute [reducible, instance] WasmGS.tagTableElem
attribute [reducible, instance] WasmGS.hostEnvGS
attribute [reducible, instance] WasmGS.hostStateElem
attribute [reducible, instance] WasmGS.instanceElem
attribute [reducible, instance] WasmGS.runtimeInstancesElem

/-! ## Concrete-bundle instance -/

/-- Every `WasmSmallStepGS` is a `WasmGS` for `GF = WasmHeapGF α`.
Existing code that uses `[WasmSmallStepGS hlc α]` gains
`[WasmGS hlc (WasmHeapGF α) α]` automatically. -/
instance instWasmGS_of_WasmSmallStepGS [gs : WasmSmallStepGS hlc α] :
    WasmGS hlc (WasmHeapGF α) α where
  invGS               := gs.toInvGS_gen
  heap                := inferInstance
  heapFrontierElem    := gs.heapDomain.heapFrontierElem
  heapFrontierName    := gs.heapDomain.heapFrontierName
  memoryPagesElem     := gs.memoryPages.memoryPagesElem
  memoryPagesName     := gs.memoryPages.memoryPagesName
  globalGS            := gs.global.toGhostMapG
  globalName          := gs.global.globalName
  dataSegmentGS       := gs.dataSegment.toGhostMapG
  dataSegmentName     := gs.dataSegment.dataSegmentName
  tableGS             := gs.table.toGhostMapG
  tableName           := gs.table.tableName
  elementSegmentGS    := gs.elementSegment.toGhostMapG
  elementSegmentName  := gs.elementSegment.elementSegmentName
  exceptionGS         := gs.exception.toGhostMapG
  exceptionName       := gs.exception.exceptionName
  runtimeModuleGS     := gs.runtime.toGhostMapG
  runtimeName         := gs.runtime.runtimeName
  tagTableElem        := gs.tagTable.tagTableElem
  tagTableName        := gs.tagTable.tagTableName
  hostEnvGS           := gs.hostEnv.toGhostMapG
  hostEnvName         := gs.hostEnv.hostEnvName
  hostStateElem       := gs.hostState.hostStateElem
  hostStateName       := gs.hostState.hostStateName
  instanceElem        := gs.instanceGS.instanceElem
  instanceName        := gs.instanceGS.instanceName
  runtimeInstancesElem  := gs.runtimeInstances.runtimeInstancesElem
  runtimeInstancesName  := gs.runtimeInstances.runtimeInstancesName

/-! ## Consumer: abstract ghost-map lookup over an abstract GF -/

/-- Abstract form of `WasmHeap.globalPointsTo_lookup`: the ghost-map lookup
lemma for Wasm globals, stated over any `GF` satisfying `[WasmGS hlc GF α]`.
Only `WasmGS.globalGS` (a `GhostMapG` obligation) and `WasmGS.globalName`
are used; there is no `stateInterp` or WP in sight.

The concrete lemma `WasmHeap.globalPointsTo_lookup` is the special case
`GF = WasmHeapGF α`, recovered via `instWasmGS_of_WasmSmallStepGS` below. -/
theorem globalPointsTo_lookup_gf [g : WasmGS hlc GF α]
    (σ : WasmGlobalMap Value) (key : GlobalKey) (value : Value) :
    (ghost_map_auth g.globalName (DFrac.own 1) σ : IProp GF) -∗
      ghost_map_elem g.globalName (DFrac.own 1) key value -∗
      iprop(⌜get? σ key = some value⌝) := by
  iapply ghost_map_lookup

/-- Specialising `globalPointsTo_lookup_gf` to `GF = WasmHeapGF α` via
`instWasmGS_of_WasmSmallStepGS` recovers `WasmHeap.globalPointsTo_lookup`.
`g.globalName` reduces definitionally to `gs.global.globalName`. -/
example [gs : WasmSmallStepGS hlc α]
    (σ : WasmGlobalMap Value) (key : GlobalKey) (value : Value) :
    (ghost_map_auth gs.global.globalName (DFrac.own 1) σ : IProp (WasmHeapGF α)) -∗
      ghost_map_elem gs.global.globalName (DFrac.own 1) key value -∗
      iprop(⌜get? σ key = some value⌝) :=
  globalPointsTo_lookup_gf σ key value

end Wasm.SmallStep
