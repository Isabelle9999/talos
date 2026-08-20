import CodeLib.SepLogic.SmallStepLanguage
import CodeLib.SepLogic.WasmRules
import Iris.ProgramLogic.WeakestPre

/-!
# Iris state interpretation for the Wasm small-step machine

The authoritative GenHeap map is existentially hidden by the state
interpretation and is required to agree with the physical bytes in
`MachineStore`. Unlike the legacy `wp_wasm` setup, the ghost heap is therefore
not a free-floating resource: any owned byte must describe the corresponding
physical memory byte.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Std
open Wasm.SepLogic

/-- Authoritative ownership of the current module instance id.
Wraps `currentInstanceAuthN` to take `ModuleInstanceId` directly. -/
def currentInstanceAuth {α : Type} [gs : WasmInstanceGS α]
    (id : ModuleInstanceId) : IProp (WasmHeapGF α) :=
  currentInstanceAuthN id.id

/-- Fragment ownership of the current module instance id.
Wraps `currentInstanceOwnN` to take `ModuleInstanceId` directly. -/
@[reducible] def currentInstanceOwn {α : Type} [gs : WasmInstanceGS α]
    (id : ModuleInstanceId) : IProp (WasmHeapGF α) :=
  currentInstanceOwnN id.id

instance {α : Type} [WasmInstanceGS α] (id : ModuleInstanceId) :
    BI.Timeless (currentInstanceAuth (α := α) id) := by
  unfold currentInstanceAuth; infer_instance

instance {α : Type} [WasmInstanceGS α] (id : ModuleInstanceId) :
    BI.Timeless (currentInstanceOwn (α := α) id) := by
  unfold currentInstanceOwn; infer_instance

theorem currentInstanceOwn_agree {α : Type} [gs : WasmInstanceGS α]
    (actual expected : ModuleInstanceId) :
    currentInstanceAuth (α := α) actual ∗ currentInstanceOwn expected ⊢
      iprop(⌜actual = expected⌝) := by
  unfold currentInstanceAuth currentInstanceOwn currentInstanceAuthN currentInstanceOwnN
  iintro ⟨Hauth, Hfrag⟩
  icombine Hauth Hfrag gives %Hvalid
  ipureintro
  have : actual.id = expected.id :=
    congrArg DiscreteO.car (ExclAuth.agree (A := DiscreteO Nat) Hvalid)
  cases actual; cases expected; cases this; rfl

theorem currentInstanceOwn_update {α : Type} [gs : WasmInstanceGS α]
    (old new' : ModuleInstanceId) :
    currentInstanceAuth (α := α) old ∗ currentInstanceOwn old ==∗
      currentInstanceAuth new' ∗ currentInstanceOwn new' := by
  unfold currentInstanceAuth currentInstanceOwn
  iapply currentInstanceOwnN_update

theorem currentInstanceOwn_update_of_any {α : Type} [gs : WasmInstanceGS α]
    (actual calleeId newId : ModuleInstanceId) :
    currentInstanceAuth (α := α) actual ∗ currentInstanceOwn calleeId ==∗
      currentInstanceAuth newId ∗ currentInstanceOwn newId ∗ ⌜actual = calleeId⌝ := by
  unfold currentInstanceAuth currentInstanceOwn currentInstanceAuthN currentInstanceOwnN
  iintro ⟨Hauth, Hfrag⟩
  ihave %heq_id : ⌜actual.id = calleeId.id⌝ $$ [Hauth Hfrag]
  · icombine Hauth Hfrag gives %Hvalid
    ipureintro
    exact congrArg DiscreteO.car (ExclAuth.agree (A := DiscreteO Nat) Hvalid)
  imod iOwn_update_op (E := gs.instanceElem)
      (ExclAuth.update (A := DiscreteO Nat)
        (a := (⟨actual.id⟩ : DiscreteO Nat))
        (b := ⟨calleeId.id⟩)
        (a' := ⟨newId.id⟩))
      $$ [Hauth Hfrag] with Hboth
  · iframe
  imodintro
  icases iOwn_op $$ Hboth with ⟨H1, H2⟩
  isplitl [H1]
  · iexact H1
  isplitl [H2]
  · iexact H2
  · ipureintro
    cases actual; cases calleeId; cases heq_id; rfl

class WasmSmallStepGS (hlc : outParam HasLC) (α : outParam Type) extends
    InvGS_gen hlc (WasmHeapGF α), WasmHeapGS α where
  global : WasmGlobalGS α
  dataSegment : WasmDataSegmentGS α
  table : WasmTableGS α
  elementSegment : WasmElementSegmentGS α
  runtime : WasmRuntimeModuleGS α
  hostEnv : WasmHostEnvGS α
  hostState : WasmHostStateGS α
  instanceGS : WasmInstanceGS α
  runtimeInstances : WasmRuntimeInstancesGS α

attribute [instance] WasmSmallStepGS.toInvGS_gen
attribute [instance] WasmSmallStepGS.toWasmHeapGS
attribute [reducible, instance] WasmSmallStepGS.global
attribute [reducible, instance] WasmSmallStepGS.dataSegment
attribute [reducible, instance] WasmSmallStepGS.table
attribute [reducible, instance] WasmSmallStepGS.elementSegment
attribute [reducible, instance] WasmSmallStepGS.runtime
attribute [reducible, instance] WasmSmallStepGS.hostEnv
attribute [reducible, instance] WasmSmallStepGS.hostState
attribute [reducible, instance] WasmSmallStepGS.instanceGS
attribute [reducible, instance] WasmSmallStepGS.runtimeInstances

variable {α : Type}

/-- Resolver that maps memory id 0 to the primary memory and ids ≥ 1 to
extra memories. Used to bridge single-Mem stateInterp facts to the
multi-memory heapAgreesWithMem API. -/
def storeResolve (store : MachineStore α) : Nat → Option Mem :=
  fun i => if i = 0 then some store.wasm.mem else store.wasm.extraMems[i - 1]?


private theorem storeResolve_zero (store : MachineStore α) :
    storeResolve store 0 = some store.wasm.mem := by simp [storeResolve]


private theorem storeResolve_update_mem0 (store : MachineStore α) (newMem : Mem) :
    (fun id => if id = 0 then some newMem else storeResolve store id) =
    storeResolve { store with wasm := { store.wasm with mem := newMem } } := by
  funext id; simp only [storeResolve]; by_cases h : id = 0 <;> simp [h]


private theorem fromResolver (store : MachineStore α) {σ : WasmHeapMap (Option UInt8)}
    (hag : heapAgreesWithMem σ (storeResolve store))
    (addr : UInt32) (v : UInt8)
    (hl : get? σ ⟨0, addr⟩ = some (some v)) :
    store.wasm.mem.read8 addr = v := by
  obtain ⟨m, hm, hr⟩ := hag ⟨0, addr⟩ v hl
  exact (Option.some.inj ((storeResolve_zero store).symm.trans hm)) ▸ hr


private theorem fromResolverBounds (store : MachineStore α) {σ : WasmHeapMap (Option UInt8)}
    (hbn : heapAddressesInBounds σ (storeResolve store))
    (addr : UInt32) (hne : get? σ ⟨0, addr⟩ ≠ none) :
    addr.toNat < store.wasm.mem.pages * 65536 := by
  obtain ⟨m, hm, hlt⟩ := hbn ⟨0, addr⟩ hne
  exact (Option.some.inj ((storeResolve_zero store).symm.trans hm)) ▸ hlt

instance instStateInterp [WasmSmallStepGS hlc α] :
    StateInterp (MachineStore α) StepKind (WasmHeapGF α) where
  stateInterp store _ _ _ := iprop%
    ∃ σ : WasmHeapMap (Option UInt8),
      ∃ globalσ : WasmGlobalMap Value,
      ∃ dataSegmentσ : WasmDataSegmentMap (Option (List UInt8)),
      ∃ tableσ : WasmTableMap TableInst,
      ∃ elementSegmentσ :
        WasmElementSegmentMap (Option (List (Option Nat))),
      ∃ runtimeModuleσ : WasmRuntimeModuleMap Module,
      ∃ hostEnvσ : WasmHostEnvMap (HostEnv α),
      genHeapInterp σ ∗
        ghost_map_auth WasmSmallStepGS.global.globalName
          (DFrac.own 1) globalσ ∗
        ghost_map_auth WasmSmallStepGS.dataSegment.dataSegmentName
          (DFrac.own 1) dataSegmentσ ∗
        ghost_map_auth WasmSmallStepGS.table.tableName
          (DFrac.own 1) tableσ ∗
        ghost_map_auth
          WasmSmallStepGS.elementSegment.elementSegmentName
          (DFrac.own 1) elementSegmentσ ∗
        ghost_map_auth WasmSmallStepGS.runtime.runtimeName
          (DFrac.own 1) runtimeModuleσ ∗
        ([∗map] id ↦ m ∈ runtimeModuleσ, runtimeModuleElem id m) ∗
        runtimeInstancesOwn store.runtime.instances ∗
        currentInstanceAuth store.runtime.entry ∗
        ghost_map_auth WasmSmallStepGS.hostEnv.hostEnvName
          (DFrac.own 1) hostEnvσ ∗
        hostStateAuth store.wasm.host ∗
      ⌜heapAgreesWithMem σ (storeResolve store) ∧
        heapAddressesInBounds σ (storeResolve store) ∧
        globalHeapAgrees globalσ store.wasm.globals ∧
        dataSegmentHeapAgrees dataSegmentσ store.wasm.dataSegments ∧
        tableHeapAgrees tableσ store.wasm.tables ∧
        elementSegmentHeapAgrees elementSegmentσ
          store.wasm.elementSegments ∧
        (∀ id m, get? runtimeModuleσ id = some m →
          store.runtime.instances[id]?.map (·.module) = some m) ∧
        ∀ id env, get? hostEnvσ id = some env →
          store.runtime.instances[id]?.map (·.host) = some env⌝

theorem stateInterp_eq [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ⊣⊢
      (iprop% ∃ σ : WasmHeapMap (Option UInt8),
        ∃ globalσ : WasmGlobalMap Value,
        ∃ dataSegmentσ : WasmDataSegmentMap (Option (List UInt8)),
        ∃ tableσ : WasmTableMap TableInst,
        ∃ elementSegmentσ :
          WasmElementSegmentMap (Option (List (Option Nat))),
        ∃ runtimeModuleσ : WasmRuntimeModuleMap Module,
        ∃ hostEnvσ : WasmHostEnvMap (HostEnv α),
        genHeapInterp σ ∗
          ghost_map_auth WasmSmallStepGS.global.globalName
            (DFrac.own 1) globalσ ∗
          ghost_map_auth WasmSmallStepGS.dataSegment.dataSegmentName
            (DFrac.own 1) dataSegmentσ ∗
          ghost_map_auth WasmSmallStepGS.table.tableName
            (DFrac.own 1) tableσ ∗
          ghost_map_auth
            WasmSmallStepGS.elementSegment.elementSegmentName
            (DFrac.own 1) elementSegmentσ ∗
          ghost_map_auth WasmSmallStepGS.runtime.runtimeName
            (DFrac.own 1) runtimeModuleσ ∗
          ([∗map] id ↦ m ∈ runtimeModuleσ, runtimeModuleElem id m) ∗
          runtimeInstancesOwn store.runtime.instances ∗
          currentInstanceAuth store.runtime.entry ∗
          ghost_map_auth WasmSmallStepGS.hostEnv.hostEnvName
            (DFrac.own 1) hostEnvσ ∗
          hostStateAuth store.wasm.host ∗
        ⌜heapAgreesWithMem σ (storeResolve store) ∧
          heapAddressesInBounds σ (storeResolve store) ∧
          globalHeapAgrees globalσ store.wasm.globals ∧
          dataSegmentHeapAgrees dataSegmentσ store.wasm.dataSegments ∧
          tableHeapAgrees tableσ store.wasm.tables ∧
          elementSegmentHeapAgrees elementSegmentσ
            store.wasm.elementSegments ∧
          (∀ id m, get? runtimeModuleσ id = some m →
            store.runtime.instances[id]?.map (·.module) = some m) ∧
          ∀ id env, get? hostEnvσ id = some env →
            store.runtime.instances[id]?.map (·.host) = some env⌝) :=
  .rfl

theorem stateInterp_pointsTo_read8 [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt8) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some value) ==∗
      ⌜store.wasm.mem.read8 address = value⌝ := by
  iintro ⟨Hstate, Hpointsto⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  icases genHeap_valid $$ [$Hheap $Hpointsto] with >%hlookup
  ipureintro
  exact fromResolver store Hfacts.1 address value hlookup

theorem stateInterp_pointsTo_inBounds [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt8) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some value) ==∗
      ⌜address.toNat < store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hpointsto⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  icases genHeap_valid $$ [$Hheap $Hpointsto] with >%hlookup
  ipureintro
  exact fromResolverBounds store Hfacts.2.1 address (by simp [hlookup])

theorem stateInterp_pointsTo_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt8) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some value) ==∗
      ⌜store.wasm.mem.read8 address = value ∧
        address.toNat < store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hpointsto⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  icases genHeap_valid $$ [$Hheap $Hpointsto] with >%hlookup
  ipureintro
  exact ⟨fromResolver store Hfacts.1 address value hlookup,
    fromResolverBounds store Hfacts.2.1 address (by simp [hlookup])⟩

/-- Changing `Store.host` requires exchanging `hostStateOwn` because
`stateInterp` holds the authoritative `hostStateAuth`. The caller supplies
the old fragment and receives the new one. -/
theorem stateInterp_host_set [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat) (host : α) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      hostStateOwn store.wasm.host ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm := { store.wasm with host } }
        steps observations threads ∗
      hostStateOwn host := by
  iintro ⟨Hσ, HP⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hσ with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep,
      HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  imod hostStateOwn_update store.wasm.host host $$ [$Hstate_auth $HP] with ⟨Hauth', HP'⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hauth']
  · iapply (stateInterp_eq
      { store with wasm := { store.wasm with host } }
      steps observations threads).mpr
    iexists σ; iexists globalσ; iexists dataSegmentσ; iexists tableσ
    iexists elementSegmentσ; iexists runtimeModuleσ; iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hauth'
    ipureintro
    exact Hfacts
  · iexact HP'

/-- Owned global state determines the corresponding physical instantiated
global. -/
theorem stateInterp_global_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (value : Value) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      globalPointsToAt 0 index value ==∗
      ⌜store.wasm.globals.globals[index]? = some value⌝ := by
  iintro ⟨Hstate, Hglobal⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  simp only [globalPointsToAt]
  ihave %hlookup := globalPointsTo_lookup globalσ ⟨0, index⟩ value $$ Hglobals Hglobal
  ipureintro
  exact Hfacts.2.2.1 index value hlookup

/-- Owned table state determines the corresponding physical instantiated table.
Uses the unfolded `tablePointsTo` form so `iframe` can match without going through the
`tablePointsToAt` def. Call after `simp only [tablePointsToAt]` to unfold the hypothesis. -/
theorem stateInterp_table_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (tableIndex : Nat) (table : TableInst) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      tablePointsTo (⟨0, tableIndex⟩ : TableKey) table ==∗
      ⌜store.wasm.tables[tableIndex]? = some table⌝ := by
  iintro ⟨Hstate, Htable⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  ihave %hlookup := tablePointsTo_lookup tableσ ⟨0, tableIndex⟩ table $$ Htables Htable
  ipureintro
  exact Hfacts.2.2.2.2.1 tableIndex table hlookup

/-- Updating an owned global updates both the authoritative ghost map and the
physical instantiated global array in lockstep. -/
theorem stateInterp_global_set [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (oldValue newValue : Value) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      globalPointsToAt 0 index oldValue ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with globals :=
                { globals := store.wasm.globals.globals.set index newValue } } }
        steps observations threads ∗
      globalPointsToAt 0 index newValue := by
  iintro ⟨Hstate, Hglobal⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  simp only [globalPointsToAt]
  ihave %hlookup :=
    globalPointsTo_lookup globalσ ⟨0, index⟩ oldValue $$ Hglobals Hglobal
  imod globalPointsTo_update globalσ ⟨0, index⟩ oldValue newValue $$
      Hglobals Hglobal with
    ⟨Hglobals, Hglobal⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with globals :=
              { globals := store.wasm.globals.globals.set index newValue } } }
      steps observations threads).mpr
    iexists σ
    iexists insert globalσ ⟨0, index⟩ newValue
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
    ipureintro
    exact ⟨Hfacts.1, Hfacts.2.1,
      ⟨global_store_sound globalσ store.wasm.globals
          index oldValue newValue Hfacts.2.2.1 hlookup,
        Hfacts.2.2.2⟩⟩
  · iexact Hglobal

/-- Owned passive-segment state determines the corresponding physical
instantiated segment entry. The framed form keeps both resources available for
a following `memory.init` or `data.drop` transition. -/
theorem stateInterp_dataSegment_facts_frame [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (value : Option (List UInt8)) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      dataSegmentPointsToAt 0 index value ==∗
      stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      dataSegmentPointsToAt 0 index value ∗
      ⌜store.wasm.dataSegments[index]? = some value⌝ := by
  iintro ⟨Hstate, Hsegment⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  simp only [dataSegmentPointsToAt]
  ihave %hlookup :=
    dataSegmentPointsTo_lookup dataSegmentσ ⟨0, index⟩ value $$
      Hsegments Hsegment
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe
    ipureintro
    exact Hfacts
  · isplitl [Hsegment]
    · iexact Hsegment
    · ipureintro
      exact Hfacts.2.2.2.1 index value hlookup

/-- `data.drop` updates the physical segment status and its authoritative
ghost entry in lockstep. -/
theorem stateInterp_dataSegment_drop [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (oldValue : Option (List UInt8)) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      dataSegmentPointsToAt 0 index oldValue ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with
              dataSegments := store.wasm.dataSegments.set index none } }
        steps observations threads ∗
      dataSegmentPointsToAt 0 index none := by
  iintro ⟨Hstate, Hsegment⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  simp only [dataSegmentPointsToAt]
  ihave %hlookup :=
    dataSegmentPointsTo_lookup dataSegmentσ ⟨0, index⟩ oldValue $$
      Hsegments Hsegment
  imod dataSegmentPointsTo_update dataSegmentσ ⟨0, index⟩ oldValue none $$
      Hsegments Hsegment with
    ⟨Hsegments, Hsegment⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with
            dataSegments := store.wasm.dataSegments.set index none } }
      steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists insert dataSegmentσ ⟨0, index⟩ none
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe
    ipureintro
    exact ⟨Hfacts.1, Hfacts.2.1, Hfacts.2.2.1,
      dataSegment_store_sound dataSegmentσ store.wasm.dataSegments
        index oldValue none Hfacts.2.2.2.1 hlookup,
      Hfacts.2.2.2.2⟩
  · iexact Hsegment

/-- Element-segment ownership identifies the live or dropped state at the
corresponding stable physical segment index. -/
theorem stateInterp_elementSegment_facts_frame [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (value : Option (List (Option Nat))) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      elementSegmentPointsToAt 0 index value ==∗
      stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      elementSegmentPointsToAt 0 index value ∗
      ⌜store.wasm.elementSegments[index]? = some value⌝ := by
  iintro ⟨Hstate, Hsegment⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  simp only [elementSegmentPointsToAt]
  ihave %hlookup :=
    elementSegmentPointsTo_lookup elementSegmentσ ⟨0, index⟩ value $$
      HelementSegments Hsegment
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe
    ipureintro
    exact Hfacts
  · isplitl [Hsegment]
    · iexact Hsegment
    · ipureintro
      exact Hfacts.2.2.2.2.2.1 index value hlookup

/-- `elem.drop` changes the physical segment status and authoritative ghost
entry to `none` without renumbering any segment. -/
theorem stateInterp_elementSegment_drop [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (oldValue : Option (List (Option Nat))) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      elementSegmentPointsToAt 0 index oldValue ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with
              elementSegments :=
                store.wasm.elementSegments.set index none } }
        steps observations threads ∗
      elementSegmentPointsToAt 0 index none := by
  iintro ⟨Hstate, Hsegment⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  simp only [elementSegmentPointsToAt]
  ihave %hlookup :=
    elementSegmentPointsTo_lookup elementSegmentσ ⟨0, index⟩ oldValue $$
      HelementSegments Hsegment
  imod elementSegmentPointsTo_update
      elementSegmentσ ⟨0, index⟩ oldValue none $$
      HelementSegments Hsegment with
    ⟨HelementSegments, Hsegment⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with
            elementSegments :=
              store.wasm.elementSegments.set index none } }
      steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists insert elementSegmentσ ⟨0, index⟩ none
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe
    ipureintro
    exact ⟨Hfacts.1, Hfacts.2.1, Hfacts.2.2.1,
      Hfacts.2.2.2.1,
      ⟨Hfacts.2.2.2.2.1,
        elementSegment_store_sound elementSegmentσ
          store.wasm.elementSegments index oldValue none
          Hfacts.2.2.2.2.2.1 hlookup,
      Hfacts.2.2.2.2.2.2.1, Hfacts.2.2.2.2.2.2.2⟩⟩
  · iexact Hsegment

/-- Owning a table fragment identifies the complete physical instantiated
table at its stable table index. -/
theorem stateInterp_table_facts_frame [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (table : TableInst) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      tablePointsToAt 0 index table ==∗
      stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      tablePointsToAt 0 index table ∗
      ⌜store.wasm.tables[index]? = some table⌝ := by
  iintro ⟨Hstate, Htable⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  simp only [tablePointsToAt]
  ihave %hlookup :=
    tablePointsTo_lookup tableσ ⟨0, index⟩ table $$ Htables Htable
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe
    ipureintro
    exact Hfacts
  · isplitl [Htable]
    · iexact Htable
    · ipureintro
      exact Hfacts.2.2.2.2.1 index table hlookup

/-- Replacing an owned table preserves its stable identity and updates the
authoritative ghost map and physical table list in lockstep. -/
theorem stateInterp_table_set [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (oldTable newTable : TableInst) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      tablePointsToAt 0 index oldTable ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with
              tables := listSetAt store.wasm.tables index newTable } }
        steps observations threads ∗
      tablePointsToAt 0 index newTable := by
  iintro ⟨Hstate, Htable⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  simp only [tablePointsToAt]
  ihave %hlookup :=
    tablePointsTo_lookup tableσ ⟨0, index⟩ oldTable $$ Htables Htable
  imod tablePointsTo_update tableσ ⟨0, index⟩ oldTable newTable $$
      Htables Htable with
    ⟨Htables, Htable⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with
            tables := listSetAt store.wasm.tables index newTable } }
      steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists insert tableσ ⟨0, index⟩ newTable
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe
    ipureintro
    exact ⟨Hfacts.1, Hfacts.2.1, Hfacts.2.2.1,
      Hfacts.2.2.2.1,
      ⟨table_store_listSetAt_sound tableσ store.wasm.tables
          index oldTable newTable Hfacts.2.2.2.2.1 hlookup,
        Hfacts.2.2.2.2.2⟩⟩
  · iexact Htable

theorem stateInterp_runtimeModule_agree [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (instanceId : ModuleInstanceId) (m : Module) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      runtimeModuleOwn instanceId m ==∗
      ⌜store.runtime.currentModule = m⌝ := by
  simp only [runtimeModuleOwn]
  iintro ⟨Hstate, Hmod, Hid⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  icombine HinstanceAuth Hid as Hentry
  ihave %hentry := currentInstanceOwn_agree store.runtime.entry instanceId $$ Hentry
  ihave %hlookup := runtimeModuleElem_lookup $$ HruntimeModuleAuth Hmod
  ipureintro
  have hma := Hfacts.2.2.2.2.2.2.1 instanceId.id m hlookup
  have hid : store.runtime.entry.id = instanceId.id := congrArg (·.id) hentry
  rw [← hid] at hma
  simp only [RuntimeEnv.currentModule, RuntimeEnv.currentInstance]
  rcases h : store.runtime.instances[store.runtime.entry.id]? with _ | inst
  · rw [h, Option.map_none] at hma; simp at hma
  · rw [h, Option.map_some, Option.some.injEq] at hma
    have hget : store.runtime.instances[store.runtime.entry.id]! = inst := by
      simp only [getElem!_def, h]
    rw [hget]; exact hma

theorem stateInterp_instances_agree [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (instances : Array (ModuleInstance α)) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      runtimeInstancesOwn instances ==∗
      ⌜store.runtime.instances = instances⌝ := by
  iintro ⟨Hstate, Hexpected⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  icombine HruntimeInstances Hexpected as Hinst
  ihave %hagrees := runtimeInstancesOwn_agree store.runtime.instances instances $$ Hinst
  ipureintro
  exact hagrees

/-- Owned fragment for the current instance id agrees with the stateInterp value. -/
theorem stateInterp_currentInstance_agree [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (id : ModuleInstanceId) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      currentInstanceOwn id ==∗
      ⌜store.runtime.entry = id⌝ := by
  iintro ⟨Hstate, Hfrag⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  icombine HinstanceAuth Hfrag as Hcombined
  ihave %hagrees := currentInstanceOwn_agree store.runtime.entry id $$ Hcombined
  ipureintro
  exact hagrees

/-- Update the current instance id in both stateInterp and the owned fragment.
`hch` asserts the new instance has the same host as the current one,
so the `hostEnvOwn` resource remains valid. -/
theorem stateInterp_currentInstance_update [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (newId : ModuleInstanceId) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      currentInstanceOwn store.runtime.entry ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with runtime := { store.runtime with entry := newId } }
        steps observations threads ∗
      currentInstanceOwn newId := by
  iintro ⟨Hstate, Hfrag⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  imod currentInstanceOwn_update store.runtime.entry newId $$ [$HinstanceAuth $Hfrag] with ⟨HinstanceAuth', Hfrag'⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth' HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq
      { store with runtime := { store.runtime with entry := newId } }
      steps observations threads).mpr
    iexists σ; iexists globalσ; iexists dataSegmentσ; iexists tableσ; iexists elementSegmentσ; iexists runtimeModuleσ; iexists hostEnvσ
    have hres : storeResolve { store with runtime := { store.runtime with entry := newId } } = storeResolve store := rfl
    simp only [hres]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth' HhostEnvAuth Hstate_auth
    ipureintro
    exact Hfacts
  · iexact Hfrag'

theorem stateInterp_currentInstance_update_of_any [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (calleeId newId : ModuleInstanceId) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      currentInstanceOwn calleeId ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with runtime := { store.runtime with entry := newId } }
        steps observations threads ∗
      currentInstanceOwn newId ∗
      ⌜store.runtime.entry = calleeId⌝ := by
  iintro ⟨Hstate, Hfrag⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  imod currentInstanceOwn_update_of_any store.runtime.entry calleeId newId $$
      [$HinstanceAuth $Hfrag] with ⟨HinstanceAuth', Hfrag', %heq⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth' HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq
        { store with runtime := { store.runtime with entry := newId } }
        steps observations threads).mpr
    iexists σ; iexists globalσ; iexists dataSegmentσ; iexists tableσ; iexists elementSegmentσ; iexists runtimeModuleσ; iexists hostEnvσ
    have hres : storeResolve { store with runtime := { store.runtime with entry := newId } } = storeResolve store := rfl
    simp only [hres]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth' HhostEnvAuth Hstate_auth
    ipureintro
    exact Hfacts
  isplitl [Hfrag']
  · iexact Hfrag'
  · ipureintro; exact heq

-- push doesn't affect elements before the pushed index
private theorem currentInstance_push_lt (re : RuntimeEnv α) (inst : ModuleInstance α)
    (h : re.entry.id < re.instances.size) :
    ({ re with instances := re.instances.push inst } : RuntimeEnv α).currentInstance =
        re.currentInstance := by
  simp only [RuntimeEnv.currentInstance]
  unfold GetElem?.getElem!
  show (re.instances.push inst).getD re.entry.id default = re.instances.getD re.entry.id default
  unfold Array.getD
  have h2 : re.entry.id < (re.instances.push inst).size := by
    simp only [Array.size_push]; omega
  rw [dif_pos h2, dif_pos h]
  exact Array.getElem_push_lt h

/-- Adding a new instance to the runtime table preserves stateInterp given
ownership of the new instances array. `runtimeInstancesOwn` is Agree-based
(frozen snapshot), so the caller must supply ownership of the pushed array;
`currentInstance_push_lt` ensures the current module and host are unchanged. -/
theorem instantiate_preserves_stateInterp [WasmSmallStepGS hlc α]
    (config : Config α) (newInst : ModuleInstance α)
    (hvalid : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (steps : Nat) (obs : List StepKind) (threads : Nat) :
    stateInterp (GF := WasmHeapGF α) config.store steps obs threads ∗
      runtimeInstancesOwn (config.store.runtime.instances.push newInst) ⊢
      stateInterp (GF := WasmHeapGF α)
        { config.store with runtime := { config.store.runtime with
            instances := config.store.runtime.instances.push newInst } }
        steps obs threads := by
  have hci := currentInstance_push_lt config.store.runtime newInst hvalid
  have hch := congrArg (·.host) hci
  have hres : storeResolve { config.store with runtime := { config.store.runtime with
        instances := config.store.runtime.instances.push newInst } } =
      storeResolve config.store := rfl
  iintro ⟨Hstate, HruntimeInstances'⟩
  icases (stateInterp_eq config.store steps obs threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  iclear HruntimeInstances
  iapply (stateInterp_eq { config.store with runtime := { config.store.runtime with
      instances := config.store.runtime.instances.push newInst } } steps obs threads).mpr
  iexists σ; iexists globalσ; iexists dataSegmentσ; iexists tableσ; iexists elementSegmentσ; iexists runtimeModuleσ; iexists hostEnvσ
  simp only [hres]
  iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances' HinstanceAuth HhostEnvAuth Hstate_auth
  ipureintro
  refine ⟨Hfacts.1, Hfacts.2.1, Hfacts.2.2.1, Hfacts.2.2.2.1, Hfacts.2.2.2.2.1, Hfacts.2.2.2.2.2.1,
    fun id m hlookup => ?_, fun id env hlookup => ?_⟩
  · have hold := Hfacts.2.2.2.2.2.2.1 id m hlookup
    rw [Array.getElem?_push]
    by_cases h_eq : id = config.store.runtime.instances.size
    · rw [h_eq] at hold; simp at hold
    · rw [if_neg h_eq]; exact hold
  · have hold := Hfacts.2.2.2.2.2.2.2 id env hlookup
    rw [Array.getElem?_push]
    by_cases h_eq : id = config.store.runtime.instances.size
    · rw [h_eq] at hold; simp at hold
    · rw [if_neg h_eq]; exact hold

/-- pointsTo is ghost state — adding an instance doesn't affect existing
byte ownership. Stated explicitly to document the design invariant. -/
theorem instantiate_pointsTo_preserved [WasmSmallStepGS hlc α]
    (key : MemoryKey) (dfrac : DFrac) (value : Option UInt8) :
    (pointsTo (GF := WasmHeapGF α) key dfrac value) ⊢
    (pointsTo (GF := WasmHeapGF α) key dfrac value) := by
  iintro H; iexact H

/-- Four-byte ownership determines the physical little-endian word and proves
the complete access is in bounds. The address equalities exclude UInt32
wraparound in the derived byte footprint. -/
theorem stateInterp_pointsTo_u32_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address value : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u32 0 address value ==∗
      ⌜store.wasm.mem.read32 address = value ∧
        address.toNat + 4 ≤ store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u32_eq 0 address value).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  ihave %hg0 :
      ⌜get? σ ⟨0, address⟩ = some (some (u32Byte value 0))⌝ $$ [Hheap H0]
  · imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro
    exact hg0
  ihave %hg1 :
      ⌜get? σ ⟨0, address + 1⟩ = some (some (u32Byte value 1))⌝ $$ [Hheap H1]
  · imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro
    exact hg1
  ihave %hg2 :
      ⌜get? σ ⟨0, address + 2⟩ = some (some (u32Byte value 2))⌝ $$ [Hheap H2]
  · imod genHeap_valid $$ [$Hheap $H2] with %hg2
    ipureintro
    exact hg2
  ihave %hg3 :
      ⌜get? σ ⟨0, address + 3⟩ = some (some (u32Byte value 3))⌝ $$ [Hheap H3]
  · imod genHeap_valid $$ [$Hheap $H3] with %hg3
    ipureintro
    exact hg3
  have hr0 := fromResolver store Hfacts.1 address (u32Byte value 0) hg0
  have hr1 := fromResolver store Hfacts.1 (address + 1) (u32Byte value 1) hg1
  have hr2 := fromResolver store Hfacts.1 (address + 2) (u32Byte value 2) hg2
  have hr3 := fromResolver store Hfacts.1 (address + 3) (u32Byte value 3) hg3
  have hb3 := fromResolverBounds store Hfacts.2.1 (address + 3) (by simp [hg3])
  ipureintro
  constructor
  · simp only [Mem.read8] at hr0 hr1 hr2 hr3
    simp only [Mem.read32]
    rw [hr0, ← h1, hr1, ← h2, hr2, ← h3, hr3]
    exact u32Byte_reassemble value
  · rw [h3] at hb3
    omega

/-- Framed form of `stateInterp_pointsTo_u32_facts`. It preserves both the
state interpretation and word ownership, so clients can extract physical
facts for multiple disjoint words sequentially. -/
theorem stateInterp_pointsTo_u32_facts_frame [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address value : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u32 0 address value ==∗
      stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u32 0 address value ∗
      ⌜store.wasm.mem.read32 address = value ∧
        address.toNat + 4 ≤ store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u32_eq 0 address value).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  ihave %hg0 :
      ⌜get? σ ⟨0, address⟩ = some (some (u32Byte value 0))⌝ $$ [Hheap H0]
  · imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro
    exact hg0
  ihave %hg1 :
      ⌜get? σ ⟨0, address + 1⟩ = some (some (u32Byte value 1))⌝ $$ [Hheap H1]
  · imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro
    exact hg1
  ihave %hg2 :
      ⌜get? σ ⟨0, address + 2⟩ = some (some (u32Byte value 2))⌝ $$ [Hheap H2]
  · imod genHeap_valid $$ [$Hheap $H2] with %hg2
    ipureintro
    exact hg2
  ihave %hg3 :
      ⌜get? σ ⟨0, address + 3⟩ = some (some (u32Byte value 3))⌝ $$ [Hheap H3]
  · imod genHeap_valid $$ [$Hheap $H3] with %hg3
    ipureintro
    exact hg3
  have hr0 := fromResolver store Hfacts.1 address (u32Byte value 0) hg0
  have hr1 := fromResolver store Hfacts.1 (address + 1) (u32Byte value 1) hg1
  have hr2 := fromResolver store Hfacts.1 (address + 2) (u32Byte value 2) hg2
  have hr3 := fromResolver store Hfacts.1 (address + 3) (u32Byte value 3) hg3
  have hb3 := fromResolverBounds store Hfacts.2.1 (address + 3) (by simp [hg3])
  have hread : store.wasm.mem.read32 address = value := by
    simp only [Mem.read8] at hr0 hr1 hr2 hr3
    simp only [Mem.read32]
    rw [hr0, ← h1, hr1, ← h2, hr2, ← h3, hr3]
    exact u32Byte_reassemble value
  have hbound :
      address.toNat + 4 ≤ store.wasm.mem.pages * 65536 := by
    rw [h3] at hb3
    omega
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe
    ipureintro
    exact Hfacts
  · isplitl [H0 H1 H2 H3]
    · iapply (pointsTo_u32_eq 0 address value).mpr
      iframe
    · ipureintro
      exact ⟨hread, hbound⟩

/-- Eight-byte ownership determines the physical little-endian word and proves
the complete access is in bounds. The address equalities exclude UInt32
wraparound in the derived byte footprint. -/
theorem stateInterp_pointsTo_u64_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt64)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3)
    (h4 : (address + 4).toNat = address.toNat + 4)
    (h5 : (address + 5).toNat = address.toNat + 5)
    (h6 : (address + 6).toNat = address.toNat + 6)
    (h7 : (address + 7).toNat = address.toNat + 7) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u64 0 address value ==∗
      ⌜store.wasm.mem.read64 address = value ∧
        address.toNat + 8 ≤ store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u64_eq 0 address value).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  ihave %hg0 :
      ⌜get? σ ⟨0, address⟩ = some (some (u64Byte value 0))⌝ $$ [Hheap H0]
  · imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro; exact hg0
  ihave %hg1 :
      ⌜get? σ ⟨0, address + 1⟩ = some (some (u64Byte value 1))⌝ $$ [Hheap H1]
  · imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro; exact hg1
  ihave %hg2 :
      ⌜get? σ ⟨0, address + 2⟩ = some (some (u64Byte value 2))⌝ $$ [Hheap H2]
  · imod genHeap_valid $$ [$Hheap $H2] with %hg2
    ipureintro; exact hg2
  ihave %hg3 :
      ⌜get? σ ⟨0, address + 3⟩ = some (some (u64Byte value 3))⌝ $$ [Hheap H3]
  · imod genHeap_valid $$ [$Hheap $H3] with %hg3
    ipureintro; exact hg3
  ihave %hg4 :
      ⌜get? σ ⟨0, address + 4⟩ = some (some (u64Byte value 4))⌝ $$ [Hheap H4]
  · imod genHeap_valid $$ [$Hheap $H4] with %hg4
    ipureintro; exact hg4
  ihave %hg5 :
      ⌜get? σ ⟨0, address + 5⟩ = some (some (u64Byte value 5))⌝ $$ [Hheap H5]
  · imod genHeap_valid $$ [$Hheap $H5] with %hg5
    ipureintro; exact hg5
  ihave %hg6 :
      ⌜get? σ ⟨0, address + 6⟩ = some (some (u64Byte value 6))⌝ $$ [Hheap H6]
  · imod genHeap_valid $$ [$Hheap $H6] with %hg6
    ipureintro; exact hg6
  ihave %hg7 :
      ⌜get? σ ⟨0, address + 7⟩ = some (some (u64Byte value 7))⌝ $$ [Hheap H7]
  · imod genHeap_valid $$ [$Hheap $H7] with %hg7
    ipureintro; exact hg7
  have hr0 := fromResolver store Hfacts.1 address (u64Byte value 0) hg0
  have hr1 := fromResolver store Hfacts.1 (address + 1) (u64Byte value 1) hg1
  have hr2 := fromResolver store Hfacts.1 (address + 2) (u64Byte value 2) hg2
  have hr3 := fromResolver store Hfacts.1 (address + 3) (u64Byte value 3) hg3
  have hr4 := fromResolver store Hfacts.1 (address + 4) (u64Byte value 4) hg4
  have hr5 := fromResolver store Hfacts.1 (address + 5) (u64Byte value 5) hg5
  have hr6 := fromResolver store Hfacts.1 (address + 6) (u64Byte value 6) hg6
  have hr7 := fromResolver store Hfacts.1 (address + 7) (u64Byte value 7) hg7
  have hb7 := fromResolverBounds store Hfacts.2.1 (address + 7) (by simp [hg7])
  ipureintro
  constructor
  · simp only [Mem.read8] at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
    simp only [Mem.read64]
    rw [hr0, ← h1, hr1, ← h2, hr2, ← h3, hr3, ← h4, hr4,
      ← h5, hr5, ← h6, hr6, ← h7, hr7]
    exact u64Byte_reassemble value
  · rw [h7] at hb7
    omega

/-- Framed form of `stateInterp_pointsTo_u64_facts`. It returns both the
authoritative state interpretation and the word ownership, allowing a client
to establish physical facts for several disjoint words sequentially. -/
theorem stateInterp_pointsTo_u64_facts_frame [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt64)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3)
    (h4 : (address + 4).toNat = address.toNat + 4)
    (h5 : (address + 5).toNat = address.toNat + 5)
    (h6 : (address + 6).toNat = address.toNat + 6)
    (h7 : (address + 7).toNat = address.toNat + 7) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u64 0 address value ==∗
      stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u64 0 address value ∗
      ⌜store.wasm.mem.read64 address = value ∧
        address.toNat + 8 ≤ store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u64_eq 0 address value).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  ihave %hg0 :
      ⌜get? σ ⟨0, address⟩ = some (some (u64Byte value 0))⌝ $$ [Hheap H0]
  · imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro; exact hg0
  ihave %hg1 :
      ⌜get? σ ⟨0, address + 1⟩ = some (some (u64Byte value 1))⌝ $$ [Hheap H1]
  · imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro; exact hg1
  ihave %hg2 :
      ⌜get? σ ⟨0, address + 2⟩ = some (some (u64Byte value 2))⌝ $$ [Hheap H2]
  · imod genHeap_valid $$ [$Hheap $H2] with %hg2
    ipureintro; exact hg2
  ihave %hg3 :
      ⌜get? σ ⟨0, address + 3⟩ = some (some (u64Byte value 3))⌝ $$ [Hheap H3]
  · imod genHeap_valid $$ [$Hheap $H3] with %hg3
    ipureintro; exact hg3
  ihave %hg4 :
      ⌜get? σ ⟨0, address + 4⟩ = some (some (u64Byte value 4))⌝ $$ [Hheap H4]
  · imod genHeap_valid $$ [$Hheap $H4] with %hg4
    ipureintro; exact hg4
  ihave %hg5 :
      ⌜get? σ ⟨0, address + 5⟩ = some (some (u64Byte value 5))⌝ $$ [Hheap H5]
  · imod genHeap_valid $$ [$Hheap $H5] with %hg5
    ipureintro; exact hg5
  ihave %hg6 :
      ⌜get? σ ⟨0, address + 6⟩ = some (some (u64Byte value 6))⌝ $$ [Hheap H6]
  · imod genHeap_valid $$ [$Hheap $H6] with %hg6
    ipureintro; exact hg6
  ihave %hg7 :
      ⌜get? σ ⟨0, address + 7⟩ = some (some (u64Byte value 7))⌝ $$ [Hheap H7]
  · imod genHeap_valid $$ [$Hheap $H7] with %hg7
    ipureintro; exact hg7
  have hr0 := fromResolver store Hfacts.1 address (u64Byte value 0) hg0
  have hr1 := fromResolver store Hfacts.1 (address + 1) (u64Byte value 1) hg1
  have hr2 := fromResolver store Hfacts.1 (address + 2) (u64Byte value 2) hg2
  have hr3 := fromResolver store Hfacts.1 (address + 3) (u64Byte value 3) hg3
  have hr4 := fromResolver store Hfacts.1 (address + 4) (u64Byte value 4) hg4
  have hr5 := fromResolver store Hfacts.1 (address + 5) (u64Byte value 5) hg5
  have hr6 := fromResolver store Hfacts.1 (address + 6) (u64Byte value 6) hg6
  have hr7 := fromResolver store Hfacts.1 (address + 7) (u64Byte value 7) hg7
  have hb7 := fromResolverBounds store Hfacts.2.1 (address + 7) (by simp [hg7])
  have hread : store.wasm.mem.read64 address = value := by
    simp only [Mem.read8] at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
    simp only [Mem.read64]
    rw [hr0, ← h1, hr1, ← h2, hr2, ← h3, hr3, ← h4, hr4,
      ← h5, hr5, ← h6, hr6, ← h7, hr7]
    exact u64Byte_reassemble value
  have hbound :
      address.toNat + 8 ≤ store.wasm.mem.pages * 65536 := by
    rw [h7] at hb7
    omega
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe
    ipureintro
    exact Hfacts
  · isplitl [H0 H1 H2 H3 H4 H5 H6 H7]
    · iapply (pointsTo_u64_eq 0 address value).mpr
      iframe
    · ipureintro
      exact ⟨hread, hbound⟩

theorem stateInterp_store8 [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (oldValue newValue : UInt8)
    (hbound : address.toNat < store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some oldValue) ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.write8 address newValue } }
        steps observations threads ∗
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some newValue) := by
  iintro ⟨Hstate, Hpointsto⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  imod genHeap_update (v₂ := some newValue) $$ [$Hheap $Hpointsto] with
    ⟨Hheap, Hpointsto⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write8 address newValue } }
      steps observations threads).mpr
    iexists insert σ ⟨0, address⟩ (some newValue)
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
    ipureintro
    have h_ag := store_sound σ (storeResolve store) 0 store.wasm.mem address newValue
        (storeResolve_zero store) Hfacts.1
    rw [storeResolve_update_mem0] at h_ag
    have h_bn := store_inBounds σ (storeResolve store) 0 store.wasm.mem address newValue
        (storeResolve_zero store) Hfacts.2.1 hbound
    rw [storeResolve_update_mem0] at h_bn
    exact ⟨h_ag, h_bn, Hfacts.2.2⟩
  · iexact Hpointsto

theorem stateInterp_pointsTo_u16_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address value : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u16 0 address value ==∗
      ⌜address.toNat + 2 ≤ store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u16_eq 0 address value).mp $$ Hword
  icases Hword with ⟨H0, H1⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  ihave %hg1 :
      ⌜get? σ ⟨0, address + 1⟩ = some (some (u32Byte value 1))⌝ $$ [Hheap H1]
  · imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro
    exact hg1
  have hb1 := fromResolverBounds store Hfacts.2.1 (address + 1) (by simp [hg1])
  ipureintro
  rw [h1] at hb1
  omega

theorem stateInterp_store16 [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address oldValue newValue : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (hbound : address.toNat + 2 ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u16 0 address oldValue ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.write16 address newValue } }
        steps observations threads ∗
      pointsTo_u16 0 address newValue := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u16_eq 0 address oldValue).mp $$ Hword
  icases Hword with ⟨H0, H1⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 0)) $$
      [$Hheap $H0] with ⟨Hheap, H0⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 1)) $$
      [$Hheap $H1] with ⟨Hheap, H1⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write16 address newValue } }
      steps observations threads).mpr
    iexists store16Heap σ 0 address newValue
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    unfold store16Heap
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
    ipureintro
    have h_ag := store16_sound σ (storeResolve store) 0 store.wasm.mem address newValue
        (storeResolve_zero store) h1 Hfacts.1
    rw [storeResolve_update_mem0] at h_ag
    have h_bn := store16_inBounds σ (storeResolve store) 0 store.wasm.mem address newValue
        (storeResolve_zero store) h1 Hfacts.2.1 hbound
    rw [storeResolve_update_mem0] at h_bn
    exact ⟨h_ag, h_bn, Hfacts.2.2⟩
  · iapply (pointsTo_u16_eq 0 address newValue).mpr
    iframe

theorem stateInterp_store32 [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address oldValue newValue : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3)
    (hbound : address.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u32 0 address oldValue ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.write32 address newValue } }
        steps observations threads ∗
      pointsTo_u32 0 address newValue := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u32_eq 0 address oldValue).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 0)) $$
      [$Hheap $H0] with ⟨Hheap, H0⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 1)) $$
      [$Hheap $H1] with ⟨Hheap, H1⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 2)) $$
      [$Hheap $H2] with ⟨Hheap, H2⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 3)) $$
      [$Hheap $H3] with ⟨Hheap, H3⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write32 address newValue } }
      steps observations threads).mpr
    iexists store32Heap σ 0 address newValue
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    unfold store32Heap
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
    ipureintro
    have h_ag := store32_sound σ (storeResolve store) 0 store.wasm.mem address newValue
        (storeResolve_zero store) h1 h2 h3 Hfacts.1
    rw [storeResolve_update_mem0] at h_ag
    have h_bn := store32_inBounds σ (storeResolve store) 0 store.wasm.mem address newValue
        (storeResolve_zero store) h1 h2 h3 Hfacts.2.1 hbound
    rw [storeResolve_update_mem0] at h_bn
    exact ⟨h_ag, h_bn, Hfacts.2.2⟩
  · iapply (pointsTo_u32_eq 0 address newValue).mpr
    iframe

theorem stateInterp_store64 [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (oldValue newValue : UInt64)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3)
    (h4 : (address + 4).toNat = address.toNat + 4)
    (h5 : (address + 5).toNat = address.toNat + 5)
    (h6 : (address + 6).toNat = address.toNat + 6)
    (h7 : (address + 7).toNat = address.toNat + 7)
    (hbound : address.toNat + 8 ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u64 0 address oldValue ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.write64 address newValue } }
        steps observations threads ∗
      pointsTo_u64 0 address newValue := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u64_eq 0 address oldValue).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  imod genHeap_update (v₂ := some (u64Byte newValue 0)) $$
      [$Hheap $H0] with ⟨Hheap, H0⟩
  imod genHeap_update (v₂ := some (u64Byte newValue 1)) $$
      [$Hheap $H1] with ⟨Hheap, H1⟩
  imod genHeap_update (v₂ := some (u64Byte newValue 2)) $$
      [$Hheap $H2] with ⟨Hheap, H2⟩
  imod genHeap_update (v₂ := some (u64Byte newValue 3)) $$
      [$Hheap $H3] with ⟨Hheap, H3⟩
  imod genHeap_update (v₂ := some (u64Byte newValue 4)) $$
      [$Hheap $H4] with ⟨Hheap, H4⟩
  imod genHeap_update (v₂ := some (u64Byte newValue 5)) $$
      [$Hheap $H5] with ⟨Hheap, H5⟩
  imod genHeap_update (v₂ := some (u64Byte newValue 6)) $$
      [$Hheap $H6] with ⟨Hheap, H6⟩
  imod genHeap_update (v₂ := some (u64Byte newValue 7)) $$
      [$Hheap $H7] with ⟨Hheap, H7⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write64 address newValue } }
      steps observations threads).mpr
    iexists store64Heap σ 0 address newValue
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    unfold store64Heap
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
    ipureintro
    have h_ag := store64_sound σ (storeResolve store) 0 store.wasm.mem address newValue
        (storeResolve_zero store) h1 h2 h3 h4 h5 h6 h7 Hfacts.1
    rw [storeResolve_update_mem0] at h_ag
    have h_bn := store64_inBounds σ (storeResolve store) 0 store.wasm.mem address newValue
        (storeResolve_zero store) h1 h2 h3 h4 h5 h6 h7 Hfacts.2.1 hbound
    rw [storeResolve_update_mem0] at h_bn
    exact ⟨h_ag, h_bn, Hfacts.2.2⟩
  · iapply (pointsTo_u64_eq 0 address newValue).mpr
    iframe

/-- Successful memory growth preserves the authoritative byte heap unchanged:
physical bytes are identical and every previously owned address remains in
bounds because the page count only increases. -/
theorem stateInterp_memoryGrow [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (delta : UInt32) (memory : Mem) (previousPages : Nat)
    (hgrow : store.wasm.mem.grow delta store.runtime.currentModule.memoryCap =
      some (memory, previousPages)) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ⊢
      stateInterp (GF := WasmHeapGF α)
        { store with wasm := { store.wasm with mem := memory } }
        steps observations threads := by
  iintro Hstate
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  iapply (stateInterp_eq
    { store with wasm := { store.wasm with mem := memory } }
    steps observations threads).mpr
  iexists σ
  iexists globalσ
  iexists dataSegmentσ
  iexists tableσ
  iexists elementSegmentσ
  iexists runtimeModuleσ
  iexists hostEnvσ
  iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
  ipureintro
  have h_ag := grow_sound σ (storeResolve store) 0 store.wasm.mem memory delta
      store.runtime.currentModule.memoryCap previousPages hgrow (storeResolve_zero store) Hfacts.1
  rw [storeResolve_update_mem0] at h_ag
  have h_bn := grow_inBounds σ (storeResolve store) 0 store.wasm.mem memory delta
      store.runtime.currentModule.memoryCap previousPages hgrow (storeResolve_zero store) Hfacts.2.1
  rw [storeResolve_update_mem0] at h_bn
  exact ⟨h_ag, h_bn, Hfacts.2.2⟩

/-- After a host-call `.Return`, the store's `wasm` field is replaced by the
host-returned store. `runtime` is unchanged and the host's mutable state is
unchanged (`h_host`), so all ghost authorities are preserved; agreement must be
re-established by the caller for each component that the host may have
modified. -/
theorem stateInterp_hostCallReturn [WasmSmallStepGS hlc α]
    (store : MachineStore α) (newWasm : Store α)
    (steps : Nat) (observations : List StepKind) (threads : Nat)
    (h_host : newWasm.host = store.wasm.host) :
    (∀ σ, heapAgreesWithMem σ (storeResolve store) →
          heapAgreesWithMem σ (storeResolve { store with wasm := newWasm })) →
    (∀ σ, heapAddressesInBounds σ (storeResolve store) →
          heapAddressesInBounds σ (storeResolve { store with wasm := newWasm })) →
    (∀ σ, globalHeapAgrees σ store.wasm.globals →
          globalHeapAgrees σ newWasm.globals) →
    (∀ σ, dataSegmentHeapAgrees σ store.wasm.dataSegments →
          dataSegmentHeapAgrees σ newWasm.dataSegments) →
    (∀ σ, tableHeapAgrees σ store.wasm.tables →
          tableHeapAgrees σ newWasm.tables) →
    (∀ σ, elementSegmentHeapAgrees σ store.wasm.elementSegments →
          elementSegmentHeapAgrees σ newWasm.elementSegments) →
    stateInterp (GF := WasmHeapGF α) store steps observations threads ⊢
      stateInterp (GF := WasmHeapGF α) { store with wasm := newWasm }
        steps observations threads := by
  intro hMem hBounds hGlobals hData hTables hElems
  iintro Hstate
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  iapply (stateInterp_eq
    { store with wasm := newWasm }
    steps observations threads).mpr
  iexists σ
  iexists globalσ
  iexists dataSegmentσ
  iexists tableσ
  iexists elementSegmentσ
  iexists runtimeModuleσ
  iexists hostEnvσ
  ihave Hstate_auth' : hostStateAuth newWasm.host $$ [Hstate_auth]
  · rw [h_host]; iexact Hstate_auth
  iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth'
  ipureintro
  exact ⟨hMem σ Hfacts.1, hBounds σ Hfacts.2.1, hGlobals globalσ Hfacts.2.2.1,
    hData dataSegmentσ Hfacts.2.2.2.1, hTables tableσ Hfacts.2.2.2.2.1,
    hElems elementSegmentσ Hfacts.2.2.2.2.2.1, Hfacts.2.2.2.2.2.2.1, Hfacts.2.2.2.2.2.2.2⟩

private theorem currentInstanceAuth_ownN_agree {α : Type} [gs : WasmInstanceGS α]
    (id : ModuleInstanceId) (n : Nat) :
    currentInstanceAuth (α := α) id ∗ currentInstanceOwnN n ⊢ ⌜id.id = n⌝ := by
  unfold currentInstanceAuth; exact currentInstanceOwnN_agree id.id n

/-- Extract the host env agreement from stateInterp by combining with a
`hostEnvOwn` witness. -/
theorem stateInterp_hostEnv [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (instanceId : Nat) (env : HostEnv α) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      currentInstanceOwnN (α := α) instanceId ∗ hostEnvOwn instanceId env ==∗
      ⌜store.runtime.currentHost = env⌝ := by
  iintro ⟨Hstate, Hid, Henv_expected⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  icombine HinstanceAuth Hid as Hentry
  ihave %hentry := currentInstanceAuth_ownN_agree store.runtime.entry instanceId $$ Hentry
  ihave %hlookup := hostEnvOwn_lookup $$ HhostEnvAuth Henv_expected
  ipureintro
  have hinst := Hfacts.2.2.2.2.2.2.2 instanceId env hlookup
  rw [← hentry] at hinst
  simp only [RuntimeEnv.currentHost, RuntimeEnv.currentInstance]
  rcases h : store.runtime.instances[store.runtime.entry.id]? with _ | inst
  · rw [h, Option.map_none] at hinst; simp at hinst
  · rw [h, Option.map_some, Option.some.injEq] at hinst
    have hget : store.runtime.instances[store.runtime.entry.id]! = inst := by
      simp only [getElem!_def, h]
    rw [hget]; exact hinst

/-- Four-byte fill update used by the manual memory example. Ownership of the
whole affected range is required and is updated atomically. -/
theorem stateInterp_fill16_four_AB [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (oldWord : UInt32)
    (hbound : 20 ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u32 0 16 oldWord ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.fill 16 4 0xAB } }
        steps observations threads ∗
      pointsTo_u32 0 16 0xABABABAB := by
  iintro ⟨Hstate, Hword⟩
  imod stateInterp_store32 store steps observations threads
      16 oldWord 0xABABABAB rfl rfl rfl hbound $$
      [$Hstate $Hword] with ⟨Hstate, Hword⟩
  imodintro
  isplitl [Hstate]
  · rw [fill16_four_AB_eq_write32]
    iexact Hstate
  · iexact Hword

/-- Four-byte passive-segment initialization used by the manual Iris example.
The segment itself is read-only during `memory.init`; only the destination
word changes. -/
theorem stateInterp_init16_four [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (oldWord : UInt32)
    (hbound : 20 ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u32 0 16 oldWord ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.writeBytesFrom 16 [1, 2, 3, 4] 0 4 } }
        steps observations threads ∗
      pointsTo_u32 0 16 0x04030201 := by
  iintro ⟨Hstate, Hword⟩
  imod stateInterp_store32 store steps observations threads
      16 oldWord 0x04030201 rfl rfl rfl hbound $$
      [$Hstate $Hword] with ⟨Hstate, Hword⟩
  imodintro
  isplitl [Hstate]
  · rw [init16_four_eq_write32]
    iexact Hstate
  · iexact Hword

/-- Aligned four-byte copy used by the manual Iris example. Source ownership
is framed, while complete destination ownership is updated atomically. -/
theorem stateInterp_copy8_zero_four [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (oldDestination : UInt32) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u32 0 0 0x04030201 ∗ pointsTo_u32 0 8 oldDestination ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.copy 8 0 4 } }
        steps observations threads ∗
      pointsTo_u32 0 0 0x04030201 ∗ pointsTo_u32 0 8 0x04030201 := by
  iintro ⟨Hstate, Hsource, Hdestination⟩
  ihave %HsourceFacts :
      ⌜store.wasm.mem.read32 0 = 0x04030201 ∧
        4 ≤ store.wasm.mem.pages * 65536⌝ $$ [Hstate Hsource]
  · imod stateInterp_pointsTo_u32_facts store steps observations threads
      0 0x04030201 rfl rfl rfl $$ [$Hstate $Hsource] with %HsourceFacts
    ipureintro
    exact HsourceFacts
  ihave %HdestinationFacts :
      ⌜store.wasm.mem.read32 8 = oldDestination ∧
        12 ≤ store.wasm.mem.pages * 65536⌝ $$ [Hstate Hdestination]
  · imod stateInterp_pointsTo_u32_facts store steps observations threads
      8 oldDestination rfl rfl rfl $$ [$Hstate $Hdestination]
      with %HdestinationFacts
    ipureintro
    exact HdestinationFacts
  imod stateInterp_store32 store steps observations threads
      8 oldDestination 0x04030201 rfl rfl rfl HdestinationFacts.2 $$
      [$Hstate $Hdestination] with ⟨Hstate, Hdestination⟩
  imodintro
  isplitl [Hstate]
  · rw [copy8_zero_four_eq_write32 store.wasm.mem HsourceFacts.1]
    iexact Hstate
  · iframe

/-- Overlapping four-byte copy from address 0 to address 2.  One eight-byte
owner covers the overlapping source and destination, and the ghost update
uses the pre-copy source bytes, matching WebAssembly memmove semantics. -/
theorem stateInterp_copy2_zero_four [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u64 0 0 0x8877665544332211 ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.copy 2 0 4 } }
        steps observations threads ∗
      pointsTo_u64 0 0 0x8877443322112211 := by
  iintro ⟨Hstate, Hword⟩
  imod stateInterp_pointsTo_u64_facts_frame
      store steps observations threads
      0 0x8877665544332211 rfl rfl rfl rfl rfl rfl rfl $$
      [$Hstate $Hword] with ⟨Hstate, Hword, %Hfacts⟩
  ihave Hword :=
    (pointsTo_u64_eq 0 0 0x8877665544332211).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  ihave H2At :
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, 2⟩ (DFrac.own 1) (some (u64Byte 0x8877665544332211 2)) $$ [H2]
  · rw [show (⟨0, (0 : UInt32) + 2⟩ : MemoryKey) = ⟨0, 2⟩ by decide]
    iexact H2
  ihave H3At :
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, 3⟩ (DFrac.own 1) (some (u64Byte 0x8877665544332211 3)) $$ [H3]
  · rw [show (⟨0, (0 : UInt32) + 3⟩ : MemoryKey) = ⟨0, 3⟩ by decide]
    iexact H3
  ihave H4At :
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, 4⟩ (DFrac.own 1) (some (u64Byte 0x8877665544332211 4)) $$ [H4]
  · rw [show (⟨0, (0 : UInt32) + 4⟩ : MemoryKey) = ⟨0, 4⟩ by decide]
    iexact H4
  ihave H5At :
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, 5⟩ (DFrac.own 1) (some (u64Byte 0x8877665544332211 5)) $$ [H5]
  · rw [show (⟨0, (0 : UInt32) + 5⟩ : MemoryKey) = ⟨0, 5⟩ by decide]
    iexact H5
  imod stateInterp_store8 store steps observations threads
      2 (u64Byte 0x8877665544332211 2) 0x11 (by
        simp only [UInt32.toNat_ofNat] at Hfacts ⊢
        omega) $$
      [$Hstate $H2At] with ⟨Hstate, H2⟩
  imod stateInterp_store8
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write8 2 0x11 } }
      steps observations threads 3
        (u64Byte 0x8877665544332211 3) 0x22 (by
        simp only [Mem.write8]
        simp only [UInt32.toNat_ofNat] at Hfacts ⊢
        omega) $$ [$Hstate $H3At] with ⟨Hstate, H3⟩
  imod stateInterp_store8
      { store with wasm :=
          { store.wasm with mem :=
              (store.wasm.mem.write8 2 0x11).write8 3 0x22 } }
      steps observations threads 4
        (u64Byte 0x8877665544332211 4) 0x33 (by
        simp only [Mem.write8]
        simp only [UInt32.toNat_ofNat] at Hfacts ⊢
        omega) $$ [$Hstate $H4At] with ⟨Hstate, H4⟩
  imod stateInterp_store8
      { store with wasm :=
          { store.wasm with mem :=
              ((store.wasm.mem.write8 2 0x11).write8 3 0x22).write8 4 0x33 } }
      steps observations threads 5
        (u64Byte 0x8877665544332211 5) 0x44 (by
        simp only [Mem.write8]
        simp only [UInt32.toNat_ofNat] at Hfacts ⊢
        omega) $$ [$Hstate $H5At] with ⟨Hstate, H5⟩
  imodintro
  isplitl [Hstate]
  · rw [copy2_zero_four_eq_write64 store.wasm.mem Hfacts.1]
    iexact Hstate
  · iapply (pointsTo_u64_eq 0 0 0x8877443322112211).mpr
    rw [show u64Byte 0x8877443322112211 0 =
        u64Byte 0x8877665544332211 0 by decide]
    rw [show u64Byte 0x8877443322112211 1 =
        u64Byte 0x8877665544332211 1 by decide]
    rw [show u64Byte 0x8877443322112211 2 = (0x11 : UInt8) by decide]
    rw [show u64Byte 0x8877443322112211 3 = (0x22 : UInt8) by decide]
    rw [show u64Byte 0x8877443322112211 4 = (0x33 : UInt8) by decide]
    rw [show u64Byte 0x8877443322112211 5 = (0x44 : UInt8) by decide]
    rw [show u64Byte 0x8877443322112211 6 =
        u64Byte 0x8877665544332211 6 by decide]
    rw [show u64Byte 0x8877443322112211 7 =
        u64Byte 0x8877665544332211 7 by decide]
    simp only [UInt32.reduceAdd]
    iframe

instance instIrisGS [WasmSmallStepGS hlc α] :
    IrisGS_gen hlc (Expr α) (WasmHeapGF α) where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

end Wasm.SmallStep
