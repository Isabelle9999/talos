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

class WasmSmallStepGS (hlc : outParam HasLC) (Î± : outParam Type) extends
    InvGS_gen hlc (WasmHeapGF α), WasmHeapGS α where
  global : WasmGlobalGS α
  dataSegment : WasmDataSegmentGS α
  table : WasmTableGS α
  elementSegment : WasmElementSegmentGS α
  exception : WasmExceptionGS α
  runtime : WasmRuntimeModuleGS Î±
  host : WasmHostGS Î±

attribute [instance] WasmSmallStepGS.toInvGS_gen
attribute [instance] WasmSmallStepGS.toWasmHeapGS
attribute [reducible, instance] WasmSmallStepGS.global
attribute [reducible, instance] WasmSmallStepGS.dataSegment
attribute [reducible, instance] WasmSmallStepGS.table
attribute [reducible, instance] WasmSmallStepGS.elementSegment
attribute [reducible, instance] WasmSmallStepGS.exception
attribute [reducible, instance] WasmSmallStepGS.runtime
attribute [reducible, instance] WasmSmallStepGS.host

instance instStateInterp [WasmSmallStepGS hlc Î±] :
    StateInterp (MachineStore Î±) StepKind (WasmHeapGF Î±) where
  stateInterp store _ _ _ := iprop%
    âˆƒ Ïƒ : WasmHeapMap (Option UInt8),
      âˆƒ globalÏƒ : WasmGlobalMap Value,
      âˆƒ dataSegmentÏƒ : WasmDataSegmentMap (Option (List UInt8)),
      âˆƒ tableÏƒ : WasmTableMap TableInst,
      âˆƒ elementSegmentÏƒ :
        WasmElementSegmentMap (Option (List (Option Nat))),
      âˆƒ exceptionÏƒ : WasmExceptionMap (Nat Ã— List Value),
      genHeapInterp Ïƒ âˆ—
        ghost_map_auth WasmSmallStepGS.global.globalName
          (DFrac.own 1) globalÏƒ âˆ—
        ghost_map_auth WasmSmallStepGS.dataSegment.dataSegmentName
          (DFrac.own 1) dataSegmentÏƒ âˆ—
        ghost_map_auth WasmSmallStepGS.table.tableName
          (DFrac.own 1) tableÏƒ âˆ—
        ghost_map_auth
          WasmSmallStepGS.elementSegment.elementSegmentName
          (DFrac.own 1) elementSegmentÏƒ âˆ—
        ghost_map_auth WasmSmallStepGS.exception.exceptionName
          (DFrac.own 1) exceptionÏƒ âˆ—
        runtimeModuleOwn store.runtime.module âˆ—
        hostStateAuth store.wasm.host âˆ—
      âŒœheapAgreesWithMem Ïƒ store.wasm.mem âˆ§
        heapAddressesInBounds Ïƒ store.wasm.mem âˆ§
        globalHeapAgrees globalÏƒ store.wasm.globals âˆ§
        dataSegmentHeapAgrees dataSegmentÏƒ store.wasm.dataSegments âˆ§
        tableHeapAgrees tableÏƒ store.wasm.tables âˆ§
        elementSegmentHeapAgrees elementSegmentÏƒ
          store.wasm.elementSegments âˆ§
        exceptionHeapAgrees exceptionÏƒ store.wasm.exns âˆ§
        store.wasm.tagIds = List.range store.runtime.module.tags.lengthâŒ

theorem stateInterp_eq [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âŠ£âŠ¢
      (iprop% âˆƒ Ïƒ : WasmHeapMap (Option UInt8),
        âˆƒ globalÏƒ : WasmGlobalMap Value,
        âˆƒ dataSegmentÏƒ : WasmDataSegmentMap (Option (List UInt8)),
        âˆƒ tableÏƒ : WasmTableMap TableInst,
        âˆƒ elementSegmentÏƒ :
          WasmElementSegmentMap (Option (List (Option Nat))),
        âˆƒ exceptionÏƒ : WasmExceptionMap (Nat Ã— List Value),
        genHeapInterp Ïƒ âˆ—
          ghost_map_auth WasmSmallStepGS.global.globalName
            (DFrac.own 1) globalÏƒ âˆ—
          ghost_map_auth WasmSmallStepGS.dataSegment.dataSegmentName
            (DFrac.own 1) dataSegmentÏƒ âˆ—
          ghost_map_auth WasmSmallStepGS.table.tableName
            (DFrac.own 1) tableÏƒ âˆ—
          ghost_map_auth
            WasmSmallStepGS.elementSegment.elementSegmentName
            (DFrac.own 1) elementSegmentÏƒ âˆ—
          ghost_map_auth WasmSmallStepGS.exception.exceptionName
            (DFrac.own 1) exceptionÏƒ âˆ—
          runtimeModuleOwn store.runtime.module âˆ—
          hostStateAuth store.wasm.host âˆ—
        âŒœheapAgreesWithMem Ïƒ store.wasm.mem âˆ§
          heapAddressesInBounds Ïƒ store.wasm.mem âˆ§
          globalHeapAgrees globalÏƒ store.wasm.globals âˆ§
          dataSegmentHeapAgrees dataSegmentÏƒ store.wasm.dataSegments âˆ§
          tableHeapAgrees tableÏƒ store.wasm.tables âˆ§
          elementSegmentHeapAgrees elementSegmentÏƒ
            store.wasm.elementSegments âˆ§
          exceptionHeapAgrees exceptionÏƒ store.wasm.exns âˆ§
          store.wasm.tagIds = List.range store.runtime.module.tags.lengthâŒ) :=
  .rfl

theorem stateInterp_pointsTo_read8 [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt8) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo (GF := WasmHeapGF Î±) (H := WasmHeapMap)
        address (DFrac.own 1) (some value) ==âˆ—
      âŒœstore.wasm.mem.read8 address = valueâŒ := by
  iintro âŸ¨Hstate, HpointstoâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  icases genHeap_valid $$ [$Hheap $Hpointsto] with >%hlookup
  ipureintro
  exact Hfacts.1 address value hlookup

theorem stateInterp_pointsTo_inBounds [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt8) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo (GF := WasmHeapGF Î±) (H := WasmHeapMap)
        address (DFrac.own 1) (some value) ==âˆ—
      âŒœaddress.toNat < store.wasm.mem.pages * 65536âŒ := by
  iintro âŸ¨Hstate, HpointstoâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  icases genHeap_valid $$ [$Hheap $Hpointsto] with >%hlookup
  ipureintro
  exact Hfacts.2.1 address value hlookup

theorem stateInterp_pointsTo_facts [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt8) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo (GF := WasmHeapGF Î±) (H := WasmHeapMap)
        address (DFrac.own 1) (some value) ==âˆ—
      âŒœstore.wasm.mem.read8 address = value âˆ§
        address.toNat < store.wasm.mem.pages * 65536âŒ := by
  iintro âŸ¨Hstate, HpointstoâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  icases genHeap_valid $$ [$Hheap $Hpointsto] with >%hlookup
  ipureintro
  exact âŸ¨Hfacts.1 address value hlookup, Hfacts.2.1 address value hlookupâŸ©

/-- Update the physical and authoritative host state in lockstep. The
exclusive fragment prevents this update while any client still describes a
different host state. -/
theorem stateInterp_host_set [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat) (host : Î±) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      hostStateOwn store.wasm.host ==âˆ—
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm := { store.wasm with host } }
        steps observations threads âˆ— hostStateOwn host := by
  iintro âŸ¨Hstate, HownâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  imod hostState_update store.wasm.host host $$ [$Hhost $Hown] with
    âŸ¨Hhost, HownâŸ©
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  Â· iapply (stateInterp_eq
      { store with wasm := { store.wasm with host } }
      steps observations threads).mpr
    iexists Ïƒ
    iexists globalÏƒ
    iexists dataSegmentÏƒ
    iexists tableÏƒ
    iexists elementSegmentÏƒ
    iexists exceptionÏƒ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
    ipureintro
    exact Hfacts
  Â· iexact Hown

/-- Regression lemma: the client fragment cannot describe a host state that
differs from the physical state protected by `StateInterp`. -/
theorem stateInterp_host_agree [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat) (host : Î±) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      hostStateOwn host âŠ¢ âŒœstore.wasm.host = hostâŒ := by
  iintro âŸ¨Hstate, HownâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%heap, %globals, %segments, %tables, %elements, %exceptions,
      Hheap, Hglobals, Hsegments, Htables, Helements, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  iapply hostState_agree store.wasm.host host
  iframe Hhost Hown

theorem stateInterp_pointsToBytes_agree [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (addr : UInt32) (bytes : List UInt8) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsToBytes addr bytes ==âˆ—
      âŒœâˆ€ i b, bytes[i]? = some b â†’
          store.wasm.mem.read8 (addr + UInt32.ofNat i) = b âˆ§
          (addr + UInt32.ofNat i).toNat < store.wasm.mem.pages * 65536âŒ := by
  induction bytes generalizing addr with
  | nil =>
      iintro âŸ¨-, -âŸ©
      ipureintro
      intro i b h
      simp at h
  | cons b rest ih =>
      iintro âŸ¨Hstate, HbytesâŸ©
      ihave Hbytes := (pointsToBytes_cons addr b rest).mp $$ Hbytes
      icases Hbytes with âŸ¨Hhead, HrestâŸ©
      ihave %hhead :
          âŒœstore.wasm.mem.read8 addr = b âˆ§
            addr.toNat < store.wasm.mem.pages * 65536âŒ $$ [Hstate Hhead]
      Â· imod stateInterp_pointsTo_facts store steps observations threads addr b $$
            [$Hstate $Hhead] with %hhead
        ipureintro; exact hhead
      ihave %hrest :
          âŒœâˆ€ i b', rest[i]? = some b' â†’
            store.wasm.mem.read8 ((addr + 1) + UInt32.ofNat i) = b' âˆ§
            ((addr + 1) + UInt32.ofNat i).toNat <
              store.wasm.mem.pages * 65536âŒ $$ [Hstate Hrest]
      Â· imod (ih (addr + 1)) $$ [$Hstate $Hrest] with %hrest
        ipureintro; exact hrest
      ipureintro
      intro i b' hget
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst hget
          simpa using hhead
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          obtain âŸ¨hmem, hboundâŸ© := hrest j b' hget
          rw [â† byte_offset_succ addr j] at hmem hbound
          exact âŸ¨hmem, hboundâŸ©

private def fillSigma (Ïƒ : WasmHeapMap (Option UInt8)) (addr : UInt32)
    (bytes : List UInt8) (val : UInt8) : WasmHeapMap (Option UInt8) :=
  match bytes with
  | [] => Ïƒ
  | _ :: rest => fillSigma (insert Ïƒ addr (some val)) (addr + 1) rest val

private theorem fillSigma_ghost [WasmSmallStepGS hlc Î±]
    (Ïƒ : WasmHeapMap (Option UInt8)) (addr : UInt32)
    (bytes : List UInt8) (val : UInt8) :
    genHeapInterp Ïƒ âˆ— pointsToBytes addr bytes ==âˆ—
    genHeapInterp (fillSigma Ïƒ addr bytes val) âˆ—
    pointsToBytes addr (List.replicate bytes.length val) := by
  induction bytes generalizing Ïƒ addr with
  | nil =>
      show genHeapInterp Ïƒ âˆ— pointsToBytes addr [] ==âˆ—
           genHeapInterp Ïƒ âˆ— pointsToBytes addr []
      iintro âŸ¨Hheap, HemptyâŸ©
      imodintro
      isplitl [Hheap]
      Â· iexact Hheap
      Â· iexact Hempty
  | cons b rest ih =>
      show genHeapInterp Ïƒ âˆ— pointsToBytes addr (b :: rest) ==âˆ—
           genHeapInterp (fillSigma (insert Ïƒ addr (some val)) (addr + 1) rest val) âˆ—
           pointsToBytes addr (val :: List.replicate rest.length val)
      iintro âŸ¨Hheap, HbytesâŸ©
      ihave Hbytes := (pointsToBytes_cons addr b rest).mp $$ Hbytes
      icases Hbytes with âŸ¨Hhead, HrestâŸ©
      imod genHeap_update (vâ‚‚ := some val) $$ [$Hheap $Hhead] with âŸ¨Hheap, HheadâŸ©
      imod (ih (insert Ïƒ addr (some val)) (addr + 1)) $$ [$Hheap $Hrest] with âŸ¨Hheap, HrestâŸ©
      imodintro
      isplitl [Hheap]
      Â· iexact Hheap
      Â· iapply (pointsToBytes_cons addr val (List.replicate rest.length val)).mpr
        isplitl [Hhead]
        Â· iexact Hhead
        Â· iexact Hrest

private theorem fillSigma_agrees
    (Ïƒ : WasmHeapMap (Option UInt8)) (mem : Mem)
    (addr : UInt32) (bytes : List UInt8) (val : UInt8)
    (hagree : heapAgreesWithMem Ïƒ mem)
    (hnowrap : addr.toNat + bytes.length < 4294967296) :
    heapAgreesWithMem (fillSigma Ïƒ addr bytes val)
      (mem.fill addr.toNat bytes.length val) := by
  induction bytes generalizing Ïƒ addr mem with
  | nil => simp only [fillSigma, List.length_nil, Mem.fill_zero]; exact hagree
  | cons b rest ih =>
      have h1 : (addr + 1).toNat = addr.toNat + 1 := by
        simp only [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]
        simp only [List.length_cons] at hnowrap; omega
      have hnowrap' : (addr + 1).toNat + rest.length < 4294967296 := by
        rw [h1]; simp only [List.length_cons] at hnowrap; omega
      have ih' := ih (insert Ïƒ addr (some val)) (mem.write8 addr val) (addr + 1)
          (store_sound Ïƒ mem addr val hagree) hnowrap'
      rw [h1, Mem.write8_fill_eq] at ih'
      exact ih'

private theorem fillSigma_inBounds
    (Ïƒ : WasmHeapMap (Option UInt8)) (mem : Mem)
    (addr : UInt32) (bytes : List UInt8) (val : UInt8)
    (hinBounds : heapAddressesInBounds Ïƒ mem)
    (hbound : addr.toNat + bytes.length â‰¤ mem.pages * 65536)
    (hnowrap : addr.toNat + bytes.length < 4294967296) :
    heapAddressesInBounds (fillSigma Ïƒ addr bytes val)
      (mem.fill addr.toNat bytes.length val) := by
  induction bytes generalizing Ïƒ addr mem with
  | nil => simp only [fillSigma, List.length_nil, Mem.fill_zero]; exact hinBounds
  | cons b rest ih =>
      have h1 : (addr + 1).toNat = addr.toNat + 1 := by
        simp only [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]
        simp only [List.length_cons] at hnowrap; omega
      have hnowrap' : (addr + 1).toNat + rest.length < 4294967296 := by
        rw [h1]; simp only [List.length_cons] at hnowrap; omega
      have hbound' : (addr + 1).toNat + rest.length â‰¤ (mem.write8 addr val).pages * 65536 := by
        have : (mem.write8 addr val).pages = mem.pages := rfl
        rw [this, h1]; simp only [List.length_cons] at hbound; omega
      have ih' := ih (insert Ïƒ addr (some val)) (mem.write8 addr val) (addr + 1)
          (store_inBounds Ïƒ mem addr val hinBounds
            (by simp only [List.length_cons] at hbound; omega))
          hbound' hnowrap'
      rw [h1, Mem.write8_fill_eq] at ih'
      exact ih'

/-- Ghost update for a bulk memory fill: given ownership of all bytes in the
fill range, updates the stateInterp and returns ownership of the same range
filled with `val`. -/
theorem stateInterp_fill_bytes [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (addr : UInt32) (oldBytes : List UInt8) (val : UInt8)
    (hbound : addr.toNat + oldBytes.length â‰¤ store.wasm.mem.pages * 65536)
    (hnowrap : addr.toNat + oldBytes.length < 4294967296) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsToBytes addr oldBytes ==âˆ—
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.fill addr.toNat oldBytes.length val } }
        steps observations threads âˆ—
      pointsToBytes addr (List.replicate oldBytes.length val) := by
  iintro âŸ¨Hstate, HbytesâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  imod fillSigma_ghost Ïƒ addr oldBytes val $$ [$Hheap $Hbytes] with âŸ¨Hheap, HbytesâŸ©
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  Â· iapply (stateInterp_eq
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.fill addr.toNat oldBytes.length val } }
        steps observations threads).mpr
    iexists fillSigma Ïƒ addr oldBytes val
    iexists globalÏƒ
    iexists dataSegmentÏƒ
    iexists tableÏƒ
    iexists elementSegmentÏƒ
    iexists exceptionÏƒ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
    ipureintro
    exact âŸ¨fillSigma_agrees Ïƒ store.wasm.mem addr oldBytes val Hfacts.1 hnowrap,
      fillSigma_inBounds Ïƒ store.wasm.mem addr oldBytes val Hfacts.2.1 hbound hnowrap,
      Hfacts.2.2âŸ©
  Â· iexact Hbytes

-- ghost map updated by a bulk copy: oldBytes[k] replaced by srcBytes[k] at dst+k
private def copySigma (Ïƒ : WasmHeapMap (Option UInt8)) (dst : UInt32)
    (oldBytes srcBytes : List UInt8) : WasmHeapMap (Option UInt8) :=
  match oldBytes, srcBytes with
  | _ :: oldRest, s :: srcRest => copySigma (insert Ïƒ dst (some s)) (dst + 1) oldRest srcRest
  | _, _ => Ïƒ

-- get? outside [dst, dst+oldBytes.length) is unchanged
private theorem copySigma_get?_out
    (Ïƒ : WasmHeapMap (Option UInt8)) (dst : UInt32)
    (oldBytes srcBytes : List UInt8) (addr : UInt32)
    (hlen : srcBytes.length = oldBytes.length)
    (hnowrap : dst.toNat + oldBytes.length < 4294967296)
    (hout : addr.toNat < dst.toNat âˆ¨ dst.toNat + oldBytes.length â‰¤ addr.toNat) :
    get? (copySigma Ïƒ dst oldBytes srcBytes) addr = get? Ïƒ addr := by
  induction oldBytes generalizing Ïƒ dst srcBytes with
  | nil => simp [copySigma]
  | cons b bRest ih =>
      cases srcBytes with
      | nil => simp at hlen
      | cons s sRest =>
          simp only [copySigma]
          have hlen' : sRest.length = bRest.length := by simpa [List.length_cons] using hlen
          have h1 : (dst + 1).toNat = dst.toNat + 1 := by
            simp only [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]
            simp only [List.length_cons] at hnowrap; omega
          have hnowrap' : (dst + 1).toNat + bRest.length < 4294967296 := by
            rw [h1]; simp only [List.length_cons] at hnowrap; omega
          have hne : addr â‰  dst := by
            intro heq; subst heq; simp only [List.length_cons] at hout; omega
          have hout' : addr.toNat < (dst + 1).toNat âˆ¨ (dst + 1).toNat + bRest.length â‰¤ addr.toNat := by
            rw [h1]; simp only [List.length_cons] at hout; omega
          rw [ih (insert Ïƒ dst (some s)) (dst + 1) sRest hlen' hnowrap' hout',
              get?_insert_ne hne.symm]

-- get? at dst + ofNat j gives some (some srcBytes[j])
private theorem copySigma_get?_in
    (Ïƒ : WasmHeapMap (Option UInt8)) (dst : UInt32)
    (oldBytes srcBytes : List UInt8) (j : Nat)
    (hlen : srcBytes.length = oldBytes.length)
    (hj : j < srcBytes.length)
    (hnowrap : dst.toNat + srcBytes.length < 4294967296) :
    get? (copySigma Ïƒ dst oldBytes srcBytes) (dst + UInt32.ofNat j) =
    some (some (srcBytes[j]'hj)) := by
  induction srcBytes generalizing Ïƒ dst oldBytes j with
  | nil => simp at hj
  | cons s sRest ih =>
      cases oldBytes with
      | nil => simp at hlen
      | cons b bRest =>
          simp only [copySigma]
          have hlen' : sRest.length = bRest.length := by simpa [List.length_cons] using hlen
          have h1 : (dst + 1).toNat = dst.toNat + 1 := by
            simp only [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]
            simp only [List.length_cons] at hnowrap; omega
          have hnowrap' : (dst + 1).toNat + sRest.length < 4294967296 := by
            rw [h1]; simp only [List.length_cons] at hnowrap; omega
          cases j with
          | zero =>
              have h0 : dst + UInt32.ofNat 0 = dst := by
                apply UInt32.toNat_inj.mp
                simp only [UInt32.toNat_add,
                           show (UInt32.ofNat 0 : UInt32).toNat = 0 from rfl]
                simp only [List.length_cons] at hnowrap; omega
              rw [h0]
              simp only [List.getElem_cons_zero]
              rw [copySigma_get?_out (insert Ïƒ dst (some s)) (dst + 1) bRest sRest dst
                    hlen' (by omega) (Or.inl (by rw [h1]; omega)),
                  get?_insert_eq rfl]
          | succ j' =>
              have hj' : j' < sRest.length := by simpa [List.length_cons] using hj
              rw [byte_offset_succ dst j',
                  ih (insert Ïƒ dst (some s)) (dst + 1) bRest j' hlen' hj' hnowrap']
              simp [List.getElem_cons_succ]

-- Iris ghost update: pointsToBytes dst oldBytes â†’ pointsToBytes dst srcBytes
private theorem copySigma_ghost [WasmSmallStepGS hlc Î±]
    (Ïƒ : WasmHeapMap (Option UInt8)) (dst : UInt32)
    (oldBytes srcBytes : List UInt8)
    (hlen : srcBytes.length = oldBytes.length) :
    genHeapInterp Ïƒ âˆ— pointsToBytes dst oldBytes ==âˆ—
    genHeapInterp (copySigma Ïƒ dst oldBytes srcBytes) âˆ—
    pointsToBytes dst srcBytes := by
  induction oldBytes generalizing Ïƒ dst srcBytes with
  | nil =>
      cases srcBytes with
      | nil =>
          show genHeapInterp Ïƒ âˆ— pointsToBytes dst [] ==âˆ—
               genHeapInterp Ïƒ âˆ— pointsToBytes dst []
          iintro âŸ¨Hheap, HemptyâŸ©
          imodintro
          isplitl [Hheap]
          Â· iexact Hheap
          Â· iexact Hempty
      | cons => simp at hlen
  | cons b bRest ih =>
      cases srcBytes with
      | nil => simp at hlen
      | cons s sRest =>
          show genHeapInterp Ïƒ âˆ— pointsToBytes dst (b :: bRest) ==âˆ—
               genHeapInterp (copySigma (insert Ïƒ dst (some s)) (dst + 1) bRest sRest) âˆ—
               pointsToBytes dst (s :: sRest)
          iintro âŸ¨Hheap, HbytesâŸ©
          ihave Hbytes := (pointsToBytes_cons dst b bRest).mp $$ Hbytes
          icases Hbytes with âŸ¨Hhead, HrestâŸ©
          imod genHeap_update (vâ‚‚ := some s) $$ [$Hheap $Hhead] with âŸ¨Hheap, HheadâŸ©
          imod (ih (insert Ïƒ dst (some s)) (dst + 1) sRest
                  (by simpa [List.length_cons] using hlen)) $$
              [$Hheap $Hrest] with âŸ¨Hheap, HrestâŸ©
          imodintro
          isplitl [Hheap]
          Â· iexact Hheap
          Â· iapply (pointsToBytes_cons dst s sRest).mpr
            isplitl [Hhead]
            Â· iexact Hhead
            Â· iexact Hrest

-- heapAgreesWithMem for copySigma, parameterized by the new physical memory
private theorem copySigma_agrees_of_read_eq
    (Ïƒ : WasmHeapMap (Option UInt8)) (mem newMem : Mem)
    (dst : UInt32) (oldBytes srcBytes : List UInt8)
    (hlen : srcBytes.length = oldBytes.length)
    (hagree : heapAgreesWithMem Ïƒ mem)
    (hnowrap : dst.toNat + oldBytes.length < 4294967296)
    (h_in : âˆ€ k b, srcBytes[k]? = some b â†’ newMem.read8 (dst + UInt32.ofNat k) = b)
    (h_out : âˆ€ addr,
        addr.toNat < dst.toNat âˆ¨ dst.toNat + oldBytes.length â‰¤ addr.toNat â†’
        newMem.read8 addr = mem.read8 addr) :
    heapAgreesWithMem (copySigma Ïƒ dst oldBytes srcBytes) newMem := by
  intro addr v hlookup
  by_cases hrange : dst.toNat â‰¤ addr.toNat âˆ§ addr.toNat < dst.toNat + oldBytes.length
  Â· obtain âŸ¨hle, hltâŸ© := hrange
    let k : Nat := addr.toNat - dst.toNat
    have hk : k < srcBytes.length := by omega
    have hget : srcBytes[k]? = some (srcBytes[k]'hk) := List.getElem?_eq_getElem hk
    have h_addr_eq : addr = dst + UInt32.ofNat k := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_add]; show addr.toNat = (dst.toNat + k % 2 ^ 32) % 2 ^ 32; omega
    rw [h_addr_eq] at hlookup
    rw [copySigma_get?_in Ïƒ dst oldBytes srcBytes k hlen hk (hlen â–¸ hnowrap)] at hlookup
    have hv : srcBytes[k]'hk = v := Option.some.inj (Option.some.inj hlookup)
    rw [h_addr_eq]
    exact (h_in k (srcBytes[k]'hk) hget).trans hv
  Â· have hout : addr.toNat < dst.toNat âˆ¨ dst.toNat + oldBytes.length â‰¤ addr.toNat := by omega
    rw [copySigma_get?_out Ïƒ dst oldBytes srcBytes addr hlen hnowrap hout] at hlookup
    rw [h_out addr hout]
    exact hagree addr v hlookup

-- heapAddressesInBounds for copySigma
private theorem copySigma_inBounds
    (Ïƒ : WasmHeapMap (Option UInt8)) (mem newMem : Mem)
    (dst : UInt32) (oldBytes srcBytes : List UInt8)
    (hlen : srcBytes.length = oldBytes.length)
    (hinBounds : heapAddressesInBounds Ïƒ mem)
    (hbound : dst.toNat + oldBytes.length â‰¤ mem.pages * 65536)
    (hnowrap : dst.toNat + oldBytes.length < 4294967296)
    (h_pages : newMem.pages = mem.pages) :
    heapAddressesInBounds (copySigma Ïƒ dst oldBytes srcBytes) newMem := by
  intro addr v hlookup
  rw [h_pages]
  by_cases hrange : dst.toNat â‰¤ addr.toNat âˆ§ addr.toNat < dst.toNat + oldBytes.length
  Â· omega
  Â· have hout : addr.toNat < dst.toNat âˆ¨ dst.toNat + oldBytes.length â‰¤ addr.toNat := by omega
    rw [copySigma_get?_out Ïƒ dst oldBytes srcBytes addr hlen hnowrap hout] at hlookup
    exact hinBounds addr v hlookup

-- helper: (dst + UInt32.ofNat k).toNat = dst.toNat + k when sum < 2^32
private theorem add_ofNat_toNat (dst : UInt32) (k : Nat) (h : dst.toNat + k < 2 ^ 32) :
    (dst + UInt32.ofNat k).toNat = dst.toNat + k := by
  rw [UInt32.toNat_add]; show (dst.toNat + k % 2 ^ 32) % 2 ^ 32 = dst.toNat + k; omega

/-- Ghost update for a bulk memory copy: given ownership of source and
destination byte ranges, updates the stateInterp and returns the destination
range filled with the source bytes (memmove semantics). -/
theorem stateInterp_copy_bytes [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (dst src : UInt32) (oldDstBytes srcBytes : List UInt8)
    (hlen : srcBytes.length = oldDstBytes.length)
    (hdst_bound : dst.toNat + oldDstBytes.length â‰¤ store.wasm.mem.pages * 65536)
    (hdst_nowrap : dst.toNat + oldDstBytes.length < 4294967296)
    (_hsrc_bound : src.toNat + srcBytes.length â‰¤ store.wasm.mem.pages * 65536)
    (hsrc_nowrap : src.toNat + srcBytes.length < 4294967296) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsToBytes src srcBytes âˆ—
      pointsToBytes dst oldDstBytes ==âˆ—
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.copy dst.toNat src.toNat oldDstBytes.length } }
        steps observations threads âˆ—
      pointsToBytes src srcBytes âˆ—
      pointsToBytes dst srcBytes := by
  iintro âŸ¨Hstate, Hsrc, HdstâŸ©
  ihave %hagree :
      âŒœâˆ€ i b, srcBytes[i]? = some b â†’
          store.wasm.mem.read8 (src + UInt32.ofNat i) = b âˆ§
          (src + UInt32.ofNat i).toNat < store.wasm.mem.pages * 65536âŒ $$ [Hstate Hsrc]
  Â· imod stateInterp_pointsToBytes_agree store steps observations threads src srcBytes $$
        [$Hstate $Hsrc] with %hagree
    ipureintro; exact hagree
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  imod copySigma_ghost Ïƒ dst oldDstBytes srcBytes hlen $$ [$Hheap $Hdst] with âŸ¨Hheap, HdstâŸ©
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  Â· iapply (stateInterp_eq
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.copy dst.toNat src.toNat oldDstBytes.length } }
        steps observations threads).mpr
    iexists copySigma Ïƒ dst oldDstBytes srcBytes
    iexists globalÏƒ; iexists dataSegmentÏƒ; iexists tableÏƒ; iexists elementSegmentÏƒ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
    ipureintro
    refine âŸ¨copySigma_agrees_of_read_eq Ïƒ store.wasm.mem
                (store.wasm.mem.copy dst.toNat src.toNat oldDstBytes.length)
                dst oldDstBytes srcBytes hlen Hfacts.1 hdst_nowrap
                (fun k b hget => ?h_in) (fun addr hout => ?h_out),
            copySigma_inBounds Ïƒ store.wasm.mem
                (store.wasm.mem.copy dst.toNat src.toNat oldDstBytes.length)
                dst oldDstBytes srcBytes hlen Hfacts.2.1 hdst_bound hdst_nowrap
                (Mem.copy_pages store.wasm.mem dst.toNat src.toNat oldDstBytes.length),
            Hfacts.2.2âŸ©
    case h_in =>
      have hk : k < srcBytes.length := by
        suffices h : Â¬ srcBytes.length â‰¤ k by omega
        intro hle
        simp [List.getElem?_eq_none hle] at hget
      have h_dst_k := add_ofNat_toNat dst k (by rw [hlen] at hk; omega)
      have h_src_k := add_ofNat_toNat src k (by omega)
      have h_copy := Mem.copy_read8_in store.wasm.mem dst.toNat src.toNat oldDstBytes.length
          (dst + UInt32.ofNat k) âŸ¨by omega, by rw [hlen] at hk; omegaâŸ©
      rw [h_dst_k, Nat.add_sub_cancel_left] at h_copy
      have h_src_read := (hagree k b hget).1
      simp only [Mem.read8, h_src_k] at h_src_read
      exact h_copy.trans h_src_read
    case h_out =>
      exact Mem.copy_read8_out store.wasm.mem dst.toNat src.toNat oldDstBytes.length addr (by omega)
  Â· isplitl [Hsrc]
    Â· iexact Hsrc
    Â· iexact Hdst

/-- Ghost update for a bulk memory init: given ownership of the destination
byte range, updates the stateInterp and returns the range filled with
the corresponding slice of the segment bytes. The segment ghost ownership
is preserved. -/
theorem stateInterp_init_bytes [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (dst : UInt32) (srcOff len : Nat) (segmentIndex : Nat)
    (oldDstBytes : List UInt8) (segmentBytes : List UInt8)
    (hlen : oldDstBytes.length = len)
    (hdst_bound : dst.toNat + len â‰¤ store.wasm.mem.pages * 65536)
    (hdst_nowrap : dst.toNat + len < 4294967296)
    (hsource : srcOff + len â‰¤ segmentBytes.length) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      dataSegmentPointsTo segmentIndex (some segmentBytes) âˆ—
      pointsToBytes dst oldDstBytes ==âˆ—
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.writeBytesFrom dst.toNat segmentBytes srcOff len } }
        steps observations threads âˆ—
      dataSegmentPointsTo segmentIndex (some segmentBytes) âˆ—
      pointsToBytes dst ((segmentBytes.drop srcOff).take len) := by
  let newDstBytes := (segmentBytes.drop srcOff).take len
  have hlen_new : newDstBytes.length = len := by
    simp only [newDstBytes, List.length_take, List.length_drop]; omega
  have hlen_eq : newDstBytes.length = oldDstBytes.length := by omega
  iintro âŸ¨Hstate, Hseg, HdstâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  imod copySigma_ghost Ïƒ dst oldDstBytes newDstBytes hlen_eq $$
      [$Hheap $Hdst] with âŸ¨Hheap, HdstâŸ©
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  Â· iapply (stateInterp_eq
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.writeBytesFrom dst.toNat segmentBytes srcOff len } }
        steps observations threads).mpr
    iexists copySigma Ïƒ dst oldDstBytes newDstBytes
    iexists globalÏƒ; iexists dataSegmentÏƒ; iexists tableÏƒ; iexists elementSegmentÏƒ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
    ipureintro
    refine âŸ¨copySigma_agrees_of_read_eq Ïƒ store.wasm.mem
                (store.wasm.mem.writeBytesFrom dst.toNat segmentBytes srcOff len)
                dst oldDstBytes newDstBytes hlen_eq Hfacts.1 (hlen â–¸ hdst_nowrap)
                (fun k b hget => ?h_in) (fun addr hout => ?h_out),
            copySigma_inBounds Ïƒ store.wasm.mem
                (store.wasm.mem.writeBytesFrom dst.toNat segmentBytes srcOff len)
                dst oldDstBytes newDstBytes hlen_eq Hfacts.2.1 (hlen â–¸ hdst_bound)
                (hlen â–¸ hdst_nowrap)
                (Mem.writeBytesFrom_pages store.wasm.mem dst.toNat segmentBytes srcOff len),
            Hfacts.2.2âŸ©
    case h_in =>
      have hk : k < newDstBytes.length := by
        suffices h : Â¬ newDstBytes.length â‰¤ k by omega
        intro hle
        simp [List.getElem?_eq_none hle] at hget
      have hk_len : k < len := by omega
      have h_dst_k := add_ofNat_toNat dst k (by omega)
      have hbound_seg : srcOff + k < segmentBytes.length := by omega
      have hin : dst.toNat â‰¤ (dst + UInt32.ofNat k).toNat âˆ§
                 (dst + UInt32.ofNat k).toNat < dst.toNat + len := by
        rw [h_dst_k]; constructor <;> omega
      have hbound_actual : srcOff + ((dst + UInt32.ofNat k).toNat - dst.toNat) <
          segmentBytes.length := by
        rw [h_dst_k, Nat.add_sub_cancel_left]; exact hbound_seg
      rw [Mem.writeBytesFrom_read8_in _ _ _ _ _ _ hin hbound_actual]
      have hidx : srcOff + ((dst + UInt32.ofNat k).toNat - dst.toNat) = srcOff + k := by
        rw [h_dst_k, Nat.add_sub_cancel_left]
      have hget_some : newDstBytes[k]? = some (newDstBytes[k]'hk) := List.getElem?_eq_getElem hk
      have hb : b = newDstBytes[k]'hk := Option.some.inj (hget.symm.trans hget_some)
      have hval : newDstBytes[k]'hk = segmentBytes[srcOff + k]'hbound_seg := by
        simp [newDstBytes, List.getElem_take, List.getElem_drop]
      have hboth : segmentBytes[srcOff + ((dst + UInt32.ofNat k).toNat - dst.toNat)]? =
                   segmentBytes[srcOff + k]? := by rw [hidx]
      have hg_actual := List.getElem?_eq_getElem (l := segmentBytes)
                          (i := srcOff + ((dst + UInt32.ofNat k).toNat - dst.toNat)) hbound_actual
      have hg_k := List.getElem?_eq_getElem (l := segmentBytes) (i := srcOff + k) hbound_seg
      exact (Option.some.inj (hg_actual.symm.trans (hboth.trans hg_k))).trans
            (hval.symm.trans hb.symm)
    case h_out =>
      exact Mem.writeBytesFrom_read8_out store.wasm.mem dst.toNat segmentBytes srcOff len addr
          (by omega)
  Â· isplitl [Hseg]
    Â· iexact Hseg
    Â· iexact Hdst

/-- Owned global state determines the corresponding physical instantiated
global. -/
theorem stateInterp_global_facts [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (value : Value) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      globalPointsTo index value ==âˆ—
      âŒœstore.wasm.globals.globals[index]? = some valueâŒ := by
  iintro âŸ¨Hstate, HglobalâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  ihave %hlookup := globalPointsTo_lookup globalÏƒ index value $$ Hglobals Hglobal
  ipureintro
  exact Hfacts.2.2.1 index value hlookup

/-- Updating an owned global updates both the authoritative ghost map and the
physical instantiated global array in lockstep. -/
theorem stateInterp_global_set [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (oldValue newValue : Value) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      globalPointsTo index oldValue ==âˆ—
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm :=
            { store.wasm with globals :=
                { globals := store.wasm.globals.globals.set index newValue } } }
        steps observations threads âˆ—
      globalPointsTo index newValue := by
  iintro âŸ¨Hstate, HglobalâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  ihave %hlookup :=
    globalPointsTo_lookup globalÏƒ index oldValue $$ Hglobals Hglobal
  imod globalPointsTo_update globalÏƒ index oldValue newValue $$
      Hglobals Hglobal with
    âŸ¨Hglobals, HglobalâŸ©
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  Â· iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with globals :=
              { globals := store.wasm.globals.globals.set index newValue } } }
      steps observations threads).mpr
    iexists Ïƒ
    iexists insert globalÏƒ index newValue
    iexists dataSegmentÏƒ
    iexists tableÏƒ
    iexists elementSegmentÏƒ
    iexists exceptionÏƒ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
    ipureintro
    exact âŸ¨Hfacts.1, Hfacts.2.1,
      âŸ¨global_store_sound globalÏƒ store.wasm.globals
          index oldValue newValue Hfacts.2.2.1 hlookup,
        Hfacts.2.2.2âŸ©âŸ©
  Â· iexact Hglobal

/-- Owned passive-segment state determines the corresponding physical
instantiated segment entry. The framed form keeps both resources available for
a following `memory.init` or `data.drop` transition. -/
theorem stateInterp_dataSegment_facts_frame [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (value : Option (List UInt8)) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      dataSegmentPointsTo index value ==âˆ—
      stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      dataSegmentPointsTo index value âˆ—
      âŒœstore.wasm.dataSegments[index]? = some valueâŒ := by
  iintro âŸ¨Hstate, HsegmentâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  ihave %hlookup :=
    dataSegmentPointsTo_lookup dataSegmentÏƒ index value $$
      Hsegments Hsegment
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  Â· iapply (stateInterp_eq store steps observations threads).mpr
    iexists Ïƒ
    iexists globalÏƒ
    iexists dataSegmentÏƒ
    iexists tableÏƒ
    iexists elementSegmentÏƒ
    iexists exceptionÏƒ
    iframe
    ipureintro
    exact Hfacts
  Â· isplitl [Hsegment]
    Â· iexact Hsegment
    Â· ipureintro
      exact Hfacts.2.2.2.1 index value hlookup

/-- `data.drop` updates the physical segment status and its authoritative
ghost entry in lockstep. -/
theorem stateInterp_dataSegment_drop [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (oldValue : Option (List UInt8)) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      dataSegmentPointsTo index oldValue ==âˆ—
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm :=
            { store.wasm with
              dataSegments := store.wasm.dataSegments.set index none } }
        steps observations threads âˆ—
      dataSegmentPointsTo index none := by
  iintro âŸ¨Hstate, HsegmentâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  ihave %hlookup :=
    dataSegmentPointsTo_lookup dataSegmentÏƒ index oldValue $$
      Hsegments Hsegment
  imod dataSegmentPointsTo_update dataSegmentÏƒ index oldValue none $$
      Hsegments Hsegment with
    âŸ¨Hsegments, HsegmentâŸ©
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  Â· iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with
            dataSegments := store.wasm.dataSegments.set index none } }
      steps observations threads).mpr
    iexists Ïƒ
    iexists globalÏƒ
    iexists insert dataSegmentÏƒ index none
    iexists tableÏƒ
    iexists elementSegmentÏƒ
    iexists exceptionÏƒ
    iframe
    ipureintro
    exact âŸ¨Hfacts.1, Hfacts.2.1, Hfacts.2.2.1,
      dataSegment_store_sound dataSegmentÏƒ store.wasm.dataSegments
        index oldValue none Hfacts.2.2.2.1 hlookup,
      Hfacts.2.2.2.2âŸ©
  Â· iexact Hsegment

/-- Element-segment ownership identifies the live or dropped state at the
corresponding stable physical segment index. -/
theorem stateInterp_elementSegment_facts_frame [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (value : Option (List (Option Nat))) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      elementSegmentPointsTo index value ==âˆ—
      stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      elementSegmentPointsTo index value âˆ—
      âŒœstore.wasm.elementSegments[index]? = some valueâŒ := by
  iintro âŸ¨Hstate, HsegmentâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  ihave %hlookup :=
    elementSegmentPointsTo_lookup elementSegmentÏƒ index value $$
      HelementSegments Hsegment
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  Â· iapply (stateInterp_eq store steps observations threads).mpr
    iexists Ïƒ
    iexists globalÏƒ
    iexists dataSegmentÏƒ
    iexists tableÏƒ
    iexists elementSegmentÏƒ
    iexists exceptionÏƒ
    iframe
    ipureintro
    exact Hfacts
  Â· isplitl [Hsegment]
    Â· iexact Hsegment
    Â· ipureintro
      exact Hfacts.2.2.2.2.2.1 index value hlookup

/-- `elem.drop` changes the physical segment status and authoritative ghost
entry to `none` without renumbering any segment. -/
theorem stateInterp_elementSegment_drop [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (oldValue : Option (List (Option Nat))) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      elementSegmentPointsTo index oldValue ==âˆ—
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm :=
            { store.wasm with
              elementSegments :=
                store.wasm.elementSegments.set index none } }
        steps observations threads âˆ—
      elementSegmentPointsTo index none := by
  iintro âŸ¨Hstate, HsegmentâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  ihave %hlookup :=
    elementSegmentPointsTo_lookup elementSegmentÏƒ index oldValue $$
      HelementSegments Hsegment
  imod elementSegmentPointsTo_update
      elementSegmentÏƒ index oldValue none $$
      HelementSegments Hsegment with
    âŸ¨HelementSegments, HsegmentâŸ©
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  Â· iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with
            elementSegments :=
              store.wasm.elementSegments.set index none } }
      steps observations threads).mpr
    iexists Ïƒ
    iexists globalÏƒ
    iexists dataSegmentÏƒ
    iexists tableÏƒ
    iexists insert elementSegmentÏƒ index none
    iexists exceptionÏƒ
    iframe
    ipureintro
    exact âŸ¨Hfacts.1, Hfacts.2.1, Hfacts.2.2.1,
      Hfacts.2.2.2.1,
      âŸ¨Hfacts.2.2.2.2.1,
        elementSegment_store_sound elementSegmentÏƒ
          store.wasm.elementSegments index oldValue none
          Hfacts.2.2.2.2.2.1 hlookup,
        Hfacts.2.2.2.2.2.2âŸ©âŸ©
  Â· iexact Hsegment

/-- Owning a table fragment identifies the complete physical instantiated
table at its stable table index. -/
theorem stateInterp_table_facts_frame [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (table : TableInst) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      tablePointsTo index table ==âˆ—
      stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      tablePointsTo index table âˆ—
      âŒœstore.wasm.tables[index]? = some tableâŒ := by
  iintro âŸ¨Hstate, HtableâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  ihave %hlookup :=
    tablePointsTo_lookup tableÏƒ index table $$ Htables Htable
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  Â· iapply (stateInterp_eq store steps observations threads).mpr
    iexists Ïƒ
    iexists globalÏƒ
    iexists dataSegmentÏƒ
    iexists tableÏƒ
    iexists elementSegmentÏƒ
    iexists exceptionÏƒ
    iframe
    ipureintro
    exact Hfacts
  Â· isplitl [Htable]
    Â· iexact Htable
    Â· ipureintro
      exact Hfacts.2.2.2.2.1 index table hlookup

/-- Replacing an owned table preserves its stable identity and updates the
authoritative ghost map and physical table list in lockstep. -/
theorem stateInterp_table_set [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (oldTable newTable : TableInst) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      tablePointsTo index oldTable ==âˆ—
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm :=
            { store.wasm with
              tables := listSetAt store.wasm.tables index newTable } }
        steps observations threads âˆ—
      tablePointsTo index newTable := by
  iintro âŸ¨Hstate, HtableâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  ihave %hlookup :=
    tablePointsTo_lookup tableÏƒ index oldTable $$ Htables Htable
  imod tablePointsTo_update tableÏƒ index oldTable newTable $$
      Htables Htable with
    âŸ¨Htables, HtableâŸ©
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  Â· iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with
            tables := listSetAt store.wasm.tables index newTable } }
      steps observations threads).mpr
    iexists Ïƒ
    iexists globalÏƒ
    iexists dataSegmentÏƒ
    iexists insert tableÏƒ index newTable
    iexists elementSegmentÏƒ
    iexists exceptionÏƒ
    iframe
    ipureintro
    exact âŸ¨Hfacts.1, Hfacts.2.1, Hfacts.2.2.1,
      Hfacts.2.2.2.1,
      âŸ¨table_store_listSetAt_sound tableÏƒ store.wasm.tables
          index oldTable newTable Hfacts.2.2.2.2.1 hlookup,
        Hfacts.2.2.2.2.2âŸ©âŸ©
  Â· iexact Htable

theorem stateInterp_runtimeModule_agree [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat) (m : Module) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      runtimeModuleOwn m ==âˆ—
      âŒœstore.runtime.module = mâŒ := by
  iintro âŸ¨Hstate, HexpectedâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hactual, Hhost,
      %HfactsâŸ©
  icombine Hactual Hexpected as Hmodules
  ihave %hagrees :=
    runtimeModuleOwn_agree store.runtime.module m $$ Hmodules
  ipureintro
  exact hagrees

theorem stateInterp_exception_facts [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (dq : DFrac) (tagAndArgs : Nat Ã— List Value) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      exceptionPointsTo index dq tagAndArgs ==âˆ—
      âŒœstore.wasm.exns[index]? = some tagAndArgsâŒ := by
  iintro âŸ¨Hstate, HexceptionâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  ihave %hlookup := exceptionPointsTo_lookup exceptionÏƒ index dq tagAndArgs $$
      Hexceptions Hexception
  ipureintro
  exact Hfacts.2.2.2.2.2.2.1 index tagAndArgs hlookup

theorem stateInterp_tagIds_facts [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads ==âˆ—
      âŒœstore.wasm.tagIds = List.range store.runtime.module.tags.lengthâŒ := by
  iintro Hstate
  imodintro
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  ipureintro
  exact Hfacts.2.2.2.2.2.2.2

/-- Four-byte ownership determines the physical little-endian word and proves
the complete access is in bounds. The address equalities exclude UInt32
wraparound in the derived byte footprint. -/
theorem stateInterp_pointsTo_u32_facts [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address value : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo_u32 address value ==âˆ—
      âŒœstore.wasm.mem.read32 address = value âˆ§
        address.toNat + 4 â‰¤ store.wasm.mem.pages * 65536âŒ := by
  iintro âŸ¨Hstate, HwordâŸ©
  ihave Hword := (pointsTo_u32_eq address value).mp $$ Hword
  icases Hword with âŸ¨H0, H1, H2, H3âŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  ihave %hg0 :
      âŒœget? Ïƒ address = some (some (u32Byte value 0))âŒ $$ [Hheap H0]
  Â· imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro
    exact hg0
  ihave %hg1 :
      âŒœget? Ïƒ (address + 1) = some (some (u32Byte value 1))âŒ $$ [Hheap H1]
  Â· imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro
    exact hg1
  ihave %hg2 :
      âŒœget? Ïƒ (address + 2) = some (some (u32Byte value 2))âŒ $$ [Hheap H2]
  Â· imod genHeap_valid $$ [$Hheap $H2] with %hg2
    ipureintro
    exact hg2
  ihave %hg3 :
      âŒœget? Ïƒ (address + 3) = some (some (u32Byte value 3))âŒ $$ [Hheap H3]
  Â· imod genHeap_valid $$ [$Hheap $H3] with %hg3
    ipureintro
    exact hg3
  have hr0 := Hfacts.1 address (u32Byte value 0) hg0
  have hr1 := Hfacts.1 (address + 1) (u32Byte value 1) hg1
  have hr2 := Hfacts.1 (address + 2) (u32Byte value 2) hg2
  have hr3 := Hfacts.1 (address + 3) (u32Byte value 3) hg3
  have hb3 := Hfacts.2.1 (address + 3) (u32Byte value 3) hg3
  ipureintro
  constructor
  Â· simp only [Mem.read8] at hr0 hr1 hr2 hr3
    simp only [Mem.read32]
    rw [hr0, â† h1, hr1, â† h2, hr2, â† h3, hr3]
    exact u32Byte_reassemble value
  Â· rw [h3] at hb3
    omega

/-- Framed form of `stateInterp_pointsTo_u32_facts`. It preserves both the
state interpretation and word ownership, so clients can extract physical
facts for multiple disjoint words sequentially. -/
theorem stateInterp_pointsTo_u32_facts_frame [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address value : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo_u32 address value ==âˆ—
      stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo_u32 address value âˆ—
      âŒœstore.wasm.mem.read32 address = value âˆ§
        address.toNat + 4 â‰¤ store.wasm.mem.pages * 65536âŒ := by
  iintro âŸ¨Hstate, HwordâŸ©
  ihave Hword := (pointsTo_u32_eq address value).mp $$ Hword
  icases Hword with âŸ¨H0, H1, H2, H3âŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  ihave %hg0 :
      âŒœget? Ïƒ address = some (some (u32Byte value 0))âŒ $$ [Hheap H0]
  Â· imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro
    exact hg0
  ihave %hg1 :
      âŒœget? Ïƒ (address + 1) = some (some (u32Byte value 1))âŒ $$ [Hheap H1]
  Â· imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro
    exact hg1
  ihave %hg2 :
      âŒœget? Ïƒ (address + 2) = some (some (u32Byte value 2))âŒ $$ [Hheap H2]
  Â· imod genHeap_valid $$ [$Hheap $H2] with %hg2
    ipureintro
    exact hg2
  ihave %hg3 :
      âŒœget? Ïƒ (address + 3) = some (some (u32Byte value 3))âŒ $$ [Hheap H3]
  Â· imod genHeap_valid $$ [$Hheap $H3] with %hg3
    ipureintro
    exact hg3
  have hr0 := Hfacts.1 address (u32Byte value 0) hg0
  have hr1 := Hfacts.1 (address + 1) (u32Byte value 1) hg1
  have hr2 := Hfacts.1 (address + 2) (u32Byte value 2) hg2
  have hr3 := Hfacts.1 (address + 3) (u32Byte value 3) hg3
  have hb3 := Hfacts.2.1 (address + 3) (u32Byte value 3) hg3
  have hread : store.wasm.mem.read32 address = value := by
    simp only [Mem.read8] at hr0 hr1 hr2 hr3
    simp only [Mem.read32]
    rw [hr0, â† h1, hr1, â† h2, hr2, â† h3, hr3]
    exact u32Byte_reassemble value
  have hbound :
      address.toNat + 4 â‰¤ store.wasm.mem.pages * 65536 := by
    rw [h3] at hb3
    omega
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  Â· iapply (stateInterp_eq store steps observations threads).mpr
    iexists Ïƒ
    iexists globalÏƒ
    iexists dataSegmentÏƒ
    iexists tableÏƒ
    iexists elementSegmentÏƒ
    iexists exceptionÏƒ
    iframe
    ipureintro
    exact Hfacts
  Â· isplitl [H0 H1 H2 H3]
    Â· iapply (pointsTo_u32_eq address value).mpr
      iframe
    Â· ipureintro
      exact âŸ¨hread, hboundâŸ©

theorem stateInterp_pointsTo_u16_facts [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address value : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo_u16 address value ==âˆ—
      âŒœstore.wasm.mem.read16 address = value &&& 0xFFFF âˆ§
        address.toNat + 2 â‰¤ store.wasm.mem.pages * 65536âŒ := by
  iintro âŸ¨Hstate, HwordâŸ©
  ihave Hword := (pointsTo_u16_eq address value).mp $$ Hword
  icases Hword with âŸ¨H0, H1âŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  ihave %hg0 :
      âŒœget? Ïƒ address = some (some (u16Byte value 0))âŒ $$ [Hheap H0]
  Â· imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro
    exact hg0
  ihave %hg1 :
      âŒœget? Ïƒ (address + 1) = some (some (u16Byte value 1))âŒ $$ [Hheap H1]
  Â· imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro
    exact hg1
  have hr0 := Hfacts.1 address (u16Byte value 0) hg0
  have hr1 := Hfacts.1 (address + 1) (u16Byte value 1) hg1
  have hb1 := Hfacts.2.1 (address + 1) (u16Byte value 1) hg1
  ipureintro
  constructor
  Â· simp only [Mem.read8] at hr0 hr1
    simp only [Mem.read16]
    rw [hr0, â† h1, hr1]
    exact u16Byte_reassemble value
  Â· rw [h1] at hb1
    omega

/-- Eight-byte ownership determines the physical little-endian word and proves
the complete access is in bounds. The address equalities exclude UInt32
wraparound in the derived byte footprint. -/
theorem stateInterp_pointsTo_u64_facts [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt64)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3)
    (h4 : (address + 4).toNat = address.toNat + 4)
    (h5 : (address + 5).toNat = address.toNat + 5)
    (h6 : (address + 6).toNat = address.toNat + 6)
    (h7 : (address + 7).toNat = address.toNat + 7) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo_u64 address value ==âˆ—
      âŒœstore.wasm.mem.read64 address = value âˆ§
        address.toNat + 8 â‰¤ store.wasm.mem.pages * 65536âŒ := by
  iintro âŸ¨Hstate, HwordâŸ©
  ihave Hword := (pointsTo_u64_eq address value).mp $$ Hword
  icases Hword with âŸ¨H0, H1, H2, H3, H4, H5, H6, H7âŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  ihave %hg0 :
      âŒœget? Ïƒ address = some (some (u64Byte value 0))âŒ $$ [Hheap H0]
  Â· imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro; exact hg0
  ihave %hg1 :
      âŒœget? Ïƒ (address + 1) = some (some (u64Byte value 1))âŒ $$ [Hheap H1]
  Â· imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro; exact hg1
  ihave %hg2 :
      âŒœget? Ïƒ (address + 2) = some (some (u64Byte value 2))âŒ $$ [Hheap H2]
  Â· imod genHeap_valid $$ [$Hheap $H2] with %hg2
    ipureintro; exact hg2
  ihave %hg3 :
      âŒœget? Ïƒ (address + 3) = some (some (u64Byte value 3))âŒ $$ [Hheap H3]
  Â· imod genHeap_valid $$ [$Hheap $H3] with %hg3
    ipureintro; exact hg3
  ihave %hg4 :
      âŒœget? Ïƒ (address + 4) = some (some (u64Byte value 4))âŒ $$ [Hheap H4]
  Â· imod genHeap_valid $$ [$Hheap $H4] with %hg4
    ipureintro; exact hg4
  ihave %hg5 :
      âŒœget? Ïƒ (address + 5) = some (some (u64Byte value 5))âŒ $$ [Hheap H5]
  Â· imod genHeap_valid $$ [$Hheap $H5] with %hg5
    ipureintro; exact hg5
  ihave %hg6 :
      âŒœget? Ïƒ (address + 6) = some (some (u64Byte value 6))âŒ $$ [Hheap H6]
  Â· imod genHeap_valid $$ [$Hheap $H6] with %hg6
    ipureintro; exact hg6
  ihave %hg7 :
      âŒœget? Ïƒ (address + 7) = some (some (u64Byte value 7))âŒ $$ [Hheap H7]
  Â· imod genHeap_valid $$ [$Hheap $H7] with %hg7
    ipureintro; exact hg7
  have hr0 := Hfacts.1 address (u64Byte value 0) hg0
  have hr1 := Hfacts.1 (address + 1) (u64Byte value 1) hg1
  have hr2 := Hfacts.1 (address + 2) (u64Byte value 2) hg2
  have hr3 := Hfacts.1 (address + 3) (u64Byte value 3) hg3
  have hr4 := Hfacts.1 (address + 4) (u64Byte value 4) hg4
  have hr5 := Hfacts.1 (address + 5) (u64Byte value 5) hg5
  have hr6 := Hfacts.1 (address + 6) (u64Byte value 6) hg6
  have hr7 := Hfacts.1 (address + 7) (u64Byte value 7) hg7
  have hb7 := Hfacts.2.1 (address + 7) (u64Byte value 7) hg7
  ipureintro
  constructor
  Â· simp only [Mem.read8] at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
    simp only [Mem.read64]
    rw [hr0, â† h1, hr1, â† h2, hr2, â† h3, hr3, â† h4, hr4,
      â† h5, hr5, â† h6, hr6, â† h7, hr7]
    exact u64Byte_reassemble value
  Â· rw [h7] at hb7
    omega

/-- Framed form of `stateInterp_pointsTo_u64_facts`. It returns both the
authoritative state interpretation and the word ownership, allowing a client
to establish physical facts for several disjoint words sequentially. -/
theorem stateInterp_pointsTo_u64_facts_frame [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt64)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3)
    (h4 : (address + 4).toNat = address.toNat + 4)
    (h5 : (address + 5).toNat = address.toNat + 5)
    (h6 : (address + 6).toNat = address.toNat + 6)
    (h7 : (address + 7).toNat = address.toNat + 7) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo_u64 address value ==âˆ—
      stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo_u64 address value âˆ—
      âŒœstore.wasm.mem.read64 address = value âˆ§
        address.toNat + 8 â‰¤ store.wasm.mem.pages * 65536âŒ := by
  iintro âŸ¨Hstate, HwordâŸ©
  ihave Hword := (pointsTo_u64_eq address value).mp $$ Hword
  icases Hword with âŸ¨H0, H1, H2, H3, H4, H5, H6, H7âŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  ihave %hg0 :
      âŒœget? Ïƒ address = some (some (u64Byte value 0))âŒ $$ [Hheap H0]
  Â· imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro; exact hg0
  ihave %hg1 :
      âŒœget? Ïƒ (address + 1) = some (some (u64Byte value 1))âŒ $$ [Hheap H1]
  Â· imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro; exact hg1
  ihave %hg2 :
      âŒœget? Ïƒ (address + 2) = some (some (u64Byte value 2))âŒ $$ [Hheap H2]
  Â· imod genHeap_valid $$ [$Hheap $H2] with %hg2
    ipureintro; exact hg2
  ihave %hg3 :
      âŒœget? Ïƒ (address + 3) = some (some (u64Byte value 3))âŒ $$ [Hheap H3]
  Â· imod genHeap_valid $$ [$Hheap $H3] with %hg3
    ipureintro; exact hg3
  ihave %hg4 :
      âŒœget? Ïƒ (address + 4) = some (some (u64Byte value 4))âŒ $$ [Hheap H4]
  Â· imod genHeap_valid $$ [$Hheap $H4] with %hg4
    ipureintro; exact hg4
  ihave %hg5 :
      âŒœget? Ïƒ (address + 5) = some (some (u64Byte value 5))âŒ $$ [Hheap H5]
  Â· imod genHeap_valid $$ [$Hheap $H5] with %hg5
    ipureintro; exact hg5
  ihave %hg6 :
      âŒœget? Ïƒ (address + 6) = some (some (u64Byte value 6))âŒ $$ [Hheap H6]
  Â· imod genHeap_valid $$ [$Hheap $H6] with %hg6
    ipureintro; exact hg6
  ihave %hg7 :
      âŒœget? Ïƒ (address + 7) = some (some (u64Byte value 7))âŒ $$ [Hheap H7]
  Â· imod genHeap_valid $$ [$Hheap $H7] with %hg7
    ipureintro; exact hg7
  have hr0 := Hfacts.1 address (u64Byte value 0) hg0
  have hr1 := Hfacts.1 (address + 1) (u64Byte value 1) hg1
  have hr2 := Hfacts.1 (address + 2) (u64Byte value 2) hg2
  have hr3 := Hfacts.1 (address + 3) (u64Byte value 3) hg3
  have hr4 := Hfacts.1 (address + 4) (u64Byte value 4) hg4
  have hr5 := Hfacts.1 (address + 5) (u64Byte value 5) hg5
  have hr6 := Hfacts.1 (address + 6) (u64Byte value 6) hg6
  have hr7 := Hfacts.1 (address + 7) (u64Byte value 7) hg7
  have hb7 := Hfacts.2.1 (address + 7) (u64Byte value 7) hg7
  have hread : store.wasm.mem.read64 address = value := by
    simp only [Mem.read8] at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
    simp only [Mem.read64]
    rw [hr0, â† h1, hr1, â† h2, hr2, â† h3, hr3, â† h4, hr4,
      â† h5, hr5, â† h6, hr6, â† h7, hr7]
    exact u64Byte_reassemble value
  have hbound :
      address.toNat + 8 â‰¤ store.wasm.mem.pages * 65536 := by
    rw [h7] at hb7
    omega
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  Â· iapply (stateInterp_eq store steps observations threads).mpr
    iexists Ïƒ
    iexists globalÏƒ
    iexists dataSegmentÏƒ
    iexists tableÏƒ
    iexists elementSegmentÏƒ
    iexists exceptionÏƒ
    iframe
    ipureintro
    exact Hfacts
  Â· isplitl [H0 H1 H2 H3 H4 H5 H6 H7]
    Â· iapply (pointsTo_u64_eq address value).mpr
      iframe
    Â· ipureintro
      exact âŸ¨hread, hboundâŸ©

theorem stateInterp_store8 [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (oldValue newValue : UInt8)
    (hbound : address.toNat < store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo (GF := WasmHeapGF Î±) (H := WasmHeapMap)
        address (DFrac.own 1) (some oldValue) ==âˆ—
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.write8 address newValue } }
        steps observations threads âˆ—
      pointsTo (GF := WasmHeapGF Î±) (H := WasmHeapMap)
        address (DFrac.own 1) (some newValue) := by
  iintro âŸ¨Hstate, HpointstoâŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  imod genHeap_update (vâ‚‚ := some newValue) $$ [$Hheap $Hpointsto] with
    âŸ¨Hheap, HpointstoâŸ©
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  Â· iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write8 address newValue } }
      steps observations threads).mpr
    iexists insert Ïƒ address (some newValue)
    iexists globalÏƒ
    iexists dataSegmentÏƒ
    iexists tableÏƒ
    iexists elementSegmentÏƒ
    iexists exceptionÏƒ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
    ipureintro
    exact âŸ¨store_sound Ïƒ store.wasm.mem address newValue Hfacts.1,
      store_inBounds Ïƒ store.wasm.mem address newValue Hfacts.2.1 hbound,
      Hfacts.2.2âŸ©
  Â· iexact Hpointsto

theorem stateInterp_store32 [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address oldValue newValue : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3)
    (hbound : address.toNat + 4 â‰¤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo_u32 address oldValue ==âˆ—
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.write32 address newValue } }
        steps observations threads âˆ—
      pointsTo_u32 address newValue := by
  iintro âŸ¨Hstate, HwordâŸ©
  ihave Hword := (pointsTo_u32_eq address oldValue).mp $$ Hword
  icases Hword with âŸ¨H0, H1, H2, H3âŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  imod genHeap_update (vâ‚‚ := some (u32Byte newValue 0)) $$
      [$Hheap $H0] with âŸ¨Hheap, H0âŸ©
  imod genHeap_update (vâ‚‚ := some (u32Byte newValue 1)) $$
      [$Hheap $H1] with âŸ¨Hheap, H1âŸ©
  imod genHeap_update (vâ‚‚ := some (u32Byte newValue 2)) $$
      [$Hheap $H2] with âŸ¨Hheap, H2âŸ©
  imod genHeap_update (vâ‚‚ := some (u32Byte newValue 3)) $$
      [$Hheap $H3] with âŸ¨Hheap, H3âŸ©
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  Â· iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write32 address newValue } }
      steps observations threads).mpr
    iexists
      insert
        (insert
          (insert
            (insert Ïƒ address (some (u32Byte newValue 0)))
            (address + 1) (some (u32Byte newValue 1)))
        (address + 2) (some (u32Byte newValue 2)))
        (address + 3) (some (u32Byte newValue 3))
    iexists globalÏƒ
    iexists dataSegmentÏƒ
    iexists tableÏƒ
    iexists elementSegmentÏƒ
    iexists exceptionÏƒ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
    ipureintro
    exact âŸ¨
        (store32_sound Ïƒ store.wasm.mem address newValue h1 h2 h3 Hfacts.1)
        , (store32_inBounds Ïƒ store.wasm.mem address newValue h1 h2 h3
          Hfacts.2.1 hbound)
        , Hfacts.2.2âŸ©
  Â· iapply (pointsTo_u32_eq address newValue).mpr
    iframe

theorem stateInterp_store16 [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address oldValue newValue : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (hbound : address.toNat + 2 â‰¤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo_u16 address oldValue ==âˆ—
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.write16 address newValue } }
        steps observations threads âˆ—
      pointsTo_u16 address newValue := by
  iintro âŸ¨Hstate, HwordâŸ©
  ihave Hword := (pointsTo_u16_eq address oldValue).mp $$ Hword
  icases Hword with âŸ¨H0, H1âŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  imod genHeap_update (vâ‚‚ := some (u16Byte newValue 0)) $$
      [$Hheap $H0] with âŸ¨Hheap, H0âŸ©
  imod genHeap_update (vâ‚‚ := some (u16Byte newValue 1)) $$
      [$Hheap $H1] with âŸ¨Hheap, H1âŸ©
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  Â· iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write16 address newValue } }
      steps observations threads).mpr
    iexists insert (insert Ïƒ address (some (u16Byte newValue 0)))
      (address + 1) (some (u16Byte newValue 1))
    iexists globalÏƒ
    iexists dataSegmentÏƒ
    iexists tableÏƒ
    iexists elementSegmentÏƒ
    iexists exceptionÏƒ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
    ipureintro
    exact âŸ¨
        (store16_sound Ïƒ store.wasm.mem address newValue h1 Hfacts.1)
        , (store16_inBounds Ïƒ store.wasm.mem address newValue h1
          Hfacts.2.1 hbound)
        , Hfacts.2.2âŸ©
  Â· iapply (pointsTo_u16_eq address newValue).mpr
    iframe

theorem stateInterp_store64 [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (oldValue newValue : UInt64)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3)
    (h4 : (address + 4).toNat = address.toNat + 4)
    (h5 : (address + 5).toNat = address.toNat + 5)
    (h6 : (address + 6).toNat = address.toNat + 6)
    (h7 : (address + 7).toNat = address.toNat + 7)
    (hbound : address.toNat + 8 â‰¤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo_u64 address oldValue ==âˆ—
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.write64 address newValue } }
        steps observations threads âˆ—
      pointsTo_u64 address newValue := by
  iintro âŸ¨Hstate, HwordâŸ©
  ihave Hword := (pointsTo_u64_eq address oldValue).mp $$ Hword
  icases Hword with âŸ¨H0, H1, H2, H3, H4, H5, H6, H7âŸ©
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  imod genHeap_update (vâ‚‚ := some (u64Byte newValue 0)) $$
      [$Hheap $H0] with âŸ¨Hheap, H0âŸ©
  imod genHeap_update (vâ‚‚ := some (u64Byte newValue 1)) $$
      [$Hheap $H1] with âŸ¨Hheap, H1âŸ©
  imod genHeap_update (vâ‚‚ := some (u64Byte newValue 2)) $$
      [$Hheap $H2] with âŸ¨Hheap, H2âŸ©
  imod genHeap_update (vâ‚‚ := some (u64Byte newValue 3)) $$
      [$Hheap $H3] with âŸ¨Hheap, H3âŸ©
  imod genHeap_update (vâ‚‚ := some (u64Byte newValue 4)) $$
      [$Hheap $H4] with âŸ¨Hheap, H4âŸ©
  imod genHeap_update (vâ‚‚ := some (u64Byte newValue 5)) $$
      [$Hheap $H5] with âŸ¨Hheap, H5âŸ©
  imod genHeap_update (vâ‚‚ := some (u64Byte newValue 6)) $$
      [$Hheap $H6] with âŸ¨Hheap, H6âŸ©
  imod genHeap_update (vâ‚‚ := some (u64Byte newValue 7)) $$
      [$Hheap $H7] with âŸ¨Hheap, H7âŸ©
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  Â· iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write64 address newValue } }
      steps observations threads).mpr
    iexists store64Heap Ïƒ address newValue
    iexists globalÏƒ
    iexists dataSegmentÏƒ
    iexists tableÏƒ
    iexists elementSegmentÏƒ
    iexists exceptionÏƒ
    unfold store64Heap
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
    ipureintro
    exact âŸ¨
      store64_sound Ïƒ store.wasm.mem address newValue
        h1 h2 h3 h4 h5 h6 h7 Hfacts.1,
      store64_inBounds Ïƒ store.wasm.mem address newValue
        h1 h2 h3 h4 h5 h6 h7 Hfacts.2.1 hbound,
      Hfacts.2.2âŸ©
  Â· iapply (pointsTo_u64_eq address newValue).mpr
    iframe

/-- Successful memory growth preserves the authoritative byte heap unchanged:
physical bytes are identical and every previously owned address remains in
bounds because the page count only increases. -/
theorem stateInterp_memoryGrow [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (delta : UInt32) (memory : Mem) (previousPages : Nat)
    (hgrow : store.wasm.mem.grow delta store.runtime.module.memoryCap =
      some (memory, previousPages)) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âŠ¢
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm := { store.wasm with mem := memory } }
        steps observations threads := by
  iintro Hstate
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    âŸ¨%Ïƒ, %globalÏƒ, %dataSegmentÏƒ, %tableÏƒ, %elementSegmentÏƒ, %exceptionÏƒ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %HfactsâŸ©
  iapply (stateInterp_eq
    { store with wasm := { store.wasm with mem := memory } }
    steps observations threads).mpr
  iexists Ïƒ
  iexists globalÏƒ
  iexists dataSegmentÏƒ
  iexists tableÏƒ
  iexists elementSegmentÏƒ
  iexists exceptionÏƒ
  iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
  ipureintro
  exact âŸ¨grow_sound Ïƒ store.wasm.mem memory delta
      store.runtime.module.memoryCap previousPages hgrow Hfacts.1,
    grow_inBounds Ïƒ store.wasm.mem memory delta
      store.runtime.module.memoryCap previousPages hgrow Hfacts.2.1,
    Hfacts.2.2âŸ©

/-- Four-byte fill update used by the manual memory example. Ownership of the
whole affected range is required and is updated atomically. -/
theorem stateInterp_fill16_four_AB [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (oldWord : UInt32)
    (hbound : 20 â‰¤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo_u32 16 oldWord ==âˆ—
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.fill 16 4 0xAB } }
        steps observations threads âˆ—
      pointsTo_u32 16 0xABABABAB := by
  iintro âŸ¨Hstate, HwordâŸ©
  imod stateInterp_store32 store steps observations threads
      16 oldWord 0xABABABAB rfl rfl rfl hbound $$
      [$Hstate $Hword] with âŸ¨Hstate, HwordâŸ©
  imodintro
  isplitl [Hstate]
  Â· rw [fill16_four_AB_eq_write32]
    iexact Hstate
  Â· iexact Hword

/-- Four-byte passive-segment initialization used by the manual Iris example.
The segment itself is read-only during `memory.init`; only the destination
word changes. -/
theorem stateInterp_init16_four [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (oldWord : UInt32)
    (hbound : 20 â‰¤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo_u32 16 oldWord ==âˆ—
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.writeBytesFrom 16 [1, 2, 3, 4] 0 4 } }
        steps observations threads âˆ—
      pointsTo_u32 16 0x04030201 := by
  iintro âŸ¨Hstate, HwordâŸ©
  imod stateInterp_store32 store steps observations threads
      16 oldWord 0x04030201 rfl rfl rfl hbound $$
      [$Hstate $Hword] with âŸ¨Hstate, HwordâŸ©
  imodintro
  isplitl [Hstate]
  Â· rw [init16_four_eq_write32]
    iexact Hstate
  Â· iexact Hword

/-- Aligned four-byte copy used by the manual Iris example. Source ownership
is framed, while complete destination ownership is updated atomically. -/
theorem stateInterp_copy8_zero_four [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (oldDestination : UInt32) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo_u32 0 0x04030201 âˆ— pointsTo_u32 8 oldDestination ==âˆ—
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.copy 8 0 4 } }
        steps observations threads âˆ—
      pointsTo_u32 0 0x04030201 âˆ— pointsTo_u32 8 0x04030201 := by
  iintro âŸ¨Hstate, Hsource, HdestinationâŸ©
  ihave %HsourceFacts :
      âŒœstore.wasm.mem.read32 0 = 0x04030201 âˆ§
        4 â‰¤ store.wasm.mem.pages * 65536âŒ $$ [Hstate Hsource]
  Â· imod stateInterp_pointsTo_u32_facts store steps observations threads
      0 0x04030201 rfl rfl rfl $$ [$Hstate $Hsource] with %HsourceFacts
    ipureintro
    exact HsourceFacts
  ihave %HdestinationFacts :
      âŒœstore.wasm.mem.read32 8 = oldDestination âˆ§
        12 â‰¤ store.wasm.mem.pages * 65536âŒ $$ [Hstate Hdestination]
  Â· imod stateInterp_pointsTo_u32_facts store steps observations threads
      8 oldDestination rfl rfl rfl $$ [$Hstate $Hdestination]
      with %HdestinationFacts
    ipureintro
    exact HdestinationFacts
  imod stateInterp_store32 store steps observations threads
      8 oldDestination 0x04030201 rfl rfl rfl HdestinationFacts.2 $$
      [$Hstate $Hdestination] with âŸ¨Hstate, HdestinationâŸ©
  imodintro
  isplitl [Hstate]
  Â· rw [copy8_zero_four_eq_write32 store.wasm.mem HsourceFacts.1]
    iexact Hstate
  Â· iframe

/-- Overlapping four-byte copy from address 0 to address 2.  One eight-byte
owner covers the overlapping source and destination, and the ghost update
uses the pre-copy source bytes, matching WebAssembly memmove semantics. -/
theorem stateInterp_copy2_zero_four [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo_u64 0 0x8877665544332211 ==âˆ—
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.copy 2 0 4 } }
        steps observations threads âˆ—
      pointsTo_u64 0 0x8877443322112211 := by
  iintro âŸ¨Hstate, HwordâŸ©
  imod stateInterp_pointsTo_u64_facts_frame
      store steps observations threads
      0 0x8877665544332211 rfl rfl rfl rfl rfl rfl rfl $$
      [$Hstate $Hword] with âŸ¨Hstate, Hword, %HfactsâŸ©
  ihave Hword :=
    (pointsTo_u64_eq 0 0x8877665544332211).mp $$ Hword
  icases Hword with âŸ¨H0, H1, H2, H3, H4, H5, H6, H7âŸ©
  ihave H2At :
      pointsTo (GF := WasmHeapGF Î±) (H := WasmHeapMap)
        2 (DFrac.own 1) (some (u64Byte 0x8877665544332211 2)) $$ [H2]
  Â· rw [show (0 : UInt32) + 2 = 2 by decide]
    iexact H2
  ihave H3At :
      pointsTo (GF := WasmHeapGF Î±) (H := WasmHeapMap)
        3 (DFrac.own 1) (some (u64Byte 0x8877665544332211 3)) $$ [H3]
  Â· rw [show (0 : UInt32) + 3 = 3 by decide]
    iexact H3
  ihave H4At :
      pointsTo (GF := WasmHeapGF Î±) (H := WasmHeapMap)
        4 (DFrac.own 1) (some (u64Byte 0x8877665544332211 4)) $$ [H4]
  Â· rw [show (0 : UInt32) + 4 = 4 by decide]
    iexact H4
  ihave H5At :
      pointsTo (GF := WasmHeapGF Î±) (H := WasmHeapMap)
        5 (DFrac.own 1) (some (u64Byte 0x8877665544332211 5)) $$ [H5]
  Â· rw [show (0 : UInt32) + 5 = 5 by decide]
    iexact H5
  imod stateInterp_store8 store steps observations threads
      2 (u64Byte 0x8877665544332211 2) 0x11 (by
        simp only [UInt32.toNat_ofNat] at Hfacts âŠ¢
        omega) $$
      [$Hstate $H2At] with âŸ¨Hstate, H2âŸ©
  imod stateInterp_store8
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write8 2 0x11 } }
      steps observations threads 3
        (u64Byte 0x8877665544332211 3) 0x22 (by
        simp only [Mem.write8]
        simp only [UInt32.toNat_ofNat] at Hfacts âŠ¢
        omega) $$ [$Hstate $H3At] with âŸ¨Hstate, H3âŸ©
  imod stateInterp_store8
      { store with wasm :=
          { store.wasm with mem :=
              (store.wasm.mem.write8 2 0x11).write8 3 0x22 } }
      steps observations threads 4
        (u64Byte 0x8877665544332211 4) 0x33 (by
        simp only [Mem.write8]
        simp only [UInt32.toNat_ofNat] at Hfacts âŠ¢
        omega) $$ [$Hstate $H4At] with âŸ¨Hstate, H4âŸ©
  imod stateInterp_store8
      { store with wasm :=
          { store.wasm with mem :=
              ((store.wasm.mem.write8 2 0x11).write8 3 0x22).write8 4 0x33 } }
      steps observations threads 5
        (u64Byte 0x8877665544332211 5) 0x44 (by
        simp only [Mem.write8]
        simp only [UInt32.toNat_ofNat] at Hfacts âŠ¢
        omega) $$ [$Hstate $H5At] with âŸ¨Hstate, H5âŸ©
  imodintro
  isplitl [Hstate]
  Â· rw [copy2_zero_four_eq_write64 store.wasm.mem Hfacts.1]
    iexact Hstate
  Â· iapply (pointsTo_u64_eq 0 0x8877443322112211).mpr
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

theorem stateInterp_writeV128 [WasmSmallStepGS hlc Î±]
    (store : MachineStore Î±) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (addr : UInt32) (lo_old hi_old lo hi : UInt64)
    (hnowrap : addr.toNat + 16 < 4294967296)
    (hbound : addr.toNat + 16 â‰¤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF Î±) store steps observations threads âˆ—
      pointsTo_u64 addr lo_old âˆ— pointsTo_u64 (addr + 8) hi_old ==âˆ—
      stateInterp (GF := WasmHeapGF Î±)
        { store with wasm := { store.wasm with mem :=
            (store.wasm.mem.write64 addr lo).write64 (addr + 8) hi } }
        steps observations threads âˆ—
      pointsTo_u64 addr lo âˆ— pointsTo_u64 (addr + 8) hi := by
  have hbound_lo : addr.toNat + 8 â‰¤ store.wasm.mem.pages * 65536 := by omega
  have h1 : (addr + 1).toNat = addr.toNat + 1 := by
    simp only [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]; omega
  have h2 : (addr + 2).toNat = addr.toNat + 2 := by
    simp only [UInt32.toNat_add, show (2 : UInt32).toNat = 2 from rfl]; omega
  have h3 : (addr + 3).toNat = addr.toNat + 3 := by
    simp only [UInt32.toNat_add, show (3 : UInt32).toNat = 3 from rfl]; omega
  have h4 : (addr + 4).toNat = addr.toNat + 4 := by
    simp only [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]; omega
  have h5 : (addr + 5).toNat = addr.toNat + 5 := by
    simp only [UInt32.toNat_add, show (5 : UInt32).toNat = 5 from rfl]; omega
  have h6 : (addr + 6).toNat = addr.toNat + 6 := by
    simp only [UInt32.toNat_add, show (6 : UInt32).toNat = 6 from rfl]; omega
  have h7 : (addr + 7).toNat = addr.toNat + 7 := by
    simp only [UInt32.toNat_add, show (7 : UInt32).toNat = 7 from rfl]; omega
  have h8 : (addr + 8).toNat = addr.toNat + 8 := by
    simp only [UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl]; omega
  have h81 : (addr + 8 + 1).toNat = (addr + 8).toNat + 1 := by
    simp only [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl,
               show (8 : UInt32).toNat = 8 from rfl]; omega
  have h82 : (addr + 8 + 2).toNat = (addr + 8).toNat + 2 := by
    simp only [UInt32.toNat_add, show (2 : UInt32).toNat = 2 from rfl,
               show (8 : UInt32).toNat = 8 from rfl]; omega
  have h83 : (addr + 8 + 3).toNat = (addr + 8).toNat + 3 := by
    simp only [UInt32.toNat_add, show (3 : UInt32).toNat = 3 from rfl,
               show (8 : UInt32).toNat = 8 from rfl]; omega
  have h84 : (addr + 8 + 4).toNat = (addr + 8).toNat + 4 := by
    simp only [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl,
               show (8 : UInt32).toNat = 8 from rfl]; omega
  have h85 : (addr + 8 + 5).toNat = (addr + 8).toNat + 5 := by
    simp only [UInt32.toNat_add, show (5 : UInt32).toNat = 5 from rfl,
               show (8 : UInt32).toNat = 8 from rfl]; omega
  have h86 : (addr + 8 + 6).toNat = (addr + 8).toNat + 6 := by
    simp only [UInt32.toNat_add, show (6 : UInt32).toNat = 6 from rfl,
               show (8 : UInt32).toNat = 8 from rfl]; omega
  have h87 : (addr + 8 + 7).toNat = (addr + 8).toNat + 7 := by
    simp only [UInt32.toNat_add, show (7 : UInt32).toNat = 7 from rfl,
               show (8 : UInt32).toNat = 8 from rfl]; omega
  let store1 := { store with wasm := { store.wasm with mem := store.wasm.mem.write64 addr lo } }
  have hbound_hi : (addr + 8).toNat + 8 â‰¤ store1.wasm.mem.pages * 65536 := by
    show (addr + 8).toNat + 8 â‰¤ store.wasm.mem.pages * 65536; rw [h8]; omega
  iintro âŸ¨HÏƒ, Hlo, HhiâŸ©
  imod stateInterp_store64 store steps observations threads addr lo_old lo
      h1 h2 h3 h4 h5 h6 h7 hbound_lo $$ [$HÏƒ $Hlo] with âŸ¨HÏƒ1, HloâŸ©
  imod stateInterp_store64 store1 steps observations threads (addr + 8) hi_old hi
      h81 h82 h83 h84 h85 h86 h87 hbound_hi $$ [$HÏƒ1 $Hhi] with âŸ¨HÏƒ2, HhiâŸ©
  imodintro
  isplitl [HÏƒ2]
  Â· iexact HÏƒ2
  isplitl [Hlo]
  Â· iexact Hlo
  Â· iexact Hhi

instance instIrisGS [WasmSmallStepGS hlc Î±] :
    IrisGS_gen hlc (Expr Î±) (WasmHeapGF Î±) where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

end Wasm.SmallStep
