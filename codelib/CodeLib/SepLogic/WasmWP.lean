import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmRules
import Interpreter.Wasm
import CodeLib.RustStd.Frame

/-! # Weakest Precondition for Wasm

Prop-level WP for termination. Per-instruction iProp rules for
ownership transfer. General iProp WP fixpoint deferred until
the instruction rules are validated on swap_elements.
-/

namespace Wasm.SepLogic

open Iris Wasm

variable [inst : WasmHeapGS]

def wp_wasm_prop (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop) : Prop :=
  ∃ fuel, match exec fuel m st locals prog env with
  | .Fallthrough st' _ => Q st' []
  | .Return st' vals => Q st' vals
  | _ => False

/-! ## Per-instruction ownership rules in iProp

Each rule describes how one instruction transforms ownership.
These compose sequentially for straight-line code (swap).
For loops, bi_least_fixpoint wraps the composition. -/

-- load64: need ownership to read, ownership preserved
def wp_load64 (addr : UInt32) (v : UInt64)
    (Q : IProp WasmHeapGF) : IProp WasmHeapGF :=
  iprop% (pointsTo_u64 addr v) ∗ (pointsTo_u64 addr v -∗ Q)

-- store64: consume old ownership, produce new
def wp_store64 (addr : UInt32) (old_v new_v : UInt64)
    (Q : IProp WasmHeapGF) : IProp WasmHeapGF :=
  iprop% (pointsTo_u64 addr old_v) ∗ (pointsTo_u64 addr new_v -∗ Q)

/-! ## iProp load rule

Read xs[k] from array ownership without consuming it. The caller
provides hmax to ensure address arithmetic doesn't overflow UInt32. -/
theorem wp_iProp_load32
    {σ : WasmHeapMap (Option UInt8)} {mem : Mem}
    (hagree : heapAgreesWithMem σ mem)
    {ptr : UInt32} {xs : List UInt32} {k : Nat}
    (hk : k < xs.length)
    (hbounds : (ptr + 4 * UInt32.ofNat k).toNat + 4 ≤ mem.pages * 65536)
    (hmax : mem.pages * 65536 ≤ 4294967296) :
    ⊢ (genHeapInterp σ ∗ arrayAt ptr xs) ==∗
      (genHeapInterp σ ∗ arrayAt ptr xs ∗
       ⌜mem.read32 (ptr + 4 * UInt32.ofNat k) = xs[k]!⌝) := by
  set addr := ptr + 4 * UInt32.ofNat k with haddr
  -- UInt32 address arithmetic (no overflow since addr.toNat + 4 ≤ 2^32)
  have hbase : addr.toNat + 4 ≤ 4294967296 := Nat.le_trans hbounds hmax
  have ha1 : (addr + 1).toNat = addr.toNat + 1 := by
    rw [UInt32.toNat_add]; simp; omega
  have ha2 : (addr + 2).toNat = addr.toNat + 2 := by
    rw [UInt32.toNat_add]; simp; omega
  have ha3 : (addr + 3).toNat = addr.toNat + 3 := by
    rw [UInt32.toNat_add]; simp; omega
  -- iProp proof
  iintro ⟨Hσ, HA⟩
  -- split off element k from the array
  icases arrayAt_get ptr xs k hk $$ [$HA] with ⟨Hpt, Hwand⟩
  -- decompose pointsTo_u32 into 4 byte ownership assertions
  have decomp : pointsTo_u32 addr xs[k] ⊢
      (addr ↦w ⟨xs[k].toNat / 256 ^ 0 % 256, by omega⟩) ∗
      ((addr + 1) ↦w ⟨xs[k].toNat / 256 ^ 1 % 256, by omega⟩) ∗
      ((addr + 2) ↦w ⟨xs[k].toNat / 256 ^ 2 % 256, by omega⟩) ∗
      ((addr + 3) ↦w ⟨xs[k].toNat / 256 ^ 3 % 256, by omega⟩) := by
    simp [pointsTo_u32]
  icases decomp $$ [$Hpt] with ⟨Hb0, Hb1, Hb2, Hb3⟩
  -- Non-consuming ghost-state lookups: ihave preserves Hσ and Hb_i in the outer context.
  -- We assert mem.bytes equalities directly (no get? in annotation) to avoid scope issues.
  -- Lean 4's definitional proof irrelevance handles omega-proof mismatches throughout.
  ihave %mb0 : ⌜mem.bytes addr.toNat = ⟨xs[k].toNat / 256 ^ 0 % 256, by omega⟩⌝ $$ [Hσ Hb0]
  · ihave >%G := genHeap_valid $$ [$Hσ $Hb0]
    ipureintro; exact hagree addr _ G
  ihave %mb1 : ⌜mem.bytes (addr.toNat + 1) = ⟨xs[k].toNat / 256 ^ 1 % 256, by omega⟩⌝ $$ [Hσ Hb1]
  · ihave >%G := genHeap_valid $$ [$Hσ $Hb1]
    ipureintro; exact ha1 ▸ hagree (addr + 1) _ G
  ihave %mb2 : ⌜mem.bytes (addr.toNat + 2) = ⟨xs[k].toNat / 256 ^ 2 % 256, by omega⟩⌝ $$ [Hσ Hb2]
  · ihave >%G := genHeap_valid $$ [$Hσ $Hb2]
    ipureintro; exact ha2 ▸ hagree (addr + 2) _ G
  ihave %mb3 : ⌜mem.bytes (addr.toNat + 3) = ⟨xs[k].toNat / 256 ^ 3 % 256, by omega⟩⌝ $$ [Hσ Hb3]
  · ihave >%G := genHeap_valid $$ [$Hσ $Hb3]
    ipureintro; exact ha3 ▸ hagree (addr + 3) _ G
  -- Conclude mem.read32 addr = xs[k] via the little-endian bridge lemma
  have hread : mem.read32 addr = xs[k] :=
    Mem.read32_of_le_bytes mem addr xs[k] mb0 mb1 mb2 mb3
  -- Reconstruct pointsTo_u32 from the 4 bytes (consumes Hb0..Hb3)
  have recomp :
      (addr ↦w ⟨xs[k].toNat / 256 ^ 0 % 256, by omega⟩) ∗
      ((addr + 1) ↦w ⟨xs[k].toNat / 256 ^ 1 % 256, by omega⟩) ∗
      ((addr + 2) ↦w ⟨xs[k].toNat / 256 ^ 2 % 256, by omega⟩) ∗
      ((addr + 3) ↦w ⟨xs[k].toNat / 256 ^ 3 % 256, by omega⟩) ⊢
      pointsTo_u32 addr xs[k] := by simp [pointsTo_u32]
  icases recomp $$ [$Hb0 $Hb1 $Hb2 $Hb3] with Hpt'
  -- Apply the wand to reconstruct full array ownership
  icases Hwand $$ [$Hpt'] with HA'
  -- Produce the conclusion: genHeapInterp ∗ arrayAt ∗ ⌜read32 = element⌝
  imodintro
  isplitl [Hσ]; · iexact Hσ
  isplitl [HA']
  · iexact HA'
  ipureintro
  rw [getElem!_pos xs k hk]
  exact hread

-- iProp store rule: update ownership on write
theorem wp_iProp_store32
    {σ : WasmHeapMap (Option UInt8)} {mem : Mem}
    (hagree : heapAgreesWithMem σ mem)
    {ptr : UInt32} {xs : List UInt32} {k : Nat}
    (hk : k < xs.length)
    (v : UInt32)
    (hbounds : (ptr + 4 * UInt32.ofNat k).toNat + 4 ≤ mem.pages * 65536)
    (hmax : mem.pages * 65536 ≤ 4294967296) :
    ⊢ (genHeapInterp σ ∗ arrayAt ptr xs) ==∗
      ∃ σ' : WasmHeapMap (Option UInt8),
      (⌜heapAgreesWithMem σ' (mem.write32 (ptr + 4 * UInt32.ofNat k) v)⌝ ∗
       genHeapInterp σ' ∗
       arrayAt ptr (xs.set k v)) := by
  set addr := ptr + 4 * UInt32.ofNat k with haddr
  have hbase : addr.toNat + 4 ≤ 4294967296 := Nat.le_trans hbounds hmax
  iintro ⟨Hσ, HA⟩
  -- Step 1: split off element k, get old pointsTo_u32 and update wand
  icases arrayAt_set ptr xs k v hk $$ [$HA] with ⟨Hold, Hwand⟩
  -- Step 2: decompose old pointsTo_u32 addr xs[k] into 4 byte assertions
  have decomp : pointsTo_u32 addr xs[k] ⊢
      (addr ↦w ⟨xs[k].toNat / 256 ^ 0 % 256, by omega⟩) ∗
      ((addr + 1) ↦w ⟨xs[k].toNat / 256 ^ 1 % 256, by omega⟩) ∗
      ((addr + 2) ↦w ⟨xs[k].toNat / 256 ^ 2 % 256, by omega⟩) ∗
      ((addr + 3) ↦w ⟨xs[k].toNat / 256 ^ 3 % 256, by omega⟩) := by
    simp [pointsTo_u32]
  icases decomp $$ [$Hold] with ⟨Hob0, Hob1, Hob2, Hob3⟩
  -- Steps 3–4: 4 genHeap_update calls via imod (strips ==∗ and destructures ∗ in one step)
  imod genHeap_update (v₂ := some ⟨v.toNat / 256 ^ 0 % 256, by omega⟩) $$ [$Hσ $Hob0] with ⟨Hσ1, Hnb0⟩
  imod genHeap_update (v₂ := some ⟨v.toNat / 256 ^ 1 % 256, by omega⟩) $$ [$Hσ1 $Hob1] with ⟨Hσ2, Hnb1⟩
  imod genHeap_update (v₂ := some ⟨v.toNat / 256 ^ 2 % 256, by omega⟩) $$ [$Hσ2 $Hob2] with ⟨Hσ3, Hnb2⟩
  imod genHeap_update (v₂ := some ⟨v.toNat / 256 ^ 3 % 256, by omega⟩) $$ [$Hσ3 $Hob3] with ⟨Hσ4, Hnb3⟩
  -- Reassemble pointsTo_u32 addr v from the 4 new byte assertions
  have recomp :
      (addr ↦w ⟨v.toNat / 256 ^ 0 % 256, by omega⟩) ∗
      ((addr + 1) ↦w ⟨v.toNat / 256 ^ 1 % 256, by omega⟩) ∗
      ((addr + 2) ↦w ⟨v.toNat / 256 ^ 2 % 256, by omega⟩) ∗
      ((addr + 3) ↦w ⟨v.toNat / 256 ^ 3 % 256, by omega⟩) ⊢
      pointsTo_u32 addr v := by simp [pointsTo_u32]
  icases recomp $$ [$Hnb0 $Hnb1 $Hnb2 $Hnb3] with Hnew
  -- Apply the wand to get arrayAt ptr (xs.set k v)
  icases Hwand $$ [$Hnew] with HA'
  -- σ4 = insert(insert(insert(insert σ ...) ...) ...) ... matches heapAgreesWithMem_write32_update
  have hagree' : heapAgreesWithMem _ (mem.write32 addr v) :=
    heapAgreesWithMem_write32_update hagree hbase
  imodintro
  iexists _
  isplitl []
  · ipureintro; exact hagree'
  isplitl [Hσ4]
  · iexact Hσ4
  iexact HA'

end Wasm.SepLogic
