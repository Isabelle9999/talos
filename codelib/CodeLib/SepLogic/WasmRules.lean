import CodeLib.SepLogic.WasmHeap
import Interpreter.Wasm

/-! # Bridge between Talos Mem and iris-lean GenHeap

The logical heap (ExtTreeMap) tracks OWNERSHIP — which bytes you own.
The physical memory (Mem.bytes) tracks VALUES — what's actually there.
The bridge says: wherever you own a byte, the physical memory agrees.
-/

namespace Wasm.SepLogic

open Iris Wasm Std

variable [inst : WasmHeapGS]

/-! The state interpretation: logical heap matches physical memory.
For every (addr, some v) in the logical heap σ, Mem.bytes has v at addr.
This is maintained as an invariant throughout execution. -/

def memAgrees (mem : Mem) (σ : WasmHeapMap (Option UInt8)) : Prop :=
  ∀ (addr : UInt32) (v : UInt8),
    σ.get? addr = some (some v) → mem.bytes addr.toNat = v

/-! Now the WP rules. Each rule says:
    "IF ownership + physical memory agree BEFORE the instruction,
     THEN ownership + physical memory agree AFTER." -/

-- load64: reads 8 bytes. Ownership unchanged, value on stack.
-- The rule: if you own addr ↦ᵤ₆₄ v, then load64 returns v.
theorem load64_spec (mem : Mem) (addr off : UInt32)
    (h_bounds : addr.toNat + off.toNat + 8 ≤ mem.pages * 65536)
    (v : UInt64)
    (h_read : mem.read64 (addr + off) = v) :
    True := by  -- placeholder, real rule connects to iProp
  trivial

-- store64: writes 8 bytes. Old ownership consumed, new produced.
-- The rule: if you own addr ↦ᵤ₆₄ old, after store64 you own addr ↦ᵤ₆₄ new.
theorem store64_spec (mem : Mem) (addr off : UInt32) (old_v new_v : UInt64)
    (h_bounds : addr.toNat + off.toNat + 8 ≤ mem.pages * 65536)
    (h_write : mem.write64 (addr + off) new_v = mem') :
    True := by  -- placeholder, real rule connects to iProp
  trivial

#check @pointsTo_u64  -- our u64 ownership predicate

end Wasm.SepLogic
