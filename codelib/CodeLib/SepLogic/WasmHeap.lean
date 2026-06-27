import Iris
import Iris.BI.Lib.GenHeap
import Interpreter.Wasm

/-! # Wasm Memory as an Iris GenHeap

Instantiates iris-lean's GenHeap for Wasm byte-level memory.
Location = UInt32 (byte address), Value = Option UInt8 (byte).
-/

namespace Wasm.SepLogic

open Iris Std

abbrev WasmHeapMap := fun V => ExtTreeMap UInt32 V compare

abbrev WasmHeapGF : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView UInt32 (Agree (LeibnizO (Option UInt8))) WasmHeapMap), by infer_instance⟩
  | 5 => ⟨constOF (HeapView UInt32 (Agree (LeibnizO GName)) WasmHeapMap), by infer_instance⟩
  | 6 => ⟨constOF MetaUR, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

-- Wire genHeapPreS (following HeapLang's instHeapLangGS_HeapLangS)
instance instWasmHeapPreS : genHeapPreS UInt32 (Option UInt8) WasmHeapGF WasmHeapMap where
  heap := by constructor; exists 4
  metaInfo := by constructor; exists 5
  metaData := by exists 6

-- The full genHeap instance with ghost names
class WasmHeapGS extends genHeapGS UInt32 (Option UInt8) WasmHeapGF WasmHeapMap

-- Now test: does the points-to notation work?
section Test
variable [inst : WasmHeapGS]

-- This is the payoff: addr ↦ byte for Wasm memory
#check (pointsTo (L := UInt32) (V := Option UInt8) (GF := WasmHeapGF) (H := WasmHeapMap))

-- Notation for Wasm points-to
notation:50 addr:50 " ↦w " v:50 => pointsTo (L := UInt32) (V := Option UInt8) 
    (GF := WasmHeapGF) (H := WasmHeapMap) addr (DFrac.own 1) (some v)

-- Multi-byte: u64 as 8 consecutive owned bytes (little-endian)
def pointsTo_u64 (addr : UInt32) (v : UInt64) : IProp WasmHeapGF :=
  let byte (n : Nat) : UInt8 := ⟨(v.toNat / (256 ^ n)) % 256, by omega⟩
  iprop%
    (addr ↦w byte 0) ∗ ((addr + 1) ↦w byte 1) ∗
    ((addr + 2) ↦w byte 2) ∗ ((addr + 3) ↦w byte 3) ∗
    ((addr + 4) ↦w byte 4) ∗ ((addr + 5) ↦w byte 5) ∗
    ((addr + 6) ↦w byte 6) ∗ ((addr + 7) ↦w byte 7)

#check @pointsTo_u64


end Test

end Wasm.SepLogic