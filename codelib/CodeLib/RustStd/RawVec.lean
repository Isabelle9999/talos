import Interpreter.Wasm

/-!
# `CodeLib.RustStd.RawVec`

Capacity-growth policy and vector-header update for Rust's
`alloc::raw_vec::RawVec` compiled to wasm32.  Each definition models one
arithmetic or memory step from the corresponding std entry point.
-/

namespace Wasm
open Wasm.SmallStep

/-- `RawVec::grow_amortized`: required bytes = `length + additional`. -/
def reserveRequired (length additional : UInt32) : UInt32 :=
  length + additional

/-- `RawVec::grow_amortized`: doubling candidate = `capacity * 2` (logical left shift). -/
def reserveDoubled (capacity : UInt32) : UInt32 :=
  capacity <<< 1

/-- `RawVec::grow_amortized`: take the larger of the required size and the doubled capacity. -/
def reserveCandidate (length additional capacity : UInt32) : UInt32 :=
  if reserveRequired length additional > reserveDoubled capacity then
    reserveRequired length additional
  else reserveDoubled capacity

/-- `RawVec::grow_amortized`: enforce `MIN_NON_ZERO_CAP = 8` bytes for `u8` allocations. -/
def reserveNewCapacity (length additional capacity : UInt32) : UInt32 :=
  if reserveCandidate length additional capacity > 8 then
    reserveCandidate length additional capacity
  else 8

/-- `RawVec::finish_grow`: write the new capacity and buffer pointer into the `RawVec` header. -/
def reserveVectorStore {α} (store : MachineStore α)
    (vector data capacity : UInt32) : MachineStore α :=
  let mem1 := store.wasm.mem.write32 vector capacity
  { store with wasm := { store.wasm with mem := mem1.write32 (vector + 4) data } }

/-- `std::io::Read::read_to_end`: grow the read buffer by `max(32 + capacity, 2 × capacity)`. -/
def readToEndNewCapacity (capacity : UInt32) : UInt32 :=
  if (32 : UInt32) + capacity > capacity <<< 1 then (32 : UInt32) + capacity
  else capacity <<< 1

end Wasm
