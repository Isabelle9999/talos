/-
Extracted from TorchLean (MIT license).
Authors: TorchLean Team
-/

import CodeLib.IEEE32.Exec

namespace CodeLib.IEEE32

open IEEE32Exec

/-- Reinterpret a runtime `Float32` as the bit-level `IEEE32Exec`. -/
@[inline] def toIEEE32Exec (x : Float32) : IEEE32Exec :=
  IEEE32Exec.ofBits x.toBits

/-- Reinterpret an `IEEE32Exec` bit-pattern as a runtime `Float32`. -/
@[inline] def ofIEEE32Exec (x : IEEE32Exec) : Float32 :=
  Float32.ofBits x.bits

/-!
## External correctness assumptions

`Init.Float32` arithmetic in Lean is implemented by external runtime calls that
are opaque to the Lean kernel, so we cannot prove bit-level correctness inside
Lean. We package the intended connection as a typeclass interface.
-/

/-- Assumption package relating Lean's runtime `Float32` primitives to `IEEE32Exec`. -/
class RuntimeFloat32MatchesIEEE32Exec : Prop where
  /-- Round-trip: converting a bit-pattern through `Float32.ofBits` and back is the identity. -/
  toBits_ofBits : ∀ b : UInt32, (Float32.ofBits b).toBits = b
  /-- Round-trip: converting a `Float32` to bits and back is the identity. -/
  ofBits_toBits : ∀ x : Float32, Float32.ofBits x.toBits = x
  /-- `Float32.isNaN` agrees with the bit-level `IEEE32Exec.isNaN`. -/
  isNaN_bits : ∀ a : Float32,
    Float32.isNaN a = IEEE32Exec.isNaN (toIEEE32Exec a)

end CodeLib.IEEE32
