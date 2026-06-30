/-
Extracted from TorchLean (MIT license).
Authors: TorchLean Team
-/

namespace CodeLib.IEEE32

/-- Executable IEEE-754 binary32 value, stored as raw bits. -/
structure IEEE32Exec where
  /-- Raw UInt32 bit pattern of the binary32 value. -/
  bits : UInt32
  deriving DecidableEq, Repr

namespace IEEE32Exec

@[inline] def ofBits (b : UInt32) : IEEE32Exec := ⟨b⟩
@[inline] def toBits (x : IEEE32Exec) : UInt32 := x.bits

@[simp] theorem toBits_ofBits (b : UInt32) : toBits (ofBits b) = b := rfl
@[simp] theorem ofBits_toBits (x : IEEE32Exec) : ofBits (toBits x) = x := by
  cases x; rfl

instance : Inhabited IEEE32Exec where default := ofBits 0

/-!
## Binary32 bit layout

IEEE-754 binary32: sign[31] exp[30..23] frac[22..0]
-/

def signMask  : UInt32 := 0x80000000
def expMask   : UInt32 := 0x7F800000
def fracMask  : UInt32 := 0x007FFFFF
def quietBit  : UInt32 := 0x00400000
def expAllOnes : UInt32 := 0xFF

@[inline] def signBit  (x : IEEE32Exec) : Bool := (x.bits &&& signMask) != 0
@[inline] def expField (x : IEEE32Exec) : UInt32 := (x.bits >>> 23) &&& expAllOnes
@[inline] def fracField (x : IEEE32Exec) : UInt32 := x.bits &&& fracMask

/-- NaN: exponent all ones and fraction nonzero. -/
@[inline] def isNaN (x : IEEE32Exec) : Bool :=
  expField x == expAllOnes && fracField x != 0

/-- Infinity: exponent all ones and fraction zero. -/
@[inline] def isInf (x : IEEE32Exec) : Bool :=
  expField x == expAllOnes && fracField x == 0

/-- Finite: exponent field is not all ones (excludes NaN/Inf). -/
@[inline] def isFinite (x : IEEE32Exec) : Bool :=
  expField x != expAllOnes

end IEEE32Exec

end CodeLib.IEEE32
