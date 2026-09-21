import Project.ByteEcho.Program
import CodeLib.RustStd.Template

/-!
# `rust_oom` instantiation for ByteEcho `func11`

`func11` (absolute Wasm index 14) is the
`_RNvNtCsebHcaeoSrxy_3std5alloc8rust_oom` function compiled into the
byte_echo crate.

This file provides the *contextual instantiation*:

1. `func11_body_eq` — a `rfl` proof that `func11`'s body is exactly
   `template_rust_oom ++ [.call 10, .unreachable]`, tying the
   WAT-decoded literal to the abstract template.

2. `func11_rustOOM` — the forward application of `rustOOM_instantiate` at
   callee abs-index 10.  Consumers supply the three frame tokens
   (`globalPointsToAt 0 0 (.i32 sp)`, `pointsTo_u32 0 (sp - 4) w1`,
   `pointsTo_u32 0 (sp - 8) w2`) from their own frame ownership.
-/

namespace Project.ByteEcho.Func11Proof

open Wasm Wasm.SmallStep

/-- `func11`'s body equals `template_rust_oom 10`.
    Proved by kernel reduction of the WAT-decoded literal. -/
theorem func11_body_eq :
    Project.ByteEcho.func11 = template_rust_oom 10 := rfl

/-- `RustOOMContractAt` at callee abs-index 10 for ByteEcho's `rust_oom`.
    Contextual instantiation: `rustOOM_instantiate` applied at index 10.
    Frame tokens are premises supplied by the caller. -/
theorem func11_rustOOM [WasmSmallStepGS hlc α]
    (sp w1 w2 : UInt32) (hsp : (16 : UInt32) ≤ sp) :
    RustOOMContractAt (α := α) (hlc := hlc) 10 sp w1 w2 :=
  rustOOM_instantiate 10 sp w1 w2 hsp

end Project.ByteEcho.Func11Proof
