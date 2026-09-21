import Project.Mergesort.Program
import CodeLib.RustStd.Template

/-!
# `rust_oom` instantiation for Mergesort `func28`

`func28` (absolute Wasm index 31) is the
`_RNvNtCsebHcaeoSrxy_3std5alloc8rust_oom` function compiled into the
mergesort crate.

Mergesort excludes functions 12–55 from closed contracts.  This file therefore
provides only the *contextual instantiation*:

1. `func28_body_eq` — a `rfl` proof that `func28`'s body is exactly
   `template_rust_oom ++ [.call 20, .unreachable]`, tying the
   WAT-decoded literal to the abstract template.

2. `func28_rustOOM` — the forward application of `rustOOM_instantiate` at
   callee abs-index 20.  Consumers supply the three frame tokens
   (`globalPointsToAt 0 0 (.i32 sp)`, `pointsTo_u32 0 (sp - 4) w1`,
   `pointsTo_u32 0 (sp - 8) w2`) from their own frame ownership.
-/

namespace Project.Mergesort.Func28Proof

open Wasm Wasm.SmallStep

/-- `func28`'s body equals `template_rust_oom 20`.
    Proved by kernel reduction of the WAT-decoded literal. -/
theorem func28_body_eq :
    Project.Mergesort.func28 = template_rust_oom 20 := rfl

/-- `RustOOMContractAt` at callee abs-index 20 for Mergesort's `rust_oom`.
    Contextual instantiation: `rustOOM_instantiate` applied at index 20.
    Frame tokens are premises supplied by the caller. -/
theorem func28_rustOOM [WasmSmallStepGS hlc α]
    (sp w1 w2 : UInt32) (hsp : (16 : UInt32) ≤ sp) :
    RustOOMContractAt (α := α) (hlc := hlc) 20 sp w1 w2 :=
  rustOOM_instantiate 20 sp w1 w2 hsp

end Project.Mergesort.Func28Proof
