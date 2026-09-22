import Project.Mergesort.Program
import CodeLib.RustStd.Template
import CodeLib.RustStd.AllocErrorHandler

/-!
# `rust_oom` instantiation for Mergesort `func28`

`func28` (absolute Wasm index 31) is the
`_RNvNtCsebHcaeoSrxy_3std5alloc8rust_oom` function compiled into the
mergesort crate.

Mergesort excludes functions 12–55 from closed contracts.  This file therefore
provides only the *contextual instantiation*:

1. `func28_body_eq` — a `rfl` proof that `func28`'s body is exactly
   `template_rust_oom 20`, tying the WAT-decoded literal to the abstract
   template.

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

/-- Two-level composed contract for Mergesort `func28` (rust_oom) and
    `func17` (alloc_error_handler).

    Pairs `RustOOMContractAt 20` (level-1, depends on abs 20 = alloc_error_handler)
    with `AllocErrorHandlerContractAt 21` (level-2, depends on abs 21 = panic hook
    dispatcher).  Together they show that every link in the L1→L2 chain is
    closed by abstract contracts, and the sole remaining external dependency is
    abs 21 — the level-3 panic hook dispatcher.

    *Note:* bridging these two contracts into a single end-to-end WP would
    require `twp_call` for the `func28 → func17` call edge, which needs
    `runtimeModuleOwn callerId runtimeModule` — a module-specific Iris resource
    that is not available in the abstract `AllocErrorHandlerContractAt` style.
    The conjunction is therefore the tightest honest composition available
    at this level. -/
theorem func28_L1_L2_chain [WasmSmallStepGS hlc α]
    (sp w1 w2 : UInt32) (hsp : (16 : UInt32) ≤ sp) :
    RustOOMContractAt (α := α) (hlc := hlc) 20 sp w1 w2 ∧
    AllocErrorHandlerContractAt (α := α) (hlc := hlc) 21 :=
  ⟨rustOOM_instantiate 20 sp w1 w2 hsp, allocErrorHandler_instantiate 21⟩

end Project.Mergesort.Func28Proof
