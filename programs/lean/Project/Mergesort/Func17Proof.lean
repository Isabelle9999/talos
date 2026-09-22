import Project.Mergesort.Program
import CodeLib.RustStd.AllocErrorHandler

/-!
# `alloc_error_handler` instantiation for Mergesort `func17`

`func17` (absolute Wasm index 20) is the `alloc_error_handler` forwarder
compiled into the mergesort crate.  Its body is
`[.localGet 0, .call 21, .unreachable]`, which exactly matches
`template_alloc_error_handler 21`.

1. `func17_body_eq` — `rfl` proof tying the WAT-decoded literal to the template.
2. `func17_allocErrorHandler` — forward application of `allocErrorHandler_instantiate`
   at callee abs-index 21 (the level-3 panic hook dispatcher).
-/

namespace Project.Mergesort.Func17Proof

open Wasm Wasm.SmallStep

/-- `func17`'s body equals `template_alloc_error_handler 21`.
    Proved by kernel reduction of the WAT-decoded literal. -/
theorem func17_body_eq :
    Project.Mergesort.func17 = template_alloc_error_handler 21 := rfl

/-- `AllocErrorHandlerContractAt` at callee abs-index 21 for Mergesort's
    `alloc_error_handler`.  Contextual instantiation via `allocErrorHandler_instantiate`. -/
theorem func17_allocErrorHandler [WasmSmallStepGS hlc α] :
    AllocErrorHandlerContractAt (α := α) (hlc := hlc) 21 :=
  allocErrorHandler_instantiate 21

end Project.Mergesort.Func17Proof
