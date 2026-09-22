import Project.ByteEcho.Program
import CodeLib.RustStd.AllocErrorHandler

/-!
# `alloc_error_handler` instantiation for ByteEcho `func7`

`func7` (absolute Wasm index 10) is the `alloc_error_handler` forwarder
compiled into the byte_echo crate.  Its body is
`[.localGet 0, .call 11, .unreachable]`, which exactly matches
`template_alloc_error_handler 11`.

1. `func7_body_eq` — `rfl` proof tying the WAT-decoded literal to the template.
2. `func7_allocErrorHandler` — forward application of `allocErrorHandler_instantiate`
   at callee abs-index 11 (the level-3 panic hook dispatcher).
-/

namespace Project.ByteEcho.Func7Proof

open Wasm Wasm.SmallStep

/-- `func7`'s body equals `template_alloc_error_handler 11`.
    Proved by kernel reduction of the WAT-decoded literal. -/
theorem func7_body_eq :
    Project.ByteEcho.func7 = template_alloc_error_handler 11 := rfl

/-- `AllocErrorHandlerContractAt` at callee abs-index 11 for ByteEcho's
    `alloc_error_handler`.  Contextual instantiation via `allocErrorHandler_instantiate`. -/
theorem func7_allocErrorHandler [WasmSmallStepGS hlc α] :
    AllocErrorHandlerContractAt (α := α) (hlc := hlc) 11 :=
  allocErrorHandler_instantiate 11

end Project.ByteEcho.Func7Proof
