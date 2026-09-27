import Project.ByteEcho.Program
import CodeLib.RustStd.BumpAlloc

/-!
# `bump_alloc` instantiation for ByteEcho `func2`

`func2` (absolute Wasm index 5) is the `__rust_alloc` / bump-allocator function
compiled into the byte_echo crate.

1. `func2_body_eq` — `rfl` proof that `func2`'s body is exactly
   `template_bump_alloc 1048576 1048592 6`.

2. `func2_bumpAlloc` — the forward application of `bumpAlloc_instantiate`
   at `(cursorAddr, heapBase, k) = (1048576, 1048592, 6)`.
-/

namespace Project.ByteEcho.Func2Proof

open Wasm Wasm.SmallStep

/-- `func2`'s body equals `template_bump_alloc 1048576 1048592 6`.
    Proved by kernel reduction of the WAT-decoded literal. -/
theorem func2_body_eq :
    Project.ByteEcho.func2 = template_bump_alloc 1048576 1048592 6 := rfl

/-- `BumpAllocContractAt` at `(cursorAddr, heapBase, k) = (1048576, 1048592, 6)` for
    ByteEcho's bump allocator.  Contextual instantiation via `bumpAlloc_instantiate`. -/
theorem func2_bumpAlloc [WasmSmallStepGS hlc α]
    (m : Module) (hmIs64 : m.memIs64 = false) :
    BumpAllocContractAt (α := α) (hlc := hlc) m hmIs64 1048576 1048592 6 :=
  bumpAlloc_instantiate m hmIs64 1048576 1048592 6

end Project.ByteEcho.Func2Proof
