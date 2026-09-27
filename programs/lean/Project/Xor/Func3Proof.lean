import Project.Xor.Program
import CodeLib.RustStd.BumpAlloc

/-!
# `bump_alloc` instantiation for Xor `func3`

`func3` (absolute Wasm index 6) is the `__rust_alloc` / bump-allocator function
compiled into the xor crate.

1. `func3_body_eq` — `rfl` proof that `func3`'s body is exactly
   `template_bump_alloc 1048576 1048592 7`.

2. `func3_bumpAlloc` — the forward application of `bumpAlloc_instantiate`
   at `(cursorAddr, heapBase, k) = (1048576, 1048592, 7)`.
-/

namespace Project.Xor.Func3Proof

open Wasm Wasm.SmallStep

/-- `func3`'s body equals `template_bump_alloc 1048576 1048592 7`.
    Proved by kernel reduction of the WAT-decoded literal. -/
theorem func3_body_eq :
    Project.Xor.func3 = template_bump_alloc 1048576 1048592 7 := rfl

/-- `BumpAllocContractAt` at `(cursorAddr, heapBase, k) = (1048576, 1048592, 7)` for
    Xor's bump allocator.  Contextual instantiation via `bumpAlloc_instantiate`. -/
theorem func3_bumpAlloc [WasmSmallStepGS hlc α]
    (m : Module) (hmIs64 : m.memIs64 = false) :
    BumpAllocContractAt (α := α) (hlc := hlc) m hmIs64 1048576 1048592 7 :=
  bumpAlloc_instantiate m hmIs64 1048576 1048592 7

end Project.Xor.Func3Proof
