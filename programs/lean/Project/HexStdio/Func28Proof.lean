import Project.HexStdio.Program
import CodeLib.RustStd.FinishGrow

/-!
# `finish_grow` instantiation for HexStdio `func28`

`func28` (absolute Wasm index 31) is the
`_RNvMs0_NtNtCsebHcaeoSrxy_5alloc7raw_vec6RawVec11finish_grow` function
compiled into the hex_stdio crate.

This file provides the contextual instantiation:

1. `func28_body_eq` — `rfl` proof that `func28`'s body is exactly
   `template_finish_grow 18 14 15`.

2. `func28_finishGrow` — the forward application of `finishGrow_instantiate`
   at call-target triple `(18, 14, 15)`.  Consumers supply the two callee
   hypotheses (realloc WP and alloc-zeroed WP) from their own context.
-/

namespace Project.HexStdio.Func28Proof

open Wasm Wasm.SmallStep

/-- `func28`'s body equals `template_finish_grow 18 14 15`.
    Proved by kernel reduction of the WAT-decoded literal. -/
theorem func28_body_eq :
    Project.HexStdio.func28 = template_finish_grow 18 14 15 := rfl

/-- `FinishGrowContractAt` at call-target triple `(18, 14, 15)` for
    HexStdio's `finish_grow`.  Contextual instantiation:
    `finishGrow_instantiate` applied at indices 18, 14, 15. -/
theorem func28_finishGrow [WasmSmallStepGS hlc α] :
    FinishGrowContractAt (α := α) (hlc := hlc) 18 14 15 :=
  finishGrow_instantiate 18 14 15

end Project.HexStdio.Func28Proof
