import Project.HexStdio.Program
import CodeLib.RustStd.GrowAmortized

/-!
# `grow_amortized` instantiation for HexStdio `func20`

`func20` (absolute Wasm index 23) is the
`_RNvMs0_NtNtCsebHcaeoSrxy_5alloc7raw_vec6RawVec14grow_amortized` function
compiled into the hex_stdio crate.

This file provides the contextual instantiation:

1. `func20_body_eq` — `rfl` proof that `func20`'s body is exactly
   `template_grow_amortized 60 31`.

2. `func20_growAmortized` — the forward application of `growAmortized_instantiate`
   at call-target pair `(60, 31)`.  Consumers supply the `FinishGrowContractAt`
   hypothesis from their own context.
-/

namespace Project.HexStdio.Func20Proof

open Wasm Wasm.SmallStep

/-- `func20`'s body equals `template_grow_amortized 60 31`.
    Proved by kernel reduction of the WAT-decoded literal. -/
theorem func20_body_eq :
    Project.HexStdio.func20 = template_grow_amortized 60 31 := rfl

/-- `GrowAmortizedContractAt` at call-target pair `(60, 31)` for
    HexStdio's `grow_amortized`.  Contextual instantiation:
    `growAmortized_instantiate` applied at indices 60, 31. -/
theorem func20_growAmortized [WasmSmallStepGS hlc α] :
    GrowAmortizedContractAt (α := α) (hlc := hlc) 60 31 :=
  growAmortized_instantiate 60 31

end Project.HexStdio.Func20Proof
