import Project.ByteEcho.Spec

set_option maxHeartbeats 0

/-!
# Proof of `ByteEchoSpec`

## Proof strategy

The proof is a TWP composition over `func0`'s body (the exported `byte_echo`,
absolute function index 3):

1. **`call 4`** (func1, no-op init) — discharged by `twp_callFuncDirect`.
2. **`call 5`** (func2, bump allocator) — closed via `Func2Proof.func2_bumpAlloc`
   (`bumpAlloc_instantiate` at `cursorAddr = 1048576`, `heapBase = 1048592`,
   `k = 6`).  The page-count `by_cases hfits : requiredPages ≤ pages.toUInt32`
   produces two branches:
   - **h_success**: alloc returned a non-null pointer → continue to host calls.
   - **h_oom**: alloc invokes `call 6` (the OOM wrapper, func3) which calls
     `talos.oom` (import 2) → trap → `outOfMemory` outcome.
3. **Host calls** (imports 0, 1, 2 and the stdlib wrappers func5–func9):
   `twp_callHost` + host-state adequacy (`hostStateAgreesAt`).

## Status: BLOCKED — awaiting host-rule merge

The total WP rules for host calls (`twp_callHost`, `hostStateAgreesAt`) and the
host-state adequacy bridge are being moved from `programs/lean/HexEncodeStdio`
into `codelib` on the `sep-logic-merge-sort` base branch.  Resume this proof
after that merge lands; the TWP skeleton above is complete, only the host steps
remain.
-/

namespace Project.ByteEcho.Proof

open Wasm Universal
open Wasm.SmallStep
open Project.ByteEcho.Spec

end Project.ByteEcho.Proof
