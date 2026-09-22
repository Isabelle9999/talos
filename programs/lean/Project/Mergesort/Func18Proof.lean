import Project.Mergesort.Program
import CodeLib.RustStd.AllocErrorHookDispatch

/-!
# Level-3 body equation for Mergesort `func18`

`func18` (absolute Wasm index 21) is the alloc-error hook dispatcher compiled
into the mergesort crate.  Its relocated immediates are:

- `hookPtrOffset = 1049504` — data address of the alloc-error hook function-
  pointer slot (mergesort-specific `const` class).
- `typeIdx = 0`, `tableIdx = 0` — `call_indirect` type and table indices.

`func18_body_eq` proves the body equals `template_alloc_error_hook_dispatch`
by `rfl`.

**No WP contract is stated or proved.**  See `AllocErrorHookDispatch.lean` for
the reasons: `call_indirect` has no `twp_callIndirect` total-WP rule, and the
contract of the hook function resolved at runtime is unknown at this level.
Closing the chain requires:
1. A `twp_callIndirect` rule (table ownership + type-checked callee WP).
2. The WP contract of the hook function the table entry points to.
-/

namespace Project.Mergesort.Func18Proof

open Wasm Wasm.SmallStep

/-- `func18`'s body equals `template_alloc_error_hook_dispatch 1049504 0 0`.
    Proved by kernel reduction of the WAT-decoded literal. -/
theorem func18_body_eq :
    Project.Mergesort.func18 = template_alloc_error_hook_dispatch 1049504 0 0 := rfl

end Project.Mergesort.Func18Proof
