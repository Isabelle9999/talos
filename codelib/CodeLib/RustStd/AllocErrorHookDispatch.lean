import CodeLib.SepLogic.SmallStepOutcomeLanguage

/-!
# `CodeLib.RustStd.AllocErrorHookDispatch`

Level-3 template for the alloc-error hook dispatcher (body class `...`).

The function is called by `alloc_error_handler` (level-2) with a pointer to
a `Layout { size: usize, align: NonZeroUsize }`.  It loads the two i32 fields
from that pointer, then dispatches via `call_indirect` to a hook function
whose address is stored in a crate-specific static slot in linear memory.

**Template rule**: every relocated immediate is a Lean parameter.
- `hookPtrOffset : UInt32` — data address (`const` class) of the alloc-error
  hook function-pointer slot; differs per crate (1049504 for mergesort,
  1048580 for byte_echo).
- `typeIdx tableIdx : Nat` — `call_indirect` type and table indices
  (`call_indirect` class); currently both 0.

`template_alloc_error_hook_dispatch hookPtrOffset typeIdx tableIdx` is the body.
Body equations for each crate are proved by `rfl`.

**No contract is stated or proved here.  STOP RULE.**

Closing the WP chain requires:
1. A `twp_callIndirect` total-WP rule — it requires table ownership and a
   type-checked WP for the resolved callee; this machinery has not yet been
   built into `SmallStepTotalLifting`.
2. The WP contract of the hook function the table entry points to (the actual
   alloc-error handler registered at runtime via `set_alloc_error_hook`, or
   the default handler if none is set).
Once both are available the chain can be closed by composing them with this
template's body equation.
-/

namespace Wasm.SmallStep

open Wasm

/-- Full body of the alloc-error hook dispatcher, parameterised by all relocated immediates.
    Consumers prove `func.body = template_alloc_error_hook_dispatch offset tIdx tbIdx`
    by `rfl`. -/
def template_alloc_error_hook_dispatch
    (hookPtrOffset : UInt32) (typeIdx tableIdx : Nat) : Wasm.Program :=
  [ .localGet 0, .load32 0, .localGet 0, .load32 4
  , .const 0, .load32 hookPtrOffset
  , .localTee 0, .const 1, .localGet 0, .select
  , .callIndirect typeIdx tableIdx, .unreachable ]

end Wasm.SmallStep
