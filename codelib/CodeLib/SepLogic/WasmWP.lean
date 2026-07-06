import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmRules
import Interpreter.Wasm

/-! # Prop-level Weakest Precondition for Wasm

`wp_wasm_prop` — the fuel-abstracted Prop-level weakest precondition:
some fuel exists under which the program runs to completion (fallthrough
or return) in a state satisfying `Q`. This is the layer program proofs
compose in: see the `wp_wasm_prop_*` rules in `Adequacy.lean`, which also
defines the iProp-level `wp_wasm` fixpoint and the adequacy bridge from
it down to this predicate. -/

namespace Wasm.SepLogic

open Iris Wasm

def wp_wasm_prop (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop) : Prop :=
  ∃ fuel, match exec fuel m st locals prog env with
  | .Fallthrough st' _ => Q st' []
  | .Return st' vals => Q st' vals
  | _ => False

/-! ## Per-instruction ownership rules in iProp

Each rule describes how one instruction transforms ownership.
These compose sequentially for straight-line code (swap).
For loops, bi_least_fixpoint wraps the composition. -/

variable [inst : WasmHeapGS]

-- load64: need ownership to read, ownership preserved
def wp_load64 (addr : UInt32) (v : UInt64)
    (Q : IProp WasmHeapGF) : IProp WasmHeapGF :=
  iprop% (pointsTo_u64 addr v) ∗ (pointsTo_u64 addr v -∗ Q)

-- store64: consume old ownership, produce new
def wp_store64 (addr : UInt32) (old_v new_v : UInt64)
    (Q : IProp WasmHeapGF) : IProp WasmHeapGF :=
  iprop% (pointsTo_u64 addr old_v) ∗ (pointsTo_u64 addr new_v -∗ Q)

end Wasm.SepLogic
