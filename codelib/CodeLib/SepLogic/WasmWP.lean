import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmRules
import Interpreter.Wasm

/-! # Weakest Precondition for Wasm in iProp

Defines wp_wasm: the WP over Talos's big-step semantics,
living inside iris-lean's iProp. This is approach (b):
bypass the Language typeclass, define WP directly.
-/

namespace Wasm.SepLogic

open Iris Wasm

variable [inst : WasmHeapGS]

/-! The WP for a single Wasm instruction.
Given an instruction, a store, locals, and a postcondition,
returns an iProp asserting the instruction is safe and
the postcondition holds afterward. -/

-- First: what types do we need?
#check @execOne
-- execOne : ℕ → Module → Store α → Locals → Instruction → HostEnv α → Continuation α

-- The WP says: there EXISTS enough fuel such that
-- executing with that fuel satisfies the postcondition.
-- For now, state it as a Prop that lifts into iProp.

-- First check exec's actual signature
#check @exec
#check @run

#print Continuation
def wp_wasm_prop (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop) : Prop :=
  ∃ fuel, match exec fuel m st locals prog env with
  | .Fallthrough st' _ => Q st' []
  | .Return st' vals => Q st' vals
  | _ => False

def wp_wasm (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → IProp WasmHeapGF) : IProp WasmHeapGF :=
  sorry -- lift wp_wasm_prop into iProp via ⌜pure⌝

#check @wp_wasm_prop
#check @wp_wasm

end Wasm.SepLogic