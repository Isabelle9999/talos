import Lean
import Iris.ProofMode
open Lean Elab Tactic

-- wpure rule
-- apply a pure wasm instruction rule and discharge hstep with σ' = σ.
-- rule must leave only hstep unresolved after apply; pass any side conditions
-- in the rule term:
--   wpure wp_wasm_const               (v inferred from goal)
--   wpure (wp_wasm_localGet hget)     (hget : locals.get i = some v)
--   wpure (wp_wasm_add hstack)        (hstack : locals.values = ...)
-- the wp_wasm continuation goal is left open after the macro runs.
elab "wpure" rule:term : tactic => do
  evalTactic (← `(tactic| apply $rule))
  evalTactic (← `(tactic| intro σ))
  evalTactic (← `(tactic| iintro Hσ))
  evalTactic (← `(tactic| imodintro))
  evalTactic (← `(tactic| iexists σ))
  evalTactic (← `(tactic| isplitl [Hσ]))
  evalTactic (← `(tactic| next => iexact Hσ))

-- wpures: apply all consecutive pure wasm instruction rules automatically.
-- stops at memory (load/store), call, block, loop, ret, or empty program.
-- uses approach A: try each rule in sequence, rollback on failure.
elab "wpures" : tactic => do
  let tryStep (act : TacticM Unit) : TacticM Bool := do
    let s ← saveState
    try
      act
      evalTactic (← `(tactic| intro σ))
      evalTactic (← `(tactic| iintro Hσ))
      evalTactic (← `(tactic| imodintro))
      evalTactic (← `(tactic| iexists σ))
      evalTactic (← `(tactic| isplitl [Hσ]))
      evalTactic (← `(tactic| next => iexact Hσ))
      return true
    catch _ =>
      restoreState s
      return false
  let tryPure : TacticM Bool := do
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_const))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_localGet (hget := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_globalGet (hget := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_localSet (hstack := rfl) (hset := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_add (hstack := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_sub (hstack := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_mul (hstack := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_and (hstack := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_or (hstack := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_xor (hstack := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_eqz (hstack := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_shl (hstack := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_shr (hstack := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_ltU (hstack := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_leU (hstack := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_gtU (hstack := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_geU (hstack := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_ne (hstack := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_eq (hstack := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_drop (hstack := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_select (hstack := rfl)))) then return true
    if ← tryStep (evalTactic (← `(tactic| apply wp_wasm_globalSet (hstack := rfl) (hbound := rfl)))) then return true
    return false
  let rec loop : Nat → TacticM Unit := fun
    | 0 => return
    | n + 1 => do
      if ← tryPure then loop n
  loop 1000

-- wmem: future pattern for memory load/store instructions.
-- load/store rules change σ (σ' ≠ σ), so the heap-unchanged proof above
-- does not apply.  ownership transfer via pointsTo_u64 must happen before
-- the hstep obligation can be closed.  use wp_load64/wp_store64 manually
-- until a wmem tactic is added here.
