import Lean
import CodeLib.Tactics.Registry

open Lean Meta Elab Tactic

namespace CodeLib.Tactics

/-- Return the last string component of `n` as a fresh simple `Name`.
Used to turn a fully-qualified constructor name such as
`Wasm.Instruction.const` into the registry key `Name.mkSimple "const"`. -/
private def nameLastSimple : Name → Name
  | .str _ s => .str .anonymous s
  | n        => n

/-- Given a Lean expression that is either a WP IProp directly or the iris
proof-mode wrapper `envs_entails Γ (WP ...)`, return the WP IProp and its
modality key string:
- `"twp"` for `TotalWp.totalWp`  (notation `WP e @ s; E [{ Φ }]`, WeakestPre.lean:72)
- `"wp"`  for `Wp.wp`            (notation `WP e @ s; E {{ Φ }}`, WeakestPre.lean:55)
Throws if neither matches. -/
private def unwrapIrisGoal (goalTy : Expr) : MetaM (Expr × String) := do
  let goalTy := goalTy.consumeMData
  let fn := goalTy.getAppFn
  -- Direct case: TotalWp.totalWp or Wp.wp is the head
  if fn.isConst then
    let n := fn.constName!.getString!
    if n == "totalWp" then return (goalTy, "twp")
    if n == "wp"       then return (goalTy, "wp")
  -- Iris proof-mode case: envs_entails Γ (WP ...)
  -- The iris goal is the last explicit argument.
  let args := goalTy.getAppArgs
  if h : args.size > 0 then
    let inner := (args[args.size - 1]).consumeMData
    let fn' := inner.getAppFn
    if fn'.isConst then
      let n' := fn'.constName!.getString!
      if n' == "totalWp" then return (inner, "twp")
      if n' == "wp"       then return (inner, "wp")
  throwError "wasm_pure: goal is not a TWP/WP goal \
    (expected TotalWp.totalWp or Wp.wp head or iris envs_entails wrapper; \
    got {goalTy})"

/-- Resolve the instruction-head key and modality from the WP goal in `goal`.

The goal type must be (or wrap) a WP proposition of the form
  `TotalWp.totalWp s E (Expr.running thread) Φ`  or
  `Wp.wp          s E (Expr.running thread) Φ`
where `thread.code` reduces (under default-transparency `whnf`) to a concrete
`List Instruction`.  Returns `(ctorKey, modality)` where `ctorKey` is the
unqualified constructor name (e.g. `Name.mkSimple "const"`) and `modality`
is `"twp"` or `"wp"`. -/
private def instrHeadKey (goal : MVarId) : MetaM (Name × String) := do
  let goalTy ← goal.getType >>= instantiateMVars
  let (wpExpr, modality) ← unwrapIrisGoal goalTy
  let args := wpExpr.getAppArgs
  if args.size < 4 then
    throwError "wasm_pure: WP applied to fewer than 4 args"
  -- args[size-4] = s, args[size-3] = E, args[size-2] = e, args[size-1] = Φ
  let e  := args[args.size - 2]!
  let e' ← whnf e
  let eFn   := e'.getAppFn
  let eArgs := e'.getAppArgs
  unless eFn.isConst && eFn.constName!.getString! == "running" do
    throwError "wasm_pure: Wasm expression is not .running (got {eFn})"
  if eArgs.size < 1 then
    throwError "wasm_pure: Expr.running has no thread argument"
  let thread  := eArgs[eArgs.size - 1]!
  let thread' ← whnf thread
  let tArgs := thread'.getAppArgs
  if tArgs.size < 3 then
    throwError "wasm_pure: could not extract code field from thread state \
      (got {tArgs.size} args for ThreadState constructor)"
  let code  := tArgs[2]!
  let code' ← whnf code
  let codeFn := code'.getAppFn
  if codeFn.isConst && codeFn.constName!.getString! == "nil" then
    return (Name.mkSimple "nil", modality)
  let cArgs := code'.getAppArgs
  if cArgs.size < 2 then
    throwError "wasm_pure: code list is not fully reduced (got {cArgs.size} \
      args for cons, need ≥ 2)"
  let instr  := cArgs[1]!
  let instr' ← whnf instr
  let instrFn := instr'.getAppFn
  unless instrFn.isConst do
    throwError "wasm_pure: instruction head did not reduce to a constructor"
  return (nameLastSimple instrFn.constName!, modality)

/-- Apply one pure-step rule (TWP or WP) determined by the head of `thread.code`.

Looks up the instruction constructor in the `@[wasm_rule]` registry under
the modality derived from the goal (`twp` for `[{ Φ }]`, `wp` for `{{ Φ }}`).
Calls iris `iapply` with the theorem as the pmTerm.  For `needsRfl = true`
rules, the pmTerm is `thm rfl`, which discharges the side condition inline.

After `iapply`, asserts that no extra side goals remain.  If the rule left
a side goal that normalisation did not close, fails with a named error
(mirroring the `throwIPMError` pattern in HeapLang/ProofMode.lean:364).

**Errors** (with the instruction name) if:
- the goal is not a TWP/WP goal (bare or iris-mode-wrapped);
- `thread.code` cannot be reduced to a concrete instruction;
- no rule is registered for the head constructor;
- the applied rule leaves an unsolved side goal. -/
elab "wasm_pure" : tactic => do
  let goal ← getMainGoal
  let (ctorKey, modality) ← instrHeadKey goal
  let env ← getEnv
  match getWasmRule env (Name.mkSimple modality) ctorKey with
  | none =>
    throwError "wasm_pure: no rule registered for {ctorKey}"
  | some entry =>
    let thmTerm : TSyntax `term := ⟨(mkIdent entry.thmName).raw⟩
    let pmt : TSyntax `pmTerm ←
      if entry.needsRfl then do
        let rflTerm : TSyntax `term := ⟨(mkIdent `rfl).raw⟩
        let appExpr ← `($thmTerm $rflTerm)
        `(pmTerm| $appExpr:term)
      else
        `(pmTerm| $thmTerm:term)
    evalTactic (← `(tactic| iapply $pmt))
    -- Defensive: detect any side goals the rule left open.
    -- Pure-step rules produce exactly one new goal (the continuation WP).
    -- Extra goals indicate a misregistered rule.
    let newGoals ← getGoals
    for g in newGoals.drop 1 do
      let sideGoalTy ← g.getType >>= instantiateMVars
      throwError "wasm_pure: unsolved side goal {sideGoalTy}"

/-- Repeat `wasm_pure` until the goal changes to one where no rule is
registered or the goal is no longer a WP goal.

The pre-check (`instrHeadKey` + `getWasmRule`) is wrapped in `try … catch`
so that all expected termination signals (wrong goal type, un-reducible code,
unregistered head) stop the loop silently.  `evalTactic wasm_pure` is
deliberately NOT wrapped: errors from it (including "unsolved side goal")
propagate to the caller rather than being swallowed. -/
private partial def wasmPuresLoop : TacticM Unit := do
  let goals ← getGoals
  if goals.isEmpty then return
  let goal ← getMainGoal
  let maybeEntry : Option WasmRuleEntry ← do
    try
      let (ctorKey, modality) ← instrHeadKey goal
      let env ← getEnv
      pure (getWasmRule env (Name.mkSimple modality) ctorKey)
    catch _ => pure none
  match maybeEntry with
  | none => return
  | some _ =>
    evalTactic (← `(tactic| wasm_pure))
    wasmPuresLoop

elab "wasm_pures" : tactic => wasmPuresLoop

end CodeLib.Tactics
