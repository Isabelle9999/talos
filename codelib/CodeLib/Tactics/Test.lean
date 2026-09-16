import CodeLib.SepLogic.SmallStepAdequacyExamples
import CodeLib.Tactics.Pure

/-!
# `wasm_pures` regression tests

Three theorems taken from `SmallStepAdequacyExamples.lean` that exercise
`wasm_pures` in place of the original hand-written `wasm_twp_pures [...]` rule
lists.  The original proof text replaced by `wasm_pures` is quoted in each
theorem's docstring.

## `#print axioms` status

Each test theorem should print `'<name>' does not depend on any axioms`
(or only the expected Iris / Classical axioms — no `sorryAx`).
-/

namespace Wasm.SmallStep

open Iris OFE COFE BI Iris.BI Iris.Algebra Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open CodeLib.Tactics

-- ─── Test 1 ──────────────────────────────────────────────────────────────────
-- Source: SmallStepAdequacyExamples.lean:2068
-- Original: wasm_twp_pures [twp_block twp_localGet twp_localGet]

/-- `i32.ge_s` on the two parameters: returns 1 if `a ≥ b` as signed 32-bit
integers, 0 otherwise.
(Identical to `signedBranch_terminatesWith` except the first `wasm_twp_pures`
call at line 2068 is replaced by `wasm_pures`.) -/
theorem signedBranch_terminatesWith_pures (a b : UInt32) :
    TerminatesWith (signedBranchConfig a b)
      (fun values _store => values = [.i32 (if a.toInt32 ≥ b.toInt32 then 1 else 0)]) := by
  apply wasm_smallStep_terminates (signedBranchConfig a b)
    (fun values => values = [.i32 (if a.toInt32 ≥ b.toInt32 then 1 else 0)])
  intro hlc gs
  have hbody : signedBranchModule.funcs[0]!.body =
      [.block 0 0 [.localGet 0, .localGet 1, .geS, .br_if 0, .const 0, .ret],
        .const 1, .ret] := rfl
  simp only [signedBranchConfig, hbody]
  wasm_pures
  by_cases h : a.toInt32 ≥ b.toInt32
  · iapply twp_geS (result := 1) (by simp [h])
    iapply twp_brIf (condition := 1) (by decide) <;> try rfl
    wasm_twp_pures [twp_const]
    wasm_twp_terminal_value twp_returnFromFunction
    ipureexact (by simp [h])
  · iapply twp_geS (result := 0) (by simp [h])
    wasm_twp_pures [twp_brIfZero twp_const]
    wasm_twp_terminal_value twp_returnFromFunction
    ipureexact (by simp [h])

-- ─── Tests 2 and 3: standalone TWP entailments ────────────────────────────────
-- These use the same section/instance pattern as SmallStepTotalLifting.lean so
-- that the WP notation resolves correctly.

section wasmPuresTests

variable {hlc : HasLC} [WasmSmallStepGS hlc α]
variable {Terminal : Type} [view : TerminalView α Terminal]
local instance (priority := high) testTerminalLanguage :
    Language (Expr α) (MachineStore α) StepKind Terminal :=
  TerminalView.canonicalLanguage
local instance (priority := high) testTerminalIrisGS :
    @IrisGS_gen hlc (Expr α) Terminal (MachineStore α) StepKind
      testTerminalLanguage (WasmHeapGF α) :=
  { numLatersPerStep _ := 0
    forkPost _ := iprop(True)
    stateInterp_mono _ _ _ _ := by iintro $ }
variable {s : Stuckness} {E : CoPset} {Φ : Terminal → IProp (WasmHeapGF α)}

-- ─── Test 2 ──────────────────────────────────────────────────────────────────
-- Source: SmallStepAdequacyExamples.lean:2206
-- Original: wasm_twp_pures [twp_const twp_localGet twp_const]
--
-- Exercises the same three-step reduction as in fillThenRead_terminatesWith:
--   [.const 0, .localGet 0, .const 4, .memoryFill, ...]
-- The three pure steps push .i32 0, .i32 val, .i32 4 onto the operand stack.

/-- `wasm_pures` applies `twp_const`, `twp_localGet`, `twp_const` to reproduce
the three pure steps at SmallStepAdequacyExamples.lean:2206. -/
theorem test_fillThenRead_pure_steps (val : UInt32) :
    WP (.running
        ⟨⟨[.i32 val], [], [.i32 4, .i32 val, .i32 0]⟩,
          [.memoryFill, .const 0, .load32 0],
          1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
        ⟨⟨[.i32 val], [], []⟩,
          [.const 0, .localGet 0, .const 4, .memoryFill, .const 0, .load32 0],
          1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  -- Original proof text (line 2206): wasm_twp_pures [twp_const twp_localGet twp_const]
  iintro H
  wasm_pures
  iexact H

-- ─── Test 3 ──────────────────────────────────────────────────────────────────
-- Source: SmallStepAdequacyExamples.lean:2256
-- Original: wasm_twp_pures [twp_localGet]
--
-- Exercises the single localGet step from exceptionLifecycle_terminatesWith:
--   [.localGet 0, .throwI 0]
-- After the step, .i32 arg is pushed and code tail is [.throwI 0].

/-- `wasm_pures` applies a single `twp_localGet` step to reproduce the one-step
reduction at SmallStepAdequacyExamples.lean:2256. -/
theorem test_exceptionLifecycle_pure_steps (arg : UInt32) :
    WP (.running
        ⟨⟨[.i32 arg], [], [.i32 arg]⟩,
          [.throwI 0],
          1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
        ⟨⟨[.i32 arg], [], []⟩,
          [.localGet 0, .throwI 0],
          1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  -- Original proof text (line 2256): wasm_twp_pures [twp_localGet]
  iintro H
  wasm_pures
  iexact H

-- ─── Test 4: #guard_msgs — "goal is not a TWP/WP goal" ─────────────────────
-- Verifies that wasm_pure emits the correct error when the goal is a plain
-- Lean Prop rather than a WP proposition.
-- Source pattern: iris BigOp.lean:595-596; aesop AesopTest/125.lean:11-17

/-- error: wasm_pure: goal is not a TWP/WP goal (expected TotalWp.totalWp or Wp.wp head or iris envs_entails wrapper; got True) -/
#guard_msgs in
example : True := by
  wasm_pure

-- ─── Test 5: #guard_msgs — "no rule registered" ─────────────────────────────
-- Verifies that wasm_pure emits the correct error message when the instruction
-- head has no registered rule in the TWP registry.
-- NOTE: The "unsolved side goal" failure path (wasm_pure: unsolved side goal ...)
-- is not tested here because exercising it requires registering a side-condition
-- rule in a file that CodeLib.lean imports, which is a novel pattern outside the
-- evidenced codebase.

/-- error: wasm_pure: no rule registered for memoryFill -/
#guard_msgs in
example :
    WP (.running ⟨⟨[], [], []⟩, [.memoryFill], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], []⟩, [.memoryFill], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure

end wasmPuresTests

-- ─── WP tests (partial WP, `{{ Φ }}` notation) ───────────────────────────────
-- These use the same variable pattern as SmallStepLifting.lean:17-23.

section wasmWpTests

variable {hlc : HasLC} [WasmSmallStepGS hlc α]
local instance testWpIrisGS : IrisGS_gen hlc (Expr α) (WasmHeapGF α) := instIrisGS
variable {s : Stuckness} {E : CoPset}
variable {Φ : List Value → IProp (WasmHeapGF α)}

-- ─── Test 5 ──────────────────────────────────────────────────────────────────
-- Source: SmallStepLifting.lean:214-225 (wp_const)
-- Tests that wasm_pure dispatches correctly under the `wp` modality
-- (partial WP, `{{ Φ }}` notation), mirroring Test 2 for the `twp` modality.

/-- `wasm_pure` applies `wp_const` to a partial-WP goal (`{{ Φ }}` notation). -/
theorem test_wp_const_step (val : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.i32 val]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], []⟩, [.const val], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

end wasmWpTests

end Wasm.SmallStep
