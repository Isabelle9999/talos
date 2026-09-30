import CodeLib.SepLogic.SmallStepAdequacyExamples
import CodeLib.Tactics.Pure
import CodeLib.Tactics.Mem
import CodeLib.Tactics.Control

/-!
# Wasm tactic regression tests

145 named theorems and 13 `#guard_msgs` error-message checks covering
`wasm_pure`, `wasm_pures`, `wasm_pures using`, `wasm_mem`, `wasm_mem using`,
`wasm_loop`, and `wasm_call`.  Each named theorem is sourced from an existing
proof or exercises a specific dispatch path for newly registered rules.

The TWP single-step tests (section `wasmPuresTests`) cover every rule registered
under `twp` in `Registry.lean`.  The WP single-step tests (section `wasmWpTests`)
cover every rule registered under `wp`, including the i64 comparison rules and
the scalar-float fallback.
-/

namespace Wasm.SmallStep

open Iris OFE COFE BI Iris.BI Iris.Algebra Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open CodeLib.Tactics

-- ─── Test 1 ──────────────────────────────────────────────────────────────────
-- `wasm_pures` replaces the `wasm_twp_pures` call in `signedBranch_terminatesWith`.

/-- `wasm_pures` drives the block/localGet/localGet/geS prefix, leaving `br_if`
for a manual case-split on the symbolic `a.toInt32 ≥ b.toInt32` condition. -/
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
  -- geS produces a symbolic if-expression; normalise it before the br_if case-split.
  by_cases h : a.toInt32 ≥ b.toInt32
  · have hge : (if a.toInt32 ≥ b.toInt32 then (1 : UInt32) else 0) = 1 := by simp [h]
    simp only [hge]
    iapply twp_brIf (condition := 1) (by decide) <;> try rfl
    wasm_twp_pures [twp_const]
    wasm_twp_terminal_value twp_returnFromFunction
    ipureexact rfl
  · have hnge : (if a.toInt32 ≥ b.toInt32 then (1 : UInt32) else 0) = 0 := by simp [h]
    simp only [hnge]
    iapply twp_brIfZero
    wasm_twp_pures [twp_const]
    wasm_twp_terminal_value twp_returnFromFunction
    ipureexact rfl

-- ─── Tests 2 and 3: standalone TWP entailments ────────────────────────────────
-- Same section/instance pattern as the TWP proofs in SmallStepTotalLifting.

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
-- `wasm_pures` applies `twp_const`, `twp_localGet`, `twp_const` from `fillThenRead_terminatesWith`.

/-- `wasm_pures` applies `twp_const`, `twp_localGet`, `twp_const` in sequence. -/
theorem test_fillThenRead_pure_steps (val : UInt32) :
    WP (.running
        ⟨⟨[.i32 val], [], [.i32 4, .i32 val, .i32 0]⟩,
          [.memoryFill, .const 0, .load32 0],
          1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
        ⟨⟨[.i32 val], [], []⟩,
          [.const 0, .localGet 0, .const 4, .memoryFill, .const 0, .load32 0],
          1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H
  wasm_pures
  iexact H

-- ─── Test 3 ──────────────────────────────────────────────────────────────────
-- `wasm_pures` applies a single `twp_localGet` step from `exceptionLifecycle_terminatesWith`.

/-- `wasm_pures` applies a single `twp_localGet` step. -/
theorem test_exceptionLifecycle_pure_steps (arg : UInt32) :
    WP (.running
        ⟨⟨[.i32 arg], [], [.i32 arg]⟩,
          [.throwI 0],
          1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
        ⟨⟨[.i32 arg], [], []⟩,
          [.localGet 0, .throwI 0],
          1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H
  wasm_pures
  iexact H

-- ─── Test 4: #guard_msgs — "goal is not a TWP/WP goal" ─────────────────────
-- `wasm_pure` errors when the goal is a plain Lean Prop, not a WP proposition.

/-- error: wasm_pure: goal is not a TWP/WP goal (expected TotalWp.totalWp or Wp.wp head or iris envs_entails wrapper; got True) -/
#guard_msgs in
example : True := by
  wasm_pure

-- ─── Test 5: #guard_msgs — "no rule registered" ─────────────────────────────
-- `wasm_pure` errors when the instruction head has no registered rule.

/-- error: wasm_pure: no rule registered for memoryFill -/
#guard_msgs in
example :
    WP (.running ⟨⟨[], [], []⟩, [.memoryFill], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], []⟩, [.memoryFill], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure

-- ─── Tests 6–8: wasm_mem ─────────────────────────────────────────────────────

-- ─── Test 6 ──────────────────────────────────────────────────────────────────
-- `wasm_mem` applies `twp_globalGet` with no side conditions.

/-- `wasm_mem` applies `twp_globalGet` with no side conditions. -/
theorem test_wasm_mem_globalGet (globalWord : UInt32) :
    globalPointsToAt 0 0 (.i32 globalWord) ∗
    (globalPointsToAt 0 0 (.i32 globalWord) -∗
      WP (.running ⟨⟨[], [], [.i32 globalWord]⟩, [], 1, [], [], []⟩ : Expr α)
        @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], []⟩, [.globalGet 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hglob, Hcont⟩
  wasm_mem
  iapply Hcont $$ Hglob

-- ─── Test 7 ──────────────────────────────────────────────────────────────────
-- `wasm_mem` applies `twp_load32` for a `load32 4` step; side conditions closed by omega.

/-- `wasm_mem` applies `twp_load32` for a `load32 4` step; omega closes side conditions. -/
theorem test_wasm_mem_load32_nonzero
    (base word : UInt32)
    (hnowrap : (base + 4 : UInt32).toNat = base.toNat + (4 : UInt32).toNat)
    (h1 : ((base + 4) + 1 : UInt32).toNat = (base + 4 : UInt32).toNat + 1)
    (h2 : ((base + 4) + 2 : UInt32).toNat = (base + 4 : UInt32).toNat + 2)
    (h3 : ((base + 4) + 3 : UInt32).toNat = (base + 4 : UInt32).toNat + 3) :
    pointsTo_u32 0 (base + 4) word ∗
    (pointsTo_u32 0 (base + 4) word -∗
      WP (.running ⟨⟨[], [], [.i32 word]⟩, [], 1, [], [], []⟩ : Expr α)
        @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 base]⟩, [.load32 4], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hword, Hcont⟩
  wasm_mem
  iapply Hcont $$ Hword

-- ─── Test 8 ──────────────────────────────────────────────────────────────────
-- `wasm_mem using [UInt32.add_zero]` exercises the addr-variant selection and
-- address normalisation path for `load32 0`.

/-- `wasm_mem using [UInt32.add_zero]` applies `twp_load32_addr` for `load32 0`
with concrete address 4; `UInt32.add_zero` normalises `4 + 0` to `4`. -/
theorem test_wasm_mem_load32_addr_using (word : UInt32) :
    pointsTo_u32 0 (4 : UInt32) word ∗
    (pointsTo_u32 0 (4 : UInt32) word -∗
      WP (.running ⟨⟨[], [], [.i32 word]⟩, [], 1, [], [], []⟩ : Expr α)
        @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 4]⟩, [.load32 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hword, Hcont⟩
  wasm_mem using [UInt32.add_zero]
  iapply Hcont $$ Hword

-- ─── Test 9: #guard_msgs — "pure rule" ───────────────────────────────────────
-- Verifies that wasm_mem emits the correct error when called on an instruction
-- whose registered rule is a pure (not mem) rule.

/-- error: wasm_mem: rule for const is a pure rule; use wasm_pure -/
#guard_msgs in
example :
    WP (.running ⟨⟨[], [], []⟩, [.const 42], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], []⟩, [.const 42], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_mem

-- ─── Test 10: #guard_msgs — wasm_pure on mem-rule instruction ────────────────
-- Verifies that wasm_pure emits the correct error when called on an instruction
-- whose registered rule is a mem rule.

/-- error: wasm_pure: rule for load32 is a mem rule; use wasm_mem -/
#guard_msgs in
example :
    WP (.running ⟨⟨[], [], []⟩, [.load32 0], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], []⟩, [.load32 0], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure

-- ─── Test 11: #guard_msgs — "no rule registered" ─────────────────────────────
-- Verifies that wasm_mem emits the correct error when the instruction head has
-- no registered rule at all.

/-- error: wasm_mem: no rule registered for memoryFill (is this instruction registered with `@[wasm_mem_rule …]`?) -/
#guard_msgs in
example :
    WP (.running ⟨⟨[], [], []⟩, [.memoryFill], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], []⟩, [.memoryFill], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_mem

-- ─── Test 12: #guard_msgs — "no hypothesis found" ────────────────────────────
-- Verifies that wasm_mem emits the correct error when there is no matching
-- pointsTo_u32 hypothesis in the Iris context (zero-match case).

/-- error: wasm_mem: no u32 hypothesis found for effective address base; check the Iris context -/
#guard_msgs in
example (base : UInt32) :
    WP (.running ⟨⟨[], [], [.i32 base]⟩, [.load32 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 base]⟩, [.load32 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro H; wasm_mem

-- ─── Test 13: #guard_msgs — "ambiguous" ──────────────────────────────────────
-- Verifies that wasm_mem emits the correct error when multiple matching
-- pointsTo_u32 hypotheses exist for the same effective address.

/-- error: wasm_mem: ambiguous — multiple u32 hypotheses match address base: [Hw1, Hw2] -/
#guard_msgs in
example (base word1 word2 : UInt32) :
    pointsTo_u32 0 base word1 ∗ pointsTo_u32 0 base word2 ∗
    (pointsTo_u32 0 base word1 -∗
      WP (.running ⟨⟨[], [], [.i32 word1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 base]⟩, [.load32 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hw1, Hw2, _⟩; wasm_mem

-- ─── Test 14 ─────────────────────────────────────────────────────────────────
-- `wasm_mem` focuses cell 1 of an `arrayAt` region and applies `twp_load32_addr`.

/-- `wasm_mem` focuses cell 1 of `arrayAt 0 4 [1, 2, 3]` and applies `twp_load32_addr`. -/
theorem test_wasm_mem_arrayAt_load :
    arrayAt 0 (4 : UInt32) [(1 : UInt32), 2, 3] ∗
    (arrayAt 0 (4 : UInt32) [(1 : UInt32), 2, 3] -∗
      WP (.running ⟨⟨[], [], [.i32 2]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 (4 + 4 * UInt32.ofNat 1)]⟩, [.load32 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Harray, Hcont⟩
  wasm_mem
  iapply Hcont $$ Harray

-- ─── Test 15 ─────────────────────────────────────────────────────────────────
-- `wasm_mem` focuses cell 1 of an `arrayAt` region with `arrayAt_set` and applies `twp_store32_addr`.

/-- `wasm_mem` focuses cell 1 of `arrayAt 0 4 [1, 2, 3]` with `arrayAt_set` and
applies `twp_store32_addr`, reassembling via the returned wand. -/
theorem test_wasm_mem_arrayAt_store :
    arrayAt 0 (4 : UInt32) [(1 : UInt32), 2, 3] ∗
    (arrayAt 0 (4 : UInt32) ([(1 : UInt32), 2, 3].set 1 5) -∗
      WP (.running ⟨⟨[], [], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 (5 : UInt32), .i32 (4 + 4 * UInt32.ofNat 1)]⟩, [.store32 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Harray, Hcont⟩
  wasm_mem
  iapply Hcont $$ Harray


-- ─── Test 16 ─────────────────────────────────────────────────────────────────
-- `wasm_pures using [UInt32.add_zero]` fires `const 4` then dispatches `wasm_mem` for `load32 0`.

/-- `wasm_pures using [UInt32.add_zero]` fires the `const 4` pure step, then
dispatches `wasm_mem using [UInt32.add_zero]` for `load32 0`, forwarding the
lemma so `normWithLemmas` normalises the effective address `4 + 0` to `4`. -/
theorem test_wasm_pures_using_load32_addr (word : UInt32) :
    pointsTo_u32 0 (4 : UInt32) word ∗
    (pointsTo_u32 0 (4 : UInt32) word -∗
      WP (.running ⟨⟨[], [], [.i32 word]⟩, [.memoryFill], 1, [], [], []⟩ : Expr α)
        @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], []⟩, [.const (4 : UInt32), .load32 0, .memoryFill], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hword, Hcont⟩
  wasm_pures using [UInt32.add_zero]
  iapply Hcont $$ Hword

-- ─── Test 17 ─────────────────────────────────────────────────────────────────
-- `wasm_pures using [UInt32.add_zero]` fires two `const` steps then dispatches `wasm_mem` for `store32 0`.

/-- `wasm_pures using [UInt32.add_zero]` fires two pure `const` steps then
dispatches `wasm_mem using [UInt32.add_zero]` for `store32 0`, forwarding the
lemma so `normWithLemmas` normalises the effective address `4 + 0` to `4`. -/
theorem test_wasm_pures_using_store32_addr (oldWord newWord : UInt32) :
    pointsTo_u32 0 (4 : UInt32) oldWord ∗
    (pointsTo_u32 0 (4 : UInt32) newWord -∗
      WP (.running ⟨⟨[], [], []⟩, [.memoryFill], 1, [], [], []⟩ : Expr α)
        @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], []⟩,
          [.const (4 : UInt32), .const newWord, .store32 0, .memoryFill], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hhold, Hcont⟩
  wasm_pures using [UInt32.add_zero]
  iapply Hcont $$ Hhold

-- ─── Test 18: #guard_msgs — "address in array region but no index found" ──────
-- `wasm_mem` errors when the address lies in an array region but is not element-aligned.

/-- error: wasm_mem: address 9 lies in array region Harray (base 4) but no cell index was found for stride 4 -/
#guard_msgs in
example (a b c : UInt32) :
    arrayAt 0 (4 : UInt32) [a, b, c] ∗
    (arrayAt 0 (4 : UInt32) [a, b, c] -∗
      WP (.running ⟨⟨[], [], [.i32 b]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 9]⟩, [.load32 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Harray, Hcont⟩; wasm_mem

-- ─── Test 19: #guard_msgs — wasm_loop head error ─────────────────────────────

/-- error: wasm_loop: head instruction is not .loop (got const) -/
#guard_msgs in
example :
    WP (.running ⟨⟨[], [], []⟩, [.const 0], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], []⟩, [.const 0], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H
  wasm_loop _ using _, _, _

-- ─── Test 20: #guard_msgs — wasm_call head error ─────────────────────────────

/-- error: wasm_call: head instruction is not .call (got const) -/
#guard_msgs in
example :
    WP (.running ⟨⟨[], [], []⟩, [.const 0], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], []⟩, [.const 0], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H
  wasm_call _

-- ─── Tests 21–22: br_if dispatch (two-entry ordered list) ────────────────────
-- `twp_brIfZero` (first entry) fires when condition = 0; `twp_brIf` (second) when ≠ 0.

/-- `wasm_pure` applies `twp_brIfZero` (first registered entry) when the condition
is 0: the branch is not taken, the condition value is dropped, and the continuation
state has an empty stack. -/
theorem test_wasm_pure_brIfZero :
    WP (.running ⟨⟨[], [], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 0]⟩, [.br_if 0], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_brIf` (second entry) when the condition is nonzero;
`twp_brIfZero` is tried first but fails, then `twp_brIf` wins. -/
theorem test_wasm_pure_brIfNonzero :
    WP (.running ⟨⟨[], [], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 5]⟩, [.br_if 0], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

-- ─── Test 23: #guard_msgs — br_if symbolic condition ─────────────────────────
-- Both `twp_brIfZero` and `twp_brIf` fail for symbolic conditions; `wasm_pure` errors.

/-- error: wasm_pure: no registered rule applied to br_if (tried: twp_brIfZero, twp_brIf) -/
#guard_msgs in
example (cond : UInt32) :
    WP (.running ⟨⟨[], [], [.i32 cond]⟩, [.br_if 0], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 cond]⟩, [.br_if 0], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure

-- ─── Tests 24–25: wasm_pures with newly registered comparison rules ───────────
-- Test 24: `twp_ne` + `twp_select` (i32); Test 25: `twp_gtUI64` + `twp_select` (i64).

/-- `wasm_pures` applies `twp_ne` and `twp_select`; symbolic `if`-expressions
normalised with `decide` before `iexact`. -/
theorem test_wasm_pures_ne_select :
    WP (.running ⟨⟨[], [], [.i32 7]⟩, [.memoryFill], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], []⟩,
        [.const 7, .const 9, .const 5, .const 3, .ne, .select, .memoryFill],
        1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H
  wasm_pures
  iexact H

/-- `wasm_pures` applies `twp_gtUI64` (i64) and `twp_select`. -/
theorem test_wasm_pures_gtUI64_select :
    WP (.running ⟨⟨[], [], [.i32 7]⟩, [.memoryFill], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], []⟩,
        [.const 7, .const 9, .constI64 5, .constI64 3, .gtUI64, .select, .memoryFill],
        1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H
  wasm_pures
  iexact H

-- ─── TWP single-step tests for registered pure rules ─────────────────────────

/-- `wasm_pure` applies `twp_const`. -/
theorem test_twp_const_step (val : UInt32) :
    WP (.running ⟨⟨[], [], [.i32 val]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], []⟩, [.const val], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_add`. -/
theorem test_twp_add_step (lhs rhs : UInt32) :
    WP (.running ⟨⟨[], [], [.i32 (rhs + lhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 rhs, .i32 lhs]⟩, [.add], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_sub`. -/
theorem test_twp_sub_step (lhs rhs : UInt32) :
    WP (.running ⟨⟨[], [], [.i32 (lhs - rhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 rhs, .i32 lhs]⟩, [.sub], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_mul`. -/
theorem test_twp_mul_step (lhs rhs : UInt32) :
    WP (.running ⟨⟨[], [], [.i32 (rhs * lhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 rhs, .i32 lhs]⟩, [.mul], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_and`. -/
theorem test_twp_and_step (lhs rhs : UInt32) :
    WP (.running ⟨⟨[], [], [.i32 (lhs &&& rhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 rhs, .i32 lhs]⟩, [.and], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_or`. -/
theorem test_twp_or_step (lhs rhs : UInt32) :
    WP (.running ⟨⟨[], [], [.i32 (lhs ||| rhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 rhs, .i32 lhs]⟩, [.or], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_shl`. -/
theorem test_twp_shl_step (lhs rhs : UInt32) :
    WP (.running ⟨⟨[], [], [.i32 (lhs <<< (rhs % 32))]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 rhs, .i32 lhs]⟩, [.shl], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_shrU`. -/
theorem test_twp_shrU_step (lhs rhs : UInt32) :
    WP (.running ⟨⟨[], [], [.i32 (lhs >>> (rhs % 32))]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 rhs, .i32 lhs]⟩, [.shrU], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_remU`. -/
theorem test_twp_remU_step (n : UInt32) :
    WP (.running ⟨⟨[], [], [.i32 (n % 3)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 3, .i32 n]⟩, [.remU], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_constI64`. -/
theorem test_twp_constI64_step (val : UInt64) :
    WP (.running ⟨⟨[], [], [.i64 val]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], []⟩, [.constI64 val], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_subI64`. -/
theorem test_twp_subI64_step (lhs rhs : UInt64) :
    WP (.running ⟨⟨[], [], [.i64 (lhs - rhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i64 rhs, .i64 lhs]⟩, [.subI64], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_mulI64`. -/
theorem test_twp_mulI64_step (lhs rhs : UInt64) :
    WP (.running ⟨⟨[], [], [.i64 (lhs * rhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i64 rhs, .i64 lhs]⟩, [.mulI64], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_orI64`. -/
theorem test_twp_orI64_step (lhs rhs : UInt64) :
    WP (.running ⟨⟨[], [], [.i64 (lhs ||| rhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i64 rhs, .i64 lhs]⟩, [.orI64], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_shlI64`. -/
theorem test_twp_shlI64_step (lhs rhs : UInt64) :
    WP (.running ⟨⟨[], [], [.i64 (lhs <<< (rhs % 64))]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i64 rhs, .i64 lhs]⟩, [.shlI64], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_shrUI64`. -/
theorem test_twp_shrUI64_step (lhs rhs : UInt64) :
    WP (.running ⟨⟨[], [], [.i64 (lhs >>> (rhs % 64))]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i64 rhs, .i64 lhs]⟩, [.shrUI64], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_ctzI64`. -/
theorem test_twp_ctzI64_step (val : UInt64) :
    WP (.running ⟨⟨[], [], [.i64 (UInt64.ofNat (ctz64 64 val))]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i64 val]⟩, [.ctzI64], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_wrapI64`. -/
theorem test_twp_wrapI64_step (val : UInt64) :
    WP (.running ⟨⟨[], [], [.i32 (UInt32.ofNat (val.toNat % 2 ^ 32))]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i64 val]⟩, [.wrapI64], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_extendUI32`. -/
theorem test_twp_extendUI32_step (val : UInt32) :
    WP (.running ⟨⟨[], [], [.i64 (UInt64.ofNat val.toNat)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 val]⟩, [.extendUI32], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_eqz`. -/
theorem test_twp_eqz_step :
    WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 0]⟩, [.eqz], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_eq`. -/
theorem test_twp_eq_step :
    WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 5, .i32 5]⟩, [.eq], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_ltU`. -/
theorem test_twp_ltU_step :
    WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 5, .i32 3]⟩, [.ltU], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_gtU`. -/
theorem test_twp_gtU_step :
    WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 3, .i32 5]⟩, [.gtU], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_ltUI64`. -/
theorem test_twp_ltUI64_step :
    WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i64 5, .i64 3]⟩, [.ltUI64], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_ltS`. -/
theorem test_twp_ltS_step :
    WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 5, .i32 3]⟩, [.ltS], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_geS`. -/
theorem test_twp_geS_step :
    WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 3, .i32 5]⟩, [.geS], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_ne`. -/
theorem test_twp_ne_step :
    WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 5, .i32 3]⟩, [.ne], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_leU`. -/
theorem test_twp_leU_step :
    WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 5, .i32 3]⟩, [.leU], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_geU`. -/
theorem test_twp_geU_step :
    WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 3, .i32 5]⟩, [.geU], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_select`. -/
theorem test_twp_select_step :
    WP (.running ⟨⟨[], [], [Value.i32 7]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 1, .i32 9, .i32 7]⟩, [.select], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_eqI64`. -/
theorem test_twp_eqI64_step :
    WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i64 5, .i64 5]⟩, [.eqI64], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_neI64`. -/
theorem test_twp_neI64_step :
    WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i64 5, .i64 3]⟩, [.neI64], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_gtUI64`. -/
theorem test_twp_gtUI64_step :
    WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i64 3, .i64 5]⟩, [.gtUI64], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_block`. -/
theorem test_twp_block_step :
    WP (.running ⟨⟨[], [], []⟩, [.nop],
          1, [],
          [{ kind := .block, paramArity := 0, resultArity := 0, body := [.nop],
             continuation := [], belowStack := [] }],
          []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], []⟩, [.block 0 0 [.nop]], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_iff`, taking the then-branch (`condition = 1`). -/
theorem test_twp_iff_step :
    WP (.running ⟨⟨[], [], []⟩, [.nop],
          1, [],
          [{ kind := .block, paramArity := 0, resultArity := 0, body := [.nop],
             continuation := [], belowStack := [] }],
          []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 1]⟩, [.iff 0 0 [.nop] [.drop]], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_iff`, taking the else-branch (`condition = 0`). -/
theorem test_twp_iff_else_step :
    WP (.running ⟨⟨[], [], []⟩, [.drop],
          1, [],
          [{ kind := .block, paramArity := 0, resultArity := 0, body := [.drop],
             continuation := [], belowStack := [] }],
          []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 0]⟩, [.iff 0 0 [.nop] [.drop]], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_exitControl`. -/
theorem test_twp_exitControl_step :
    WP (.running ⟨⟨[], [], []⟩, [.nop], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], []⟩, [],
          1, [],
          [{ kind := .block, paramArity := 0, resultArity := 0, body := [.nop],
             continuation := [.nop], belowStack := [] }],
          []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_br`. -/
theorem test_twp_br_step :
    WP (.running ⟨⟨[], [], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], []⟩, [.br 0], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_localGet`. -/
theorem test_twp_localGet_step :
    WP (.running ⟨⟨[], [.i32 5], [.i32 5]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [.i32 5], []⟩, [.localGet 0], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_localSet`. -/
theorem test_twp_localSet_step :
    WP (.running ⟨⟨[], [.i32 7], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [.i32 5], [.i32 7]⟩, [.localSet 0], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_localTee`. -/
theorem test_twp_localTee_step :
    WP (.running ⟨⟨[], [.i32 7], [.i32 7]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [.i32 5], [.i32 7]⟩, [.localTee 0], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_scalarFloat0` for `f32Const`. -/
theorem test_twp_f32Const_step (val : UInt32) :
    WP (.running ⟨⟨[], [], [.f32 val]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], []⟩, [.f32Const val], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `twp_scalarFloat0` for `f64Const`. -/
theorem test_twp_f64Const_step (val : UInt64) :
    WP (.running ⟨⟨[], [], [.f64 val]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], []⟩, [.f64Const val], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

-- ─── TWP scalar-float single-step tests ──────────────────────────────────────

/-- `wasm_pure` dispatches `twp_scalarFloat1` for `f32Neg`; `rfl` closes both
`hzero` (`evalScalarFloat0? .f32Neg = none`) and `heval`
(`evalScalarFloat1? .f32Neg (.f32 val) = some (.f32 (f32Neg val))`),
leaving `iexact H` a syntactic match. -/
theorem test_twp_scalarFloat1_f32Neg (val : UInt32) :
    WP (.running ⟨⟨[], [], [.f32 (Wasm.f32Neg val)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.f32 val]⟩, [.f32Neg], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` dispatches `twp_scalarFloat2` for `f32Copysign`; `rfl` closes
`hzero`, `hunary`, and `heval`
(`evalScalarFloat2? .f32Copysign (.f32 a) (.f32 b) = some (.f32 (f32Copysign a b))`),
leaving `iexact H` a syntactic match. -/
theorem test_twp_scalarFloat2_f32Copysign (a b : UInt32) :
    WP (.running ⟨⟨[], [], [.f32 (Wasm.f32Copysign a b)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.f32 b, .f32 a]⟩, [.f32Copysign], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` dispatches `twp_scalarFloat2` for `f32Add`; `rfl` closes
`hzero`, `hunary`, and `heval`
(`evalScalarFloat2? .f32Add (.f32 a) (.f32 b) = some (.f32 (f32Add a b))`),
leaving `iexact H` a syntactic match. -/
theorem test_twp_scalarFloat2_f32Add (a b : UInt32) :
    WP (.running ⟨⟨[], [], [.f32 (Wasm.f32Add a b)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.f32 b, .f32 a]⟩, [.f32Add], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` dispatches `twp_scalarFloat2` for `f32Min`; `rfl` closes
`hzero`, `hunary`, and `heval`
(`evalScalarFloat2? .f32Min (.f32 a) (.f32 b) = some (.f32 (f32Min a b))`),
leaving `iexact H` a syntactic match. -/
theorem test_twp_scalarFloat2_f32Min (a b : UInt32) :
    WP (.running ⟨⟨[], [], [.f32 (Wasm.f32Min a b)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.f32 b, .f32 a]⟩, [.f32Min], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` dispatches `twp_scalarFloat2` for `f32Max`; `rfl` closes
`hzero`, `hunary`, and `heval`
(`evalScalarFloat2? .f32Max (.f32 a) (.f32 b) = some (.f32 (f32Max a b))`),
leaving `iexact H` a syntactic match. -/
theorem test_twp_scalarFloat2_f32Max (a b : UInt32) :
    WP (.running ⟨⟨[], [], [.f32 (Wasm.f32Max a b)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.f32 b, .f32 a]⟩, [.f32Max], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

-- ─── TWP mem single-step tests (rules without existing tests) ─────────────────

/-- `wasm_mem` applies `twp_globalSet` for `globalSet 0`; the old value is
replaced with `7` and the side condition closes by `rfl`. -/
theorem test_wasm_mem_globalSet (oldWord : UInt32) :
    globalPointsToAt 0 0 (.i32 oldWord) ∗
    (globalPointsToAt 0 0 (.i32 (7 : UInt32)) -∗
      WP (.running ⟨⟨[], [], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 7]⟩, [.globalSet 0], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hglob, Hcont⟩
  wasm_mem
  iapply Hcont $$ Hglob

-- ─── TWP load64 / store64 tests ──────────────────────────────────────────────

/-- `wasm_mem` applies `twp_load64` for `load64 0` with concrete address 4;
the hypothesis uses `4 + 0` so IntoWand can structurally assign `address = 4,
offset = 0` to `twp_load64`'s `address + offset` premise. -/
theorem test_wasm_mem_load64_off0 (word : UInt64) :
    pointsTo_u64 0 ((4 : UInt32) + 0) word ∗
    (pointsTo_u64 0 ((4 : UInt32) + 0) word -∗
      WP (.running ⟨⟨[], [], [.i64 word]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 4]⟩, [.load64 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hword, Hcont⟩
  wasm_mem
  iapply Hcont $$ Hword

/-- `wasm_mem` applies `twp_load64` for `load64 4` with symbolic base;
`hnowrap` and `h1`–`h7` let `omega` close all eight arithmetic side conditions. -/
theorem test_wasm_mem_load64_off4 (base : UInt32) (word : UInt64)
    (hnowrap : (base + 4 : UInt32).toNat = base.toNat + (4 : UInt32).toNat)
    (h1 : ((base + 4) + 1 : UInt32).toNat = (base + 4 : UInt32).toNat + 1)
    (h2 : ((base + 4) + 2 : UInt32).toNat = (base + 4 : UInt32).toNat + 2)
    (h3 : ((base + 4) + 3 : UInt32).toNat = (base + 4 : UInt32).toNat + 3)
    (h4 : ((base + 4) + 4 : UInt32).toNat = (base + 4 : UInt32).toNat + 4)
    (h5 : ((base + 4) + 5 : UInt32).toNat = (base + 4 : UInt32).toNat + 5)
    (h6 : ((base + 4) + 6 : UInt32).toNat = (base + 4 : UInt32).toNat + 6)
    (h7 : ((base + 4) + 7 : UInt32).toNat = (base + 4 : UInt32).toNat + 7) :
    pointsTo_u64 0 (base + 4) word ∗
    (pointsTo_u64 0 (base + 4) word -∗
      WP (.running ⟨⟨[], [], [.i64 word]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 base]⟩, [.load64 4], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hword, Hcont⟩
  wasm_mem
  iapply Hcont $$ Hword

/-- `wasm_mem` applies `twp_store64` for `store64 4` with symbolic base;
`hnowrap` and `h1`–`h7` let `omega` close all eight arithmetic side conditions. -/
theorem test_wasm_mem_store64_off4 (base : UInt32) (oldWord : UInt64)
    (hnowrap : (base + 4 : UInt32).toNat = base.toNat + (4 : UInt32).toNat)
    (h1 : ((base + 4) + 1 : UInt32).toNat = (base + 4 : UInt32).toNat + 1)
    (h2 : ((base + 4) + 2 : UInt32).toNat = (base + 4 : UInt32).toNat + 2)
    (h3 : ((base + 4) + 3 : UInt32).toNat = (base + 4 : UInt32).toNat + 3)
    (h4 : ((base + 4) + 4 : UInt32).toNat = (base + 4 : UInt32).toNat + 4)
    (h5 : ((base + 4) + 5 : UInt32).toNat = (base + 4 : UInt32).toNat + 5)
    (h6 : ((base + 4) + 6 : UInt32).toNat = (base + 4 : UInt32).toNat + 6)
    (h7 : ((base + 4) + 7 : UInt32).toNat = (base + 4 : UInt32).toNat + 7) :
    pointsTo_u64 0 (base + 4) oldWord ∗
    (pointsTo_u64 0 (base + 4) (7 : UInt64) -∗
      WP (.running ⟨⟨[], [], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i64 7, .i32 base]⟩, [.store64 4], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hword, Hcont⟩
  wasm_mem
  iapply Hcont $$ Hword

/-- `wasm_mem` applies `twp_store32` for `store32 4` with symbolic base;
`hnowrap` and `h1`–`h3` let `omega` close all four arithmetic side conditions. -/
theorem test_wasm_mem_store32_off4 (base oldWord : UInt32)
    (hnowrap : (base + 4 : UInt32).toNat = base.toNat + (4 : UInt32).toNat)
    (h1 : ((base + 4) + 1 : UInt32).toNat = (base + 4 : UInt32).toNat + 1)
    (h2 : ((base + 4) + 2 : UInt32).toNat = (base + 4 : UInt32).toNat + 2)
    (h3 : ((base + 4) + 3 : UInt32).toNat = (base + 4 : UInt32).toNat + 3) :
    pointsTo_u32 0 (base + 4) oldWord ∗
    (pointsTo_u32 0 (base + 4) (7 : UInt32) -∗
      WP (.running ⟨⟨[], [], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 7, .i32 base]⟩, [.store32 4], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hword, Hcont⟩
  wasm_mem
  iapply Hcont $$ Hword

-- ─── TWP arrayAt regression tests ────────────────────────────────────────────

/-- `wasm_mem` applies `twp_load32_addr` after focusing cell 1 of
`arrayAt 0 100 [a, b]` at effective address `100 + 4 * 1`. -/
theorem test_wasm_mem_arrayAt_index1 (a b : UInt32) :
    arrayAt 0 (100 : UInt32) [a, b] ∗
    (arrayAt 0 (100 : UInt32) [a, b] -∗
      WP (.running ⟨⟨[], [], [.i32 b]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 (100 + 4 * UInt32.ofNat 1)]⟩, [.load32 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Harray, Hcont⟩
  wasm_mem
  iapply Hcont $$ Harray

/-- `wasm_mem` applies `twp_load32_addr` after disambiguating two array regions:
the first array (base 4, 2 cells) has index 25 which is OOB and is skipped;
cell 1 of the second array (base 100, 3 cells) is the unique match. -/
theorem test_wasm_mem_arrayAt_two_regions (a b c d e : UInt32) :
    arrayAt 0 (4 : UInt32) [a, b] ∗
    arrayAt 0 (100 : UInt32) [c, d, e] ∗
    (arrayAt 0 (4 : UInt32) [a, b] -∗
     arrayAt 0 (100 : UInt32) [c, d, e] -∗
      WP (.running ⟨⟨[], [], [.i32 d]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 (100 + 4 * UInt32.ofNat 1)]⟩, [.load32 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Harray1, Harray2, Hcont⟩
  wasm_mem
  ispecialize Hcont $$ Harray1
  iapply Hcont $$ Harray2

/-- `wasm_mem` applies `twp_load32_addr` after focusing cell 1 of a symbolic
list `xs` of length 3: `findArrayListLen` returns `none` for a symbolic-length
list, so the candidate is treated as in-bounds and focused normally. -/
theorem test_wasm_mem_arrayAt_symbolic_list (xs : List UInt32) (hlen : xs.length = 3) :
    arrayAt 0 (4 : UInt32) xs ∗
    (arrayAt 0 (4 : UInt32) xs -∗
      WP (.running ⟨⟨[], [], [.i32 (xs[1]'(by omega))]⟩, [], 1, [], [], []⟩ : Expr α)
        @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 (4 + 4 * UInt32.ofNat 1)]⟩, [.load32 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Harray, Hcont⟩
  wasm_mem
  iapply Hcont $$ Harray

/-- error: wasm_mem: address 108 is past the end of array region Harray (base 100, 2 cells) -/
#guard_msgs in
example (a b : UInt32) :
    arrayAt 0 (100 : UInt32) [a, b] ∗
    (arrayAt 0 (100 : UInt32) [a, b] -∗
      WP (.running ⟨⟨[], [], [.i32 a]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 108]⟩, [.load32 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Harray, Hcont⟩; wasm_mem

-- ─── Test 26: #guard_msgs — wasm_pures surfaces wasm_mem error ───────────────
-- `wasm_pures` propagates the `wasm_mem` "no u32 hypothesis found" error rather
-- than stopping silently when a mem rule is registered but ownership is missing.

/-- error: wasm_mem: no u32 hypothesis found for effective address base; check the Iris context -/
#guard_msgs in
example (base : UInt32) :
    WP (.running ⟨⟨[], [], [.i32 base]⟩, [.load32 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 base]⟩, [.load32 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro H; wasm_pures

end wasmPuresTests

-- ─── WP tests (partial WP, `{{ Φ }}` notation) ───────────────────────────────
-- Same section/instance pattern as the partial-WP proofs in SmallStepLifting.

section wasmWpTests

variable {hlc : HasLC} [WasmSmallStepGS hlc α]
local instance testWpIrisGS : IrisGS_gen hlc (Expr α) (WasmHeapGF α) := instIrisGS
variable {s : Stuckness} {E : CoPset}
variable {Φ : List Value → IProp (WasmHeapGF α)}

-- ─── Test 27: drop (TWP) ─────────────────────────────────────────────────────
-- `twp_drop` uses `instIrisGS`, matching `testWpIrisGS` but not `testTerminalIrisGS`.

/-- `wasm_pure` applies the newly registered `twp_drop` rule: the top stack value
is discarded with no side conditions. -/
theorem test_wasm_pure_drop :
    WP (.running ⟨⟨[], [], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], [.i32 5]⟩, [.drop], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_pure; iexact H

-- ─── WP dispatch: wasm_pure under wp modality (`{{ Φ }}`) ───────────────────

/-- `wasm_pure` applies `wp_const` to a partial-WP goal (`{{ Φ }}` notation). -/
theorem test_wp_const_step (val : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.i32 val]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], []⟩, [.const val], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

-- ─── Test 28: wp_xor ─────────────────────────────────────────────────────────

/-- `wasm_pure` applies `wp_xor`. -/
theorem test_wp_xor_step (lhs rhs : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.i32 (lhs ^^^ rhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 rhs, .i32 lhs]⟩, [.xor], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

-- ─── Test 29: wp_shrS ────────────────────────────────────────────────────────

/-- `wasm_pure` applies `wp_shrS`. -/
theorem test_wp_shrS_step (lhs rhs : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.i32 (UInt32.ofNat (BitVec.sshiftRight lhs.toBitVec (rhs % 32).toNat).toNat)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 rhs, .i32 lhs]⟩, [.shrS], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

-- ─── Test 30: wp_rotl ────────────────────────────────────────────────────────

/-- `wasm_pure` applies `wp_rotl`. -/
theorem test_wp_rotl_step (lhs rhs : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.i32 (if rhs % 32 = 0 then lhs
          else (lhs <<< (rhs % 32)) ||| (lhs >>> (32 - rhs % 32)))]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 rhs, .i32 lhs]⟩, [.rotl], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

-- ─── Test 31: wp_rotr ────────────────────────────────────────────────────────

/-- `wasm_pure` applies `wp_rotr`. -/
theorem test_wp_rotr_step (lhs rhs : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.i32 (if rhs % 32 = 0 then lhs
          else (lhs >>> (rhs % 32)) ||| (lhs <<< (32 - rhs % 32)))]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 rhs, .i32 lhs]⟩, [.rotr], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

-- ─── Test 32: wp_divU ────────────────────────────────────────────────────────

/-- `wasm_pure` applies `wp_divU`. -/
theorem test_wp_divU_step (n : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.i32 (n / 2)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 2, .i32 n]⟩, [.divU], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

-- ─── Test 33: wp_divS ────────────────────────────────────────────────────────

/-- `wasm_pure` applies `wp_divS`. -/
theorem test_wp_divS_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 (Int32.ofInt (Int.tdiv (10 : UInt32).toInt32.toInt (2 : UInt32).toInt32.toInt)).toUInt32]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 2, .i32 10]⟩, [.divS], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

-- ─── Test 34: wp_remS ────────────────────────────────────────────────────────

/-- `wasm_pure` applies `wp_remS`. -/
theorem test_wp_remS_step (n : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.i32 (Int32.ofInt (Int.tmod n.toInt32.toInt (3 : UInt32).toInt32.toInt)).toUInt32]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 3, .i32 n]⟩, [.remS], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

-- ─── Test 35: wp_clz ─────────────────────────────────────────────────────────

/-- `wasm_pure` applies `wp_clz`. -/
theorem test_wp_clz_step (value : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.i32 (UInt32.ofNat (clz32 32 value))]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 value]⟩, [.clz], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

-- ─── Test 36: wp_nop ─────────────────────────────────────────────────────────

/-- `wasm_pure` applies `wp_nop`. -/
theorem test_wp_nop_step :
    ▷ WP (.running ⟨⟨[], [], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], []⟩, [.nop], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

-- ─── Test 37: wp_leS ─────────────────────────────────────────────────────────

/-- `wasm_pure` applies `wp_leS`. -/
theorem test_wp_leS_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 5, .i32 3]⟩, [.leS], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

-- ─── Test 38: wp_gtS ─────────────────────────────────────────────────────────

/-- `wasm_pure` applies `wp_gtS`. -/
theorem test_wp_gtS_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 3, .i32 5]⟩, [.gtS], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H


-- ─── WP single-step tests for registered pure rules ───────────────────────────

/-- `wasm_pure` applies `wp_add`. -/
theorem test_wp_add_step (lhs rhs : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.i32 (rhs + lhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 rhs, .i32 lhs]⟩, [.add], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_sub`. -/
theorem test_wp_sub_step (lhs rhs : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.i32 (lhs - rhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 rhs, .i32 lhs]⟩, [.sub], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_mul`. -/
theorem test_wp_mul_step (lhs rhs : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.i32 (rhs * lhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 rhs, .i32 lhs]⟩, [.mul], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_and`. -/
theorem test_wp_and_step (lhs rhs : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.i32 (lhs &&& rhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 rhs, .i32 lhs]⟩, [.and], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_or`. -/
theorem test_wp_or_step (lhs rhs : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.i32 (lhs ||| rhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 rhs, .i32 lhs]⟩, [.or], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_shl`. -/
theorem test_wp_shl_step (lhs rhs : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.i32 (lhs <<< (rhs % 32))]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 rhs, .i32 lhs]⟩, [.shl], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_constI64`. -/
theorem test_wp_constI64_step (val : UInt64) :
    ▷ WP (.running ⟨⟨[], [], [.i64 val]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], []⟩, [.constI64 val], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_addI64`. -/
theorem test_wp_addI64_step (lhs rhs : UInt64) :
    ▷ WP (.running ⟨⟨[], [], [.i64 (lhs + rhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 rhs, .i64 lhs]⟩, [.addI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_subI64`. -/
theorem test_wp_subI64_step (lhs rhs : UInt64) :
    ▷ WP (.running ⟨⟨[], [], [.i64 (lhs - rhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 rhs, .i64 lhs]⟩, [.subI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_mulI64`. -/
theorem test_wp_mulI64_step (lhs rhs : UInt64) :
    ▷ WP (.running ⟨⟨[], [], [.i64 (lhs * rhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 rhs, .i64 lhs]⟩, [.mulI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_andI64`. -/
theorem test_wp_andI64_step (lhs rhs : UInt64) :
    ▷ WP (.running ⟨⟨[], [], [.i64 (lhs &&& rhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 rhs, .i64 lhs]⟩, [.andI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_orI64`. -/
theorem test_wp_orI64_step (lhs rhs : UInt64) :
    ▷ WP (.running ⟨⟨[], [], [.i64 (lhs ||| rhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 rhs, .i64 lhs]⟩, [.orI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_shlI64`. -/
theorem test_wp_shlI64_step (lhs rhs : UInt64) :
    ▷ WP (.running ⟨⟨[], [], [.i64 (lhs <<< (rhs % 64))]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 rhs, .i64 lhs]⟩, [.shlI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_shrUI64`. -/
theorem test_wp_shrUI64_step (lhs rhs : UInt64) :
    ▷ WP (.running ⟨⟨[], [], [.i64 (lhs >>> (rhs % 64))]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 rhs, .i64 lhs]⟩, [.shrUI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_ctzI64`. -/
theorem test_wp_ctzI64_step (val : UInt64) :
    ▷ WP (.running ⟨⟨[], [], [.i64 (UInt64.ofNat (ctz64 64 val))]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 val]⟩, [.ctzI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_wrapI64`. -/
theorem test_wp_wrapI64_step (val : UInt64) :
    ▷ WP (.running ⟨⟨[], [], [.i32 (UInt32.ofNat (val.toNat % 2 ^ 32))]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 val]⟩, [.wrapI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_extendUI32`. -/
theorem test_wp_extendUI32_step (val : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.i64 (UInt64.ofNat val.toNat)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 val]⟩, [.extendUI32], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_block`. -/
theorem test_wp_block_step :
    ▷ WP (.running ⟨⟨[], [], []⟩, [.nop],
          1, [],
          [{ kind := .block, paramArity := 0, resultArity := 0, body := [.nop],
             continuation := [], belowStack := [] }],
          []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], []⟩, [.block 0 0 [.nop]], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_iff`, taking the then-branch (`condition = 1`). -/
theorem test_wp_iff_step :
    ▷ WP (.running ⟨⟨[], [], []⟩, [.nop],
          1, [],
          [{ kind := .block, paramArity := 0, resultArity := 0, body := [.nop],
             continuation := [], belowStack := [] }],
          []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 1]⟩, [.iff 0 0 [.nop] [.drop]], 1, [], [], []⟩ : Expr α)
      @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_iff`, taking the else-branch (`condition = 0`). -/
theorem test_wp_iff_else_step :
    ▷ WP (.running ⟨⟨[], [], []⟩, [.drop],
          1, [],
          [{ kind := .block, paramArity := 0, resultArity := 0, body := [.drop],
             continuation := [], belowStack := [] }],
          []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 0]⟩, [.iff 0 0 [.nop] [.drop]], 1, [], [], []⟩ : Expr α)
      @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_exitControl`. -/
theorem test_wp_exitControl_step :
    ▷ WP (.running ⟨⟨[], [], []⟩, [.nop], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], []⟩, [],
          1, [],
          [{ kind := .block, paramArity := 0, resultArity := 0, body := [.nop],
             continuation := [.nop], belowStack := [] }],
          []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_br`. -/
theorem test_wp_br_step :
    ▷ WP (.running ⟨⟨[], [], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], []⟩, [.br 0], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_brIfZero` when the condition is 0. -/
theorem test_wp_brIfZero_step :
    ▷ WP (.running ⟨⟨[], [], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 0]⟩, [.br_if 0], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_brIf` when the condition is nonzero. -/
theorem test_wp_brIfNonzero_step :
    ▷ WP (.running ⟨⟨[], [], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 5]⟩, [.br_if 0], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_localGet`. -/
theorem test_wp_localGet_step :
    ▷ WP (.running ⟨⟨[], [.i32 5], [.i32 5]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [.i32 5], []⟩, [.localGet 0], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_localSet`. -/
theorem test_wp_localSet_step :
    ▷ WP (.running ⟨⟨[], [.i32 7], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [.i32 5], [.i32 7]⟩, [.localSet 0], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_localTee`. -/
theorem test_wp_localTee_step :
    ▷ WP (.running ⟨⟨[], [.i32 7], [.i32 7]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [.i32 5], [.i32 7]⟩, [.localTee 0], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_drop`. -/
theorem test_wp_drop_step :
    ▷ WP (.running ⟨⟨[], [], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 5]⟩, [.drop], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_remU`. -/
theorem test_wp_remU_step (n : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.i32 (n % 3)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 3, .i32 n]⟩, [.remU], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_xorI64`. -/
theorem test_wp_xorI64_step (lhs rhs : UInt64) :
    ▷ WP (.running ⟨⟨[], [], [.i64 (lhs ^^^ rhs)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 rhs, .i64 lhs]⟩, [.xorI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_divUI64`. -/
theorem test_wp_divUI64_step (n : UInt64) :
    ▷ WP (.running ⟨⟨[], [], [.i64 (n / 2)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 2, .i64 n]⟩, [.divUI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_remUI64`. -/
theorem test_wp_remUI64_step (n : UInt64) :
    ▷ WP (.running ⟨⟨[], [], [.i64 (n % 3)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 3, .i64 n]⟩, [.remUI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_eqz`. -/
theorem test_wp_eqz_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 0]⟩, [.eqz], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_eq`. -/
theorem test_wp_eq_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 5, .i32 5]⟩, [.eq], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_ltU`. -/
theorem test_wp_ltU_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 5, .i32 3]⟩, [.ltU], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_gtU`. -/
theorem test_wp_gtU_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 3, .i32 5]⟩, [.gtU], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_ltUI64`. -/
theorem test_wp_ltUI64_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 5, .i64 3]⟩, [.ltUI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_ne`. -/
theorem test_wp_ne_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 5, .i32 3]⟩, [.ne], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_ltS`. -/
theorem test_wp_ltS_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 5, .i32 3]⟩, [.ltS], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_geS`. -/
theorem test_wp_geS_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 3, .i32 5]⟩, [.geS], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_leU`. -/
theorem test_wp_leU_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 5, .i32 3]⟩, [.leU], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_geU`. -/
theorem test_wp_geU_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 3, .i32 5]⟩, [.geU], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_select`. -/
theorem test_wp_select_step :
    ▷ WP (.running ⟨⟨[], [], [Value.i32 7]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i32 1, .i32 9, .i32 7]⟩, [.select], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_eqI64`. -/
theorem test_wp_eqI64_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 5, .i64 5]⟩, [.eqI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_neI64`. -/
theorem test_wp_neI64_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 5, .i64 3]⟩, [.neI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_gtUI64`. -/
theorem test_wp_gtUI64_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 3, .i64 5]⟩, [.gtUI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_leUI64`. -/
theorem test_wp_leUI64_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 5, .i64 3]⟩, [.leUI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_gtSI64`. -/
theorem test_wp_gtSI64_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 3, .i64 5]⟩, [.gtSI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_leSI64`. -/
theorem test_wp_leSI64_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 5, .i64 3]⟩, [.leSI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_geSI64`. -/
theorem test_wp_geSI64_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 3, .i64 5]⟩, [.geSI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_eqzI64`. -/
theorem test_wp_eqzI64_step :
    ▷ WP (.running ⟨⟨[], [], [.i32 1]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.i64 0]⟩, [.eqzI64], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_scalarFloat0` for `f32Const`. -/
theorem test_wp_f32Const_step (val : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.f32 val]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], []⟩, [.f32Const val], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` applies `wp_scalarFloat0` for `f64Const`. -/
theorem test_wp_f64Const_step (val : UInt64) :
    ▷ WP (.running ⟨⟨[], [], [.f64 val]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], []⟩, [.f64Const val], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

-- ─── WP scalar-float single-step tests ───────────────────────────────────────

/-- `wasm_pure` dispatches `wp_scalarFloat1` for `f32Neg` under the partial-WP
modality; `rfl` closes `heval` leaving `iexact H` a syntactic match. -/
theorem test_wp_scalarFloat1_f32Neg (val : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.f32 (Wasm.f32Neg val)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.f32 val]⟩, [.f32Neg], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` dispatches `wp_scalarFloat2` for `f32Copysign` under the
partial-WP modality; `rfl` closes `heval` leaving `iexact H` a syntactic match. -/
theorem test_wp_scalarFloat2_f32Copysign (a b : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.f32 (Wasm.f32Copysign a b)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.f32 b, .f32 a]⟩, [.f32Copysign], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` dispatches `wp_scalarFloat2` for `f32Add` under the partial-WP
modality; `rfl` closes `heval` leaving `iexact H` a syntactic match. -/
theorem test_wp_scalarFloat2_f32Add (a b : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.f32 (Wasm.f32Add a b)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.f32 b, .f32 a]⟩, [.f32Add], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` dispatches `wp_scalarFloat2` for `f32Min` under the partial-WP
modality; `rfl` closes `heval` leaving `iexact H` a syntactic match. -/
theorem test_wp_scalarFloat2_f32Min (a b : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.f32 (Wasm.f32Min a b)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.f32 b, .f32 a]⟩, [.f32Min], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

/-- `wasm_pure` dispatches `wp_scalarFloat2` for `f32Max` under the partial-WP
modality; `rfl` closes `heval` leaving `iexact H` a syntactic match. -/
theorem test_wp_scalarFloat2_f32Max (a b : UInt32) :
    ▷ WP (.running ⟨⟨[], [], [.f32 (Wasm.f32Max a b)]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running ⟨⟨[], [], [.f32 b, .f32 a]⟩, [.f32Max], 1, [], [], []⟩ : Expr α) @ s; E {{ Φ }} := by
  iintro H; wasm_pure; iexact H

-- ─── TWP load8U / store8 / store64_addr tests ────────────────────────────────
-- These theorems live in SmallStepTotalLiftingBytes (Φ : List Value → IProp),
-- so they require `instIrisGS` / `testWpIrisGS`, not `testTerminalIrisGS`.

/-- `wasm_mem` applies `twp_load8U_addr` for `load8U 0` with concrete address 4;
`UInt32.add_zero` normalises the effective address `4 + 0` to `4`. -/
theorem test_wasm_mem_load8U_off0 (byte : UInt8) :
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap) ⟨0, (4 : UInt32)⟩ (DFrac.own 1) (some byte) ∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap) ⟨0, (4 : UInt32)⟩ (DFrac.own 1) (some byte) -∗
      WP (.running ⟨⟨[], [], [.i32 byte.toUInt32]⟩, [], 1, [], [], []⟩ : Expr α)
        @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 4]⟩, [.load8U 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hbyte, Hcont⟩
  wasm_mem using [UInt32.add_zero]
  iapply Hcont $$ Hbyte

/-- `wasm_mem` applies `twp_load8U` for `load8U 4` with symbolic base;
`hnowrap` lets `omega` close the one arithmetic side condition. -/
theorem test_wasm_mem_load8U_off4 (base : UInt32) (byte : UInt8)
    (hnowrap : (base + 4 : UInt32).toNat = base.toNat + (4 : UInt32).toNat) :
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap) ⟨0, base + 4⟩ (DFrac.own 1) (some byte) ∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap) ⟨0, base + 4⟩ (DFrac.own 1) (some byte) -∗
      WP (.running ⟨⟨[], [], [.i32 byte.toUInt32]⟩, [], 1, [], [], []⟩ : Expr α)
        @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 base]⟩, [.load8U 4], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hbyte, Hcont⟩
  wasm_mem
  iapply Hcont $$ Hbyte

/-- `wasm_mem` applies `twp_store8_addr` for `store8 0` with concrete address 4;
`UInt32.add_zero` normalises `4 + 0` to `4`. -/
theorem test_wasm_mem_store8_off0 (oldByte : UInt8) :
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap) ⟨0, (4 : UInt32)⟩ (DFrac.own 1) (some oldByte) ∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap) ⟨0, (4 : UInt32)⟩ (DFrac.own 1) (some (7 : UInt32).toUInt8) -∗
      WP (.running ⟨⟨[], [], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 7, .i32 4]⟩, [.store8 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hbyte, Hcont⟩
  wasm_mem using [UInt32.add_zero]
  iapply Hcont $$ Hbyte

/-- `wasm_mem` applies `twp_store8` for `store8 4` with symbolic base;
`hnowrap` lets `omega` close the one arithmetic side condition. -/
theorem test_wasm_mem_store8_off4 (base : UInt32) (oldByte : UInt8)
    (hnowrap : (base + 4 : UInt32).toNat = base.toNat + (4 : UInt32).toNat) :
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap) ⟨0, base + 4⟩ (DFrac.own 1) (some oldByte) ∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap) ⟨0, base + 4⟩ (DFrac.own 1) (some (7 : UInt32).toUInt8) -∗
      WP (.running ⟨⟨[], [], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 7, .i32 base]⟩, [.store8 4], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hbyte, Hcont⟩
  wasm_mem
  iapply Hcont $$ Hbyte

/-- `wasm_mem` applies `twp_store64_addr` for `store64 0` with concrete address 4;
all arithmetic side conditions close by `decide`. -/
theorem test_wasm_mem_store64_off0 (oldWord : UInt64) :
    pointsTo_u64 0 (4 : UInt32) oldWord ∗
    (pointsTo_u64 0 (4 : UInt32) (7 : UInt64) -∗
      WP (.running ⟨⟨[], [], []⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i64 7, .i32 4]⟩, [.store64 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hword, Hcont⟩
  wasm_mem using [UInt32.add_zero]
  iapply Hcont $$ Hword

end wasmWpTests

end Wasm.SmallStep
