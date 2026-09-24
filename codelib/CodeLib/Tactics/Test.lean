import CodeLib.SepLogic.SmallStepAdequacyExamples
import CodeLib.Tactics.Pure
import CodeLib.Tactics.Mem

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

-- ─── Tests 6–8: wasm_mem ─────────────────────────────────────────────────────

-- ─── Test 6 ──────────────────────────────────────────────────────────────────
-- Source: SmallStepTotalLifting.lean:1179 (twp_globalGet)
-- Exercises wasm_mem on a globalGet 0 step.
-- twp_globalGet has zero explicit args before the wand, so wasm_mem
-- calls `iapply twp_globalGet $$ Hglob` with no side-condition terms.

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
-- Source: SmallStepTotalLifting.lean:860 (twp_load32); consumer: Func1Proof.lean:269
-- Exercises wasm_mem on a load32 with nonzero offset (4).
-- Supplies hnowrap, h1, h2, h3 as hypotheses; wasm_mem discharges them via omega.

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
-- Source: SmallStepTotalLifting.lean:1775 (twp_load32_addr)
-- Exercises wasm_mem with `using [UInt32.add_zero]` on a load32 0 step.
-- The addr-variant is selected (offset 0 → twp_load32_addr).
-- `using [UInt32.add_zero]` normalises the effective address expression before
-- the hypothesis scan; with a concrete stack address the lemma is not strictly
-- required, but this test exercises the `using` code path end-to-end.
-- (For symbolic addresses, `using` is needed when the hypothesis address was
-- left in the form `addr + 0` by a prior `ihave`/`irw_exact` step, matching
-- the `wasm_twp_bind` pattern at SmallStepTotalLifting.lean:265–266.)

/-- `wasm_mem using [UInt32.add_zero]` exercises the normalisation path;
all side conditions are concrete and discharged by `decide`. -/
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

-- ─── Test 10: #guard_msgs — "no rule registered" ─────────────────────────────
-- Verifies that wasm_mem emits the correct error when the instruction head has
-- no registered rule at all.

/-- error: wasm_mem: no rule registered for memoryFill (is this instruction registered with `@[wasm_mem_rule …]`?) -/
#guard_msgs in
example :
    WP (.running ⟨⟨[], [], []⟩, [.memoryFill], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨[], [], []⟩, [.memoryFill], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro H; wasm_mem

-- ─── Test 11: #guard_msgs — "no hypothesis found" ────────────────────────────
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

-- ─── Test 12: #guard_msgs — "ambiguous" ──────────────────────────────────────
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

-- ─── Test 13 ─────────────────────────────────────────────────────────────────
-- Exercises wasm_mem with an arrayAt region hypothesis:
-- load32 0 at effective address 4 + 4*1, closed array [1, 2, 3].
-- wasm_mem focuses cell index 1 with arrayAt_get and applies twp_load32_addr.
-- The WP goal uses the formula address (4 + 4 * UInt32.ofNat 1) to match
-- the address that arrayAt_get produces syntactically, avoiding isDefEq in iapply.

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

-- ─── Test 14 ─────────────────────────────────────────────────────────────────
-- Exercises wasm_mem with arrayAt_set:
-- store32 0 at effective address 4 + 4*1, writing value 5 into closed [1, 2, 3].
-- wasm_mem focuses cell index 1 with arrayAt_set, applies twp_store32_addr,
-- and reassembles using the wand returned by arrayAt_set.
-- The continuation uses .set notation so its type matches _wasm_mem_close syntactically.

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

-- ─── Test 15: #guard_msgs — "address in array region but no index found" ──────
-- Verifies that wasm_mem emits the correct error when the effective address
-- is in the array region's span but is not aligned to the element stride.

/-- error: wasm_mem: address 9 lies in array region Harray (base 4) but no cell index was found for stride 4 -/
#guard_msgs in
example (a b c : UInt32) :
    arrayAt 0 (4 : UInt32) [a, b, c] ∗
    (arrayAt 0 (4 : UInt32) [a, b, c] -∗
      WP (.running ⟨⟨[], [], [.i32 b]⟩, [], 1, [], [], []⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨[], [], [.i32 9]⟩, [.load32 0], 1, [], [], []⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Harray, Hcont⟩; wasm_mem

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
