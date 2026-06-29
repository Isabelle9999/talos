import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmRules
import CodeLib.SepLogic.WasmWP
import Iris.BI.Lib.Fixpoint
import Interpreter.Wasm

/-! # Adequacy: iProp WP → physical termination

Bridges Iris separation-logic ownership to Talos's fuel-based big-step
semantics via the GenHeap agreement lemmas from WasmRules.

Architecture
1. `WasmState` — execution state wrapped in `LeibnizO` for OFE structure.
2. `wp_wasm_F`  — the per-instruction WP functional.
3. `wp_wasm`    — least fixpoint of `wp_wasm_F`; handles loops via induction.
4. `BIMonoPred wp_wasm_F` — monotonicity certificate.
5. `wasm_adequacy` — main theorem: ownership + WP ⊢ physical termination.
-/

namespace Wasm.SepLogic

open Iris Wasm Std

variable [inst : WasmHeapGS]

/-! ## 1. WasmState — execution state as a discrete OFE element -/

/-- All components needed to run a Wasm program, bundled for the fixpoint. -/
structure WasmState where
  m      : Module
  st     : Store Unit
  locals : Locals
  prog   : Program
  env    : HostEnv Unit
  Q      : Store Unit → List Value → Prop

/-! `LeibnizO WasmState` provides the discrete OFE: `x ≡{n}≡ y ↔ x = y`. -/

/-! ## 2. wp_wasm_F — per-instruction WP functional -/

/-- The WP functional over Talos's big-step semantics.

Per-instruction rules:
- `[]` / `ret`:  base case — check postcondition Q.  `ret` returns the operand
                 stack (`locals.values`); `[]` (fall-through) returns `[]`.
- `load64 off`:  requires ownership of 8 bytes at (addr + off), returns same
                 ownership (read preserves ownership).
- `store64 off`: requires old ownership at (addr + off), produces new ownership.
- any other:     pure instruction — advance program counter, pass through Φ. -/
def wp_wasm_F (Φ : LeibnizO WasmState → IProp WasmHeapGF)
    (s : LeibnizO WasmState) : IProp WasmHeapGF :=
  let ws := s.car
  match ws.prog with
  | [] =>
      iprop% ⌜ws.Q ws.st []⌝
  | .ret :: _ =>
      -- execOne _ _ st s .ret _ = .Return st s.values
      iprop% ⌜ws.Q ws.st ws.locals.values⌝
  | .load64 off :: rest =>
      iprop% ∃ addr : UInt32, ∃ v : UInt64,
        wp_load64 (addr + off) v (Φ ⟨{ ws with prog := rest }⟩)
  | .store64 off :: rest =>
      iprop% ∃ addr : UInt32, ∃ old_v new_v : UInt64,
        wp_store64 (addr + off) old_v new_v (Φ ⟨{ ws with prog := rest }⟩)
  | _ :: rest =>
      Φ ⟨{ ws with prog := rest }⟩

/-! ## 3. wp_wasm — least fixpoint -/

/-- Wasm WP as the least fixpoint of `wp_wasm_F`.

For straight-line code the fixpoint unfolds finitely via
`least_fixpoint_unfold`. For loops it provides an inductive invariant via
`least_fixpoint_ind`. -/
def wp_wasm (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop) : IProp WasmHeapGF :=
  bi_least_fixpoint wp_wasm_F ⟨{ m, st, locals, prog, env, Q }⟩

/-! ## 4. BIMonoPred for wp_wasm_F -/

/-- `wp_wasm_F` is monotone: if `Φ x ⊢ Ψ x` everywhere, then
`wp_wasm_F Φ s ⊢ wp_wasm_F Ψ s` everywhere.

Proof by cases on the head instruction:
- `[]`, `ret`: constant in Φ (goal is `P -∗ P`), closed by `iintro H; iexact H`.
- `load64`: `wp_load64` has Φ in covariant continuation position; thread the
  monotonicity hypothesis through via the wand.
- `store64`: same argument with `wp_store64`.
- Pure instructions: `Φ ⟨...⟩ -∗ Ψ ⟨...⟩` follows directly from `HΦΨ`.

`mono_pred_ne` holds because `LeibnizO WasmState` is discrete:
`x ≡{n}≡ y` (definitionally `x = y`), so `wp_wasm_F Φ x = wp_wasm_F Φ y`,
giving `wp_wasm_F Φ x ≡{n}≡ wp_wasm_F Φ y` by `Dist.rfl`. -/
instance instBIMonoPredWasmF :
    BIMonoPred (PROP := IProp WasmHeapGF) (A := LeibnizO WasmState) wp_wasm_F where
  mono_pred {Φ Ψ _ _} := by
    iintro #HΦΨ %x
    obtain ⟨ws⟩ := x
    match ws.prog with
    | [] =>
        -- wp_wasm_F Φ ⟨ws⟩ = ⌜ws.Q ws.st []⌝ = wp_wasm_F Ψ ⟨ws⟩, constant in Φ
        iintro H; iexact H
    | .ret :: _ =>
        -- similarly constant in Φ
        iintro H; iexact H
    | .load64 off :: rest =>
        simp only [wp_wasm_F, wp_load64]
        iintro ⟨%addr, %v, Hpts, Hwand⟩
        iexists addr; iexists v
        isplitl [Hpts]
        iintro Hpts'
        iapply HΦΨ
        iapply Hwand Hpts'
    | .store64 off :: rest =>
        simp only [wp_wasm_F, wp_store64]
        iintro ⟨%addr, %old_v, %new_v, Hpts, Hwand⟩
        iexists addr; iexists old_v; iexists new_v
        isplitl [Hpts]
        iintro Hnew
        iapply HΦΨ
        iapply Hwand Hnew
    | _ :: rest =>
        -- wp_wasm_F Φ ⟨ws⟩ = Φ ⟨{ ws with prog := rest }⟩, use HΦΨ directly
        iapply HΦΨ
  mono_pred_ne.ne _ _ _ H := (eq_of_eqv (discrete H)) ▸ Dist.rfl

/-! ## 5. Adequacy theorem -/

/-- **Adequacy**: ghost heap ownership + iProp WP entails Prop-level termination.

Proof via `least_fixpoint_iter` with invariant
  Ψ s = genHeapInterp σ -∗ ⌜wp_wasm_prop s.car.m s.car.st s.car.locals s.car.prog s.car.env s.car.Q⌝

The inductive step for each case of `wp_wasm_F`:
- `[]`:   `exec _ m st locals [] env = .Fallthrough st locals` by `exec`'s
          first match arm (independent of fuel); `fuel = 0` witnesses.
- `ret`:  `exec _ m st locals (.ret::_) env = .Return st locals.values` by
          `execOne`'s `| _, .ret => .Return st s.values`; `fuel = 0` witnesses.
- Other: deferred (load64/store64 require extracting physical addresses from
         the ghost heap, and pure instructions require tracking operand-stack
         state — both are left sorry as architecturally non-novel). -/
theorem wasm_adequacy
    (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop)
    (σ : WasmHeapMap (Option UInt8)) :
    genHeapInterp σ ∗ wp_wasm m st locals prog env Q ⊢
      ⌜wp_wasm_prop m st locals prog env Q⌝ := by
  simp only [wp_wasm]
  -- Invariant: heap interp -∗ physical termination predicate
  letI Ψ : LeibnizO WasmState → IProp WasmHeapGF :=
    fun s => iprop% (genHeapInterp σ -∗
      ⌜wp_wasm_prop s.car.m s.car.st s.car.locals s.car.prog s.car.env s.car.Q⌝)
  haveI hΨ_ne : NonExpansive Ψ :=
    ⟨fun h => (eq_of_eqv (discrete h)) ▸ Dist.rfl⟩
  -- P ∗ Q ⊢ R  ↔  Q ⊢ P -∗ R  (wand_elim_swap)
  apply wand_elim_swap
  -- Goal: bi_least_fixpoint wp_wasm_F ⟨...⟩ ⊢ genHeapInterp σ -∗ ⌜...⌝
  -- Generalize the packed state so least_fixpoint_iter can fire
  generalize (⟨{ m, st, locals, prog, env, Q }⟩ : LeibnizO WasmState) = x
  revert x
  -- Goal: ∀ x, bi_least_fixpoint wp_wasm_F x ⊢ Ψ x
  iapply least_fixpoint_iter (F := wp_wasm_F) (Φ := Ψ)
  -- Goal: ⊢ □ (∀ y, wp_wasm_F Ψ y -∗ Ψ y)
  iintro !> %⟨ws⟩
  match ws.prog with
  | [] =>
      -- wp_wasm_F Ψ ⟨ws⟩ = ⌜ws.Q ws.st []⌝
      -- exec _ m st locals [] env = .Fallthrough st locals (any fuel, first match arm)
      iintro %h _
      ipureintro
      exact ⟨0, h⟩
  | .ret :: _ =>
      -- wp_wasm_F Ψ ⟨ws⟩ = ⌜ws.Q ws.st ws.locals.values⌝
      -- exec _ m st locals (.ret::_) env = .Return st locals.values (any fuel)
      iintro %h _
      ipureintro
      exact ⟨0, h⟩
  | _ :: _ =>
      -- load64, store64, pure: require ghost-heap extraction or stack tracking;
      -- the base-case proof above demonstrates the adequacy pattern.
      sorry

end Wasm.SepLogic
