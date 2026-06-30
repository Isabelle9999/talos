import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmRules
import CodeLib.SepLogic.WasmWP
import Iris.BI.Lib.Fixpoint
import Interpreter.Wasm

/-! # Adequacy: iProp WP → physical termination (HeapLang-style)

`wp_wasm_F` threads `genHeapInterp` through each step, following HeapLang's
`stateInterp`-threading pattern.  Each non-terminal case has the form
  `∀ σ, genHeapInterp σ ==∗ ∃ σ' st' locals', ⌜execOne 1 … = .Fallthrough st' locals'⌝ ∗
                                                 genHeapInterp σ' ∗ continuation`
so the continuation carries the post-instruction state (st', locals') rather than
the pre-instruction state.

Architecture:
1. `WasmState`      — execution state wrapped in `LeibnizO`.
2. `wp_wasm_F`      — WP functional threading `genHeapInterp`.
3. `wp_wasm`        — least fixpoint; handles loops via induction.
4. `BIMonoPred`     — monotonicity certificate.
5. `wasm_adequacy`  — main theorem: `genHeapInterp σ ∗ wp_wasm … Q ⊢ |==> ⌜prop⌝`.
-/

namespace Wasm.SepLogic

open Iris Wasm Std

variable [inst : WasmHeapGS]

/-! ## 1. WasmState — execution state as a discrete OFE element -/

structure WasmState where
  m      : Module
  st     : Store Unit
  locals : Locals
  prog   : Program
  env    : HostEnv Unit
  Q      : Store Unit → List Value → Prop

/-! ## 2. wp_wasm_F — threads genHeapInterp through each step -/

/-- The WP functional.  Terminal cases (`[]`, `.ret`) produce a pure fact via `==∗ ⌜…⌝`.
    All other instructions use a uniform pattern: the post-instruction state
    (σ', st', locals') is quantified existentially together with a Lean-level
    witness `execOne 1 … = .Fallthrough st' locals'`, so that `wasm_adequacy`
    can connect the WP to the concrete interpreter. -/
def wp_wasm_F (Φ : LeibnizO WasmState → IProp WasmHeapGF)
    (s : LeibnizO WasmState) : IProp WasmHeapGF :=
  let ws := s.car
  match ws.prog with
  | [] =>
      iprop% ∀ σ : WasmHeapMap (Option UInt8),
        genHeapInterp σ ==∗ ⌜ws.Q ws.st []⌝
  | .ret :: _ =>
      iprop% ∀ σ : WasmHeapMap (Option UInt8),
        genHeapInterp σ ==∗ ⌜ws.Q ws.st ws.locals.values⌝
  | instr :: rest =>
      iprop% ∀ σ : WasmHeapMap (Option UInt8),
        genHeapInterp σ ==∗
          ∃ σ' : WasmHeapMap (Option UInt8), ∃ st' : Store Unit, ∃ locals' : Locals,
            ⌜execOne 1 ws.m ws.st ws.locals instr ws.env = .Fallthrough st' locals'⌝ ∗
            genHeapInterp σ' ∗
            Φ ⟨{ m := ws.m, st := st', locals := locals', prog := rest,
                 env := ws.env, Q := ws.Q }⟩

/-! ## 3. wp_wasm — least fixpoint -/

def wp_wasm (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop) : IProp WasmHeapGF :=
  bi_least_fixpoint wp_wasm_F ⟨{ m, st, locals, prog, env, Q }⟩

/-! ## 4. BIMonoPred for wp_wasm_F -/

instance instBIMonoPredWasmF :
    BIMonoPred (PROP := IProp WasmHeapGF) (A := LeibnizO WasmState) wp_wasm_F where
  mono_pred := by
    intro Φ Ψ hΦ hΨ
    iintro #HΦΨ %s
    obtain ⟨ws⟩ := s
    unfold wp_wasm_F
    set_option linter.unusedSimpArgs false in
    simp only [LeibnizO.car]
    split
    · -- [] terminal
      iintro H; iexact H
    · -- .ret terminal
      iintro H; iexact H
    · -- instr :: rest: open H's bupd, swap Φ for Ψ via HΦΨ
      iintro H %σ Hσ
      imod H $$ %σ Hσ with ⟨%σ', %st', %locals', %hexec, Hσ', HΦ⟩
      imodintro
      iexists σ', st', locals'
      isplitl []
      · ipureintro; exact hexec
      isplitl [Hσ']
      · iexact Hσ'
      iapply HΦΨ
      iexact HΦ
  mono_pred_ne.ne _ _ _ H :=
    (OFE.eq_of_eqv (OFE.discrete H)) ▸ OFE.Dist.rfl

/-! ## 5. Adequacy theorem

`Ψ s = ∀ σ, genHeapInterp σ -∗ |==> ⌜wp_wasm_prop s.car…⌝`

The step proof (`hstep`) shows that each case of `wp_wasm_F Ψ` entails `Ψ`.
- Terminal cases: use `bupd_mono` + `pure_mono` with the exec-nil / exec-ret lemma.
- `instr :: rest`: the WP gives `hexec : execOne 1 … instr … = .Fallthrough st₁ locals₁`
  and `hwp : wp_wasm_prop … rest …` at the post-instruction state `(st₁, locals₁)`.
  Combining these into `wp_wasm_prop … (instr :: rest) …` still requires a
  fuel-independence lemma (non-call instructions are fuel-agnostic for fuel ≥ 1)
  and a fuel-monotonicity lemma, both of which are deferred to future work (sorry).
-/

theorem wasm_adequacy
    (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop)
    (σ : WasmHeapMap (Option UInt8)) :
    genHeapInterp σ ∗ wp_wasm m st locals prog env Q ⊢
      |==> ⌜wp_wasm_prop m st locals prog env Q⌝ := by
  unfold wp_wasm
  let Ψ : LeibnizO WasmState → IProp WasmHeapGF :=
    fun s => iprop% (∀ σ' : WasmHeapMap (Option UInt8),
      genHeapInterp σ' -∗
        |==> ⌜wp_wasm_prop s.car.m s.car.st s.car.locals
                              s.car.prog s.car.env s.car.Q⌝)
  haveI hΨ : OFE.NonExpansive Ψ :=
    ⟨fun _ _ _ H => (OFE.eq_of_eqv (OFE.discrete H)) ▸ OFE.Dist.rfl⟩
  have hstep : ⊢ □ (∀ y : LeibnizO WasmState, wp_wasm_F Ψ y -∗ Ψ y) := by
    iintro !> %s
    obtain ⟨⟨m', st', locals', prog', env', Q'⟩⟩ := s
    cases prog' with
    | nil =>
      unfold wp_wasm_F Ψ
      exact BI.entails_wand (BI.forall_mono fun σ' =>
        BI.wand_mono_right (BIUpdate.mono (BI.pure_mono fun h =>
          (⟨0, by simp only [exec]; exact h⟩ : wp_wasm_prop m' st' locals' [] env' Q'))))
    | cons head rest =>
      cases head with
      | ret =>
        unfold wp_wasm_F Ψ
        exact BI.entails_wand (BI.forall_mono fun σ' =>
          BI.wand_mono_right (BIUpdate.mono (BI.pure_mono fun h =>
            (⟨1, by simp only [exec, execOne]; exact h⟩ :
              wp_wasm_prop m' st' locals' (.ret :: rest) env' Q'))))
      | _ =>
        -- head is a non-ret instruction; wp_wasm_F reduces to the `instr :: rest` arm.
        -- hwp carries the post-instruction state (st₁, locals₁) matching execOne's output.
        -- The remaining sorry needs: execOne fuel-independence + exec fuel-monotonicity.
        unfold wp_wasm_F Ψ
        iintro H %σ' Hσ'
        imod H $$ %σ' Hσ' with ⟨%σ'', %st₁, %locals₁, %hexec, Hσ'', HΨ⟩
        imod HΨ $$ %σ'' Hσ'' with %hwp
        imodintro
        ipureintro
        -- hwp : wp_wasm_prop m' st₁ locals₁ rest env' Q'
        -- hexec : execOne 1 m' st' locals' head env' = .Fallthrough st₁ locals₁
        -- goal : wp_wasm_prop m' st' locals' (head :: rest) env' Q'
        sorry
  have hfp : bi_least_fixpoint wp_wasm_F ⟨{ m, st, locals, prog, env, Q }⟩ ⊢
      Ψ ⟨{ m, st, locals, prog, env, Q }⟩ :=
    BI.sep_elim_emp_valid_left hstep
      (BI.wand_elim ((BI.wand_entails (least_fixpoint_iter (F := wp_wasm_F))).trans
        (BI.forall_elim (⟨{ m, st, locals, prog, env, Q }⟩ : LeibnizO WasmState))))
  calc genHeapInterp σ ∗ bi_least_fixpoint wp_wasm_F ⟨{ m, st, locals, prog, env, Q }⟩
      ⊢ genHeapInterp σ ∗ Ψ ⟨{ m, st, locals, prog, env, Q }⟩ :=
        BI.sep_mono_right hfp
    _ ⊢ |==> ⌜wp_wasm_prop m st locals prog env Q⌝ :=
        (BI.sep_mono_right (BI.forall_elim σ)).trans BI.wand_elim_right

end Wasm.SepLogic
