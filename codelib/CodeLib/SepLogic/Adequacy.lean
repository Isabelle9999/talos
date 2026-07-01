import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmRules
import CodeLib.SepLogic.WasmWP
import Iris.BI.Lib.Fixpoint
import Interpreter.Wasm

namespace Wasm.SepLogic
open Iris Wasm Std
variable [inst : WasmHeapGS]

structure WasmState where
  m      : Module
  st     : Store Unit
  locals : Locals
  prog   : Program
  env    : HostEnv Unit
  Q      : Store Unit → List Value → Prop

def wp_wasm_F (Φ : LeibnizO WasmState → IProp WasmHeapGF)
    (s : LeibnizO WasmState) : IProp WasmHeapGF :=
  let ws := s.car
  match ws.prog with
  | [] =>
      iprop% ⌜ws.Q ws.st []⌝
  | .ret :: _ =>
      iprop% ⌜ws.Q ws.st ws.locals.values⌝
  | instr :: rest =>
      iprop% ∀ σ : WasmHeapMap (Option UInt8),
        genHeapInterp σ ==∗
          ∃ σ' : WasmHeapMap (Option UInt8),
          ∃ st' : Store Unit,
          ∃ locals' : Locals,
            ⌜execOne 1 ws.m ws.st ws.locals instr ws.env = .Fallthrough st' locals'⌝ ∗
            genHeapInterp σ' ∗
            Φ ⟨{ m := ws.m, st := st', locals := locals',
                 prog := rest, env := ws.env, Q := ws.Q }⟩

def wp_wasm (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop) : IProp WasmHeapGF :=
  bi_least_fixpoint wp_wasm_F ⟨{ m, st, locals, prog, env, Q }⟩

instance instBIMonoPredWasmF :
    BIMonoPred (PROP := IProp WasmHeapGF) (A := LeibnizO WasmState) wp_wasm_F where
  mono_pred := by
    intro Φ Ψ hΦ hΨ
    iintro #HΦΨ %s
    obtain ⟨ws⟩ := s
    unfold wp_wasm_F
    simp only [LeibnizO.car]
    split
    · iintro H; iexact H
    · iintro H; iexact H
    · next instr rest =>
      iintro Hwp
      iintro %σ₀
      iintro Hσ₀
      imod Hwp $$ % σ₀ Hσ₀ with ⟨%σ', %st₁, %locals₁, hexec, Hσ', HΦ⟩
      imodintro
      iexists σ', st₁, locals₁
      isplitl [hexec]
      · iexact hexec
      · isplitl [Hσ']
        · iexact Hσ'
        · iapply HΦΨ
          iexact HΦ
  mono_pred_ne.ne _ _ _ H :=
    (OFE.eq_of_eqv (OFE.discrete H)) ▸ OFE.Dist.rfl

private theorem exec_cons {m : Module} {st : Store Unit} {locals : Locals}
    {env : HostEnv Unit} {head : Instruction} {rest : Program}
    {st₁ : Store Unit} {locals₁ : Locals}
    {Q : Store Unit → List Value → Prop}
    (hexec : execOne 1 m st locals head env = .Fallthrough st₁ locals₁)
    (hrest : wp_wasm_prop m st₁ locals₁ rest env Q) :
    wp_wasm_prop m st locals (head :: rest) env Q := by
  obtain ⟨n, hn⟩ := hrest
  refine ⟨n + 1, ?_⟩
  have hne1 : execOne 1 m st locals head env ≠ .OutOfFuel := by simp [hexec]
  have h1 : execOne (n + 1) m st locals head env = .Fallthrough st₁ locals₁ :=
    (execOne_fuel_mono (by omega) hne1).trans hexec
  have hne2 : exec n m st₁ locals₁ rest env ≠ .OutOfFuel := by
    intro h; simp [h] at hn
  have h2 : exec (n + 1) m st₁ locals₁ rest env = exec n m st₁ locals₁ rest env :=
    exec_fuel_mono (by omega) hne2
  simp only [exec, h1, h2]
  exact hn

theorem wasm_adequacy
    (m : Module) (st : Store Unit) (locals : Locals)
    (prog : Program) (env : HostEnv Unit)
    (Q : Store Unit → List Value → Prop)
    (σ : WasmHeapMap (Option UInt8)) :
    genHeapInterp σ ∗ wp_wasm m st locals prog env Q ⊢
      ⌜wp_wasm_prop m st locals prog env Q⌝ := by
  unfold wp_wasm
  let Ψ : LeibnizO WasmState → IProp WasmHeapGF :=
    fun s => iprop% ∀ σ' : WasmHeapMap (Option UInt8), genHeapInterp σ' -∗
      ⌜wp_wasm_prop s.car.m s.car.st s.car.locals s.car.prog s.car.env s.car.Q⌝
  haveI hΨ : OFE.NonExpansive Ψ :=
    ⟨fun _ _ _ H => (OFE.eq_of_eqv (OFE.discrete H)) ▸ OFE.Dist.rfl⟩
  have hstep : ⊢ □ (∀ y : LeibnizO WasmState, wp_wasm_F Ψ y -∗ Ψ y) := by
    iintro !> %s
    obtain ⟨⟨m', st', locals', prog', env', Q'⟩⟩ := s
    unfold wp_wasm_F Ψ
    simp only [LeibnizO.car]
    split
    · refine BI.entails_wand (BI.pure_elim' fun h =>
        BI.forall_intro fun _ => BI.wand_intro (BI.pure_intro ⟨0, ?_⟩))
      simp only [exec]; exact h
    · refine BI.entails_wand (BI.pure_elim' fun h =>
        BI.forall_intro fun _ => BI.wand_intro (BI.pure_intro ⟨1, ?_⟩))
      simp only [exec, execOne]; exact h
    · next instr rest =>
      iintro Hwp
      iintro %σ_any
      iintro Hσ_any
      imod Hwp $$ % σ_any Hσ_any with ⟨%σ₁, %st₁, %locals₁, hexec, Hσ₁, Hcont⟩
      icases hexec with %hexec_lean
      icases Hcont $$ % σ₁ Hσ₁ with %hwp_lean
      exact BI.pure_intro (exec_cons hexec_lean hwp_lean)
  have hfp : bi_least_fixpoint wp_wasm_F ⟨{ m, st, locals, prog, env, Q }⟩ ⊢
      Ψ ⟨{ m, st, locals, prog, env, Q }⟩ :=
    BI.sep_elim_emp_valid_left hstep
      (BI.wand_elim ((BI.wand_entails (least_fixpoint_iter (F := wp_wasm_F))).trans
        (BI.forall_elim (⟨{ m, st, locals, prog, env, Q }⟩ : LeibnizO WasmState))))
  exact ((BI.sep_mono_right hfp).trans
    (BI.sep_mono_right (BI.forall_elim σ))).trans BI.wand_elim_right

end Wasm.SepLogic
