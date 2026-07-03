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

theorem wp_wasm_step
    {m : Module} {st st' : Store Unit} {locals locals' : Locals}
    {instr₀ : Instruction} {rest₀ : Program}
    {env : HostEnv Unit} {Q : Store Unit → List Value → Prop}
    (hexec : execOne 1 m st locals instr₀ env = .Fallthrough st' locals')
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st' locals' rest₀ env Q) :
    ⊢ wp_wasm m st locals (instr₀ :: rest₀) env Q := by
  unfold wp_wasm
  iapply least_fixpoint_unfold_mpr
  -- simp only (not unfold): leaves non-applied wp_wasm_F inside bi_least_fixpoint named,
  -- so iexact Hwp can unify the recursive call after unfold wp_wasm at hstep below
  simp only [wp_wasm_F]
  split
  · -- nil: instr₀ :: rest₀ = [] is impossible
    contradiction
  · -- ret: instr₀ = .ret, contradicts hexec
    next tail h =>
    obtain ⟨rfl, _⟩ := List.cons.inj h
    simp [execOne] at hexec
  · -- general: subst equalities, then iris proof
    next instr rest h =>
    obtain ⟨h1, h2⟩ := List.cons.inj h
    subst h1; subst h2
    -- unfold wp_wasm in the Lean hypothesis before entering iris mode
    -- so Hwp arrives with the bi_least_fixpoint form iexact can unify
    unfold wp_wasm at hstep
    iintro %σ Hσ
    imod (hstep σ) $$ Hσ with ⟨%σ', Hσ', Hwp⟩
    imodintro
    iexists σ', st', locals'
    isplitl []
    · exact BI.pure_intro hexec
    · isplitl [Hσ']
      · iexact Hσ'
      · iexact Hwp

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

-- call rule: if the callee terminates with a postcondition that implies the
-- continuation terminates, the whole call sequence terminates.
theorem wp_wasm_prop_call
    {m : Module} {st : Store Unit} {locals : Locals}
    {callid : Nat} {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    (htw : TerminatesWith env m callid st locals.values
           (fun st' vs => wp_wasm_prop m st' { locals with values := vs } rest env Q)) :
    wp_wasm_prop m st locals (.call callid :: rest) env Q := by
  obtain ⟨N, hN⟩ := htw
  obtain ⟨vs', st', hrun, hwp⟩ := hN N le_rfl
  obtain ⟨fuel_rest, hfuel⟩ := hwp
  have hrun_ne : run N m callid st locals.values env ≠ .OutOfFuel := by
    rw [hrun]; intro h; cases h
  have hfuel_ne : exec fuel_rest m st' { locals with values := vs' } rest env ≠ .OutOfFuel := by
    intro h; simp only [h] at hfuel
  refine ⟨max N fuel_rest + 1, ?_⟩
  have hrun' : run (max N fuel_rest) m callid st locals.values env = .Success vs' st' :=
    (run_fuel_mono (Nat.le_max_left N fuel_rest) hrun_ne).trans hrun
  have hfuel' : exec (max N fuel_rest + 1) m st' { locals with values := vs' } rest env
      = exec fuel_rest m st' { locals with values := vs' } rest env :=
    exec_fuel_mono (by omega) hfuel_ne
  simp only [exec_call_cons, hrun', hfuel']
  exact hfuel

-- per-instruction iProp rules for wp_wasm
-- each wraps wp_wasm_step and discharges the execOne obligation

theorem wp_wasm_globalGet
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {i : Nat} {v : Value}
    (hget : st.globals.globals[i]? = some v)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := v :: locals.values } rest env Q) :
    ⊢ wp_wasm m st locals (.globalGet i :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hget]) hstep

theorem wp_wasm_globalSet
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {i : Nat} {v : Value} {vs : List Value} {old : Value}
    (hstack : locals.values = v :: vs)
    (hbound : st.globals.globals[i]? = some old)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m
          { st with globals := { globals := st.globals.globals.set i v } }
          { locals with values := vs } rest env Q) :
    ⊢ wp_wasm m st locals (.globalSet i :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack, hbound]) hstep

theorem wp_wasm_localGet
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {i : Nat} {v : Value}
    (hget : locals.get i = some v)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := v :: locals.values } rest env Q) :
    ⊢ wp_wasm m st locals (.localGet i :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hget]) hstep

theorem wp_wasm_localSet
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {i : Nat} {v : Value} {vs : List Value} {locals' : Locals}
    (hstack : locals.values = v :: vs)
    (hset : locals.set? i v = some locals')
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals' with values := vs } rest env Q) :
    ⊢ wp_wasm m st locals (.localSet i :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack, hset]) hstep

theorem wp_wasm_const
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    (v : UInt32)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := .i32 v :: locals.values } rest env Q) :
    ⊢ wp_wasm m st locals (.const v :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def]) hstep

theorem wp_wasm_add
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {a b : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 a :: .i32 b :: vs)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := .i32 (a + b) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.add :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack]) hstep

theorem wp_wasm_sub
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {a b : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 a :: .i32 b :: vs)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st { locals with values := .i32 (b - a) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.sub :: rest) env Q :=
  wp_wasm_step (by simp only [execOne.eq_def, hstack]) hstep

theorem wp_wasm_load64
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {addr : UInt32} {off : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 addr :: vs)
    (hbounds : addr.toNat + off.toNat + 8 ≤ st.mem.pages * 65536)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st
          { locals with values := .i64 (st.mem.read64 (addr + off)) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.load64 off :: rest) env Q :=
  wp_wasm_step
    (by simp only [execOne.eq_def, hstack]; rw [if_neg (by omega)])
    hstep

theorem wp_wasm_store64
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {addr : UInt32} {off : UInt32} {v : UInt64} {vs : List Value}
    (hstack : locals.values = .i64 v :: .i32 addr :: vs)
    (hbounds : addr.toNat + off.toNat + 8 ≤ st.mem.pages * 65536)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m
          { st with mem := st.mem.write64 (addr + off) v }
          { locals with values := vs } rest env Q) :
    ⊢ wp_wasm m st locals (.store64 off :: rest) env Q :=
  wp_wasm_step
    (by simp only [execOne.eq_def, hstack]; rw [if_neg (by omega)])
    hstep

theorem wp_wasm_load32
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {addr : UInt32} {off : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 addr :: vs)
    (hbounds : addr.toNat + off.toNat + 4 ≤ st.mem.pages * 65536)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m st
          { locals with values := .i32 (st.mem.read32 (addr + off)) :: vs } rest env Q) :
    ⊢ wp_wasm m st locals (.load32 off :: rest) env Q :=
  wp_wasm_step
    (by simp only [execOne.eq_def, hstack]; rw [if_neg (by omega)])
    hstep

theorem wp_wasm_store32
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {addr : UInt32} {off : UInt32} {v : UInt32} {vs : List Value}
    (hstack : locals.values = .i32 v :: .i32 addr :: vs)
    (hbounds : addr.toNat + off.toNat + 4 ≤ st.mem.pages * 65536)
    (hstep : ∀ σ : WasmHeapMap (Option UInt8),
        ⊢ genHeapInterp σ ==∗
        ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ∗ wp_wasm m
          { st with mem := st.mem.write32 (addr + off) v }
          { locals with values := vs } rest env Q) :
    ⊢ wp_wasm m st locals (.store32 off :: rest) env Q :=
  wp_wasm_step
    (by simp only [execOne.eq_def, hstack]; rw [if_neg (by omega)])
    hstep

theorem wp_wasm_prop_to_TerminatesWith
    {m : Module} {id : Nat} {f : Function}
    {initial : Store Unit} {args : List Value}
    {P : Store Unit → List Value → Prop}
    (hf : m.funcs[id - m.imports.length]? = some f)
    (himp : m.imports[id]? = none)
    (hresults : f.results.length = 0)
    (hlen : args.length ≤ f.numParams)
    (hcompat : ∀ st' vals, P st' vals → P st' [])
    (hwp : wp_wasm_prop m initial
        (f.toLocals (args.take f.numParams).reverse)
        f.body {} P) :
    TerminatesWith {} m id initial args P := by
  obtain ⟨fuel₀, hwp_fuel⟩ := hwp
  have hcr : args.drop f.numParams = [] := List.drop_eq_nil_of_le hlen
  cases hexec : exec fuel₀ m initial (f.toLocals (args.take f.numParams).reverse) f.body {} with
  | Fallthrough st' s' =>
    rw [hexec] at hwp_fuel
    exact TerminatesWith.of_run fuel₀ [] st'
      (by rw [run_eq himp]; simp [hf, hexec, hresults, hcr])
      hwp_fuel
  | Return st' vals =>
    rw [hexec] at hwp_fuel
    exact TerminatesWith.of_run fuel₀ [] st'
      (by rw [run_eq himp]; simp [hf, hexec, hresults, hcr])
      (hcompat st' vals hwp_fuel)
  | Break n st' s' => rw [hexec] at hwp_fuel; exact hwp_fuel.elim
  | Trap msg => rw [hexec] at hwp_fuel; exact hwp_fuel.elim
  | Invalid msg => rw [hexec] at hwp_fuel; exact hwp_fuel.elim
  | OutOfFuel => rw [hexec] at hwp_fuel; exact hwp_fuel.elim
  | ReturnCall fid st' vs => rw [hexec] at hwp_fuel; exact hwp_fuel.elim
  | Throwing tag targs st' s' => rw [hexec] at hwp_fuel; exact hwp_fuel.elim

end Wasm.SepLogic
