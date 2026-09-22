import CodeLib.SepLogic.SmallStepOutcomeLanguage
import CodeLib.SepLogic.SmallStepTotalLifting

/-!
# `CodeLib.RustStd.AllocErrorHandler`

Level-2 template for the `__rust_alloc_error_handler` / `alloc_error_handler`
forwarder (class `1a8fb9c3de74`).

Every Rust crate that links `std` contains a tiny one-argument forwarder with
body `[.localGet 0, .call k, .unreachable]`: it takes the panic-info pointer
from its sole `(param i32)` and immediately forwards it to the level-3 panic
hook dispatcher, parameterised by the crate-specific call target `k`.

`template_alloc_error_handler k` is the full body.
`AllocErrorHandlerContractAt calleeIdx` states the WP contract.
`allocErrorHandler_instantiate` proves it holds for any call target.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open scoped Outcome

/-- Full body of the alloc_error_handler forwarder, parameterised by call target.
    Consumers prove `func.body = template_alloc_error_handler calleeAbsIdx` by `rfl`. -/
def template_alloc_error_handler (k : Nat) : Wasm.Program :=
  [.localGet 0, .call k, .unreachable]

/-- Contract for `template_alloc_error_handler calleeIdx`.

    The function has one `(param i32)` parameter `arg` and no extra locals.
    The caller supplies only an abstract resource `R`.

    `hcallee` is the WP for calling `calleeIdx` once `local.get 0` has
    pushed `arg` onto the stack; consumers supply it from the level-3
    callee's own contract.

    *Note:* the `hcallee` state has `locals = []` because this function has
    no extra locals beyond its single param. -/
def AllocErrorHandlerContractAt [WasmSmallStepGS hlc α]
    (calleeIdx : Nat) : Prop :=
  ∀ (arg : UInt32)
    {R : IProp (WasmHeapGF α)}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → IProp (WasmHeapGF α)},
    (R ⊢
       WP (Expr.running
             ⟨⟨[.i32 arg], [], [.i32 arg]⟩,
               .call calleeIdx :: .unreachable :: code,
               arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) →
    R ⊢
      WP (Expr.running
            ⟨⟨[.i32 arg], [], []⟩,
              template_alloc_error_handler calleeIdx ++ code,
              arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]

/-- `AllocErrorHandlerContractAt` holds for any call target.

    Proof: `local.get 0` is a pure step that pushes the param onto the
    stack; then `hcallee` closes the goal. -/
theorem allocErrorHandler_instantiate [WasmSmallStepGS hlc α]
    (calleeIdx : Nat) : AllocErrorHandlerContractAt (α := α) (hlc := hlc) calleeIdx := by
  unfold AllocErrorHandlerContractAt template_alloc_error_handler
  intro arg R code arity remainder controls calls s E Φ hcallee
  simp only [List.cons_append, List.nil_append]
  iintro HR
  wasm_twp_pures [twp_localGet]
  iapply hcallee
  iexact HR

end Wasm.SmallStep
