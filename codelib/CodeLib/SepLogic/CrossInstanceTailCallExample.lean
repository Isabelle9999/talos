import CodeLib.SepLogic.SmallStepAdequacy

/-! # Cross-instance tail-call example

Two hand-built modules exercise `twp_returnCallCrossInstance`.

- **Module A** (instance 0, caller): one function whose body is `[.returnCall 0]`,
  which tail-calls import 0.  Import 0 is resolved to instance 1's function 0.
- **Module B** (instance 1, callee): one function whose body is `[.const 42, .ret]`,
  returning the constant 42.

The theorem `tailCallCrossInstance_partiallyMeets` proves that running the caller
function to completion always yields `[.i32 42]`, using the total-WP rule
`twp_returnCallCrossInstance` together with `wasm_smallStep_runtime_instance_partiallyMeets`.
-/

namespace Wasm.SmallStep

open Iris Iris.BI Iris.ProgramLogic OFE COFE Iris.Algebra
  Language.Notation Std Wasm.SepLogic

/-! ### Helper -/

@[simp] private theorem RuntimeEnv.currentModule_inst0_of2
    {α : Type} (i1 i2 : ModuleInstance α) :
    ({ instances := #[i1, i2], entry := ⟨0⟩ } : RuntimeEnv α).currentModule = i1.module := by
  simp [RuntimeEnv.currentModule, RuntimeEnv.currentInstance]

/-! ### Module B (callee): returns the constant 42 -/

def constFn : Function where
  results := [.i32]
  body    := [.const 42, .ret]

def modB : Module where
  funcs := [constFn]

/-! ### Module A (caller): tail-calls import 0 -/

private abbrev tailCallImp : ImportDecl :=
  { «module» := "B", name := "const42", params := [], results := [.i32] }

def tailCallFn : Function where
  results := [.i32]
  body    := [.returnCall 0]

def modA : Module where
  imports := [tailCallImp]
  funcs   := [tailCallFn]

/-! ### Instances -/

/-- Instance 0 (caller): modA, import 0 resolved to instance 1's function 0. -/
def instA : ModuleInstance Unit where
  module          := modA
  host            := { funcs := [] }
  resolvedImports := #[.wasm ⟨1⟩ 0]

/-- Instance 1 (callee): modB, no imports. -/
def instB : ModuleInstance Unit where
  module := modB
  host   := { funcs := [] }

@[simp] private theorem instA_module : instA.module = modA := rfl

/-! ### Config -/

def tailCallConfig : Config Unit :=
  { expr  := .running
      { locals          := {}
        code            := [.returnCall 0]
        resultArity     := 1
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[instA, instB], entry := ⟨0⟩ }
        wasm    :=
          { globals := { globals := [] }
            mem     := Mem.empty 0
            host    := () } } }

/-! ### Partial-correctness theorem -/

theorem tailCallCrossInstance_partiallyMeets :
    PartiallyMeets tailCallConfig (fun values _ => values = [.i32 42]) := by
  apply wasm_smallStep_runtime_instance_partiallyMeets
  · decide
  · intro gs
    simp only [tailCallConfig, RuntimeEnv.currentModule_inst0_of2, instA_module]
    iintro ⟨Hruntime, HruntimeInstances⟩
    iapply twp.to_wp
    simp only [runtimeModuleOwn]
    icases Hruntime with ⟨HruntimeElem, HinstanceOwn⟩
    iintuitionistic HruntimeElem
    iapply twp_returnCallCrossInstance ⟨0⟩ instA ⟨1⟩ instB #[instA, instB]
        0 tailCallImp 0 constFn rfl rfl (by decide) rfl Nat.le.refl rfl rfl
        $$ [HinstanceOwn] HruntimeInstances
    · -- prove runtimeModuleOwn ⟨0⟩ modA
      simp only [runtimeModuleOwn, instA_module]
      isplitl []
      · iexact HruntimeElem
      · iexact HinstanceOwn
    · -- continuation: prove the callee's WP
      iintro ⟨HinstanceOwn', HruntimeInstances'⟩
      iclear HinstanceOwn' HruntimeInstances'
      simp only [constFn, Function.toLocals, List.map_nil,
                 List.length_nil, List.take_zero, List.reverse_nil]
      iapply twp_const
      iapply twp_returnFromFunction
      simp only [List.take_succ_cons, List.take_zero, List.append_nil]
      iapply twp.value rfl
      ipureexact rfl

end Wasm.SmallStep
