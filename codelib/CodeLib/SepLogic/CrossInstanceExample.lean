import CodeLib.SepLogic.SmallStepAdequacy

namespace Wasm.SmallStep

open Iris Iris.BI Iris.ProgramLogic OFE COFE Iris.Algebra
  Language.Notation Std Wasm.SepLogic

-- i32 add: params[0] = a, params[1] = b; pushes b then a, adds, returns a+b
def addFn : Function where
  params  := [.i32, .i32]
  locals  := []
  results := [.i32]
  body    := [.localGet 1, .localGet 0, .add, .ret]

private abbrev addImp : ImportDecl :=
  { module := "add", name := "f", params := [.i32, .i32], results := [.i32] }

def addModule : Module where
  funcs   := [addFn]
  imports := [addImp]

-- import 0 resolves to (instance 1, function 0)
def addInst : ModuleInstance Unit where
  module          := addModule
  host            := { funcs := [] }
  resolvedImports := #[.wasm ⟨1⟩ 0]

-- caller (instance 0) has b on top, a below; callee gets params [a, b]
@[simp] private theorem addInst_currentModule :
    ({ instances := #[addInst, addInst], entry := ⟨0⟩ } : RuntimeEnv Unit).currentModule = addInst.module := by
  simp [RuntimeEnv.currentModule, RuntimeEnv.currentInstance]

def addConfig (a b : UInt32) : Config Unit :=
  { expr := .running
      { locals          := { params := [], locals := [], values := [.i32 b, .i32 a] }
        code            := [.call 0]
        resultArity     := 1
        callerRemainder := []
        control         := []
        calls           := [] }
    store :=
      { runtime :=
          { instances := #[addInst, addInst]
            entry     := ⟨0⟩ }
        wasm :=
          { globals := { globals := [] }
            mem     := Mem.empty 0
            host    := () } } }

theorem crossAdd_partiallyMeets (a b : UInt32) :
    PartiallyMeets (addConfig a b) (fun values _store => values = [.i32 (a + b)]) := by
  apply wasm_smallStep_runtime_instance_partiallyMeets (α := Unit)
  · simp only [addConfig]; decide
  · intro gs
    simp only [addConfig, addInst_currentModule]
    iintro ⟨Hruntime, HruntimeInstances⟩
    iapply wp_callCrossInstance ⟨0⟩ addInst ⟨1⟩ addInst #[addInst, addInst]
        0 addImp 0 addFn
        rfl rfl rfl (by decide) rfl (Nat.le.refl) rfl rfl
        $$ [Hruntime] HruntimeInstances
    · inext; iexact Hruntime
    · inext
      iintro ⟨HinstanceOwn', HruntimeInstances'⟩
      simp only [addFn, Function.toLocals, List.map_nil]
      iapply wp_localGet rfl
      inext
      iapply wp_localGet rfl
      inext
      iapply wp_add
      inext
      iapply wp_returnFromCallCrossInstance ⟨1⟩ addInst addInst #[addInst, addInst]
          (by decide) rfl rfl rfl
          $$ [HinstanceOwn'] HruntimeInstances'
      · inext; iexact HinstanceOwn'
      · inext
        iintro _HinstanceCaller
        iapply wp_finish
        inext
        iapply wp_value'
        ipureintro
        rfl

theorem crossAdd_terminates :
    TerminatesWith (addConfig 3 5) (fun _ _ => True) :=
  runSteps_checked_terminates (fuel := 30)
    (fun _ _ => true)
    (by native_decide)
    (fun _ _ _ => trivial)

theorem crossAdd_result :
    TerminatesWith (addConfig 3 5)
      (fun values _ => values = [.i32 8]) :=
  TerminatesWith.of_termination_and_partial crossAdd_terminates
    (crossAdd_partiallyMeets 3 5)

end Wasm.SmallStep
