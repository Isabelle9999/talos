import Iris
import Iris.HeapLang
import Interpreter.Wasm

/-! # Exploring iris-lean's API for Wasm integration -/

section IrisCore
#check @Iris.BI.BIBase
#check @Iris.BI.BIBase.sep
#check @Iris.BI.BIBase.wand
#check @Iris.BI.BIBase.pure
#check @Iris.BI.BIBase.emp
end IrisCore

section GenHeap
#check @Iris.BI.Lib.GenHeap.genHeapGS
-- search for genHeapInterp alternative:
#print Iris.BI.Lib.GenHeap.genHeapGS
end GenHeap

section HeapLangExample
#check @Iris.HeapLang.Exp
#check @Iris.HeapLang.Val
#check @Iris.HeapLang.State
-- search correct names:
#print Iris.BI.Lib.GenHeap.genHeapGS
end HeapLangExample

section TalosTypes
open Wasm
#check Instruction
#check Value
#check @Store
#check Mem
#check @Mem.read8
#check @Mem.write8
#check @execOne
#check Continuation
end TalosTypes

section LanguageFit
#print Iris.ProgramLogic.Language
end LanguageFit