import Lean

open Lean

namespace CodeLib.Tactics

/-- Extra data for a memory/global step rule registered via `@[wasm_rule … mem …]`. -/
structure WasmMemRuleInfo where
  predWidth     : String  -- "u32" | "u64" | "byte" | "global"
  addrVariantThm : Name   -- offset-zero `_addr` theorem, or .anonymous
  deriving Inhabited

/-- Kind tag distinguishing pure-step rules from memory/global rules. -/
inductive WasmRuleKind
  | pure (needsRfl : Bool)
  | mem  (info : WasmMemRuleInfo)
  deriving Inhabited

/-- Data stored for each registered TWP/WP rule. -/
structure WasmRuleEntry where
  thmName : Name
  kind    : WasmRuleKind
  deriving Inhabited

-- NameMap is core Lean (RBMap Name α Name.lt); no extra import needed.
-- Key combines modality and ctor into one Name: e.g. twp ++ const = `twp.const`.
abbrev WasmRuleMap := NameMap WasmRuleEntry

-- Flat tuple encoding:
-- (modality, ctor, thm, needsRfl, isMem, predWidth, addrVariant)
-- Pure rules: (mod, ctor, thm, needsRfl, false, "", .anonymous)
-- Mem rules:  (mod, ctor, thm, false,    true,  width, addrVariant)
private def wasmRuleAddEntry (m : WasmRuleMap)
    (entry : Name × Name × Name × Bool × Bool × String × Name) : WasmRuleMap :=
  let (mod, ctor, thm, needsRfl, isMem, predWidth, addrVariant) := entry
  let kind : WasmRuleKind :=
    if isMem then .mem { predWidth, addrVariantThm := addrVariant }
    else .pure needsRfl
  m.insert (mod ++ ctor) { thmName := thm, kind }

initialize wasmRuleExt : SimplePersistentEnvExtension
    (Name × Name × Name × Bool × Bool × String × Name) WasmRuleMap ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := wasmRuleAddEntry
    addImportedFn := fun nss =>
      nss.foldl (fun (m : WasmRuleMap) ns =>
        ns.foldl wasmRuleAddEntry m) (∅ : WasmRuleMap)
  }

/-- Look up the registered rule for a given modality and instruction constructor. -/
def getWasmRule (env : Environment) (modality : Name) (ctor : Name) :
    Option WasmRuleEntry :=
  (wasmRuleExt.getState env).find? (modality ++ ctor)

-- Pure form: `@[wasm_rule <modality> <head>]` or `@[wasm_rule <modality> <head> rfl]`
syntax (name := wasm_rule)     "wasm_rule"     ident ident (&"rfl")? : attr
-- Mem form:  `@[wasm_mem_rule <modality> <head> <width> [<addrVariantThm>]?]`
-- Note: we avoid using "mem" as a keyword atom here because Lean 4 registers it
-- globally, which would break uses of `mem` as a field name elsewhere.
syntax (name := wasm_mem_rule) "wasm_mem_rule" ident ident  ident   (ident)? : attr

private def wasmRuleAddHandler (thmName : Name) (stx : Syntax) (_ : AttributeKind) : AttrM Unit := do
  let modality := stx[1].getId
  let head     := stx[2].getId
  -- Pure form: stx[3] is optional (&"rfl")
  let needsRfl := !stx[3].isNone
  modifyEnv (wasmRuleExt.addEntry · (modality, head, thmName, needsRfl, false, "", .anonymous))

private def wasmMemRuleAddHandler (thmName : Name) (stx : Syntax) (_ : AttributeKind) : AttrM Unit := do
  -- Mem form: stx[1]=modality, stx[2]=head, stx[3]=predWidth, stx[4]=optional addrVariant
  let modality  := stx[1].getId
  let head      := stx[2].getId
  let predWidth := stx[3].getId.getString!
  let addrVariant : Name :=
    if stx[4].isNone then .anonymous
    else
      let inner := stx[4].getArgs
      if inner.size > 0 then inner[0]!.getId else .anonymous
  modifyEnv (wasmRuleExt.addEntry · (modality, head, thmName, false, true, predWidth, addrVariant))

initialize registerBuiltinAttribute {
  name            := `wasm_rule
  descr           := "Register a TWP/WP pure-step rule for an instruction constructor."
  applicationTime := .afterCompilation
  add             := wasmRuleAddHandler
  erase           := fun _ => pure ()
}

initialize registerBuiltinAttribute {
  name            := `wasm_mem_rule
  descr           := "Register a TWP/WP memory/global step rule for an instruction constructor."
  applicationTime := .afterCompilation
  add             := wasmMemRuleAddHandler
  erase           := fun _ => pure ()
}

end CodeLib.Tactics
