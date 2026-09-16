import Lean

open Lean

namespace CodeLib.Tactics

/-- Data stored for each registered TWP rule. -/
structure WasmRuleEntry where
  thmName  : Name  -- fully-qualified theorem name
  needsRfl : Bool  -- true → `iapply thm rfl`, false → `iapply thm`
  deriving Inhabited

-- NameMap is core Lean (RBMap Name α Name.lt); no extra import needed.
-- Key combines modality and ctor into one Name: e.g. twp ++ const = `twp.const`.
abbrev WasmRuleMap := NameMap WasmRuleEntry

-- NOTE: SimplePersistentEnvExtension is standard Lean 4 stdlib API, but is not
-- used elsewhere in this repo. All existing attributes in Attrs.lean use
-- registerBuiltinAttribute with no-op `add` callbacks (marker-only storage).
-- Using addEntry here for persistent cross-module state is the one novel API
-- pattern introduced by this file.
private def wasmRuleAddEntry (m : WasmRuleMap) (entry : Name × Name × Name × Bool) :
    WasmRuleMap :=
  let (mod, ctor, thm, rfl_) := entry
  m.insert (mod ++ ctor) { thmName := thm, needsRfl := rfl_ }

initialize wasmRuleExt : SimplePersistentEnvExtension
    (Name × Name × Name × Bool) WasmRuleMap ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := wasmRuleAddEntry
    addImportedFn := fun nss =>
      nss.foldl (fun (m : WasmRuleMap) ns =>
        ns.foldl wasmRuleAddEntry m) (∅ : WasmRuleMap)
  }

/-- Look up the registered rule for a given modality and instruction constructor
last-component name (e.g. `Name.mkSimple "const"` for `Instruction.const`).
Returns `none` if no rule has been registered. -/
def getWasmRule (env : Environment) (modality : Name) (ctor : Name) :
    Option WasmRuleEntry :=
  (wasmRuleExt.getState env).find? (modality ++ ctor)

/-- `@[wasm_rule <modality> <head>]` or `@[wasm_rule <modality> <head> rfl]`.
Register a theorem as the TWP rule for the given instruction constructor.
`<modality>` is currently always `twp`.
`<head>` is the unqualified constructor name of `Wasm.Instruction`
(e.g. `const`, `add`, `localGet`) or a sentinel (`nil` for empty-code rules,
`scalarFloat0` for the scalar-float fallback). -/
syntax (name := wasm_rule) "wasm_rule" ident ident ("rfl")? : attr

initialize registerBuiltinAttribute {
  name            := `wasm_rule
  descr           := "Register a theorem as the TWP rule for an instruction constructor."
  applicationTime := .afterCompilation
  add             := fun thmName stx _ => do
    match stx with
    | `(attr| wasm_rule $modality $head rfl) =>
      modifyEnv (wasmRuleExt.addEntry ·
        (modality.getId, head.getId, thmName, true))
    | `(attr| wasm_rule $modality $head) =>
      modifyEnv (wasmRuleExt.addEntry ·
        (modality.getId, head.getId, thmName, false))
    | _ => throwError "wasm_rule: unexpected syntax"
  erase := fun _ => pure ()
}

end CodeLib.Tactics
