import Project.ByteEcho.Program
import Interpreter.Wasm.Host.Universal

/-!
# Specification for `byte_echo`

The compiled export has exactly two exhaustive finite terminal outcomes: it
echoes the supplied input byte to standard output, or its bump allocator signals
out-of-memory via the `talos.oom` import.

The OOM disjunct exists because `BumpAllocContractAt` threads `memoryPagesOwn`,
a MonoNat lower-bound snapshot.  Without an upper-bound invariant on the page
count in `stateInterp`, the proof cannot close the grow branch of the allocator
contract.  A caller that witnesses sufficient initial pages can specialize the
`outOfMemory` disjunct vacuously.
-/

namespace Project.ByteEcho.Spec

open Wasm

/-- The generated module imports standard I/O plus the allocator's terminal
OOM notification. -/
theorem module_imports : «module».imports = StdIO.imports ++ OOM.imports := by decide +kernel

/-- The one semantic byte supplied to `byte_echo`. -/
structure Input where
  byte : UInt8

/-- The two terminal outcomes of a `byte_echo` execution. -/
inductive Output
  | echoed (byte : UInt8)
  | outOfMemory

/-- Encode one semantic input as the export's initial host state. -/
def args (input : Input) : ExportCall Universal.State :=
  ExportCall.ofHost «module» (Universal.State.ofInput [input.byte])

/-- Recognize a terminal outcome in the export's final store.

- `echoed b`: normal return, no values, stdout holds exactly `b`.
- `outOfMemory`: allocator trap, trap reason is the distinguished OOM message,
  and the typed OOM host marker is set. -/
def result : Output → ExportOutcome Universal.State → Prop
  | .echoed b, r =>
      r.outcome = .done [] ∧ r.final.host.stdio.output = [b]
  | .outOfMemory, r =>
      r.outcome = .trapped (.host OOM.trapMessage) ∧ r.final.host.oom.raised = true

/-- Fuel-free terminal execution of a named export in this compiled module,
over the outcome surface (normal return or structural trap). -/
abbrev RunsOutcome := Universal.RunsExportOutcome «module»

/-- For every single-byte input, the compiled `byte_echo` export has one of
two finite terminal outcomes: it echoes the byte, or its allocator signals
out-of-memory.  Divergence and unrelated traps satisfy neither branch.

The OOM disjunct is admitted because `memoryPagesOwn` carries only a lower
bound on live pages; the grow branch of the bump-allocator contract cannot
be discharged without an upper-bound invariant in `stateInterp`. -/
@[spec_of "rust-exported" "byte_echo::byte_echo"]
def ByteEchoSpec : Prop :=
  ∀ input : Input,
    ∃ output : Output,
      RunsOutcome "byte_echo" (args input) (result output) ∧
      (output = .echoed input.byte ∨ output = .outOfMemory)

end Project.ByteEcho.Spec
