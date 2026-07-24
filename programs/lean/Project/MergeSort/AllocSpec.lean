import Interpreter.Wasm
import Project.MergeSort.Program

namespace Wasm.SepLogic
open Wasm Project.MergeSort

/-- Allocator hypothesis: dlmalloc at func index 5 allocates n u32 slots.
    This is a hypothesis rather than a global axiom — any theorem depending
    on allocation passes this as a parameter. When the allocator is eventually
    proved (after small-step rewrite), it instantiates this hypothesis. -/
def AllocSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (n : UInt32),
    (∀ i, i < 1050240 → st.mem.bytes i = («module».initialStore (α := Unit)).mem.bytes i) →
    (1050240 + 4 * n.toNat ≤ st.mem.pages * 65536) →
    TerminatesWith env «module» 5 st [.i32 n]
      (fun st' rs => ∃ ptr : UInt32,
        rs = [.i32 ptr] ∧
        1050240 ≤ ptr.toNat ∧
        ptr.toNat + 4 * n.toNat ≤ st'.mem.pages * 65536 ∧
        st'.mem.pages * 65536 ≤ 4294967296 ∧
        st'.globals = st.globals ∧
        (∀ i, i ≥ 1050240 + 4 * n.toNat →
          st'.mem.bytes i = st.mem.bytes i))

axiom run_env_indep
    (hm : «module».imports.length = 0)
    (fuel id : Nat) (st : Store Unit) (args : List Value)
    (env env' : HostEnv Unit) :
    run fuel «module» id st args env = run fuel «module» id st args env'

end Wasm.SepLogic
