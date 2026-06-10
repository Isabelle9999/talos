import Project.Itoa.Proofs

namespace Project.Itoa.Proofs

open Wasm
open Project.Itoa

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem func2_terminates (env : HostEnv Unit) (n : UInt64) (cap : UInt32) :
    TerminatesWith env «module» 2 «module».initialStore [.i32 cap, .i64 n]
      (fun _ rs => rs = []) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i32], [.i32, .i32], func2, []⟩) rfl
  unfold func2
  sorry

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem func4_terminates (env : HostEnv Unit) (n : UInt64) (cap : UInt32) :
    TerminatesWith env «module» 4 «module».initialStore [.i32 cap, .i64 n]
      (fun _ rs => rs = []) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i32], [.i32, .i32, .i32], func4, []⟩) rfl
  unfold func4
  sorry

@[proves Project.Itoa.Spec.CheckI64Spec]
theorem check_i64_correct : Project.Itoa.Spec.CheckI64Spec :=
  check_i64_correct_of_func2_spec (fun env n cap => func2_terminates env n cap)

@[proves Project.Itoa.Spec.CheckU64Spec]
theorem check_u64_correct : Project.Itoa.Spec.CheckU64Spec :=
  check_u64_correct_of_func4_spec (fun env n cap => func4_terminates env n cap)

end Project.Itoa.Proofs