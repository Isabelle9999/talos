import Project.InsertionSort.Program

/-!
# Specification for `insertion_sort`
-/

namespace Project.InsertionSort.Spec

open Wasm

/-- TODO: state and prove the behaviour of the wasm export `insertion_sort`.

Informal spec:
Describe what `insertion_sort` computes here, then replace `True` with a
`TerminatesWith` / `PartiallyMeets` statement over `«module»` (the decoded
program emitted into `Program.lean`). -/
@[spec_of "rust-exported" "insertion_sort::insertion_sort"]
def InsertionSortSpec : Prop :=
  True

end Project.InsertionSort.Spec
