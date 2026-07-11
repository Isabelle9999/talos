import Mathlib.Data.List.Sort
import Project.MergeSort.Spec

/-!
# Pure-Mathlib content lemmas for merge sort

Four lemmas used by the merge-sort correctness proof:

1. `merge_sorted`  — the merge of two sorted lists is sorted.
2. `merge_perm`    — `List.merge l r` is a permutation of `l ++ r`.
3. `sort_recursive` — inductive composition: sorted+perm halves ⟹ sorted+perm merge.
4. `wordsAt_split` — splitting a `wordsAt` region at an index.

No Wasm execution traces are used here; lemmas 1–3 are purely about `List` and
lemma 4 follows from unfolding the `wordsAt` definition and `List.range_add`.
-/

namespace Project.MergeSort.ContentLemmas

section MergeLemmas

variable {α : Type*} [LinearOrder α]

/-- The merge of two `Pairwise (· ≤ ·)` lists is `Pairwise (· ≤ ·)`.
    Delegates to `List.Pairwise.merge`, which holds for any total transitive relation;
    both instances are supplied by `[LinearOrder α]`. -/
theorem merge_sorted {left right : List α}
    (hl : left.Pairwise (· ≤ ·)) (hr : right.Pairwise (· ≤ ·)) :
    (List.merge left right).Pairwise (· ≤ ·) := by
  simpa using hl.merge hr

/-- `List.merge left right` is a permutation of `left ++ right`.
    Uses `List.merge_perm_append` from the Lean 4 core library. -/
theorem merge_perm (left right : List α) :
    (List.merge left right).Perm (left ++ right) := by
  apply List.merge_perm_append

/-- Inductive step: if each half is sorted and a permutation of its input,
    the merged result is sorted and a permutation of the concatenation.
    Composes `merge_sorted`, `merge_perm`, and `List.Perm.trans`. -/
theorem sort_recursive {left right sleft sright : List α}
    (hls : sleft.Pairwise (· ≤ ·)) (hlp : sleft.Perm left)
    (hrs : sright.Pairwise (· ≤ ·)) (hrp : sright.Perm right) :
    (List.merge sleft sright).Pairwise (· ≤ ·) ∧
    (List.merge sleft sright).Perm (left ++ right) :=
  ⟨merge_sorted hls hrs,
   (merge_perm sleft sright).trans (hlp.append hrp)⟩

end MergeLemmas

section WordsAt

open Wasm Project.MergeSort.Spec

/-- Splitting a `wordsAt` region: the first `mid` words followed by the
    remaining `n - mid` words starting at `ptr + 4 * mid`.
    Proved by unfolding the definition and using `List.range_add`. -/
theorem wordsAt_split (m : Mem) (ptr : UInt32) (n mid : Nat) (h : mid ≤ n) :
    wordsAt m ptr n =
    wordsAt m ptr mid ++ wordsAt m (ptr + 4 * UInt32.ofNat mid) (n - mid) := by
  simp only [wordsAt]
  conv_lhs =>
    rw [← Nat.add_sub_cancel' h, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  have key : ptr + 4 * UInt32.ofNat (mid + i) =
             (ptr + 4 * UInt32.ofNat mid) + 4 * UInt32.ofNat i := by
    simp only [UInt32.ofNat_add, UInt32.mul_add]
    rw [← UInt32.add_assoc]
  simp only [Function.comp, key]

end WordsAt

end Project.MergeSort.ContentLemmas
