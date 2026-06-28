import Project.SwapElements.Program
import Project.SwapElements.Spec
import CodeLib.SepLogic.WasmWP

/-! # Swap Elements — Separation Logic Integration

Demonstrates iris-lean ownership reasoning for Wasm memory.
Phase 1: express swap's pre/postcondition using pointsTo_u64.
Phase 2 (future): prove SwapElementsSpec via iProp WP.
-/

namespace Project.SwapElements.SwapSepLogic

open Iris Wasm Wasm.SepLogic Project.SwapElements.Spec

variable [inst : WasmHeapGS]

/-! ## Ownership-based spec for the swap

The manual spec (Spec.lean) says:
  ∀ k, k ≠ i → k ≠ j → read64(k) unchanged

The separation logic spec says:
  { arr[i] ↦ a ∗ arr[j] ↦ b }
    swap
  { arr[i] ↦ b ∗ arr[j] ↦ a }

The frame rule gives "everything else unchanged" for free.
No ∀ k quantifier needed. -/

def swapPre (ptr i j : UInt32) (a b : UInt64) : IProp WasmHeapGF :=
  iprop% (pointsTo_u64 (ptr + 8 * i) a) ∗ (pointsTo_u64 (ptr + 8 * j) b)

def swapPost (ptr i j : UInt32) (a b : UInt64) : IProp WasmHeapGF :=
  iprop% (pointsTo_u64 (ptr + 8 * i) b) ∗ (pointsTo_u64 (ptr + 8 * j) a)

#check @swapPre
#check @swapPost

/-! ## Proof path

Connecting swapPre/swapPost to SwapElementsSpec requires:
1. A WP defined inside iProp (wp_wasm, currently sorry'd)
2. Per-instruction ownership rules for load64/store64
3. An adequacy theorem: iProp WP holds → TerminatesWith holds -/

theorem swap_spec_sep : SwapElementsSpec := by
  sorry -- requires iProp WP + adequacy

end Project.SwapElements.SwapSepLogic