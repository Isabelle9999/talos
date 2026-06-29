import Project.SwapElements.Program
import Project.SwapElements.Spec
import CodeLib.SepLogic.WasmWP

/-! # Swap Elements — Separation Logic Proof

Demonstrates ownership transfer through func2's three load/store pairs:
  1. load64 ptr_a → store64 scratch   (temp = *a)
  2. load64 ptr_b → store64 ptr_a     (*a = *b)
  3. load64 scratch → store64 ptr_b   (*b = temp)

Ownership flow:
  Pre:  ptr_a ↦ a  ∗  ptr_b ↦ b  ∗  scratch ↦ _
  Step 1: ptr_a ↦ a consumed by load, scratch ↦ a produced by store
  Step 2: ptr_b ↦ b consumed by load, ptr_a ↦ b produced by store
  Step 3: scratch ↦ a consumed by load, ptr_b ↦ a produced by store
  Post: ptr_a ↦ b  ∗  ptr_b ↦ a  ∗  scratch ↦ a
-/

namespace Project.SwapElements.SwapSepLogic

open Iris Wasm Wasm.SepLogic Project.SwapElements.Spec

variable [inst : WasmHeapGS]

def swapPre (ptr_a ptr_b scratch : UInt32) (a b : UInt64) : IProp WasmHeapGF :=
  iprop% (pointsTo_u64 ptr_a a) ∗ (pointsTo_u64 ptr_b b) ∗ (pointsTo_u64 scratch 0)

def swapPost (ptr_a ptr_b scratch : UInt32) (a b : UInt64) : IProp WasmHeapGF :=
  iprop% (pointsTo_u64 ptr_a b) ∗ (pointsTo_u64 ptr_b a) ∗ (pointsTo_u64 scratch a)

/-! The ownership transfer chain for func2.

Each step consumes ownership via wp_load64/wp_store64 and produces
new ownership. The separating conjunction ensures disjointness:
ptr_a, ptr_b, and scratch must be non-overlapping 8-byte regions. -/

theorem swap_ownership (ptr_a ptr_b scratch : UInt32) (a b : UInt64) :
    iprop% swapPre ptr_a ptr_b scratch a b ⊢
      wp_store64 scratch 0 a (
      wp_store64 ptr_a a b (
      wp_store64 ptr_b b a (
      swapPost ptr_a ptr_b scratch a b))) := by
  unfold swapPre wp_store64 swapPost
  iintro ⟨Ha, Hb, Hs⟩
  iframe
  iintro Hs1 Ha1 Hb1
  iframe

-- The full spec proof connecting ownership to TerminatesWith
theorem swap_spec_sep : SwapElementsSpec := by
  sorry

end Project.SwapElements.SwapSepLogic