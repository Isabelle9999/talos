import Project.SelectionSort.Program
import Project.SelectionSort.Spec
import CodeLib.SepLogic.ModuleLinking
import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.Adequacy

/-!
# Selection Sort — Separation Logic Proof Skeleton

First program to use module linking: the sort (func0/func8) calls swap (func3→func5)
and is proved correct by importing func3's `funcSatisfies` spec, never seeing
func5's implementation.

## Proof chain

1. `func5_swap_satisfies`  — func5 satisfies the raw-pointer u32-swap iProp spec
2. `func3_swap_satisfies`  — func3 satisfies the bounds-checked swap iProp spec
                             (proved using func5_swap_satisfies + frame_rule for the
                              shadow-stack temp and the rest of the array)
3. `func3_swap_framed`     — frame_rule lifts func3's spec to preserve caller frame R
4. `func0_sort_correct`    — func0 sorts the array
                             (wp_wasm_prop_loop with sortInv; each swap call uses
                              func3_swap_framed to exchange two cells while
                              preserving the rest of the array via arrayAt)
5. `selection_sort_correct`— func8 (slice setup + func0) satisfies SelectionSortSpec

## Call graph
  func8 → func7 (slice init) → func0 (sort loop) → func3 (swap) → func5 (raw swap)

## Wasm function indices in «module»
  func0: 0   outer sort loop (params: arr i32, n i32)
  func3: 3   bounds-checked swap (params: arr len i j err_str: i32)
  func5: 5   raw pointer swap (params: ptr0 ptr1: i32)
  func7: 7   slice init (params: dst src len extra: i32)
  func8: 8   entry point / export (params: ptr len: i32)
-/

namespace Project.SelectionSort.SepLogic

open Wasm Wasm.SepLogic Wasm.SepLogic.ModuleLinking Iris

variable [WasmHeapGS]

-- ─────────────────────────────────────────────────────────────────────────────
-- § 1.  Raw-pointer swap: func5
-- ─────────────────────────────────────────────────────────────────────────────
/-!
func5 body (params: ptr0 i32, ptr1 i32; 1 local):
  globalGet 0 → sp (= 1048576); const 16; sub; localSet 2  -- local2 = sp-16
  local2; ptr0; load32 0; store32 12                        -- *(sp-4) = *ptr0   (save)
  ptr0; ptr1; load32 0; store32 0                           -- *ptr0  = *ptr1
  ptr1; local2; load32 12; store32 0                        -- *ptr1  = *(sp-4)  (restore)
  ret

The temp cell lives at sp - 16 + 12 = sp - 4 = 1048572.
The caller must own it (any value) before the call and gets it back after.
For the sort proof the temp cell is framed out: it is disjoint from the
array (which starts at ≥ 0 but must avoid the shadow-stack area, enforced
by the global-0 precondition in SelectionSortSpec). -/

/-- Byte address of the 4-byte temp slot used by func5. -/
abbrev func5TempAddr : UInt32 := 1048572

/-- func5 satisfies the raw-pointer swap spec.

    Pre : own both cells; the 4-byte temp at 1048572 is in the frame.
    Post: cells exchanged; temp is in the frame (contents irrelevant to caller). -/
theorem func5_swap_satisfies (ptr0 ptr1 v0 v1 : UInt32) :
    funcSatisfies «module» 5
      (fun _ => iprop% pointsTo_u32 ptr0 v0 ∗ pointsTo_u32 ptr1 v1)
      (fun _ _ => iprop% pointsTo_u32 ptr0 v1 ∗ pointsTo_u32 ptr1 v0) := by
  -- Proof outline:
  --   Unfold funcSatisfies; exhibit f = func5Def, m.funcs[5]? = some func5Def.
  --   For arbitrary env, st, args:
  --     intro pre (pointsTo_u32 ptr0 v0 ∗ pointsTo_u32 ptr1 v1)
  --     Step through wp_wasm_iProp_F for each instruction in func5's body:
  --       [globalGet 0, const 16, sub, localSet 2]  — wpures (no memory)
  --       load32 ptr0 0  → push v0 onto stack (need pointsTo_u32 ptr0 v0)
  --       store32 (local2+12) = *(1048572) = v0  (need pointsTo_u32 1048572 t for any t)
  --         [this temp comes from the frame; caller holds it via frame_rule]
  --       load32 ptr1 0 → push v1 (need pointsTo_u32 ptr1 v1)
  --       store32 ptr0 0  → *ptr0 = v1 (consume ptr0 v0, yield ptr0 v1)
  --       load32 1048572  → push v0 (temp)
  --       store32 ptr1 0  → *ptr1 = v0 (consume ptr1 v1, yield ptr1 v0)
  --       ret → postcondition holds
  --   The shadow-stack temp (1048572) must be in the FRAME, not in pre/post,
  --   so callers use frame_rule R := pointsTo_u32 1048572 _ to thread it through.
  sorry

-- ─────────────────────────────────────────────────────────────────────────────
-- § 2.  Bounds-checked indexed swap: func3
-- ─────────────────────────────────────────────────────────────────────────────
/-!
func3 body (params: arr len i j err_str: i32; 1 local):
  Checks i < len; else panic(call 60).
  Computes ptr_i = arr + i*4; local5 = ptr_i.
  Checks j < len; else panic(call 60).
  call 5 (func5) with (ptr_i, arr + j*4).
  ret.

The iProp spec: pre owns arr[i] and arr[j]; post has them exchanged.
The frame (rest of array + shadow temp) is threaded through by frame_rule. -/

/-- Pre for a swap of cells i and j in array at arr. -/
def swapPre (arr i j v_i v_j : UInt32) : Store Unit → IProp WasmHeapGF :=
  fun _ => iprop% pointsTo_u32 (arr + 4 * i) v_i ∗ pointsTo_u32 (arr + 4 * j) v_j

/-- Post for the same swap: values exchanged. -/
def swapPost (arr i j v_i v_j : UInt32) : Store Unit → List Value → IProp WasmHeapGF :=
  fun _ _ => iprop% pointsTo_u32 (arr + 4 * i) v_j ∗ pointsTo_u32 (arr + 4 * j) v_i

/-- func3 satisfies the indexed swap spec (when i < len and j < len).

    Proof by symbolic execution of func3's body:
      bounds checks pass (hi, hj), .call 5 applies func5_swap_satisfies,
      frame_rule preserves the shadow temp and any extra caller frame. -/
theorem func3_swap_satisfies
    (arr len i j v_i v_j : UInt32) (hi : i < len) (hj : j < len) :
    funcSatisfies «module» 3
      (swapPre arr i j v_i v_j)
      (swapPost arr i j v_i v_j) := by
  -- Proof outline:
  --   Unfold funcSatisfies; exhibit f = func3Def, m.funcs[3]? = some func3Def.
  --   For arbitrary env, st, args:
  --     intro pre (swapPre arr i j v_i v_j st)
  --     wpures through the outer block preamble
  --     bounds check i < len:
  --       eqz(ltU i len) = 0 since hi : i < len → br_if 0 not taken → continue
  --     compute ptr_i = arr + i*4; localSet 5 → local5 = ptr_i
  --     bounds check j < len:
  --       ltU j len = 1 since hj : j < len → br_if 1 taken → exit inner block
  --     at .call 5 with stack [arr + j*4, local5=arr+i*4]:
  --       apply func5_swap_satisfies (arr+4*i) (arr+4*j) v_i v_j
  --       (using frame_rule for any shadow temp in the frame)
  --     ret → swapPost holds
  sorry

/-- Frame rule for the indexed swap: preserves additional caller resource R. -/
theorem func3_swap_framed
    (arr len i j v_i v_j : UInt32) (hi : i < len) (hj : j < len)
    (R : IProp WasmHeapGF) :
    funcSatisfies «module» 3
      (fun st => iprop% swapPre arr i j v_i v_j st ∗ R)
      (fun st' vs => iprop% swapPost arr i j v_i v_j st' vs ∗ R) :=
  frame_rule R (func3_swap_satisfies arr len i j v_i v_j hi hj)

-- ─────────────────────────────────────────────────────────────────────────────
-- § 3.  Sort loop invariant
-- ─────────────────────────────────────────────────────────────────────────────
/-!
At outer-loop step i (0-based), the heap contains a permutation `ys` of the
original array `orig` such that:
  • ys[0..i) is sorted (pairwise ≤)
  • every ys[k] for k < i is ≤ every ys[k'] for k' ≥ i
  • the full array is owned in the Iris heap (via genHeapInterp σ ∗ arrayAt arr ys)

`sortInv` packages this as a Lean Prop (using an existential over the Iris auth
ghost σ) so it can be passed to `wp_wasm_prop_loop`. -/

def sortInv (arr n : UInt32) (orig : List UInt32)
    (_ : Store Unit) (_ : Locals) : Prop :=
  ∃ (i : Nat) (ys : List UInt32) (σ : WasmHeapMap (Option UInt8)),
    -- loop progress
    i ≤ n.toNat ∧
    -- array content
    ys.length = n.toNat ∧
    ys.Perm orig ∧
    -- sorted prefix
    (ys.take i).Pairwise (· ≤ ·) ∧
    -- sorted prefix ≤ unsorted suffix (use membership to avoid dependent indexing)
    (∀ a b, a ∈ ys.take i → b ∈ ys.drop i → a ≤ b) ∧
    -- heap ownership: auth+frag combined assertion, a Lean Prop
    (⊢ genHeapInterp σ ∗ arrayAt arr ys)

/-- Measure for termination: remaining elements to sort.
    The real proof would extract the outer loop index `i` from the shadow-stack
    locals in `st` and return `n.toNat - i`.  Skeleton uses `n.toNat` as a
    conservative placeholder (non-increasing); see hstep sorry for details. -/
def sortMeasure (n : UInt32) (_ : Store Unit) (_ : Locals) : Nat := n.toNat

-- ─────────────────────────────────────────────────────────────────────────────
-- § 4.  func0: the sort loop
-- ─────────────────────────────────────────────────────────────────────────────
/-!
func0 (params: arr i32, n i32):
  Sets up an 80-byte shadow frame via globalGet/sub/globalSet.
  Outer .loop: calls func2 (range iterator), which advances the outer cursor.
    Exit condition: outer range exhausted → cleanup frame and .ret.
    Inner .loop: calls func2 (inner range iterator) to scan arr[i+1..n].
      Compare arr[j] < current-min; if so update min-index.
      Exit inner loop when inner range exhausted.
    Call func3(arr, n, i, min_idx, err_string) via `.call 3`.
    Continue outer loop.

The iProp proof applies wp_wasm_prop_loop with `sortInv`.
At each `.call 3`, `func3_swap_framed` is applied, splitting the ownership:
  arrayAt arr ys ⊢ pointsTo_u32 (arr+4*i) ys[i] ∗
                   pointsTo_u32 (arr+4*j) ys[j] ∗
                   R_rest
(via arrayAt_get twice), and reassembled (via arrayAt_set) after the swap.
-/

theorem func0_sort_correct
    (env : HostEnv Unit) (st : Store Unit) (arr n : UInt32)
    (orig : List UInt32)
    (hlen   : orig.length = n.toNat)
    (hbounds : arr.toNat + 4 * n.toNat ≤ st.mem.pages * 65536)
    (hglobal : st.globals.globals[0]? = some (.i32 (1048576 : UInt32)))
    (σ : WasmHeapMap (Option UInt8))
    (hown   : ⊢ genHeapInterp σ ∗ arrayAt arr orig) :
    TerminatesWith env «module» 0 st [.i32 n, .i32 arr]
      (fun st' _ =>
        ∃ ys : List UInt32,
          ys.length = n.toNat ∧
          ys.Perm orig ∧
          ys.Pairwise (· ≤ ·) ∧
          ∃ σ' : WasmHeapMap (Option UInt8), ⊢ genHeapInterp σ' ∗ arrayAt arr ys) := by
  -- Proof outline:
  --   Convert to wp_wasm_prop form via wp_wasm_prop_to_TerminatesWith.
  --   Apply wp_wasm_prop_loop with:
  --     I   := sortInv arr n orig
  --     μ   := sortMeasure n
  --   hinit: sortInv holds at i=0: the identity permutation, empty sorted prefix.
  --   hstep for each outer iteration:
  --     a. wpures through the shadow-stack setup and func1/func2 calls
  --        (these are range-iterator helpers; treat them as black-box
  --         TerminatesWith specs derived from their bodies).
  --     b. At .call 3 (swap arr n i min_idx err):
  --          Use arrayAt_get to extract pointsTo_u32 (arr+4*i) ys[i].
  --          Use arrayAt_get to extract pointsTo_u32 (arr+4*j) ys[j].
  --          Let R_rest = wand-application of arrayAt_set that reconstructs
  --            arrayAt arr ys from the two cells.
  --          Apply func3_swap_framed arr n i min_idx ys[i] ys[j] R_rest.
  --            This gives post: pointsTo_u32 (arr+4*i) ys[j] ∗
  --                              pointsTo_u32 (arr+4*j) ys[i] ∗ R_rest.
  --          Reassemble via arrayAt_set twice to get arrayAt arr ys'.
  --     c. Rebuild sortInv: ys' = ys.set i ys[j]; the new prefix 0..i+1 is sorted
  --        because ys[j] = min of ys[i..n) (inner loop invariant establishes this).
  --     d. The measure n.toNat - (i+1) < n.toNat - i, so μ decreases.
  --   At exit (i = n), sortInv gives ys.Pairwise (· ≤ ·) ∧ ys.Perm orig.
  sorry

-- ─────────────────────────────────────────────────────────────────────────────
-- § 5.  func8: entry point
-- ─────────────────────────────────────────────────────────────────────────────
/-!
func8 (export "selection_sort", params: ptr i32, len i32):
  Sets up a 16-byte shadow frame.
  const 1048684; localSet 3             — some sentinel / error string
  (local2+8); ptr; len; local3; call 7  — func7 writes (ptr, len) into shadow
  load32 (local2+12); localSet 4        — local4 = len
  load32 (local2+8);  local4; call 0   — func0(arr=ptr, n=len)
  restore shadow; ret.

The proof calls func0_sort_correct for the `.call 0` step. -/

theorem selection_sort_correct : SelectionSortSpec := by
  intro env st ptr len xs hlen hbounds hglobal harr
  -- Proof outline:
  --   1. Convert to wp_wasm_prop form: unfold func8Def.
  --   2. wpures: shadow-stack setup (globalGet/sub/globalSet), const, localSets.
  --   3. .call 7 (func7 = slice init):
  --        Prove func7 terminates writing (ptr, len) into shadow memory at local2+8/12.
  --        func7's body is pure stores: .store32 4 then .store32 0, no loops.
  --        Treat via a TerminatesWith lemma for func7 (or inline wp_run).
  --   4. load32 (local2+12) → len; load32 (local2+8) → ptr.
  --   5. .call 0 (func0 = sort):
  --        Need: ∃ σ, ⊢ genHeapInterp σ ∗ arrayAt ptr xs.
  --        Obtain σ from the heap model: construct initial genHeapInterp from
  --          harr (wordsAt st.mem ptr ... = xs) via genHeap_init.
  --          (This step requires the heap-agrees-with-mem invariant set up for st.)
  --        Apply func0_sort_correct ptr len xs hlen ... σ hown.
  --   6. The postcondition of func0 gives ys.Perm xs ∧ ys.Pairwise (· ≤ ·).
  --      Extract wordsAt st'.mem ptr ... = ys from ∃ σ', ⊢ genHeapInterp σ' ∗ arrayAt ptr ys
  --      via heapAgreesWithMem (maintained as loop invariant).
  --   7. Wrap result to match SelectionSortSpec's postcondition.
  sorry

end Project.SelectionSort.SepLogic
