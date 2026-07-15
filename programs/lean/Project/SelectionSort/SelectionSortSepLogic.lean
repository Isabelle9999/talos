import Project.SelectionSort.Program
import Project.SelectionSort.Spec
import CodeLib.SepLogic.ModuleLinking
import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.Adequacy
import Interpreter.Wasm.Wp.Tactic

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

/-! ### Memory read/write helpers (private) -/

/-- Byte at index `i` after writing to `[a.toNat, a.toNat+3]` is unchanged
    when `i` is outside that range. -/
private theorem Wasm.Mem.write32_bytes_other (m : Wasm.Mem) (a v : UInt32)
    (i : Nat) (h : i < a.toNat ∨ a.toNat + 4 ≤ i) :
    (m.write32 a v).bytes i = m.bytes i := by
  simp only [Wasm.Mem.write32]
  split_ifs with h0 h1 h2 h3 <;> first | rfl | omega

/-- Reading at a 4-byte-disjoint address after write32 is unchanged. -/
private theorem Wasm.Mem.read32_write32_other (m : Wasm.Mem) (a b v : UInt32)
    (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Wasm.Mem.read32]
  -- Prove each of the 4 byte indices separately to avoid b.toNat vs b.toNat+0 mismatch
  have k0 : (m.write32 a v).bytes b.toNat = m.bytes b.toNat :=
    Wasm.Mem.write32_bytes_other m a v b.toNat (by rcases h with h | h <;> omega)
  have k1 : (m.write32 a v).bytes (b.toNat + 1) = m.bytes (b.toNat + 1) :=
    Wasm.Mem.write32_bytes_other m a v (b.toNat + 1) (by rcases h with h | h <;> omega)
  have k2 : (m.write32 a v).bytes (b.toNat + 2) = m.bytes (b.toNat + 2) :=
    Wasm.Mem.write32_bytes_other m a v (b.toNat + 2) (by rcases h with h | h <;> omega)
  have k3 : (m.write32 a v).bytes (b.toNat + 3) = m.bytes (b.toNat + 3) :=
    Wasm.Mem.write32_bytes_other m a v (b.toNat + 3) (by rcases h with h | h <;> omega)
  simp only [k0, k1, k2, k3]

/-- Reading at address `a` after writing `v` to `a` recovers `v`. -/
private theorem Wasm.Mem.read32_write32_self (m : Wasm.Mem) (a v : UInt32) :
    (m.write32 a v).read32 a = v := by
  -- Prove each byte at a.toNat+k individually via split_ifs
  have byte0 : (m.write32 a v).bytes a.toNat = (v &&& 0xFF).toUInt8 := by
    simp only [Wasm.Mem.write32]; split_ifs <;> first | rfl | omega
  have byte1 : (m.write32 a v).bytes (a.toNat + 1) = ((v >>> 8) &&& 0xFF).toUInt8 := by
    simp only [Wasm.Mem.write32]; split_ifs <;> first | rfl | omega
  have byte2 : (m.write32 a v).bytes (a.toNat + 2) = ((v >>> 16) &&& 0xFF).toUInt8 := by
    simp only [Wasm.Mem.write32]; split_ifs <;> first | rfl | omega
  have byte3 : (m.write32 a v).bytes (a.toNat + 3) = ((v >>> 24) &&& 0xFF).toUInt8 := by
    simp only [Wasm.Mem.write32]; split_ifs <;> first | rfl | omega
  simp only [Wasm.Mem.read32, byte0, byte1, byte2, byte3]
  -- Reconstruct: prove via BitVec using @[simp, int_toBitVec] lemmas, close with bv_decide
  rw [← UInt32.toBitVec_inj]
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft,
             UInt8.toBitVec_toUInt32, UInt32.toBitVec_toUInt8,
             UInt32.toBitVec_and, UInt32.toBitVec_shiftRight]
  bv_decide

/-- write32 does not change the page count. -/
private theorem Wasm.Mem.write32_pages (m : Wasm.Mem) (a v : UInt32) :
    (m.write32 a v).pages = m.pages := rfl

/-- func5 (raw-pointer swap) terminates and swaps the values at ptr0 and ptr1.

    This is stated as TerminatesWith rather than funcSatisfies because
    funcSatisfies quantifies over all argument lists; the spec fixes the
    Wasm calling convention ([ptr1, ptr0] with ptr1 on top of stack).

    Preconditions:
    - hg:    global 0 holds the shadow-stack base 1048576
    - hb0/1: ptr0/ptr1 regions are in-bounds
    - htemp: the temp slot at 1048572–1048575 is in-bounds (1048576 ≤ pages×65536)
    - hmem0/1: initial memory content
    - h01:   ptr0 and ptr1 regions are disjoint (4-byte)
    - h0t/h1t: ptr0/ptr1 regions are disjoint from the temp slot -/
theorem func5_swap_terminates (ptr0 ptr1 v0 v1 : UInt32)
    (env : HostEnv Unit) (st : Store Unit)
    (hg    : st.globals.globals[0]? = some (.i32 (1048576 : UInt32)))
    (hb0   : ptr0.toNat + 4 ≤ st.mem.pages * 65536)
    (hb1   : ptr1.toNat + 4 ≤ st.mem.pages * 65536)
    (htemp : 1048576 ≤ st.mem.pages * 65536)
    (hmem0 : st.mem.read32 ptr0 = v0)
    (hmem1 : st.mem.read32 ptr1 = v1)
    (h01   : ptr0.toNat + 4 ≤ ptr1.toNat ∨ ptr1.toNat + 4 ≤ ptr0.toNat)
    (h0t   : ptr0.toNat + 4 ≤ 1048572 ∨ 1048576 ≤ ptr0.toNat)
    (h1t   : ptr1.toNat + 4 ≤ 1048572 ∨ 1048576 ≤ ptr1.toNat) :
    TerminatesWith env «module» 5 st [.i32 ptr1, .i32 ptr0]
      (fun st' _ => st'.mem.read32 ptr0 = v1 ∧ st'.mem.read32 ptr1 = v0) := by
  -- Named intermediate memory states (for postcondition only)
  let mem1 := st.mem.write32 func5TempAddr v0      -- after save v0 to temp
  let mem2 := mem1.write32 ptr0 v1                  -- after *ptr0 = v1
  let mem3 := mem2.write32 ptr1 v0                  -- after *ptr1 = v0 (final)
  -- Postcondition holds for the final store
  have hpost : mem3.read32 ptr0 = v1 ∧ mem3.read32 ptr1 = v0 := by
    refine ⟨?_, ?_⟩
    · rw [Wasm.Mem.read32_write32_other mem2 ptr1 ptr0 v0
            (by rcases h01 with h | h <;> omega)]
      exact Wasm.Mem.read32_write32_self mem1 ptr0 v1
    · exact Wasm.Mem.read32_write32_self mem2 ptr1 v0
  -- wp proof for func5's body
  have hwp : wp «module» func5
      (fun c => c = .Return { st with mem := mem3 } [])
      st (func5Def.toLocals [.i32 ptr0, .i32 ptr1]) env := by
    -- func5TempAddr.toNat = 1048572 is needed by omega inside the memory helpers
    have hfunc5 : func5TempAddr.toNat = 1048572 := rfl
    -- Memory read facts in the form that matches the simp-reduced goal
    have hmem0' : st.mem.read32 ptr0 = v0 := hmem0
    have hmem1' : (st.mem.write32 func5TempAddr v0).read32 ptr1 = v1 :=
      (Wasm.Mem.read32_write32_other st.mem func5TempAddr ptr1 v0
        (by rcases h1t with h | h <;> omega)).trans hmem1
    have htemp' : ((st.mem.write32 func5TempAddr v0).write32 ptr0 v1).read32
        func5TempAddr = v0 :=
      (Wasm.Mem.read32_write32_other _ ptr0 func5TempAddr v1
        (by rcases h0t with h | h <;> omega)).trans
          (Wasm.Mem.read32_write32_self st.mem func5TempAddr v0)
    simp only [func5, func5Def, Function.toLocals,
               wp_simp, Locals.get, Locals.set?, Locals.validIndex,
               List.take, List.drop, List.reverse, List.length,
               List.map, List.replicate, ValueType.zero,
               Function.numParams, Function.numLocals]
    -- simp handles: UInt32 arithmetic, if_false_left→¬oob, bounds (hb0/hb1/htemp),
    -- and memory read substitution (hmem0'/hmem1'/htemp')
    simp [hg, hb0, hb1, htemp, hmem0', hmem1', htemp']
    -- residual: LHS = mem3, which is definitional equality via let-unfolding + func5TempAddr abbrev
    exact rfl
  -- Convert wp (∃ N, ∀ fuel ≥ N, ...) to TerminatesWith via run_eq
  unfold Wasm.wp at hwp
  obtain ⟨N, hN⟩ := hwp
  have hexec := hN N (le_refl N)
  apply TerminatesWith.of_run N [] { st with mem := mem3 }
  · rw [Wasm.run_eq (show «module».imports[5]? = none from rfl)]
    have hfunc : «module».funcs[5 - «module».imports.length]? = some func5Def := rfl
    rw [hfunc]
    -- Reduce all concrete list and Function field computations
    simp only [show func5Def.numParams = 2 from rfl,
               show func5Def.results.length = 0 from rfl,
               show func5Def.body = func5 from rfl,
               show ([.i32 ptr1, .i32 ptr0] : List Value).take 2 =
                    [.i32 ptr1, .i32 ptr0] from rfl,
               show ([.i32 ptr1, .i32 ptr0] : List Value).reverse =
                    [.i32 ptr0, .i32 ptr1] from rfl,
               show ([.i32 ptr1, .i32 ptr0] : List Value).drop 2 = [] from rfl]
    rw [hexec]
    simp
  · exact hpost

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
  refine ⟨func3Def, rfl, fun env st args => ?_⟩
  iintro HPre
  -- func3 = [.block 0 0 outer_body, j_panic].
  -- Under hi (i < len) and hj (j < len), outer_body → Return (via .ret in success_path):
  --
  --   Block 0 (middle block B, wp_wasm_iProp_block, body exits Break 0 → Fallthrough):
  --     Block 1 (inner block C, wp_wasm_iProp_block, body exits Break 1 → Break 0):
  --       hi : i < len  → ltU i len = 1 → and 1 → eqz = 0 → br_if 0 NOT taken
  --       compute ptr_i := arr + i*4  (localGet 0, localGet 2, const 2, shl, add, localSet 5)
  --       hj : j < len  → ltU j len = 1 → and 1 → br_if 1 taken → Break 1
  --     execOne(.block inner) = Break 0; middle block body = Break 0
  --     execOne(.block middle) = Fallthrough; outer_body continues with success_path
  --
  --   success_path (wpures after blocks):
  --     localGet 5  = ptr_i  (= arr + 4*i, set during inner block)
  --     localGet 0  = arr
  --     localGet 3  = j
  --     const 2; shl  →  4*j
  --     add           →  ptr_j = arr + 4*j
  --
  --   .call 5 (wp_wasm_iProp_call + func5_swap_satisfies):
  --     func5 swaps *ptr_i ↔ *ptr_j in physical memory
  --     (needs func5_swap_satisfies : funcSatisfies «module» 5 swapPre swapPost,
  --      which requires iProp-level load32/store32 rules — not yet in the framework)
  --
  --   .ret → Return st' []
  --
  -- Ghost update (the key missing piece):
  --   HPre : pointsTo_u32 (arr+4*i) v_i ∗ pointsTo_u32 (arr+4*j) v_j
  --   genHeap_update × 8 bytes  →  pointsTo_u32 (arr+4*i) v_j ∗ pointsTo_u32 (arr+4*j) v_i
  --   Requires genHeapInterp σ, available via wp_wasm_iProp_block_ret_bupd's ∀σ hook.
  --
  -- Full proof once wp_wasm_iProp_block_ret_bupd is provable and iProp call/mem rules exist:
  --   apply wp_wasm_iProp_block_ret_bupd
  --   refine ⟨N, st', [], hexec, fun σ => ?_⟩
  --   · -- hexec : exec N ... outer_body ... = Return st' [] (from execution trace above)
  --   · iintro Hσ
  --     imod (Hσ.sep HPre) with ...  -- split auth + frags
  --     genHeap_update ×8 to swap bytes at ptr_i and ptr_j
  --     imodintro; iexists σ'; isplitl [Hσ']; exact Hσ'; exact swapPost_assembled
  -- Proof needs wp_wasm_iProp_block_ret_bupd (Adequacy.lean) for the outer block's Return.
  -- The goal here is:
  --   ⊢ wp_wasm_iProp «module» st (func3Def.toLocals args)
  --       func3Def.body env (fun st' vs => swapPost arr i j v_i v_j st' vs)
  -- Two blockers before the sorry can be removed:
  -- (1) exec N «module» st (func3Def.toLocals args) outer_body env = Return st' []:
  --     funcSatisfies universally quantifies args; the concrete exec trace above
  --     requires args = [.i32 arr, .i32 len, .i32 i, .i32 j, .i32 err].
  -- (2) genHeapInterp σ ==∗ ∃ σ', genHeapInterp σ' ∗ swapPost:
  --     wp_wasm_iProp_block_ret_bupd itself is sorry'd pending the ==∗ extension
  --     to wp_wasm_iProp_F's Return branch (see Adequacy.lean comment).
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
