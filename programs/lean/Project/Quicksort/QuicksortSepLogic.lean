import Project.Quicksort.Program
import Project.Quicksort.Spec
import CodeLib.SepLogic.Adequacy
import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmRules
import CodeLib.SepLogic.WasmWP
import CodeLib.SepLogic.Tactics

/-!
# Quicksort — Separation Logic Proof Skeleton

## Pipeline (iris-lean)

    iris ownership (arrayAt / pointsTo_u32)   ← WasmHeap.lean
          ↓ wasm_heap_adequacy                 ← Adequacy.lean
    wp_wasm_prop  (Prop-level WP)             ← WasmWP.lean
          ↓ wp_wasm_prop_call
          ↓ wp_wasm_prop_loop
          ↓ wp_wasm_prop_block
    composed wp_wasm_prop
          ↓ wp_wasm_prop_to_TerminatesWith    ← Adequacy.lean
    TerminatesWith  →  QuicksortSpec          ← Spec.lean

BANNED:  wp_run, of_wp_entry_for, wp_call_tw, TerminatesWith.of_run
REQUIRED: wp_wasm_prop, wp_wasm_prop_to_TerminatesWith

## Call graph  (funcIdx within «module», imports = [])

    12 (quicksort entry)
      └─  8 (func8: slice setup — stores ptr/len into frame)
      └─ 11 (func11: recursive quicksort)
              └─ 10 (func10: Lomuto partition)
              │       └─  9 (func9:  initialise scan iterator)
              │       └─  5 (func5:  advance scan iterator)
              │       └─  7 (func7:  swap arr[i] ↔ arr[j])
              │               └─  4 (func4:  swap *ptr_a ↔ *ptr_b)
              └─  1 (func1:  build left-slice descriptor [0..pivot_idx))
              └─ 11 (recursive — left  half, length = pivot_idx)
              └─  2 (func2:  build right-slice descriptor [pivot_idx+1..len))
              └─ 11 (recursive — right half, length = len - pivot_idx - 1)

## Global0 / shadow-stack invariant

    global0 = frame pointer (shadow stack top).
    Every function that uses local frame storage:
      Prologue : frame := global0 − FrameSize ; global0 := frame
      Epilogue : global0 := frame + FrameSize   (= original global0)
    Frame sizes: func4 (scratch only, global0 NOT modified)
                 func7 (no frame, global0 NOT modified)
                 func10: 48 bytes
                 func11: 16 bytes
                 func12: 16 bytes
-/

namespace Project.Quicksort.QuicksortSepLogic

open Wasm Wasm.SepLogic Project.Quicksort

variable [inst : WasmHeapGS]

-- ======================================================================
-- §0  Auxiliary list operations
-- ======================================================================

/-- Swap elements at positions i and j in a list.
    Returns xs unchanged if either index is out of bounds. -/
def swapElems (xs : List UInt32) (i j : Nat) : List UInt32 :=
  match xs[i]?, xs[j]? with
  | some xi, some xj => (xs.set i xj).set j xi
  | _,       _       => xs

omit inst in
@[simp] theorem swapElems_length (xs : List UInt32) (i j : Nat) :
    (swapElems xs i j).length = xs.length := by
  simp only [swapElems]; split <;> simp [List.length_set]

theorem swapElems_perm (xs : List UInt32) (i j : Nat)
    (hi : i < xs.length) (hj : j < xs.length) :
    (swapElems xs i j).Perm xs := by
  sorry
  -- Strategy:
  --   swapElems xs i j = (xs.set i xs[j]).set j xs[i]
  --   List.Perm.set swaps element at one position, preserving all others.
  --   Composition of two List.Perm.set gives the overall permutation.
  --   If i = j, swapElems xs i j = xs.set i xs[i] = xs (set same value), Perm.refl.
  --   Supporting lemma needed: List.perm_set (or prove by List.Perm.swap / List.Perm.cons).

theorem swapElems_get_at (xs : List UInt32) (i j k : Nat)
    (hi : i < xs.length) (hj : j < xs.length) :
    (swapElems xs i j)[k]! =
      if k = i ∧ i ≠ j then xs[j]!
      else if k = j ∧ i ≠ j then xs[i]!
      else if k = i ∧ i = j then xs[k]!  -- k = i = j, value unchanged (swap is identity)
      else xs[k]! := by
  sorry
  -- Strategy:
  --   Unfold swapElems using xs.get? i = some xs[i]!, xs.get? j = some xs[j]!.
  --   Case split on k = i, k = j (with i ≠ j or i = j).
  --   Use List.getElem!_set_eq and List.getElem!_set_ne.

-- ======================================================================
-- §1  Memory read/write algebra  (pure — omit inst)
-- ======================================================================

omit inst in
private theorem write32_bytes_ne (m : Mem) (a v : UInt32) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 4 ≤ i) :
    (m.write32 a v).bytes i = m.bytes i := by
  simp only [Mem.write32]
  have h0 : i ≠ a.toNat     := by omega
  have h1 : i ≠ a.toNat + 1 := by omega
  have h2 : i ≠ a.toNat + 2 := by omega
  have h3 : i ≠ a.toNat + 3 := by omega
  simp [h0, h1, h2, h3]

omit inst in
private theorem read32_write32_same (m : Mem) (a v : UInt32) :
    (m.write32 a v).read32 a = v := by
  sorry
  -- Strategy:
  --   Unfold Mem.write32 — sets bytes at a, a+1, a+2, a+3 to the four LE bytes of v.
  --   Unfold Mem.read32 — reads bytes at a, a+1, a+2, a+3 and reconstructs the u32.
  --   Show that the four written bytes reconstruct v via UInt32 bit-shifting.
  --   Needs: UInt8/UInt32 lemmas for toNat, shiftRight, or, and.

omit inst in
private theorem read32_write32_ne (m : Mem) (a b v : UInt32)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [write32_bytes_ne m a v b.toNat        (by omega),
      write32_bytes_ne m a v (b.toNat + 1)  (by omega),
      write32_bytes_ne m a v (b.toNat + 2)  (by omega),
      write32_bytes_ne m a v (b.toNat + 3)  (by omega)]

omit inst in
/-- A write32 to an address disjoint from every cell of the array
    leaves wordsAt unchanged. -/
private theorem wordsAt_write32_ne (m : Mem) (base a v : UInt32) (n : Nat)
    (h : ∀ k < n,
      a.toNat + 4 ≤ base.toNat + 4 * k ∨
      base.toNat + 4 * k + 4 ≤ a.toNat) :
    wordsAt (m.write32 a v) base n = wordsAt m base n := by
  sorry
  -- Strategy:
  --   Unfold wordsAt = List.map (fun k => m.read32 (base + 4 * k)) (List.range n).
  --   Apply List.map_congr: for each k < n, show
  --     (m.write32 a v).read32 (base + 4 * k) = m.read32 (base + 4 * k)
  --   by read32_write32_ne with h k (by omega).

omit inst in
/-- Two consecutive write32 to disjoint addresses commute on read32. -/
private theorem read32_write32_write32_comm (m : Mem) (a b va vb c : UInt32)
    (hdisj : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat)
    (hc_a : c.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ c.toNat)
    (hc_b : c.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ c.toNat) :
    ((m.write32 a va).write32 b vb).read32 c = m.read32 c := by
  sorry
  -- Strategy:
  --   ((m.write32 a va).write32 b vb).read32 c
  --   = (m.write32 a va).read32 c  (by read32_write32_ne with hc_b)
  --   = m.read32 c                 (by read32_write32_ne with hc_a)

-- ======================================================================
-- §2  func4 spec — swap two u32 memory cells
-- ======================================================================

/-!
func4 (funcIdx 4)  params [ptr_a, ptr_b]  results []

  scratch := global0 − 16       (global0 NOT modified by func4)
  scratch[12] := *ptr_a          write 1: save old *ptr_a at scratch+12 = global0−4
  *ptr_a      := *ptr_b          write 2: overwrite ptr_a
  *ptr_b      := scratch[12]     write 3: complete the swap

TerminatesWith args order (stack top first): [.i32 ptr_b, .i32 ptr_a]
→ (args.take 2).reverse = [ptr_a, ptr_b] → local0=ptr_a, local1=ptr_b.
-/
private theorem func4_spec (st : Store Unit)
    (ptr_a ptr_b : UInt32) (va vb : UInt32) (g0 : UInt32)
    (hg0    : st.globals.globals[0]? = some (.i32 g0))
    (hpa    : ptr_a.toNat + 4 ≤ st.mem.pages * 65536)
    (hpb    : ptr_b.toNat + 4 ≤ st.mem.pages * 65536)
    -- scratch slot g0−4 is in bounds
    (hscr   : (g0.toNat - 4) + 4 ≤ st.mem.pages * 65536)
    -- scratch g0−4 is disjoint from both pointer cells (4-byte regions)
    (hsa    : (g0 - 4).toNat + 4 ≤ ptr_a.toNat ∨ ptr_a.toNat + 4 ≤ (g0 - 4).toNat)
    (hsb    : (g0 - 4).toNat + 4 ≤ ptr_b.toNat ∨ ptr_b.toNat + 4 ≤ (g0 - 4).toNat)
    (hva    : st.mem.read32 ptr_a = va)
    (hvb    : st.mem.read32 ptr_b = vb)
    (hdisj  : ptr_a = ptr_b
            ∨ ptr_a.toNat + 4 ≤ ptr_b.toNat
            ∨ ptr_b.toNat + 4 ≤ ptr_a.toNat) :
    TerminatesWith {} «module» 4 st [.i32 ptr_b, .i32 ptr_a]
      (fun st' _ =>
        st'.mem.read32 ptr_a = vb ∧
        st'.mem.read32 ptr_b = va ∧
        st'.globals = st.globals ∧
        st'.mem.pages = st.mem.pages ∧
        ∀ p : UInt32,
          (p.toNat + 4 ≤ ptr_a.toNat ∨ ptr_a.toNat + 4 ≤ p.toNat) →
          (p.toNat + 4 ≤ ptr_b.toNat ∨ ptr_b.toNat + 4 ≤ p.toNat) →
          (p.toNat + 4 ≤ (g0 - 4).toNat ∨ (g0 - 4).toNat + 4 ≤ p.toNat) →
          st'.mem.read32 p = st.mem.read32 p) := by
  apply wp_wasm_prop_to_TerminatesWith (f := func4Def)
    (by rfl) (by rfl) (by rfl) (by simp [func4Def, Function.numParams])
    (by intro _ _ h; exact h)
  sorry
  -- Strategy (straight-line, no loops — provide explicit fuel):
  --
  --   refine ⟨12, ?_⟩
  --   simp only [exec, func4Def, func4, execOne, Locals.get, Locals.set?]
  --   Unfold each instruction:
  --     globalGet 0  → push g0           (from hg0)
  --     const 16     → push 16
  --     sub          → push g0−16
  --     localSet 2   → local2 := g0−16  (no memory change)
  --     localGet 2, localGet 0, load32 0, store32 12
  --       → mem1 := st.mem.write32 (g0−16+12) va
  --              = st.mem.write32 (g0−4)    va
  --       bounds: (g0−4)+4 ≤ pages  (from hscr)
  --     localGet 0, localGet 1, load32 0, store32 0
  --       → read32 ptr_b from mem1:
  --           mem1.read32 ptr_b = st.mem.read32 ptr_b = vb  (by read32_write32_ne, hsb)
  --       → mem2 := mem1.write32 ptr_a vb
  --       bounds: ptr_a+4 ≤ pages  (from hpa)
  --     localGet 1, localGet 2, load32 12, store32 0
  --       → read32 (g0−4) from mem2:
  --           mem2.read32 (g0−4) = mem1.read32 (g0−4) = va  (by read32_write32_ne, hsa)
  --       → mem3 := mem2.write32 ptr_b va
  --       bounds: ptr_b+4 ≤ pages  (from hpb)
  --     ret  → Fallthrough (st with mem := mem3)
  --
  --   Postcondition verification:
  --     mem3.read32 ptr_a = vb:
  --       If ptr_a ≠ ptr_b: mem3.read32 ptr_a = mem2.read32 ptr_a = vb
  --         (by read32_write32_ne at ptr_b ≠ ptr_a for the last write)
  --         and mem2.read32 ptr_a = vb by read32_write32_same.
  --       If ptr_a = ptr_b: both reads give vb (last write wins).
  --     mem3.read32 ptr_b = va:
  --       read32_write32_same on mem3 at ptr_b.
  --     Frame / framing for other p:
  --       Three writes: to g0−4, ptr_a, ptr_b. For p disjoint from all three,
  --       read32_write32_ne applied three times.
  --   Supporting lemmas: read32_write32_same, read32_write32_ne, hscr, hsa, hsb.

-- ======================================================================
-- §3  func7 spec — array element swap by index
-- ======================================================================

/-!
func7 (funcIdx 7)  params [ptr, len, i, j, err_ptr]  results []

  Checks i < len and j < len (panics via call 65 if not).
  addr_i := ptr + i*4    (using SHL 2 for *4)
  addr_j := ptr + j*4
  Calls func4(addr_i, addr_j) to swap *addr_i ↔ *addr_j.

func7 does NOT allocate a frame and does NOT modify global0.
func4 uses scratch at global0−4 without modifying global0.

Stack convention (top first before call):  [err_ptr, j, i, len, ptr]
→ args = [.i32 err_ptr, .i32 j, .i32 i, .i32 len, .i32 ptr]
→ (args.take 5).reverse = [ptr, len, i, j, err_ptr]
→ local0=ptr  local1=len  local2=i  local3=j  local4=err_ptr  local5=0 (scratch)
-/
theorem func7_spec (st : Store Unit)
    (ptr : UInt32) (xs : List UInt32) (i j : Nat) (err_ptr : UInt32) (g0 : UInt32)
    (hi     : i < xs.length)
    (hj     : j < xs.length)
    (hpg    : ptr.toNat + 4 * xs.length ≤ st.mem.pages * 65536)
    (hg0    : st.globals.globals[0]? = some (.i32 g0))
    (hg0_ok : (4 : Nat) ≤ g0.toNat)
    -- scratch slot g0−4 is strictly below (or above) the array
    (hscr   : (g0 - 4).toNat + 4 ≤ ptr.toNat
            ∨ ptr.toNat + 4 * xs.length ≤ (g0 - 4).toNat)
    (hmem   : wordsAt st.mem ptr xs.length = xs) :
    TerminatesWith {} «module» 7 st
      [.i32 err_ptr, .i32 (UInt32.ofNat j), .i32 (UInt32.ofNat i),
       .i32 (UInt32.ofNat xs.length), .i32 ptr]
      (fun st' _ =>
        wordsAt st'.mem ptr xs.length = swapElems xs i j ∧
        st'.globals = st.globals ∧
        st'.mem.pages = st.mem.pages ∧
        ∀ p : UInt32,
          (p.toNat + 4 ≤ ptr.toNat
          ∨ ptr.toNat + 4 * xs.length ≤ p.toNat) →
          st'.mem.read32 p = st.mem.read32 p) := by
  apply wp_wasm_prop_to_TerminatesWith (f := func7Def)
    (by rfl) (by rfl) (by rfl) (by simp [func7Def, Function.numParams])
    (by intro _ _ h; exact h)
  sorry
  -- Strategy:
  --
  -- 1. PROLOGUE — three nested .block instructions:
  --
  --    Outer block (block 0):
  --      localGet 2 (= i), localGet 1 (= len), ltU → i < len → 1
  --      const 1, and → 1; eqz → 0; br_if 0 → NOT taken (i < len by hi)
  --      localGet 0 (= ptr), localGet 2 (= i), const 2, shl, add
  --        → ptr + i*4;  localSet 5 → local5 := ptr + i*4  (= addr_i)
  --      localGet 3 (= j), localGet 1 (= len), ltU → j < len → 1
  --        const 1, and → 1; br_if 1 → NOT taken (j < len by hj, this exits to middle block)
  --
  --    Wait, re-reading func7: the blocks are structured as:
  --      block A (outer):
  --        block B (middle):
  --          block C (inner):
  --            i < len check → if NOT: br 0 (into C, which traps)
  --            compute addr_i
  --            j < len check → if: br 1 (into B, which does the swap); else br 2 (return)
  --          [C exits here → trap via call 65]
  --        [B body: addr_i, ptr+j*4, call 4, ret]
  --      [A exits via j ≥ len path → trap]
  --
  --    Since hi : i < xs.length, the inner check passes.
  --    Since hj : j < xs.length, br_if 1 fires → we enter block B body.
  --
  -- 2. MIDDLE BLOCK body:
  --    Stack: [addr_i]
  --    localGet 0 (= ptr), localGet 3 (= j), const 2, shl, add → ptr + j*4 (= addr_j)
  --    Stack: [addr_j, addr_i]  (top first: addr_j on top for the call)
  --
  --    Apply wp_wasm_prop_call with func4_spec:
  --      func4_spec st (ptr+i*4) (ptr+j*4) xs[i]! xs[j]! g0
  --      where we need:
  --        hpa: (ptr+i*4)+4 ≤ pages  (from hi, hpg, and 4*i+4 ≤ 4*len ≤ pages-ptr)
  --        hpb: (ptr+j*4)+4 ≤ pages  (from hj, hpg)
  --        hscr: (g0-4)+4 ≤ pages  (from hg0_ok and pages ≥ g0 or hscr)
  --        hsa: (g0-4) disjoint from ptr+i*4 (from hscr and i ∈ [0,len))
  --        hsb: (g0-4) disjoint from ptr+j*4 (from hscr and j ∈ [0,len))
  --        hva: st.mem.read32 (ptr+i*4) = xs[i]!
  --          (from hmem: wordsAt st.mem ptr xs.length = xs at index i)
  --        hvb: st.mem.read32 (ptr+j*4) = xs[j]!
  --          (from hmem at index j)
  --        hdisj: either i=j or cells are 4-apart (from comparing ptr+i*4 vs ptr+j*4)
  --    Postcondition of func4_spec for state st':
  --      st'.mem.read32 (ptr+i*4) = xs[j]!
  --      st'.mem.read32 (ptr+j*4) = xs[i]!
  --      other cells in array: unchanged
  --      globals: st'.globals = st.globals
  --      pages:   st'.mem.pages = st.mem.pages
  --
  -- 3. EPILOGUE: .ret → Fallthrough.
  --
  -- 4. POSTCONDITION reconstruction:
  --    Prove wordsAt st'.mem ptr xs.length = swapElems xs i j:
  --      For cell k: (wordsAt st'.mem ptr xs.length)[k]! = (swapElems xs i j)[k]!
  --        k = i: st'.mem.read32 (ptr+i*4) = xs[j]! = (swapElems xs i j)[i]!
  --               (from swapElems_get_at when i ≠ j)
  --        k = j: st'.mem.read32 (ptr+j*4) = xs[i]! = (swapElems xs i j)[j]!
  --        k other: unchanged = xs[k]! = (swapElems xs i j)[k]!  (swapElems_get_at)
  --    Use wordsAt_write32_ne for framing (all three writes of func4 are inside [ptr, ptr+4*len)).
  --
  -- Supporting lemmas needed:
  --   func4_spec
  --   read32_write32_ne  (extracting xs[i]!, xs[j]! from hmem)
  --   wordsAt_write32_ne  (framing of wordsAt for cells outside [ptr, ptr+4*len))
  --   swapElems_get_at    (list algebra for the postcondition)
  --   ptr+i*4 and ptr+j*4 in bounds: omega from hi, hj, hpg
  --   hscr + i/j ∈ [0,len) → (g0−4) ∉ {ptr+i*4, ptr+j*4}

-- ======================================================================
-- §4  Lomuto partition invariant + func10 spec
-- ======================================================================

/-!
Lomuto partition (func10, funcIdx 10, params [ptr, len], results [i32]):

  frame := global0 − 48 ; global0 := frame
  if len < 1: trap (len is unsigned, so len = 0 → trap)
  pivot := arr[len−1]   (last element)
  i     := 0            (write-head for ≤-elements)
  j     := 0            (scan index, managed by func5/func9 via frame)
  LOOP:
    advance scan via call 5 (func5 returns next j and whether exhausted)
    if loop_done:
      swap arr[i] ↔ arr[len−1]  (via call 7 = func7)
      global0 := frame + 48
      return i
    if arr[j] > pivot:
      j++ ;  continue
    else:                         (arr[j] ≤ pivot)
      swap arr[i] ↔ arr[j]       (via call 7 = func7)
      i++ ; j++ ; continue

func10 allocates a 48-byte frame and uses func7 for swaps.
func7 calls func4 which uses scratch at global0−4 = (old_g0−48)−4 = old_g0−52.
So we need at least 52 bytes of shadow stack before the array.
-/

/-- Lomuto partition loop invariant (parameterised by the scan state).

    After scanning positions [0..j) with write-head i:
    (1) ∀ k < i,           arr[k] ≤ pivot   (left region settled)
    (2) ∀ k, i ≤ k < j,   arr[k] > pivot   (right region identified)
    (3) arr[len−1] = pivot                  (pivot stays at last position)
    (4) arr.Perm orig_xs                    (no elements lost/duplicated)
    (5) 0 ≤ i ≤ j < len                    (index sanity)
    (6) array in bounds                     (pages constraint)

    arr = wordsAt st.mem ptr orig_xs.length,  pivot = orig_xs.getLast! -/
def partition_inv
    (ptr     : UInt32)
    (orig_xs : List UInt32)
    (i j     : Nat)
    (st      : Store Unit) : Prop :=
  let arr   := wordsAt st.mem ptr orig_xs.length
  let pivot := orig_xs.getLast!
  0 < orig_xs.length ∧
  i ≤ j ∧
  j < orig_xs.length ∧
  (∀ k < i,              arr[k]! ≤ pivot) ∧
  (∀ k, i ≤ k → k < j → arr[k]! > pivot) ∧
  arr.getLast! = pivot ∧
  arr.Perm orig_xs ∧
  ptr.toNat + 4 * orig_xs.length ≤ st.mem.pages * 65536

/-!
NOTE on wp_wasm_prop_to_TerminatesWith:
  That theorem requires `hresults : f.results.length = 0` (void function).
  func10Def has `results := [.i32]`, so it CANNOT be converted via this theorem.
  The skeleton therefore proves func10_spec as a direct TerminatesWith sorry.

  A generalised version would be:
    wp_wasm_prop_to_TerminatesWith_with_return
      ... (hresults : f.results.length = k) ...
      (hwp : wp_wasm_prop m initial locals f.body {} (fun st' vs => P st' vs)) :
      TerminatesWith {} m id initial args P
  This handles the .Return branch of wp_wasm_prop (the .Fallthrough branch
  is impossible for a function with results, so hcompat is vacuous).
-/
theorem func10_spec (st : Store Unit)
    (ptr : UInt32) (xs : List UInt32) (g0 : UInt32)
    (hlen     : 1 ≤ xs.length)
    (hpg      : ptr.toNat + 4 * xs.length ≤ st.mem.pages * 65536)
    (hptr     : (52 : Nat) ≤ ptr.toNat)      -- ensures g0−52 is non-negative
    (hg0      : st.globals.globals[0]? = some (.i32 g0))
    (hg0_ok   : (52 : Nat) ≤ g0.toNat)       -- func10 (48) + func4 scratch (4) = 52
    (hframe   : g0.toNat ≤ ptr.toNat)        -- frame [g0−48, g0) strictly below array
    (hmem     : wordsAt st.mem ptr xs.length = xs) :
    TerminatesWith {} «module» 10 st
      [.i32 (UInt32.ofNat xs.length), .i32 ptr]
      (fun st' vs =>
        ∃ pivot_idx : UInt32,
          vs = [.i32 pivot_idx] ∧
          pivot_idx.toNat < xs.length ∧
          ∃ arr : List UInt32,
            arr.length = xs.length ∧
            wordsAt st'.mem ptr xs.length = arr ∧
            arr.Perm xs ∧
            (∀ k < pivot_idx.toNat, arr[k]! ≤ arr[pivot_idx.toNat]!) ∧
            (∀ k, pivot_idx.toNat < k → k < xs.length → arr[k]! > arr[pivot_idx.toNat]!) ∧
            st'.globals = st.globals ∧
            st'.mem.pages = st.mem.pages) := by
  sorry
  -- Strategy:
  --
  -- A. PROLOGUE (straight-line exec_cons chain):
  --    globalGet 0 → g0; const 48; sub; localSet 2 → frame := g0−48
  --    localGet 2; globalSet 0 → global0 := frame = g0−48
  --    local3 := xs.length − 1     (= len−1, the last index)
  --    Bounds check: local3 < local1 (i.e. len−1 < len → always true for len ≥ 1).
  --    If len = 0: branch not taken (hlen : 1 ≤ xs.length).
  --    pivot := arr[len−1] = xs.getLast! (loaded from ptr + (len−1)*4, from hmem).
  --      Use read32_write32_ne / hmem to establish xs.getLast! = st.mem.read32 (ptr+4*(len−1)).
  --    local6 := 0   (write-head i initialised to 0)
  --    Call func9(frame+16, 0, len−1):
  --      func9 sets up a scan iterator in frame[16..32):
  --        frame[16] = start (= 0), frame[20] = end (= len−1)
  --      Requires func9_terminates (a helper TerminatesWith sorry'd separately).
  --
  -- B. LOOP (apply wp_wasm_prop_loop):
  --
  --    I := fun (st_loop : Store Unit) (loc : Locals) =>
  --           ∃ i j : Nat,
  --             partition_inv ptr xs i j st_loop ∧
  --             -- Wasm state encodes i in frame[28] and j via the iterator in frame[8..16)
  --             loc.get? 6 = some (.i32 (UInt32.ofNat i)) ∧
  --             j_from_iter loc st_loop = j   -- connect Wasm locals to abstract j
  --    μ := fun st_loop loc =>
  --           xs.length − 1 − j   -- j strictly increases each iteration
  --
  --    hinit: I holds initially with i = 0, j = 0:
  --      partition_inv established by partition_inv_init (empty ranges trivially ok).
  --
  --    hstep: for each iteration, one of three outcomes:
  --      (a) Loop exits (j = len−1, iterator exhausted → Fallthrough):
  --          Inner check: iter exhausted → fire the block exit path.
  --          Call func7(ptr, len, i, len−1, err_ptr) for the FINAL swap.
  --            func7_spec with xi := xs_cur[i]!, xj = pivot, i := i, j := len−1.
  --          After swap: arr[i] = pivot.
  --          Load local10 := frame[28] = i.
  --          global0 := frame + 48 (restored).
  --          Return .i32 i.
  --          → wp_wasm_prop returns here via .Return st' [.i32 i].
  --          Postcondition: produce the ∃ pivot_idx = i with all required facts.
  --
  --      (b) arr[j] > pivot → BREAK 0 (continue):
  --          j incremented (via func5 advancing the iterator).
  --          I maintained: partition_inv with (i, j+1).
  --          partition_inv_step_gt: extends the right region by one.
  --          μ decreases: len−1 − (j+1) < len−1 − j.
  --
  --      (c) arr[j] ≤ pivot → swap arr[i] ↔ arr[j], BREAK 0:
  --          Call func7(ptr, len, i, j, err_ptr).
  --          func7_spec with xi = xs_cur[i]!, xj = xs_cur[j]! ≤ pivot.
  --          After swap: arr[i] = old arr[j] ≤ pivot; i++ stored in frame[28].
  --          j incremented (via func5).
  --          I maintained with (i+1, j+1):
  --            partition_inv_step_le: extends left region by one.
  --          μ decreases.
  --
  -- C. POSTCONDITION (after loop exits via Fallthrough):
  --    Derive the ∃ pivot_idx from the final i:
  --      arr[i] = pivot         (from final swap placing pivot at position i)
  --      ∀ k < i, arr[k] ≤ pivot = arr[i]  (from partition_inv.left_le)
  --      ∀ k > i, k < len, arr[k] > pivot = arr[i]  (from partition_inv.right_gt + final)
  --      arr.Perm xs            (from partition_inv.perm, composed across all swaps)
  --      st'.globals = st.globals  (global0 restored at exit)
  --    Package as ∃ pivot_idx = i, ∃ arr = wordsAt st'.mem ptr len, ...
  --
  -- Supporting lemmas needed:
  --   func7_spec
  --   func5_terminates : TerminatesWith for func5 (advance scan iterator)
  --   func9_terminates : TerminatesWith for func9 (initialise iterator)
  --   partition_inv_init, partition_inv_step_gt, partition_inv_step_le
  --   partition_inv_conclusion (after final swap)
  --   wordsAt_write32_ne (framing: only [ptr, ptr+4*len) changes)
  --   Frame accounting: frame [g0−48, g0); func4 scratch at frame−4 = g0−52 < ptr

-- ======================================================================
-- §5  func11 spec — recursive quicksort (strong induction on len)
-- ======================================================================

/-!
func11 (funcIdx 11)  params [ptr, len]  results []

  frame := global0 − 16 ; global0 := frame
  if len ≤ 1 :                              ← BASE CASE (br_if exits block)
    global0 := frame + 16 ; ret
  pivot_idx := partition(ptr, len)          call 10 (func10)
  call 1 (func1) with (frame, pivot_idx, ptr, len, err_str):
    → writes frame[0] = ptr, frame[4] = pivot_idx  (left-slice descriptor)
  quicksort(frame[0], frame[4])             call 11 (func11, left half)
  call 2 (func2) with (frame+8, pivot_idx+1, ptr, len, err_str):
    → writes frame[8] = ptr+(pivot_idx+1)*4, frame[12] = len−pivot_idx−1
  quicksort(frame[8], frame[12])            call 11 (func11, right half)
  global0 := frame + 16 ; ret

TerminatesWith args order: [.i32 len, .i32 ptr]
→ (args.take 2).reverse = [ptr, len] → local0=ptr, local1=len.

Termination:
  Left  half length = pivot_idx.toNat              < len  (by func10_spec)
  Right half length = len − pivot_idx.toNat − 1   < len  (by arithmetic)
  So strong induction on n = len terminates.
-/
theorem func11_spec (n : Nat) : ∀
    (st : Store Unit) (ptr : UInt32) (xs : List UInt32) (g0 : UInt32),
    xs.length = n →
    ptr.toNat + 4 * n ≤ st.mem.pages * 65536 →
    (1048576 : Nat) ≤ st.mem.pages * 65536 →
    -- ptr above the shadow stack's maximum extent (n levels of 16-byte frames
    -- plus 52 bytes for func10+func4 scratch; 64*(n+1) is a safe over-estimate)
    64 * (n + 1) ≤ ptr.toNat →
    st.globals.globals[0]? = some (.i32 g0) →
    -- g0 is the current frame pointer; it is ≤ ptr (shadow stack grows down from 1048576)
    g0.toNat ≤ ptr.toNat →
    -- enough room below g0 for func11's own frame (16 bytes) plus recursive calls
    16 ≤ g0.toNat →
    wordsAt st.mem ptr n = xs →
    TerminatesWith {} «module» 11 st
      [.i32 (UInt32.ofNat n), .i32 ptr]
      (fun st' _ =>
        ∃ ys : List UInt32,
          wordsAt st'.mem ptr n = ys ∧
          ys.Pairwise (· ≤ ·) ∧
          ys.Perm xs ∧
          st'.globals = st.globals ∧
          st'.mem.pages = st.mem.pages) := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro st ptr xs g0 hlen hpg hpg_min hptr hg0 hg0_le hg0_ok hmem
    sorry
    -- Strategy:
    --
    -- CASE n ≤ 1 (BASE):
    --   refine ⟨K, ?_⟩  for some small fuel K.
    --   Unfold func11 body:
    --     globalGet 0 → g0; const 16; sub; localSet 2 → frame = g0−16.
    --     localGet 2; globalSet 0 → global0 := g0−16.
    --     Block body:
    --       localGet 1 (= n), const 1, leU → n ≤ 1 → 1
    --       const 1, and → 1; br_if 0 → TAKEN.  Block exits.
    --     localGet 2 (= g0−16), const 16, add → g0−16+16 = g0.
    --     globalSet 0 → global0 := g0  (restored).
    --     ret → Fallthrough.
    --   Postcondition:
    --     ys := xs  (memory unchanged).
    --     ys.Pairwise (·≤·): trivially by List.Pairwise.nil (n=0) or singleton (n=1).
    --     ys.Perm xs: List.Perm.refl.
    --     globals restored: global0 = g0.
    --
    -- CASE n ≥ 2 (INDUCTIVE):
    --   refine ⟨big_fuel, ?_⟩  or use exec_cons chain + call rules.
    --
    --   1. PROLOGUE:
    --      frame := g0−16; global0 := g0−16.
    --      Block body: n ≥ 2 → leU = 0 → br_if NOT taken.  Continue in block body.
    --
    --   2. wp_wasm_prop_call with func10_spec:
    --      func10_spec st_after_prologue ptr xs g0_after
    --        where g0_after = g0−16 (stored global0 after prologue).
    --      Preconditions:
    --        hlen: 1 ≤ xs.length  (from n ≥ 2 ≥ 1)
    --        hpg:  ptr + 4*n ≤ pages  (from hpg)
    --        hptr_f10: 52 ≤ ptr.toNat  (from 64*(n+1) ≤ ptr, n ≥ 1)
    --        hg0_f10:  52 ≤ (g0−16).toNat  (from hg0_ok, n ≥ 2)
    --        hframe_f10: (g0−16).toNat ≤ ptr.toNat  (from hg0_le: g0 ≤ ptr and g0−16 < g0)
    --        hmem: wordsAt st' ptr n = xs
    --      Postcondition (for continuation):
    --        ∃ pivot_idx < n,  ∃ arr with arr.Perm xs ∧ partition property.
    --        Continuation receives pivot_idx on the stack (localSet 3 pops it).
    --
    --   3. wp_wasm_prop_call with func1_terminates:
    --      func1(frame, pivot_idx, ptr, n, err_str):
    --        Writes frame[0] = ptr, frame[4] = pivot_idx.
    --      Preconditions:
    --        frame = g0−16; frame[0..8) in bounds (from hg0_ok).
    --        Frame disjoint from array (g0 ≤ ptr implies g0−16 < ptr).
    --      Postcondition: st''.mem.read32 frame = ptr; st''.mem.read32 (frame+4) = pivot_idx.
    --
    --   4. Load frame[4] = pivot_idx into local4.
    --
    --   5. wp_wasm_prop_call with IH applied to the LEFT half:
    --      IH (pivot_idx.toNat) pivot_idx_lt_n
    --        st'' ptr xs_left g0_f10
    --        hlen' := pivot_idx.toNat (= n_left)
    --        hpg'  := ptr + 4*pivot_idx.toNat ≤ pages  (smaller than hpg)
    --        hptr_left := 64*(n_left+1) ≤ ptr  (n_left < n)
    --        hg0_left := g0_f10 = g0−16  (from func10_spec postcondition)
    --        hmem_left := wordsAt st''.mem ptr n_left = arr[0..pivot_idx.toNat)
    --      Gives ∃ ys_left sorted + perm of arr[0..pivot_idx.toNat).
    --      TerminatesWith args: [.i32 (UInt32.ofNat n_left), .i32 ptr]
    --        = [.i32 pivot_idx, .i32 ptr]  (pushed in func11 body as frame[0], frame[4]).
    --
    --   6. wp_wasm_prop_call with func2_terminates:
    --      func2(frame+8, pivot_idx+1, ptr, n, err_str):
    --        Writes frame[8] = ptr+(pivot_idx+1)*4, frame[12] = n−pivot_idx−1.
    --
    --   7. Load frame[8], frame[12] into locals. Load local7 = frame[12].
    --      wp_wasm_prop_call with IH applied to the RIGHT half:
    --      IH (n−pivot_idx−1) right_lt_n
    --        st''' (ptr+(pivot_idx+1)*4) xs_right g0_left
    --      Gives ∃ ys_right sorted + perm of xs_right.
    --
    --   8. EPILOGUE:
    --      global0 := frame + 16 = g0  (restored).
    --      ret.
    --
    --   9. POSTCONDITION COMPOSITION:
    --      full_arr = arr[0..pivot_idx) ++ [arr[pivot_idx]] ++ arr[pivot_idx+1..n)
    --      ys_left  = sorted permutation of arr[0..pivot_idx)  ← from IH left
    --      ys_right = sorted permutation of arr[pivot_idx+1..n) ← from IH right
    --      arr[pivot_idx] is the partition pivot:
    --        ∀ x ∈ ys_left,  x ≤ arr[pivot_idx]   (from func10_spec left_le)
    --        ∀ x ∈ ys_right, x > arr[pivot_idx]   (from func10_spec right_gt)
    --      Conclude ys := ys_left ++ [arr[pivot_idx]] ++ ys_right is sorted:
    --        sorted_of_sorted_split lemma.
    --      ys.Perm xs:
    --        arr.Perm xs (from func10_spec)
    --        ys_left.Perm arr[0..pivot_idx) and ys_right.Perm arr[pivot_idx+1..n)
    --        Compose: ys.Perm arr (split + left + right) then ys.Perm xs via Perm.trans.
    --
    -- Supporting lemmas needed:
    --   func10_spec
    --   func1_terminates (helper for left slice setup — sorry'd separately)
    --   func2_terminates (helper for right slice setup — sorry'd separately)
    --   IH at pivot_idx.toNat and n−pivot_idx−1 (both < n)
    --   sorted_of_sorted_split: three-way sort composition
    --   List.Perm.trans, List.Perm.append
    --   Memory disjointness: left half [ptr, ptr+4*pivot_idx) and
    --     right half [ptr+(pivot_idx+1)*4, ptr+4*n) are non-overlapping sub-ranges
    --   Frame accounting: each recursive call gets a fresh g0 one level lower

-- ======================================================================
-- §6  func12 spec — entry point
-- ======================================================================

/-!
func12 (funcIdx 12)  params [ptr, len]  results []

  frame := global0 − 16 = 1048576 − 16 = 1048560
  global0 := 1048560
  local3 := 1048724   (data segment address for error messages)
  call func8(frame+8, ptr, len, 1048724):   funcIdx 8
    func8 stores:  (frame+8)[0] = ptr   →  mem[1048568] = ptr
                   (frame+8)[4] = len   →  mem[1048572] = len
  local4 := mem[frame+12] = len
  call func11(mem[frame+8], local4) = func11(ptr, len)
  global0 := 1048560 + 16 = 1048576   (restored)
  ret

TerminatesWith args: [.i32 len, .i32 ptr]
→ local0 = ptr, local1 = len.
-/
theorem func12_spec (st : Store Unit)
    (ptr len : UInt32) (xs : List UInt32)
    (hlen    : xs.length = len.toNat)
    (hpg     : ptr.toNat + 4 * xs.length ≤ st.mem.pages * 65536)
    (hpg_min : (1048576 : Nat) ≤ st.mem.pages * 65536)
    (hptr    : 64 * (xs.length + 1) ≤ ptr.toNat)   -- shadow-stack room
    (hg0     : st.globals.globals[0]? = some (.i32 (1048576 : UInt32)))
    (hmem    : wordsAt st.mem ptr xs.length = xs) :
    TerminatesWith {} «module» 12 st [.i32 len, .i32 ptr]
      (fun st' _ =>
        ∃ ys : List UInt32,
          wordsAt st'.mem ptr ys.length = ys ∧
          ys.Pairwise (· ≤ ·) ∧
          ys.Perm xs) := by
  apply wp_wasm_prop_to_TerminatesWith (f := func12Def)
    (by rfl) (by rfl) (by rfl) (by simp [func12Def, Function.numParams])
    (by intro _ _ h; exact h)
  sorry
  -- Strategy (wp_wasm_prop composition):
  --
  -- 1. PROLOGUE (exec_cons for each straight-line instruction):
  --    globalGet 0 → 1048576; const 16; sub → 1048560; localSet 2 → frame := 1048560.
  --    localGet 2; globalSet 0 → global0 := 1048560.
  --    const 1048724; localSet 3 → local3 := 1048724.
  --
  -- 2. wp_wasm_prop_call with func8_terminates:
  --    func8(frame+8, ptr, len, 1048724) = func8(1048568, ptr, len, 1048724).
  --    func8Def: params [dst_ptr, ptr, len, data], results [].
  --    func8 body:
  --      dst_ptr[4] := len     →  mem[1048572] := len
  --      dst_ptr[0] := ptr     →  mem[1048568] := ptr
  --    Preconditions:
  --      1048568 + 4 ≤ pages (from hpg_min: pages ≥ 1048576 > 1048568+4).
  --      1048572 + 4 ≤ pages.
  --      [1048568, 1048576) disjoint from array at ptr ≥ 64*(len+1) ≥ 64.
  --        Actually we need ptr ≥ 1048576 for disjointness with [1048544, 1048576).
  --        This is a SPEC GAP: hptr only gives 64*(len+1) ≤ ptr,
  --        not necessarily ptr ≥ 1048576 when len is small.
  --        Resolution: strengthen hptr or add separate hptr_min: 1048576 ≤ ptr.toNat.
  --        (Same gap as in SwapSepLogic.lean swap_spec_sep.)
  --    Postcondition: st_f8.mem.read32 1048568 = ptr ∧ st_f8.mem.read32 1048572 = len.
  --
  -- 3. load32 at frame+12 = 1048572 → local4 := len.
  --
  -- 4. load32 at frame+8  = 1048568 → push ptr.
  --    push local4 = len.
  --
  -- 5. wp_wasm_prop_call with func11_spec (xs.length):
  --    func11_spec (xs.length)
  --      st_f8 ptr xs g0_f11
  --      where g0_f11 = 1048560  (global0 after func12 allocated its frame).
  --    Preconditions:
  --      hlen: xs.length = xs.length  ✓
  --      hpg: ptr + 4*xs.length ≤ pages  (from hpg)
  --      hpg_min: 1048576 ≤ pages  (from hpg_min)
  --      hptr_f11: 64*(xs.length+1) ≤ ptr  (from hptr)
  --      hg0_f11: g0_f11 = 1048560 ≤ ptr  (from hptr and xs.length ≥ 0)
  --      hg0_le_f11: 1048560 ≤ ptr  (from hptr ≥ 64 ≥ 16)
  --        Actually: hptr gives 64*(len+1) ≤ ptr, and 64*(len+1) ≥ 64 ≥ 16.
  --      hmem_f11: wordsAt st_f8.mem ptr xs.length = xs
  --        (wordsAt unchanged because func8 only wrote to [1048568, 1048576)
  --         which is disjoint from [ptr, ptr+4*len) when ptr ≥ 1048576.)
  --    Postcondition: ∃ ys, wordsAt st'.mem ptr ys.length = ys ∧ sorted ∧ perm.
  --    The continuation: pull out ys, check ys.length = xs.length from hmem.
  --
  -- 6. EPILOGUE:
  --    localGet 2 = 1048560; const 16; add → 1048576.
  --    globalSet 0 → global0 := 1048576 (restored).
  --    ret → Fallthrough.
  --
  -- Postcondition: pass through from func11_spec postcondition.
  --   ys.length = xs.length  (from wordsAt length and hmem ← func11 sorted same-length array).
  --
  -- Supporting lemmas needed:
  --   func8_terminates: TerminatesWith {} «module» 8 st ... (straight-line, provable by exec_cons)
  --   func11_spec (at n = xs.length)
  --   wordsAt_write32_ne for [1048568, 1048576) vs [ptr, ptr+4*len) disjointness
  --   read32_write32_same to recover ptr and len from frame after func8

-- ======================================================================
-- §7  QuicksortSpec
-- ======================================================================

/-! The host environment does not affect execution when the module has no imports. -/
private theorem terminatesWith_env_irrel
    {m : Module} {id : Nat} {st : Store Unit} {args : List Value}
    {P : Store Unit → List Value → Prop}
    (hno_imports : m.imports = [])
    (env : HostEnv Unit)
    (h : TerminatesWith {} m id st args P) :
    TerminatesWith env m id st args P := by
  sorry
  -- Strategy:
  --   Unfold TerminatesWith: ∃ N, ∀ fuel ≥ N, ∃ vs st', run fuel m id st args {} = .Success vs st' ∧ P st' vs.
  --   Since m.imports = [], 'run' and 'exec'/'execOne' never invoke a host function:
  --     execOne checks for .call / .tailCall; both look up m.funcs[id - m.imports.length]?,
  --     never reaching any host slot (those would come from m.imports).
  --   Therefore: run fuel m id st args {} = run fuel m id st args env for all fuel.
  --   Rewrite in h to get the goal.
  -- Formal path:
  --   run_no_imports : m.imports = [] → run fuel m id st args env₁ = run fuel m id st args env₂
  --   (Proved by induction on fuel / exec / execOne, using hno_imports to rule out the import arm.)

/-- QuicksortSpec: calling func12 sorts the array in place. -/
theorem quicksort_correct : QuicksortSpec := by
  intro env st ptr len xs hlen hpg hpg_min hg0 hmem
  apply terminatesWith_env_irrel (by native_decide) env
  apply func12_spec st ptr len xs hlen hpg hpg_min _ hg0 hmem
  sorry
  -- Spec gap: QuicksortSpec does not include 64*(xs.length+1) ≤ ptr.toNat.
  -- Without this precondition, the shadow stack (growing down from 1048576) could
  -- overlap the array during recursive calls.
  --
  -- The gap mirrors the one in SwapSepLogic.lean (swap_spec_sep says
  -- "st.globals.globals[0]? = some (.i32 1048576)" is missing from SwapElementsSpec).
  --
  -- Resolution options:
  --   (A) Strengthen QuicksortSpec to add hptr: 1048576 ≤ ptr.toNat
  --       (then the shadow stack [1048544, 1048576) is disjoint from the array).
  --   (B) Derive from the existing preconditions:
  --       hg0 gives global0 = 1048576 (the initial stack pointer).
  --       ptr + 4*len ≤ pages * 65536  and  pages * 65536 ≥ 1048576
  --       DO NOT directly imply 1048576 ≤ ptr.
  --       The missing fact is that user allocations are above 1048576.
  --   (C) Accept the spec gap and note it in the theorem.

end Project.Quicksort.QuicksortSepLogic
