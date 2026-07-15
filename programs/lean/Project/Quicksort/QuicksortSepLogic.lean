import Project.Quicksort.Program
import Project.Quicksort.Spec
import CodeLib.SepLogic.Adequacy
import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmRules
import CodeLib.SepLogic.WasmWP
import CodeLib.SepLogic.Tactics
import CodeLib.RustStd.Frame

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
    (m.write32 a v).read32 a = v := Mem.read32_write32_same m a v

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
      (base + 4 * UInt32.ofNat k).toNat + 4 ≤ a.toNat ∨
      a.toNat + 4 ≤ (base + 4 * UInt32.ofNat k).toNat) :
    wordsAt (m.write32 a v) base n = wordsAt m base n := by
  unfold wordsAt
  apply List.map_congr_left
  intro k hk
  simp only [List.mem_range] at hk
  exact read32_write32_ne _ a _ v (h k hk)

omit inst in
/-- Two consecutive write32 to disjoint addresses commute on read32. -/
private theorem read32_write32_write32_comm (m : Mem) (a b va vb c : UInt32)
    (hdisj : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat)
    (hc_a : c.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ c.toNat)
    (hc_b : c.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ c.toNat) :
    ((m.write32 a va).write32 b vb).read32 c = m.read32 c := by
  calc ((m.write32 a va).write32 b vb).read32 c
      = (m.write32 a va).read32 c := read32_write32_ne _ b c vb hc_b
    _ = m.read32 c                := read32_write32_ne _ a c va hc_a

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
set_option maxHeartbeats 4000000 in
private theorem func4_spec (st : Store Unit)
    (ptr_a ptr_b : UInt32) (va vb : UInt32) (g0 : UInt32)
    (hg0_min : 16 ≤ g0.toNat)
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
  have hge16 : (16 : UInt32) ≤ g0 := UInt32.le_iff_toNat_le.mpr hg0_min
  have h_g016 : (g0 - 16 : UInt32).toNat = g0.toNat - 16 :=
    UInt32.toNat_sub_of_le g0 16 hge16
  have h_g04 : (g0 - 4 : UInt32).toNat = g0.toNat - 4 :=
    UInt32.toNat_sub_of_le g0 4 (UInt32.le_iff_toNat_le.mpr (by omega : 4 ≤ g0.toNat))
  have h_scr : (g0 - 16 : UInt32) + 12 = g0 - 4 := by
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_add, h_g016, h_g04,
               show UInt32.toNat (12 : UInt32) = 12 from by decide,
               show (2 : Nat) ^ 32 = 4294967296 from by norm_num]
    have hlt : g0.toNat < 4294967296 := UInt32.toNat_lt_size g0
    omega
  -- Bounds checks shaped to match execOne's condition: a.toNat + UInt32.toNat offset + 4 > pages
  have hb_a : ¬(ptr_a.toNat + UInt32.toNat (0 : UInt32) + 4 > st.mem.pages * 65536) := by
    simp only [show UInt32.toNat (0 : UInt32) = 0 from rfl]; omega
  have hb_b : ¬(ptr_b.toNat + UInt32.toNat (0 : UInt32) + 4 > st.mem.pages * 65536) := by
    simp only [show UInt32.toNat (0 : UInt32) = 0 from rfl]; omega
  have hb_scr : ¬((g0 - 16 : UInt32).toNat + UInt32.toNat (12 : UInt32) + 4 > st.mem.pages * 65536) := by
    rw [h_g016, show UInt32.toNat (12 : UInt32) = 12 from rfl]; omega
  have h_rb : (st.mem.write32 (g0 - 4) va).read32 ptr_b = vb :=
    (read32_write32_ne _ (g0 - 4) ptr_b va (Or.comm.mp hsb)).trans hvb
  have h_rscr : ((st.mem.write32 (g0 - 4) va).write32 ptr_a vb).read32 (g0 - 4) = va := by
    rw [read32_write32_ne _ ptr_a (g0 - 4) vb hsa]
    exact read32_write32_same _ _ _
  have hlp : (func4Def.toLocals ([.i32 ptr_b, .i32 ptr_a].take func4Def.numParams).reverse).params
      = [.i32 ptr_a, .i32 ptr_b] := rfl
  have hll : (func4Def.toLocals ([.i32 ptr_b, .i32 ptr_a].take func4Def.numParams).reverse).locals
      = [.i32 0] := rfl
  have hvv : (func4Def.toLocals ([.i32 ptr_b, .i32 ptr_a].take func4Def.numParams).reverse).values
      = [] := rfl
  unfold wp_wasm_prop
  refine ⟨1, ?_⟩
  simp only [show func4Def.body = func4 from rfl, func4, exec, execOne.eq_def,
             hlp, hll, hvv,
             Locals.get, Locals.set?,
             List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
             List.set_cons_zero, List.set_cons_succ,
             List.length_cons, List.length_nil, List.length_set,
             UInt32.add_zero,
             hg0, hva, h_rb, h_rscr, h_scr,
             Mem.read32_write32_same, Mem.write32_pages,
             if_neg hb_scr, if_neg hb_a, if_neg hb_b,
             show ¬((2 : Nat) < 2) from by omega,
             show (2 : Nat) < 2 + 1 from by omega,
             show (2 - 2 : Nat) = 0 from by omega,
             show (0 : Nat) < 2 from by omega,
             show (1 : Nat) < 2 from by omega,
             ite_true, ite_false,
             and_true, true_and]
  constructor
  · rcases hdisj with rfl | h | h
    · have hveq : va = vb := hva.symm.trans hvb
      rw [Mem.read32_write32_same]; exact hveq
    · rw [read32_write32_ne _ ptr_b ptr_a va (Or.inl h), Mem.read32_write32_same]
    · rw [read32_write32_ne _ ptr_b ptr_a va (Or.inr h), Mem.read32_write32_same]
  · intro p hp_a hp_b hp_scr
    rw [read32_write32_ne _ ptr_b p va hp_b,
        read32_write32_ne _ ptr_a p vb hp_a,
        read32_write32_ne _ (g0 - 4) p va hp_scr]

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
set_option maxHeartbeats 4000000 in
theorem func7_spec (st : Store Unit)
    (ptr : UInt32) (xs : List UInt32) (i j : Nat) (err_ptr : UInt32) (g0 : UInt32)
    (hi      : i < xs.length)
    (hj      : j < xs.length)
    (hpg     : ptr.toNat + 4 * xs.length ≤ st.mem.pages * 65536)
    (hpg_u32 : st.mem.pages * 65536 ≤ 4294967296)
    (hg0     : st.globals.globals[0]? = some (.i32 g0))
    (hg0_ok  : (16 : Nat) ≤ g0.toNat)
    (hg0_pg  : g0.toNat ≤ st.mem.pages * 65536)
    (hscr    : (g0 - 4).toNat + 4 ≤ ptr.toNat
             ∨ ptr.toNat + 4 * xs.length ≤ (g0 - 4).toNat)
    (hmem    : wordsAt st.mem ptr xs.length = xs) :
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
          (p.toNat + 4 ≤ (g0 - 4).toNat
          ∨ (g0 - 4).toNat + 4 ≤ p.toNat) →
          st'.mem.read32 p = st.mem.read32 p) := by
  apply wp_wasm_prop_to_TerminatesWith (f := func7Def)
    (by rfl) (by rfl) (by rfl)
    (by
      have h1 : ([.i32 err_ptr, .i32 (UInt32.ofNat j), .i32 (UInt32.ofNat i),
                  .i32 (UInt32.ofNat xs.length), .i32 ptr] : List Value).length = 5 := rfl
      have h2 : func7Def.numParams = 5 := rfl
      omega)
    (by intro _ _ h; exact h)
  -- Local shorthands for the initial Locals struct
  have hlp : (func7Def.toLocals ([.i32 err_ptr, .i32 (UInt32.ofNat j), .i32 (UInt32.ofNat i),
      .i32 (UInt32.ofNat xs.length), .i32 ptr].take func7Def.numParams).reverse).params
      = [.i32 ptr, .i32 (UInt32.ofNat xs.length), .i32 (UInt32.ofNat i),
         .i32 (UInt32.ofNat j), .i32 err_ptr] := rfl
  have hll : (func7Def.toLocals ([.i32 err_ptr, .i32 (UInt32.ofNat j), .i32 (UInt32.ofNat i),
      .i32 (UInt32.ofNat xs.length), .i32 ptr].take func7Def.numParams).reverse).locals
      = [.i32 0] := rfl
  have hlv : (func7Def.toLocals ([.i32 err_ptr, .i32 (UInt32.ofNat j), .i32 (UInt32.ofNat i),
      .i32 (UInt32.ofNat xs.length), .i32 ptr].take func7Def.numParams).reverse).values
      = [] := rfl
  -- Arithmetic bounds (both indices < 2^32)
  have hlen_lt : xs.length < 4294967296 := by omega
  have hi_lt   : i < 4294967296 := by omega
  have hj_lt   : j < 4294967296 := by omega
  -- UInt32 comparisons for the branch instructions
  have hhi_u32 : UInt32.ofNat i < UInt32.ofNat xs.length := by
    rw [UInt32.lt_iff_toNat_lt]
    simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hi_lt, Nat.mod_eq_of_lt hlen_lt]
    exact hi
  have hhj_u32 : UInt32.ofNat j < UInt32.ofNat xs.length := by
    rw [UInt32.lt_iff_toNat_lt]
    simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hj_lt, Nat.mod_eq_of_lt hlen_lt]
    exact hj
  -- Shift reductions: ofNat k <<< (2%32) = 4 * ofNat k
  have hshl_i : UInt32.ofNat i <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat i := by
    rw [show (2 : UInt32) % 32 = 2 from by decide]
    apply UInt32.toNat_inj.mp
    have hi_bnd : i < 2 ^ 30 := by omega
    simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
               show (4 : UInt32).toNat = 4 from rfl,
               Nat.mod_eq_of_lt (show i < 4294967296 from by omega),
               Nat.mod_eq_of_lt (show i * 4 < 4294967296 from by omega)]
    simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
  have hshl_j : UInt32.ofNat j <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat j := by
    rw [show (2 : UInt32) % 32 = 2 from by decide]
    apply UInt32.toNat_inj.mp
    have hj_bnd : j < 2 ^ 30 := by omega
    simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
               show (4 : UInt32).toNat = 4 from rfl,
               Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
               Nat.mod_eq_of_lt (show j * 4 < 4294967296 from by omega)]
    simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
  -- Address .toNat computations
  have haddr_i_toNat : (ptr + 4 * UInt32.ofNat i).toNat = ptr.toNat + 4 * i := by
    simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat, UInt32.toNat_ofNat']
    omega
  have haddr_j_toNat : (ptr + 4 * UInt32.ofNat j).toNat = ptr.toNat + 4 * j := by
    simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat, UInt32.toNat_ofNat']
    omega
  -- (g0 - 4).toNat = g0.toNat - 4
  have h_g04 : (g0 - 4 : UInt32).toNat = g0.toNat - 4 :=
    UInt32.toNat_sub_of_le g0 4 (UInt32.le_iff_toNat_le.mpr (by omega : 4 ≤ g0.toNat))
  -- func4_spec preconditions
  have hpa : (ptr + 4 * UInt32.ofNat i).toNat + 4 ≤ st.mem.pages * 65536 := by
    rw [haddr_i_toNat]; omega
  have hpb : (ptr + 4 * UInt32.ofNat j).toNat + 4 ≤ st.mem.pages * 65536 := by
    rw [haddr_j_toNat]; omega
  have hscr4 : (g0.toNat - 4) + 4 ≤ st.mem.pages * 65536 := by omega
  have hsa : (g0 - 4).toNat + 4 ≤ (ptr + 4 * UInt32.ofNat i).toNat
           ∨ (ptr + 4 * UInt32.ofNat i).toNat + 4 ≤ (g0 - 4).toNat := by
    rw [h_g04, haddr_i_toNat]
    rcases hscr with h | h <;> [left; right] <;> omega
  have hsb : (g0 - 4).toNat + 4 ≤ (ptr + 4 * UInt32.ofNat j).toNat
           ∨ (ptr + 4 * UInt32.ofNat j).toNat + 4 ≤ (g0 - 4).toNat := by
    rw [h_g04, haddr_j_toNat]
    rcases hscr with h | h <;> [left; right] <;> omega
  have hdisj : ptr + 4 * UInt32.ofNat i = ptr + 4 * UInt32.ofNat j
             ∨ (ptr + 4 * UInt32.ofNat i).toNat + 4 ≤ (ptr + 4 * UInt32.ofNat j).toNat
             ∨ (ptr + 4 * UInt32.ofNat j).toNat + 4 ≤ (ptr + 4 * UInt32.ofNat i).toNat := by
    rw [haddr_i_toNat, haddr_j_toNat]
    rcases Nat.lt_trichotomy i j with h | h | h
    · right; left; omega
    · left; rw [h]
    · right; right; omega
  -- Read memory values for func4_spec
  have h_get : ∀ k, k < xs.length → st.mem.read32 (ptr + 4 * UInt32.ofNat k) = xs[k]! := by
    intro k hk
    have hk_wa : k < (wordsAt st.mem ptr xs.length).length := by simp [wordsAt, hk]
    have hge? : (wordsAt st.mem ptr xs.length)[k]? = some (st.mem.read32 (ptr + 4 * UInt32.ofNat k)) :=
      List.getElem?_eq_some_iff.mpr ⟨hk_wa, by simp only [wordsAt, List.getElem_map, List.getElem_range]⟩
    rw [hmem] at hge?
    exact (List.getElem!_of_getElem? hge?).symm
  have hva : st.mem.read32 (ptr + 4 * UInt32.ofNat i) = xs[i]! := h_get i hi
  have hvb : st.mem.read32 (ptr + 4 * UInt32.ofNat j) = xs[j]! := h_get j hj
  -- Apply func4_spec to get a fuel N4 and result store st4
  have h_f4 := func4_spec st (ptr + 4 * UInt32.ofNat i) (ptr + 4 * UInt32.ofNat j)
      (xs[i]!) (xs[j]!) g0 hg0_ok hg0 hpa hpb hscr4 hsa hsb hva hvb hdisj
  obtain ⟨N4, hN4⟩ := h_f4
  obtain ⟨vs4, st4, hrun4, hrd_i, hrd_j, hglob, hpages, hframe⟩ := hN4 N4 le_rfl
  -- Lift run fuel from N4 to N4+2
  have hrun4_ne : run N4 «module» 4 st
      [.i32 (ptr + 4 * UInt32.ofNat j), .i32 (ptr + 4 * UInt32.ofNat i)] {} ≠ .OutOfFuel := by
    rw [hrun4]; simp
  -- run fuel is N4+21:
  --   exec does NOT decrement fuel between sequential instructions
  --   exec_block_cons continuation has exec fuel N4+22 = (N4+21)+1
  --   every execOne in [localGet5..add, call4, ret] uses fuel N4+22
  --   execOne (N4+22) for .call 4: pattern f+1=N4+22 → f=N4+21 → run (N4+21)
  have hrun4_D : run (N4 + 21) «module» 4 st
      [.i32 (ptr + 4 * UInt32.ofNat j), .i32 (ptr + 4 * UInt32.ofNat i)] {} = .Success vs4 st4 :=
    (run_fuel_mono (by omega) hrun4_ne).trans hrun4
  -- Step 1: exec body_C (straight-line, no blocks/calls) → .Break 1
  have h_body_c : exec (N4 + 20) «module» st
      (func7Def.toLocals ([.i32 err_ptr, .i32 (UInt32.ofNat j), .i32 (UInt32.ofNat i),
        .i32 (UInt32.ofNat xs.length), .i32 ptr].take func7Def.numParams).reverse)
      [.localGet 2, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
       .localGet 0, .localGet 2, .const (2 : UInt32), .shl, .add, .localSet 5,
       .localGet 3, .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2] {} =
      .Break 1 st
      { params := [.i32 ptr, .i32 (UInt32.ofNat xs.length), .i32 (UInt32.ofNat i),
                   .i32 (UInt32.ofNat j), .i32 err_ptr],
        locals := [.i32 (ptr + 4 * UInt32.ofNat i)],
        values := [] } := by
    rw [show func7Def.toLocals ([.i32 err_ptr, .i32 (UInt32.ofNat j), .i32 (UInt32.ofNat i),
        .i32 (UInt32.ofNat xs.length), .i32 ptr].take func7Def.numParams).reverse =
      ({ params := [.i32 ptr, .i32 (UInt32.ofNat xs.length), .i32 (UInt32.ofNat i),
                   .i32 (UInt32.ofNat j), .i32 err_ptr],
         locals := [.i32 0],
         values := [] } : Locals) from rfl]
    simp only [exec, execOne.eq_def,
               show ({ params := [.i32 ptr, .i32 (UInt32.ofNat xs.length),
                                  .i32 (UInt32.ofNat i), .i32 (UInt32.ofNat j), .i32 err_ptr],
                       locals := [.i32 0],
                       values := [] } : Locals).params =
                   [.i32 ptr, .i32 (UInt32.ofNat xs.length), .i32 (UInt32.ofNat i),
                    .i32 (UInt32.ofNat j), .i32 err_ptr] from rfl,
               show ({ params := [.i32 ptr, .i32 (UInt32.ofNat xs.length),
                                  .i32 (UInt32.ofNat i), .i32 (UInt32.ofNat j), .i32 err_ptr],
                       locals := [.i32 0],
                       values := [] } : Locals).locals = [.i32 0] from rfl,
               show ({ params := [.i32 ptr, .i32 (UInt32.ofNat xs.length),
                                  .i32 (UInt32.ofNat i), .i32 (UInt32.ofNat j), .i32 err_ptr],
                       locals := [.i32 0],
                       values := [] } : Locals).values = [] from rfl,
               Locals.get, Locals.set?,
               List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
               List.set_cons_zero, List.set_cons_succ,
               List.length_cons, List.length_nil, List.length_set,
               if_pos (show (0 : Nat) < 5 from by omega),
               if_pos (show (1 : Nat) < 5 from by omega),
               if_pos (show (2 : Nat) < 5 from by omega),
               if_pos (show (3 : Nat) < 5 from by omega),
               if_neg (show ¬(5 : Nat) < 5 from by omega),
               if_pos (show (5 : Nat) < 5 + 1 from by omega),
               show (5 - 5 : Nat) = 0 from by omega,
               if_pos (show (0 : Nat) < 1 from by omega),
               show (0 - 0 : Nat) = 0 from by omega,
               if_pos hhi_u32,
               if_pos hhj_u32,
               hshl_i,
               show (1 : UInt32) &&& (1 : UInt32) = 1 from by decide,
               show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
               if_neg (show ¬(0 : UInt32) ≠ 0 from by decide),
               if_pos (show (1 : UInt32) ≠ 0 from by decide),
               if_neg (show ¬(1 : UInt32) = 0 from by decide),
               show 4 * UInt32.ofNat i + ptr = ptr + 4 * UInt32.ofNat i from UInt32.add_comm _ _,
               ite_true, ite_false]
    -- match [Value.i32 1] with | Value.i32 0 :: vs => ... reduces by kernel (1 ≠ 0 : UInt32)
    rfl
  -- Step 2: exec body_B (block_C → Break 1 → Break 0)
  have h_body_b : exec (N4 + 21) «module» st
      (func7Def.toLocals ([.i32 err_ptr, .i32 (UInt32.ofNat j), .i32 (UInt32.ofNat i),
        .i32 (UInt32.ofNat xs.length), .i32 ptr].take func7Def.numParams).reverse)
      [.block 0 0 [.localGet 2, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                   .localGet 0, .localGet 2, .const (2 : UInt32), .shl, .add, .localSet 5,
                   .localGet 3, .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2],
       .localGet 2, .localGet 1, .localGet 4, .call 65, .unreachable] {} =
      .Break 0 st
      { params := [.i32 ptr, .i32 (UInt32.ofNat xs.length), .i32 (UInt32.ofNat i),
                   .i32 (UInt32.ofNat j), .i32 err_ptr],
        locals := [.i32 (ptr + 4 * UInt32.ofNat i)],
        values := [] } := by
    rw [show N4 + 21 = (N4 + 20) + 1 from by omega, exec_block_cons, h_body_c]
  -- Step 3: exec body_A (block_B → Break 0 → swap_code → call 4 → ret → Return)
  have h_body_a : exec (N4 + 22) «module» st
      (func7Def.toLocals ([.i32 err_ptr, .i32 (UInt32.ofNat j), .i32 (UInt32.ofNat i),
        .i32 (UInt32.ofNat xs.length), .i32 ptr].take func7Def.numParams).reverse)
      [.block 0 0
          [.block 0 0 [.localGet 2, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                       .localGet 0, .localGet 2, .const (2 : UInt32), .shl, .add, .localSet 5,
                       .localGet 3, .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2],
           .localGet 2, .localGet 1, .localGet 4, .call 65, .unreachable],
       .localGet 5, .localGet 0, .localGet 3, .const (2 : UInt32), .shl, .add, .call 4, .ret] {} =
      .Return st4 vs4 := by
    rw [show N4 + 22 = (N4 + 21) + 1 from by omega, exec_block_cons, h_body_b]
    simp only [List.take_zero, List.drop_zero, List.nil_append, List.append_nil, hlv]
    simp only [exec, execOne.eq_def,
               show ({ params := [.i32 ptr, .i32 (UInt32.ofNat xs.length),
                                  .i32 (UInt32.ofNat i), .i32 (UInt32.ofNat j), .i32 err_ptr],
                       locals := [.i32 (ptr + 4 * UInt32.ofNat i)],
                       values := [] } : Locals).params =
                   [.i32 ptr, .i32 (UInt32.ofNat xs.length), .i32 (UInt32.ofNat i),
                    .i32 (UInt32.ofNat j), .i32 err_ptr] from rfl,
               show ({ params := [.i32 ptr, .i32 (UInt32.ofNat xs.length),
                                  .i32 (UInt32.ofNat i), .i32 (UInt32.ofNat j), .i32 err_ptr],
                       locals := [.i32 (ptr + 4 * UInt32.ofNat i)],
                       values := [] } : Locals).locals =
                   [.i32 (ptr + 4 * UInt32.ofNat i)] from rfl,
               show ({ params := [.i32 ptr, .i32 (UInt32.ofNat xs.length),
                                  .i32 (UInt32.ofNat i), .i32 (UInt32.ofNat j), .i32 err_ptr],
                       locals := [.i32 (ptr + 4 * UInt32.ofNat i)],
                       values := [] } : Locals).values = [] from rfl,
               Locals.get,
               List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
               List.length_cons, List.length_nil,
               if_pos (show (0 : Nat) < 5 from by omega),
               if_pos (show (3 : Nat) < 5 from by omega),
               if_neg (show ¬(5 : Nat) < 5 from by omega),
               if_pos (show (5 : Nat) < 5 + 1 from by omega),
               show (5 - 5 : Nat) = 0 from by omega,
               if_pos (show (0 : Nat) < 1 from by omega),
               show (0 - 0 : Nat) = 0 from by omega,
               hshl_j,
               show 4 * UInt32.ofNat j + ptr = ptr + 4 * UInt32.ofNat j from UInt32.add_comm _ _,
               hrun4_D, ite_true, ite_false]
  -- Main wp_wasm_prop proof
  unfold wp_wasm_prop
  refine ⟨N4 + 23, ?_⟩
  simp only [show func7Def.body = func7 from rfl, func7]
  rw [show N4 + 23 = (N4 + 22) + 1 from by omega, exec_block_cons, h_body_a]
  -- Prove the postcondition: ⟨wordsAt = swapElems, globals, pages, frame⟩
  refine ⟨?_, hglob, hpages, ?_⟩
  · -- Goal: wordsAt st4.mem ptr xs.length = swapElems xs i j
    apply List.ext_getElem
    · simp [wordsAt, swapElems_length]
    · intro k hk1 hk2
      have hk : k < xs.length := by simp [wordsAt] at hk1; exact hk1
      rw [show (wordsAt st4.mem ptr xs.length)[k]'hk1 =
              st4.mem.read32 (ptr + 4 * UInt32.ofNat k) from by
            simp only [wordsAt, List.getElem_map, List.getElem_range],
          show (swapElems xs i j)[k]'hk2 = (swapElems xs i j)[k]! from
            (List.getElem!_of_getElem? (List.getElem?_eq_some_iff.mpr ⟨hk2, rfl⟩)).symm,
          swapElems_get_at xs i j k hi hj]
      split_ifs with h1 h2 h3
      · -- k = i, i ≠ j
        rw [h1.1]; exact hrd_i
      · -- k = j, i ≠ j
        rw [h2.1]; exact hrd_j
      · -- k = i = j
        obtain ⟨hki, hji⟩ := h3; subst hki; rw [hji] at hrd_i ⊢; exact hrd_i
      · -- k ≠ i, k ≠ j — use frame
        push_neg at h1 h2 h3
        have hki : k ≠ i := fun hki => absurd (h1 hki) (h3 hki)
        have hkj : k ≠ j := fun hkj => hki (hkj.trans (h2 hkj).symm)
        have hk_lt : k < 4294967296 := by omega
        have hk_addr_toNat : (ptr + 4 * UInt32.ofNat k).toNat = ptr.toNat + 4 * k := by
          simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat, UInt32.toNat_ofNat']
          omega
        have h_ki : (ptr + 4 * UInt32.ofNat k).toNat + 4 ≤ (ptr + 4 * UInt32.ofNat i).toNat
                  ∨ (ptr + 4 * UInt32.ofNat i).toNat + 4 ≤ (ptr + 4 * UInt32.ofNat k).toNat := by
          rw [hk_addr_toNat, haddr_i_toNat]
          rcases Nat.lt_or_ge k i with h | h
          · left; omega
          · right; omega
        have h_kj : (ptr + 4 * UInt32.ofNat k).toNat + 4 ≤ (ptr + 4 * UInt32.ofNat j).toNat
                  ∨ (ptr + 4 * UInt32.ofNat j).toNat + 4 ≤ (ptr + 4 * UInt32.ofNat k).toNat := by
          rw [hk_addr_toNat, haddr_j_toNat]
          rcases Nat.lt_or_ge k j with h | h
          · left; omega
          · right; omega
        have h_kscr : (ptr + 4 * UInt32.ofNat k).toNat + 4 ≤ (g0 - 4).toNat
                    ∨ (g0 - 4).toNat + 4 ≤ (ptr + 4 * UInt32.ofNat k).toNat := by
          rw [h_g04, hk_addr_toNat]
          rcases hscr with h | h
          · right; omega
          · left; omega
        rw [hframe _ h_ki h_kj h_kscr, h_get k hk]
  · -- Goal: frame condition for func7
    intro p hp_arr hp_scr
    apply hframe
    · rw [haddr_i_toNat]
      rcases hp_arr with h | h
      · left; omega
      · right; omega
    · rw [haddr_j_toNat]
      rcases hp_arr with h | h
      · left; omega
      · right; omega
    · exact hp_scr

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
  -- Joint induction on fuel: execOne / exec / run all ignore env when m.imports = [].
  set_option maxHeartbeats 4000000 in
  have run_irrel : ∀ (f : Nat), run f m id st args env = run f m id st args {} := by
    intro f
    have h_all : ∀ (g : Nat),
        (∀ (m : Module) (hm : m.imports = []) (st : Store Unit) (s : Locals)
            (inst : Instruction) (env : HostEnv Unit),
            execOne g m st s inst env = execOne g m st s inst {}) ∧
        (∀ (m : Module) (hm : m.imports = []) (st : Store Unit) (s : Locals)
            (p : Program) (env : HostEnv Unit),
            exec g m st s p env = exec g m st s p {}) ∧
        (∀ (m : Module) (hm : m.imports = []) (id : Nat) (st : Store Unit)
            (args : List Value) (env : HostEnv Unit),
            run g m id st args env = run g m id st args {}) := by
      intro g
      induction g with
      | zero =>
        refine ⟨?_, ?_, ?_⟩
        · intro m hm st s inst env
          simp only [execOne.eq_def]
        · intro m hm st s p env
          cases p with
          | nil => rfl
          | cons _ _ => simp only [exec, execOne.eq_def]
        · intro m hm id st args env
          have hImp : m.imports[id]? = none := by simp [hm]
          simp only [run, hImp]
          rcases m.funcs[id - m.imports.length]? with _ | f
          · rfl
          · cases f.body with
            | nil => simp only [exec]
            | cons _ _ => simp only [exec, execOne.eq_def]
      | succ k ih =>
        obtain ⟨ihOne, ihExec, ihRun⟩ := ih
        have irrelOne : ∀ (m : Module) (hm : m.imports = []) (st : Store Unit) (s : Locals)
            (inst : Instruction) (env : HostEnv Unit),
            execOne (k + 1) m st s inst env = execOne (k + 1) m st s inst {} := by
          intro m hm st s inst env
          cases inst with
          | block _ _ _ => simp only [execOne.eq_def, ihExec m hm]
          | loop _ _ _ => simp only [execOne_loop_succ, ihExec m hm, ihOne m hm]
          | iff _ _ _ _ => simp only [execOne.eq_def, ihExec m hm]
          | call _ => simp only [execOne.eq_def, ihRun m hm]
          | callRef _ => simp only [execOne.eq_def, ihRun m hm]
          | callIndirect _ _ => simp only [execOne.eq_def, ihRun m hm]
          | tryTable _ _ _ _ => simp only [execOne.eq_def, ihExec m hm]
          | memOp kIdx inner =>
            simp only [execOne_memOp_succ]
            rcases st.extraMems[kIdx - 1]? with _ | memK
            · rfl
            · rcases m.extraMemories[kIdx - 1]? with _ | declK
              · rfl
              · have hm' : ({ m with memory := some declK } : Module).imports = [] := hm
                simp only [ihOne { m with memory := some declK } hm']
          | _ => simp only [execOne.eq_def]
        have irrelExec : ∀ (m : Module) (hm : m.imports = []) (st : Store Unit) (s : Locals)
            (p : Program) (env : HostEnv Unit),
            exec (k + 1) m st s p env = exec (k + 1) m st s p {} := by
          intro m hm st s p env
          induction p generalizing st s with
          | nil => rfl
          | cons inst rest ihRest =>
            simp only [exec]
            rw [irrelOne m hm st s inst env]
            rcases execOne (k + 1) m st s inst {} with ⟨st', s'⟩ | _ | _ | _ | _ | _ | _ | _
            · exact ihRest st' s'
            all_goals rfl
        refine ⟨irrelOne, irrelExec, ?_⟩
        intro m hm id st args env
        have hImp : m.imports[id]? = none := by simp [hm]
        conv_lhs => rw [run_eq hImp]
        conv_rhs => rw [run_eq hImp]
        rcases m.funcs[id - m.imports.length]? with _ | f
        · rfl
        · simp only [irrelExec m hm]
          rcases exec (k + 1) m st (f.toLocals (args.take f.numParams).reverse) f.body {} with
            _ | ⟨n, _, _⟩ | _ | _ | _ | _ | ⟨id', st', vs'⟩ | _
          · rfl
          · cases n <;> rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · simp only [runTail, ihRun m hm]
          · rfl
    exact (h_all f).2.2 m hno_imports id st args env
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun fuel hle => by
    obtain ⟨vs, st', hrun, hP⟩ := hN fuel hle
    exact ⟨vs, st', (run_irrel fuel).trans hrun, hP⟩⟩
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
