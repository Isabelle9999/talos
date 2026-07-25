import Project.Quicksort.Program
import Project.Quicksort.Spec
import CodeLib.SepLogic.Adequacy
import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmRules
import CodeLib.SepLogic.WasmWP
import CodeLib.SepLogic.Tactics
import CodeLib.RustStd.Frame

/-!
# Quicksort — Separation Logic Proof (iris-lean iProp)

## Pipeline (iris-lean)

    iris ownership (arrayAt / pointsTo_u32)   ← WasmHeap.lean
          ↓ wasm_heap_adequacy_with_mem        ← Adequacy.lean
    wp_wasm  (iProp-level WP)                 ← Adequacy.lean
          ↓ wp_wasm_prop_call / loop / block   ← Adequacy.lean
    TerminatesWith  →  QuicksortSpec          ← Spec.lean

REQUIRED: wasm_heap_adequacy_with_mem, arrayAt, wp_iProp_load32, wp_iProp_store32
iProp tactics: iintro, imod, imodintro, iexists, isplitl, iexact, icases

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

open Iris Wasm Wasm.SepLogic Project.Quicksort

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

omit inst in
theorem swapElems_perm (xs : List UInt32) (i j : Nat)
    (hi : i < xs.length) (hj : j < xs.length) :
    (swapElems xs i j).Perm xs := by
  have hswap : swapElems xs i j = (xs.set i xs[j]).set j xs[i] := by
    simp [swapElems, hi, hj]
  rw [hswap]
  by_cases h : i = j
  · subst h
    rw [List.set_set]
    apply List.perm_iff_count.mpr
    intro b
    rw [List.count_set hi]
    split_ifs with h1
    · exact Nat.sub_add_cancel (List.one_le_count_iff.mpr
        (beq_iff_eq.mp h1 ▸ List.getElem_mem hi))
    · omega
  · have hj' : j < (xs.set i xs[j]).length := by simp [hj]
    have hget := List.getElem_set_ne h hj'
    apply List.perm_iff_count.mpr
    intro b
    rw [List.count_set hj', hget, List.count_set hi]
    split_ifs with h1 h2
    · have : 1 ≤ List.count b xs :=
        List.one_le_count_iff.mpr (beq_iff_eq.mp h1 ▸ List.getElem_mem hi)
      omega
    · have : 1 ≤ List.count b xs :=
        List.one_le_count_iff.mpr (beq_iff_eq.mp h1 ▸ List.getElem_mem hi)
      omega
    · omega
    · omega

omit inst in
theorem swapElems_get_at (xs : List UInt32) (i j k : Nat)
    (hi : i < xs.length) (hj : j < xs.length) :
    (swapElems xs i j)[k]! =
      if k = i ∧ i ≠ j then xs[j]!
      else if k = j ∧ i ≠ j then xs[i]!
      else if k = i ∧ i = j then xs[k]!  -- k = i = j, value unchanged (swap is identity)
      else xs[k]! := by
  have hix : xs[i]? = some xs[i]! := by simp [hi]
  have hjx : xs[j]? = some xs[j]! := by simp [hj]
  simp only [swapElems, hix, hjx]
  by_cases hki : k = i
  · by_cases hij : i = j
    · rw [if_neg (by rintro ⟨_, h⟩; exact h hij),
          if_neg (by rintro ⟨_, h⟩; exact h hij),
          if_pos ⟨hki, hij⟩]
      rw [hki, hij]
      simp [hj]
    · rw [if_pos ⟨hki, hij⟩, hki]
      simp [hi, hj, Ne.symm hij]
  · by_cases hkj : k = j
    · have hji : i ≠ j := Ne.symm (hkj ▸ hki)
      rw [if_neg (fun ⟨h, _⟩ => hki h), if_pos ⟨hkj, hji⟩, hkj]
      simp [hi, hj]
    · rw [if_neg (fun ⟨h, _⟩ => hki h), if_neg (fun ⟨h, _⟩ => hkj h),
          if_neg (fun ⟨h, _⟩ => hki h)]
      simp only [List.getElem!_eq_getElem?_getD,
                 List.getElem?_set_ne (Ne.symm hkj),
                 List.getElem?_set_ne (Ne.symm hki)]

-- ======================================================================
-- §2  func4 spec — swap two u32 memory cells (iProp)
-- ======================================================================

/-!
func4 (funcIdx 4)  params [ptr_a, ptr_b]  results []
Swaps *ptr_a ↔ *ptr_b using scratch at global0−4.
iProp spec: takes ownership of ptr_a, ptr_b, and the scratch word at g0−4;
returns ownership updated with swapped values.

Proof sketch (6 memory ops):
  load ptr_a → va on stack        (wp_iProp_load32, non-consuming)
  store va → scratch g0−4         (wp_iProp_store32)
  load ptr_b → vb on stack        (wp_iProp_load32, non-consuming)
  store vb → ptr_a                (wp_iProp_store32)
  load scratch g0−4 → va on stack (wp_iProp_load32, non-consuming)
  store va → ptr_b                (wp_iProp_store32)
-/
set_option maxHeartbeats 800000000 in
private theorem func4_spec (st : Store Unit) (σ : WasmHeapMap (Option UInt8))
    (ptr_a ptr_b : UInt32) (va vb old_scr : UInt32) (g0 : UInt32)
    (hg0_min : 16 ≤ g0.toNat)
    (hg0     : st.globals.globals[0]? = some (.i32 g0))
    (hpa     : ptr_a.toNat + 4 ≤ st.mem.pages * 65536)
    (hpb     : ptr_b.toNat + 4 ≤ st.mem.pages * 65536)
    (hscr    : (g0 - 4).toNat + 4 ≤ st.mem.pages * 65536)
    (hpg_u32 : st.mem.pages * 65536 ≤ 4294967296)
    (hdisj_ab : ptr_a.toNat + 4 ≤ ptr_b.toNat ∨ ptr_b.toNat + 4 ≤ ptr_a.toNat)
    (hagree  : heapAgreesWithMem σ st.mem) :
    ⊢ genHeapInterp σ ∗ pointsTo_u32 ptr_a va ∗ pointsTo_u32 ptr_b vb
                     ∗ pointsTo_u32 (g0 - 4) old_scr -∗
      wp_wasm «module» st
        (func4Def.toLocals ([.i32 ptr_b, .i32 ptr_a].take func4Def.numParams).reverse)
        func4Def.body {}
        (fun st' _ =>
          st'.mem.read32 ptr_a = vb ∧
          st'.mem.read32 ptr_b = va ∧
          st'.globals = st.globals ∧
          st'.mem.pages = st.mem.pages) := by
  -- ── arithmetic helpers ──────────────────────────────────────────────────
  have hge16 : (16 : UInt32) ≤ g0 :=
    UInt32.le_iff_toNat_le.mpr (by simp only [show (16:UInt32).toNat = 16 from rfl]; exact hg0_min)
  have hge4  : (4  : UInt32) ≤ g0 :=
    UInt32.le_iff_toNat_le.mpr (by simp only [show (4:UInt32).toNat = 4 from rfl]; omega)
  have h_g016 : (g0 - 16 : UInt32).toNat = g0.toNat - 16 :=
    UInt32.toNat_sub_of_le g0 16 hge16
  have h_g04  : (g0 - 4  : UInt32).toNat = g0.toNat - 4  :=
    UInt32.toNat_sub_of_le g0 4  hge4
  -- (g0−16)+12 = g0−4  (frame's scratch slot)
  have h_scr_addr : (g0 - 16 : UInt32) + 12 = g0 - 4 := by
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_add, h_g016, show (12:UInt32).toNat = 12 from rfl,
               show UInt32.size = 4294967296 from rfl, h_g04]
    have := UInt32.toNat_lt_size g0; omega
  -- 4*0 = 0 in UInt32 (named for use in rewriting wp_iProp bounds)
  have h40 : (4:UInt32) * UInt32.ofNat 0 = 0 := by decide
  -- (g0−4)+4*0 = (g0−16)+12 (match wp_iProp address to Wasm store address)
  have h_eq_scr : (g0 - 4 : UInt32) + 4 * UInt32.ofNat 0 = (g0 - 16 : UInt32) + 12 := by
    rw [h40, UInt32.add_zero, h_scr_addr.symm]
  -- ptr+0 identities for read/write address matching
  have h_pa0 : ptr_a + (0:UInt32) = ptr_a := UInt32.add_zero _
  have h_pb0 : ptr_b + (0:UInt32) = ptr_b := UInt32.add_zero _
  -- lift pointsTo_u32 p v to arrayAt p [v] (the form expected by wp_iProp_*)
  have to_arr_a : pointsTo_u32 ptr_a va ⊢ arrayAt ptr_a [va] := by
    simp only [arrayAt]; exact BI.sep_emp.mpr
  have to_arr_b : pointsTo_u32 ptr_b vb ⊢ arrayAt ptr_b [vb] := by
    simp only [arrayAt]; exact BI.sep_emp.mpr
  have to_arr_scr : pointsTo_u32 (g0 - 4) old_scr ⊢ arrayAt (g0 - 4) [old_scr] := by
    simp only [arrayAt]; exact BI.sep_emp.mpr
  -- ── iProp introduction ──────────────────────────────────────────────────
  iintro ⟨Hσ, HA_a_pt, HA_b_pt, HA_scr_pt⟩
  icases to_arr_a $$ [$HA_a_pt] with HA_a
  icases to_arr_b $$ [$HA_b_pt] with HA_b
  icases to_arr_scr $$ [$HA_scr_pt] with HA_scr
  -- ── globalGet 0 (inline; hget = hg0 ≠ rfl) ────────────────────────────
  -- `show func4Def.body = .globalGet 0 :: _` lets simp reduce the match without
  -- expanding func4Def/func4 globally (which would bloat the goal via «module»).
  unfold wp_wasm; iapply least_fixpoint_unfold_mpr
  simp only [wp_wasm_F,
    show func4Def.body = .globalGet 0 ::
      [.const (16:UInt32), .sub, .localSet 2, .localGet 2, .localGet 0,
       .load32 (0:UInt32), .store32 (12:UInt32), .localGet 0, .localGet 1,
       .load32 (0:UInt32), .store32 (0:UInt32), .localGet 1, .localGet 2,
       .load32 (12:UInt32), .store32 (0:UInt32), .ret] from rfl]
  iintro %σ₀ %hagree₀ Hσ₀
  imodintro; iexists σ₀, _, _
  -- simp only (not simp) avoids Fallthrough.injEq decomposing the equality
  -- before simp can close it via metavar assignment
  isplitl []; · exact BI.pure_intro (by simp only [execOne.eq_def, hg0]; rfl)
  isplitl []; · exact BI.pure_intro hagree₀
  isplitl [Hσ₀]; · iexact Hσ₀
  have hloc4 : func4Def.toLocals ([.i32 ptr_b, .i32 ptr_a].take func4Def.numParams).reverse =
      { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 0], values := [] } := by
    have hnp : func4Def.numParams = 2 := by decide
    rw [hnp]; simp [Function.toLocals, func4Def, ValueType.zero]
  simp [hloc4]
  -- ── const 16; sub; localSet 2; localGet 2; localGet 0 (all pure) ────────
  iwpures
  -- ── STEP 7: load32 0 at ptr_a → read va ────────────────────────────────
  (try unfold wp_wasm); iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
  iintro %σ₁ %hagree₁ Hσ₁
  imod (wp_iProp_load32 hagree₁ (ptr := ptr_a) (xs := [va]) (k := 0) (hk := by simp)
        (hbounds := by rw [h40, UInt32.add_zero]; exact hpa)
        hpg_u32) $$ [$Hσ₁ $HA_a] with ⟨Hσ₁', HA_a', hread_a⟩
  imodintro; iexists σ₁, _, _
  isplitl []; · exact BI.pure_intro (by
    simp only [execOne.eq_def, show (0:UInt32).toNat = 0 from rfl]
    have hok : ¬(ptr_a.toNat + 0 + 4 > st.mem.pages * 65536) := by omega
    simp only [if_neg hok]; rfl)
  isplitl []; · exact BI.pure_intro hagree₁
  isplitl [Hσ₁']; · iexact Hσ₁'
  -- ── STEP 8: store32 12 at g0−16 → write va to scratch (g0−4) ───────────
  (try unfold wp_wasm); iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
  iintro %σ₂ %hagree₂ Hσ₂
  imod (wp_iProp_store32 hagree₂ (ptr := g0 - 4) (xs := [old_scr]) (k := 0) (hk := by simp)
        (st.mem.read32 (ptr_a + (0:UInt32)))
        (hbounds := by rw [h40, UInt32.add_zero]; exact hscr)
        hpg_u32) $$ [$Hσ₂ $HA_scr] with ⟨%σ₃, Hagree₃_raw, Hσ₃, HA_scr'⟩
  simp only [h_eq_scr] at Hagree₃_raw
  imodintro; iexists σ₃, _, _
  isplitl []; · exact BI.pure_intro (by
    simp only [execOne.eq_def, show (12:UInt32).toNat = 12 from rfl, h_g016]
    have hok : ¬(g0.toNat - 16 + 12 + 4 > st.mem.pages * 65536) := by
      have := hscr; rw [h_g04] at this; omega
    simp only [if_neg hok]; rfl)
  isplitl [Hagree₃_raw]; · iexact Hagree₃_raw
  isplitl [Hσ₃]; · iexact Hσ₃
  -- ── localGet 0; localGet 1 (pure) ───────────────────────────────────────
  iwpures
  -- ── STEP 11: load32 0 at ptr_b → read vb ───────────────────────────────
  (try unfold wp_wasm); iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
  iintro %σ₄ %hagree₄ Hσ₄
  imod (wp_iProp_load32 hagree₄ (ptr := ptr_b) (xs := [vb]) (k := 0) (hk := by simp)
        (hbounds := by rw [h40, UInt32.add_zero]; simp only [Mem.write32_pages]; exact hpb)
        (by simp only [Mem.write32_pages]; exact hpg_u32)) $$ [$Hσ₄ $HA_b] with ⟨Hσ₄', HA_b', hread_b⟩
  imodintro; iexists σ₄, _, _
  isplitl []; · exact BI.pure_intro (by
    simp only [execOne.eq_def, show (0:UInt32).toNat = 0 from rfl, Mem.write32_pages]
    have hok : ¬(ptr_b.toNat + 0 + 4 > st.mem.pages * 65536) := by omega
    simp only [if_neg hok]; rfl)
  isplitl []; · exact BI.pure_intro hagree₄
  isplitl [Hσ₄']; · iexact Hσ₄'
  -- ── STEP 12: store32 0 at ptr_a → write vb ──────────────────────────────
  (try unfold wp_wasm); iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
  iintro %σ₅ %hagree₅ Hσ₅
  imod (wp_iProp_store32 hagree₅ (ptr := ptr_a) (xs := [va]) (k := 0) (hk := by simp)
        vb
        (hbounds := by rw [h40, UInt32.add_zero]; simp only [Mem.write32_pages]; exact hpa)
        (by simp only [Mem.write32_pages]; exact hpg_u32)) $$ [$Hσ₅ $HA_a'] with ⟨%σ₆, Hagree₆_raw, Hσ₆, HA_a''⟩
  -- Rewrite vb → mem.read32(ptr_b) in Hagree₆_raw to match the Wasm stack value
  simp only [h40, UInt32.add_zero] at hread_b
  simp only [← hread_b, h40, UInt32.add_zero] at Hagree₆_raw
  imodintro; iexists σ₆, _, _
  isplitl []; · exact BI.pure_intro (by
    simp only [execOne.eq_def, show (0:UInt32).toNat = 0 from rfl, Mem.write32_pages,
               UInt32.add_zero]
    have hok : ¬(ptr_a.toNat + 0 + 4 > st.mem.pages * 65536) := by omega
    simp only [if_neg hok]; rfl)
  isplitl [Hagree₆_raw]; · iexact Hagree₆_raw
  isplitl [Hσ₆]; · iexact Hσ₆
  -- ── localGet 1; localGet 2 (pure) ───────────────────────────────────────
  iwpures
  -- ── STEP 15: load32 12 at g0−16 → read va from scratch ─────────────────
  (try unfold wp_wasm); iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
  iintro %σ₇ %hagree₇ Hσ₇
  imod (wp_iProp_load32 hagree₇ (ptr := g0 - 4)
        (xs := [st.mem.read32 (ptr_a + (0:UInt32))]) (k := 0) (hk := by simp)
        (hbounds := by rw [h40, UInt32.add_zero]; simp only [Mem.write32_pages]; exact hscr)
        (by simp only [Mem.write32_pages]; exact hpg_u32)) $$ [$Hσ₇ $HA_scr'] with ⟨Hσ₇', HA_scr'', hread_scr⟩
  imodintro; iexists σ₇, _, _
  isplitl []; · exact BI.pure_intro (by
    simp only [execOne.eq_def, show (12:UInt32).toNat = 12 from rfl, Mem.write32_pages, h_g016]
    have hok : ¬(g0.toNat - 16 + 12 + 4 > st.mem.pages * 65536) := by
      have := hscr; rw [h_g04] at this; omega
    simp only [if_neg hok]; rfl)
  isplitl []; · exact BI.pure_intro hagree₇
  isplitl [Hσ₇']; · iexact Hσ₇'
  -- ── STEP 16: store32 0 at ptr_b → write va ──────────────────────────────
  (try unfold wp_wasm); iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
  iintro %σ₈ %hagree₈ Hσ₈
  imod (wp_iProp_store32 hagree₈ (ptr := ptr_b) (xs := [vb]) (k := 0) (hk := by simp)
        va
        (hbounds := by rw [h40, UInt32.add_zero]; simp only [Mem.write32_pages]; exact hpb)
        (by simp only [Mem.write32_pages]; exact hpg_u32)) $$ [$Hσ₈ $HA_b'] with ⟨%σ₉, Hagree₉_raw, Hσ₉, HA_b''⟩
  -- Rewrite va → mem.read32((g0-16)+12) in Hagree₉_raw to match the Wasm stack value
  simp only [h40, UInt32.add_zero] at hread_a
  simp only [h40, UInt32.add_zero, ← h_scr_addr] at hread_scr
  simp only [h40, UInt32.add_zero] at Hagree₉_raw
  rw [← hread_scr.trans hread_a] at Hagree₉_raw
  imodintro; iexists σ₉, _, _
  isplitl []; · exact BI.pure_intro (by
    simp only [execOne.eq_def, show (0:UInt32).toNat = 0 from rfl, Mem.write32_pages,
               UInt32.add_zero]
    have hok : ¬(ptr_b.toNat + 0 + 4 > st.mem.pages * 65536) := by omega
    simp only [if_neg hok]; rfl)
  isplitl [Hagree₉_raw]; · iexact Hagree₉_raw
  isplitl [Hσ₉]; · iexact Hσ₉
  -- ── .ret: close WP with postcondition ───────────────────────────────────
  (try unfold wp_wasm)
  iapply least_fixpoint_unfold_mpr
  simp only [wp_wasm_F]
  ipureintro
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- mem_final.read32 ptr_a = vb
    -- mem_final = mem₂.write32(ptr_b+0)(mem₂.read32((g0-16)+12))
    -- Step: disjoint write to ptr_b+0 doesn't affect read at ptr_a
    rw [Mem.read32_write32_of_disjoint _ _ _ _ (by
          simp only [UInt32.add_zero, h_pb0]
          exact Or.comm.mp hdisj_ab)]
    -- Now: mem₂.read32 ptr_a = vb
    -- mem₂ = mem₁.write32(ptr_a+0) vb (step 12 wrote vb to ptr_a+0)
    -- Need ptr_a+0 = ptr_a to apply read32_write32_same
    rw [← h_pa0]
    exact Mem.read32_write32_same _ _ _
  · -- mem_final.read32 ptr_b = va
    -- write32(ptr_b+0)(val) where val = mem₂.read32((g0-16)+12) = va
    rw [← h_pb0]
    exact Mem.read32_write32_same _ _ _
  · -- globals unchanged
    rfl
  · -- pages unchanged (three stores, each preserves pages)
    simp only [Mem.write32_pages]

-- ======================================================================
-- §3  func7 spec — array element swap by index
-- ======================================================================

/-!
func7 (funcIdx 7)  params [ptr, len, i, j, err_ptr]  results []
Swaps arr[i] ↔ arr[j] in array at ptr. iProp spec: consumes arrayAt ownership.
-/
set_option maxHeartbeats 800000000 in
theorem func7_spec (st : Store Unit) (σ : WasmHeapMap (Option UInt8))
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
    (hagree  : heapAgreesWithMem σ st.mem) :
    ⊢ genHeapInterp σ ∗ arrayAt ptr xs -∗
      wp_wasm «module» st
        (func7Def.toLocals ([.i32 err_ptr, .i32 (UInt32.ofNat j), .i32 (UInt32.ofNat i),
         .i32 (UInt32.ofNat xs.length), .i32 ptr].take func7Def.numParams).reverse)
        func7Def.body {}
        (fun st' _ =>
          st'.globals = st.globals ∧
          st'.mem.pages = st.mem.pages ∧
          wordsAt st'.mem ptr xs.length = swapElems xs i j) := by
  iintro ⟨Hσ, HA⟩
  sorry

-- ======================================================================
-- §3b  func8 spec — slice descriptor write (store ptr and len into frame)
-- ======================================================================

/-!
func8 (funcIdx 8)  params [dst_ptr, ptr, len, data]  results []
Writes ptr_val at dst_ptr and len_val at dst_ptr+4. iProp spec: pointsTo_u32 ownership.
-/
set_option maxHeartbeats 800000000 in
private theorem func8_spec (st : Store Unit) (σ : WasmHeapMap (Option UInt8))
    (dst_ptr ptr_val len_val data old_v0 old_v4 : UInt32)
    (hb8     : dst_ptr.toNat + 8 ≤ st.mem.pages * 65536)
    (hb4     : dst_ptr.toNat + 4 ≤ st.mem.pages * 65536)
    (hpg_u32 : st.mem.pages * 65536 ≤ 4294967296)
    (hagree  : heapAgreesWithMem σ st.mem) :
    ⊢ genHeapInterp σ ∗ pointsTo_u32 dst_ptr old_v0 ∗ pointsTo_u32 (dst_ptr + 4) old_v4 -∗
      wp_wasm «module» st
        (func8Def.toLocals ([.i32 data, .i32 len_val, .i32 ptr_val, .i32 dst_ptr].take
         func8Def.numParams).reverse)
        func8Def.body {}
        (fun st' _ =>
          st'.mem.read32 dst_ptr = ptr_val ∧
          st'.mem.read32 (dst_ptr + 4) = len_val ∧
          st'.mem.pages = st.mem.pages ∧
          st'.globals = st.globals) := by
  iintro ⟨Hσ, HA0, HA4⟩
  -- Combine HA0 and HA4 into arrayAt dst_ptr [old_v0, old_v4]
  have to_arr : pointsTo_u32 dst_ptr old_v0 ∗ pointsTo_u32 (dst_ptr + 4) old_v4 ⊢
      arrayAt dst_ptr [old_v0, old_v4] := by
    simp only [arrayAt]; exact BI.sep_mono_right BI.sep_emp.mpr
  icases to_arr $$ [$HA0 $HA4] with HA_arr
  -- localGet 0: manual first step; body hint reduces the match, func8Def reduces toLocals
  unfold wp_wasm; iapply least_fixpoint_unfold_mpr
  simp only [wp_wasm_F,
    show func8Def.body = .localGet 0 ::
      [.localGet 2, .store32 (4:UInt32), .localGet 0, .localGet 1,
       .store32 (0:UInt32), .ret] from rfl]
  iintro %σ₀ %hagree₀ Hσ₀
  imodintro; iexists σ₀, _, _
  isplitl []; · exact BI.pure_intro (by
    -- Function.toLocals is @[semireducible] — rfl can't unfold it.
    -- Compute the concrete locals first, then use simp only (no injEq) to close.
    have hnp : func8Def.numParams = 4 := by decide
    have hloc : Function.toLocals func8Def
        ([.i32 data, .i32 len_val, .i32 ptr_val, .i32 dst_ptr].take 4).reverse =
        { params := [.i32 dst_ptr, .i32 ptr_val, .i32 len_val, .i32 data],
          locals := [], values := [] } := by
      simp [Function.toLocals, func8Def]
    simp only [execOne.eq_def, hnp, hloc, Locals.get,
               List.length_cons, List.length_nil,
               if_pos (show (0 : Nat) < 4 from by omega),
               List.getElem?_cons_zero]
    rfl)
  isplitl []; · exact BI.pure_intro hagree₀
  isplitl [Hσ₀]; · iexact Hσ₀
  -- localGet 2: pure step, prog is now a concrete list tail
  iwpures
  -- store32 4: write len_val at dst_ptr + 4 (consumes HA_arr, k=1)
  (try unfold wp_wasm); iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
  iintro %σ₂ %hagree₂ Hσ₂
  imod (wp_iProp_store32 hagree₂ (ptr := dst_ptr) (xs := [old_v0, old_v4]) (k := 1)
      (hk := by simp) len_val
      (hbounds := by
        have h1 : (4 : UInt32) * UInt32.ofNat 1 = 4 := by decide
        rw [h1, UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        omega)
      hpg_u32) $$ [$Hσ₂ $HA_arr] with ⟨%σ₃, Hagree₃, Hσ₃, HA_arr'⟩
  simp only [show (4:UInt32) * UInt32.ofNat 1 = 4 from by decide] at Hagree₃
  imodintro; iexists σ₃, _, _
  isplitl []; · exact BI.pure_intro (by
    simp only [execOne.eq_def, show (4:UInt32).toNat = 4 from rfl]
    have hok : ¬(dst_ptr.toNat + 4 + 4 > st.mem.pages * 65536) := by omega
    simp only [if_neg hok]; rfl)
  isplitl [Hagree₃]; · iexact Hagree₃
  isplitl [Hσ₃]; · iexact Hσ₃
  -- localGet 0 + localGet 1 (pure; inside iris mode)
  iwpures
  -- store32 0: write ptr_val at dst_ptr + 0 (consumes HA_arr', k=0)
  (try unfold wp_wasm); iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
  iintro %σ₆ %hagree₆ Hσ₆
  imod (wp_iProp_store32 hagree₆ (ptr := dst_ptr) (xs := [old_v0, len_val]) (k := 0)
      (hk := by simp) ptr_val
      (hbounds := by
        have h0 : (4 : UInt32) * UInt32.ofNat 0 = 0 := by decide
        rw [h0, UInt32.add_zero, Mem.write32_pages, UInt32.toNat_add,
            show (0 : UInt32).toNat = 0 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        omega)
      (by simp only [Mem.write32_pages]; exact hpg_u32)) $$ [$Hσ₆ $HA_arr'] with ⟨%σ₇, Hagree₇, Hσ₇, HA_final⟩
  simp only [show (4:UInt32) * UInt32.ofNat 0 = 0 from by decide, UInt32.add_zero] at Hagree₇
  imodintro; iexists σ₇, _, _
  isplitl []; · exact BI.pure_intro (by
    simp only [execOne.eq_def, show (0:UInt32).toNat = 0 from rfl, Mem.write32_pages,
               UInt32.add_zero]
    have hok : ¬(dst_ptr.toNat + 0 + 4 > st.mem.pages * 65536) := by omega
    simp only [if_neg hok]; rfl)
  isplitl [Hagree₇]; · iexact Hagree₇
  isplitl [Hσ₇]; · iexact Hσ₇
  -- .ret: close WP with pure postcondition
  (try unfold wp_wasm)
  iapply least_fixpoint_unfold_mpr
  simp only [wp_wasm_F]
  ipureintro
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- read32 dst_ptr = ptr_val  (last write was ptr_val at dst_ptr + 0 = dst_ptr)
    simp only [show (4:UInt32) * UInt32.ofNat 0 = 0 from by decide,
               UInt32.add_zero, Mem.read32_write32_same]
  · -- read32 (dst_ptr + 4) = len_val  (first write; second write at dst_ptr is disjoint)
    rw [Mem.read32_write32_of_disjoint _ _ _ ptr_val (Or.inl (by
      have h0 : (4 : UInt32) * UInt32.ofNat 0 = 0 := by decide
      have hadd0 : (dst_ptr + 4 * UInt32.ofNat 0).toNat = dst_ptr.toNat := by
        rw [h0, UInt32.add_zero]
      have hadd4 : (dst_ptr + 4).toNat = dst_ptr.toNat + 4 := by
        rw [UInt32.toNat_add, show (4:UInt32).toNat = 4 from rfl,
            Nat.mod_eq_of_lt (by omega)]
      omega))]
    exact Mem.read32_write32_same _ _ _
  · simp [Mem.write32_pages]
  · rfl

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
-- §4.5  Helpers for func11_spec inductive case
-- ======================================================================

private theorem sorted_of_sorted_split
    {ys_left ys_right : List UInt32} {pivot : UInt32}
    (hl : ys_left.Pairwise (· ≤ ·))
    (hr : ys_right.Pairwise (· ≤ ·))
    (h_lp : ∀ x ∈ ys_left, x ≤ pivot)
    (h_pr : ∀ x ∈ ys_right, pivot < x) :
    (ys_left ++ [pivot] ++ ys_right).Pairwise (· ≤ ·) := by
  apply List.pairwise_append.mpr
  refine ⟨?_, hr, ?_⟩
  · apply List.pairwise_append.mpr
    exact ⟨hl, List.pairwise_singleton _ _,
      fun a ha b hb => by
        simp only [List.mem_singleton] at hb; subst hb; exact h_lp a ha⟩
  · intro a ha b hb
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · have h1 := UInt32.le_iff_toNat_le.mp (h_lp a ha)
      have h2 : pivot.toNat < b.toNat := h_pr b hb
      apply UInt32.le_iff_toNat_le.mpr; omega
    · -- after rcases rfl, `pivot` is subst'd by `a`; variable in scope is `a`
      have h : a.toNat < b.toNat := h_pr b hb
      apply UInt32.le_iff_toNat_le.mpr; omega

private theorem func1_terminates
    (st : Store Unit) (frame pivot_idx ptr n_val data : UInt32) :
    TerminatesWith {} «module» 1 st
      [.i32 data, .i32 n_val, .i32 ptr, .i32 pivot_idx, .i32 frame]
      (fun st' _ =>
        st'.mem.read32 frame = ptr ∧
        st'.mem.read32 (frame + 4) = pivot_idx ∧
        st'.globals = st.globals ∧
        st'.mem.pages = st.mem.pages) := by
  sorry

set_option maxHeartbeats 4000000 in
private theorem func2_terminates
    (st : Store Unit) (frame pivot_idx ptr n_val data : UInt32)
    (h_le : pivot_idx + 1 ≤ n_val)
    (h_bnd : frame.toNat + 16 ≤ st.mem.pages * 65536) :
    TerminatesWith {} «module» 2 st
      [.i32 data, .i32 n_val, .i32 ptr, .i32 (pivot_idx + 1), .i32 (frame + 8)]
      (fun st' _ =>
        st'.mem.read32 (frame + 8) = ptr + 4 * (pivot_idx + 1) ∧
        st'.mem.read32 (frame + 12) = n_val - (pivot_idx + 1) ∧
        st'.globals = st.globals ∧
        st'.mem.pages = st.mem.pages) := by
  apply wp_wasm_prop_to_TerminatesWith (f := func2Def)
    (by rfl) (by rfl) (by rfl)
    (by simp [func2Def, Function.numParams])
    (by intro _ _ h; exact h)
  have h_ngt : ¬(pivot_idx + 1 > n_val) := by
    intro h
    have h1 : n_val.toNat < (pivot_idx + 1).toNat := UInt32.lt_iff_toNat_lt.mp h
    have h2 : (pivot_idx + 1).toNat ≤ n_val.toNat := UInt32.le_iff_toNat_le.mp h_le
    omega
  have h_f8_le : (frame + 8 : UInt32).toNat ≤ frame.toNat + 8 := by
    simp only [UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl,
               show UInt32.size = 4294967296 from rfl]
    omega
  have h_bnd12 : ¬((frame + 8 : UInt32).toNat + (4 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
    simp only [show (4 : UInt32).toNat = 4 from rfl]; omega
  have h_bnd8 : ¬((frame + 8 : UInt32).toNat + (0 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
    simp only [show (0 : UInt32).toNat = 0 from rfl]; omega
  have h_shl : (pivot_idx + 1 : UInt32) <<< (2 : UInt32) = 4 * (pivot_idx + 1) := by
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_mul, show (4 : UInt32).toNat = 4 from rfl]
    simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq,
          show (2 : UInt32).toNat = 2 from rfl]
    omega
  have h_disj : (frame + 12 : UInt32).toNat + 4 ≤ (frame + 8 : UInt32).toNat
             ∨ (frame + 8 : UInt32).toNat + 4 ≤ (frame + 12 : UInt32).toNat := by
    have hlt := UInt32.toNat_lt_size frame
    simp only [UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl,
               show (12 : UInt32).toNat = 12 from rfl,
               show UInt32.size = 4294967296 from rfl]
    omega
  let ls₀ : Locals :=
    { params := [.i32 (frame + 8), .i32 (pivot_idx + 1), .i32 ptr, .i32 n_val, .i32 data],
      locals := [.i32 0, .i32 0], values := [] }
  have hlocals : func2Def.toLocals
      ([.i32 data, .i32 n_val, .i32 ptr, .i32 (pivot_idx + 1), .i32 (frame + 8)].take
       func2Def.numParams).reverse = ls₀ := rfl
  have h_body_exec : exec 1 «module» st ls₀
      [.localGet 1, .localGet 3, .gtU, .const (1 : UInt32), .and, .br_if 0,
       .localGet 3, .localGet 1, .sub, .localSet 5,
       .localGet 2, .localGet 1, .const (2 : UInt32), .shl, .add, .localSet 6,
       .localGet 0, .localGet 5, .store32 (4 : UInt32),
       .localGet 0, .localGet 6, .store32 (0 : UInt32),
       .ret] {} =
      .Return { st with mem := (st.mem.write32 ((frame + 8) + (4 : UInt32)) (n_val - (pivot_idx + 1))).write32
                               ((frame + 8) + (0 : UInt32)) (ptr + 4 * (pivot_idx + 1)) } [] := by
    simp only [exec, execOne.eq_def,
               show ls₀.params = [.i32 (frame + 8), .i32 (pivot_idx + 1), .i32 ptr,
                                   .i32 n_val, .i32 data] from rfl,
               show ls₀.locals = [.i32 0, .i32 0] from rfl,
               show ls₀.values = ([] : List Value) from rfl,
               Locals.get, Locals.set?,
               List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
               List.set_cons_zero, List.set_cons_succ,
               List.length_cons, List.length_nil, List.length_set,
               if_pos (show (0 : Nat) < 5 from by omega),
               if_pos (show (1 : Nat) < 5 from by omega),
               if_pos (show (2 : Nat) < 5 from by omega),
               if_pos (show (3 : Nat) < 5 from by omega),
               if_neg (show ¬(5 : Nat) < 5 from by omega),
               if_pos (show (5 : Nat) < 5 + 2 from by omega),
               show (5 - 5 : Nat) = 0 from by omega,
               if_neg (show ¬(6 : Nat) < 5 from by omega),
               if_pos (show (6 : Nat) < 5 + 2 from by omega),
               show (6 - 5 : Nat) = 1 from by omega,
               if_neg h_ngt,
               show ((1 : UInt32) &&& (0 : UInt32) = 0) from by decide,
               show (2 : UInt32) % 32 = 2 from by decide,
               h_shl,
               if_neg h_bnd12, if_neg h_bnd8,
               Mem.write32_pages]
    rw [UInt32.add_comm (4 * (pivot_idx + 1)) ptr]
  have h_addr : (frame + 8 : UInt32) + 4 = frame + 12 := by
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl,
               show (4 : UInt32).toNat = 4 from rfl,
               show (12 : UInt32).toNat = 12 from rfl,
               show UInt32.size = 4294967296 from rfl]
    omega
  have h_add0 : (frame + 8 : UInt32) + 0 = frame + 8 := by
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl,
               show (0 : UInt32).toNat = 0 from rfl,
               show UInt32.size = 4294967296 from rfl]
    omega
  -- execOne 2 for the .block reduces exec 1 via h_body_exec, then normalises addresses
  have h_execOne_block : execOne 2 «module» st ls₀
      (.block 0 0
        [.localGet 1, .localGet 3, .gtU, .const (1 : UInt32), .and, .br_if 0,
         .localGet 3, .localGet 1, .sub, .localSet 5,
         .localGet 2, .localGet 1, .const (2 : UInt32), .shl, .add, .localSet 6,
         .localGet 0, .localGet 5, .store32 (4 : UInt32),
         .localGet 0, .localGet 6, .store32 (0 : UInt32),
         .ret]) {} =
      .Return { st with mem := (st.mem.write32 (frame + 12) (n_val - (pivot_idx + 1))).write32
                               (frame + 8) (ptr + 4 * (pivot_idx + 1)) } [] := by
    simp only [execOne.eq_def, h_body_exec, h_addr, h_add0]
  -- exec 2 on func2: func2 starts with the block, so h_execOne_block short-circuits via exec
  have h_exec2 : exec 2 «module» st ls₀ func2 {} =
      .Return { st with mem := (st.mem.write32 (frame + 12) (n_val - (pivot_idx + 1))).write32
                               (frame + 8) (ptr + 4 * (pivot_idx + 1)) } [] := by
    simp only [func2, exec, h_execOne_block]
  unfold wp_wasm_prop
  refine ⟨2, ?_⟩
  simp only [hlocals, show func2Def.body = func2 from rfl, h_exec2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Mem.read32_write32_same _ _ _
  · rw [Mem.read32_write32_of_disjoint _ _ _ _ (Or.comm.mp h_disj)]
    exact Mem.read32_write32_same _ _ _
  · trivial
  · simp only [Mem.write32_pages]

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
    by_cases hbase : n ≤ 1
    · -- Base case: n ≤ 1; block exits via br_if 0 (leU = 1 ∧ 1 → taken)
      apply wp_wasm_prop_to_TerminatesWith (f := func11Def)
        (by rfl) (by rfl) (by rfl) (by simp [func11Def, Function.numParams])
        (by intro _ _ h; exact h)
      have hlp11 : (func11Def.toLocals ([.i32 (UInt32.ofNat n), .i32 ptr].take
            func11Def.numParams).reverse).params =
          [.i32 ptr, .i32 (UInt32.ofNat n)] := rfl
      have hll11 : (func11Def.toLocals ([.i32 (UInt32.ofNat n), .i32 ptr].take
            func11Def.numParams).reverse).locals =
          [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0] := rfl
      have hlv11 : (func11Def.toLocals ([.i32 (UInt32.ofNat n), .i32 ptr].take
            func11Def.numParams).reverse).values =
          ([] : List Value) := rfl
      -- UInt32: 16 ≤ g0 and (g0 - 16).toNat = g0.toNat - 16
      have hge16 : (16 : UInt32) ≤ g0 := UInt32.le_iff_toNat_le.mpr
          (show (16 : UInt32).toNat ≤ g0.toNat from by
            simp only [show (16 : UInt32).toNat = 16 from rfl]; exact hg0_ok)
      have h_g016 : (g0 - 16 : UInt32).toNat = g0.toNat - 16 :=
        UInt32.toNat_sub_of_le g0 16 hge16
      -- epilogue: (16 : UInt32) + (g0 - 16) = g0
      have hframe_add : (16 : UInt32) + (g0 - 16 : UInt32) = g0 := by
        apply UInt32.toNat_inj.mp
        simp only [UInt32.toNat_add, h_g016,
                   show (16 : UInt32).toNat = 16 from by decide,
                   show (2 : Nat) ^ 32 = 4294967296 from by norm_num]
        have hlt : g0.toNat < 4294967296 := UInt32.toNat_lt_size g0
        omega
      -- global 0 after preamble globalSet 0 (g0 - 16)
      have hg0_pre : ({ st with globals :=
              { globals := st.globals.globals.set 0 (.i32 (g0 - 16)) } } : Store Unit).globals.globals[0]? =
          some (.i32 (g0 - 16)) := by
        cases h : st.globals.globals with
        | nil => simp [h] at hg0
        | cons _ _ => simp [h, List.set_cons_zero]
      -- globals restoration: (set 0 (g0-16); set 0 g0) = original
      have hglob_restore : (st.globals.globals.set 0 (.i32 (g0 - 16))).set 0 (.i32 g0) =
          st.globals.globals := by
        cases h : st.globals.globals with
        | nil => simp [h] at hg0
        | cons v rest =>
          have hv : v = .i32 g0 := by
            simp only [h, List.getElem?_cons_zero] at hg0; exact Option.some.inj hg0
          subst hv; simp [List.set_cons_zero]
      -- Globals eta: { globals := st.globals.globals } = st.globals
      have hglob_eta : { globals := st.globals.globals } = st.globals := by
        cases st.globals; rfl
      -- leU condition: UInt32.ofNat n ≤ 1 (from hbase : n ≤ 1)
      have hleU : UInt32.ofNat n ≤ (1 : UInt32) := by
        have h0 : n = 0 ∨ n = 1 := by omega
        rcases h0 with rfl | rfl <;> decide
      -- xs is sorted: n ≤ 1 → length ≤ 1 → trivially Pairwise
      have hxs_sorted : xs.Pairwise (· ≤ ·) := by
        rcases xs with _ | ⟨x, _ | ⟨y, rest⟩⟩
        · exact List.Pairwise.nil
        · exact List.pairwise_singleton _ _
        · simp only [List.length_cons, List.length_nil] at hlen; omega
      -- length normalizations for Locals.get / Locals.set?
      have h_plen : (0 + 1 + 1 : Nat) = 2 := rfl
      have h_llen : (0 + 1 + 1 + 1 + 1 + 1 + 1 : Nat) = 6 := rfl
      -- block inner body exec: base case path exits via br_if 0 (leU=1 ∧ 1 → taken).
      -- Stated as a function-application equality so simp CAN fire it as a rewrite rule
      -- (unlike a match-expression LHS, which simp cannot match).
      have h_body_c : exec 1 «module»
          ({ st with globals :=
               { globals := st.globals.globals.set 0 (.i32 (g0 - 16)) } } : Store Unit)
          ({ params := [.i32 ptr, .i32 (UInt32.ofNat n)],
             locals := [.i32 (g0 - 16), .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
             values := [] } : Locals)
          [.localGet 1, .const (1 : UInt32), .leU, .const (1 : UInt32), .and, .br_if 0,
           .localGet 0, .localGet 1, .call 10,
           .localSet 3,
           .localGet 2, .localGet 3, .localGet 0, .localGet 1, .const (1048664 : UInt32), .call 1,
           .localGet 2, .load32 (4 : UInt32), .localSet 4,
           .localGet 2, .load32 (0 : UInt32), .localGet 4, .call 11,
           .localGet 3, .const (1 : UInt32), .add, .localSet 5,
           .const (1048680 : UInt32), .localSet 6,
           .localGet 2, .const (8 : UInt32), .add,
           .localGet 5, .localGet 0, .localGet 1, .localGet 6, .call 2,
           .localGet 2, .load32 (12 : UInt32), .localSet 7,
           .localGet 2, .load32 (8 : UInt32), .localGet 7, .call 11] {} =
          .Break 0
          ({ st with globals :=
               { globals := st.globals.globals.set 0 (.i32 (g0 - 16)) } } : Store Unit)
          ({ params := [.i32 ptr, .i32 (UInt32.ofNat n)],
             locals := [.i32 (g0 - 16), .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
             values := [] } : Locals) := by
        simp only [exec, execOne.eq_def,
          show ({ params := [.i32 ptr, .i32 (UInt32.ofNat n)],
                  locals := [.i32 (g0 - 16), .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
                  values := [] } : Locals).params =
               [.i32 ptr, .i32 (UInt32.ofNat n)] from rfl,
          show ({ params := [.i32 ptr, .i32 (UInt32.ofNat n)],
                  locals := [.i32 (g0 - 16), .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
                  values := [] } : Locals).locals =
               [.i32 (g0 - 16), .i32 0, .i32 0, .i32 0, .i32 0, .i32 0] from rfl,
          show ({ params := [.i32 ptr, .i32 (UInt32.ofNat n)],
                  locals := [.i32 (g0 - 16), .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
                  values := [] } : Locals).values = [] from rfl,
          Locals.get,
          List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
          List.length_cons, List.length_nil,
          if_pos (show (0 : Nat) < 2 from by omega),
          if_pos (show (1 : Nat) < 2 from by omega),
          if_pos hleU,
          show (1 : UInt32) &&& (1 : UInt32) = 1 from by decide]
        -- match [Value.i32 1] with | Value.i32 0 :: vs => ... reduces by kernel (1 ≠ 0 : UInt32)
        rfl
      -- exec equality at fuel 2: preamble sets global→g0-16, block exits via br_if,
      -- epilogue restores global→g0.  h_body_c fires for the block body (function-app equality);
      -- hg0_pre fires for the epilogue's globalSet on the post-preamble state.
      have h_exec : exec 2 «module» st
          (func11Def.toLocals ([.i32 (UInt32.ofNat n), .i32 ptr].take func11Def.numParams).reverse)
          func11Def.body {} =
          .Return
            { st with globals :=
                { globals := (st.globals.globals.set 0 (.i32 (g0 - 16))).set 0 (.i32 g0) } }
            [] := by
        set_option maxHeartbeats 2000000 in
        simp only [show func11Def.body = func11 from rfl, hlp11, hll11, hlv11, func11,
          exec, execOne.eq_def,
          Locals.get, Locals.set?,
          List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
          List.set_cons_zero, List.set_cons_succ,
          List.length_cons, List.length_nil, List.length_set,
          h_plen, h_llen, List.nil_append, List.take_zero, List.drop_zero,
          if_pos (show (0 : Nat) < 2 from by omega),
          if_pos (show (1 : Nat) < 2 from by omega),
          if_neg (show ¬(2 : Nat) < 2 from by omega),
          if_pos (show (2 : Nat) < 2 + 6 from by omega),
          show (2 - 2 : Nat) = 0 from by omega,
          hg0, hg0_pre, h_body_c, hframe_add,
          ite_true, ite_false]
      -- use h_exec to close the wp_wasm_prop goal
      unfold wp_wasm_prop
      refine ⟨2, ?_⟩
      rw [h_exec]
      dsimp only
      exact ⟨xs, hmem, hxs_sorted, List.Perm.refl xs, by rw [hglob_restore, hglob_eta], rfl⟩
    · -- Inductive case: n ≥ 2
      apply wp_wasm_prop_to_TerminatesWith (f := func11Def)
        (by rfl) (by rfl) (by rfl) (by simp [func11Def, Function.numParams])
        (by intro _ _ h; exact h)
      -- Initial locals (same as base case)
      have hlp11 : (func11Def.toLocals ([.i32 (UInt32.ofNat n), .i32 ptr].take
            func11Def.numParams).reverse).params =
          [.i32 ptr, .i32 (UInt32.ofNat n)] := rfl
      have hll11 : (func11Def.toLocals ([.i32 (UInt32.ofNat n), .i32 ptr].take
            func11Def.numParams).reverse).locals =
          [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0] := rfl
      have hlv11 : (func11Def.toLocals ([.i32 (UInt32.ofNat n), .i32 ptr].take
            func11Def.numParams).reverse).values =
          ([] : List Value) := rfl
      have hge16 : (16 : UInt32) ≤ g0 := UInt32.le_iff_toNat_le.mpr
          (show (16 : UInt32).toNat ≤ g0.toNat from by
            simp only [show (16 : UInt32).toNat = 16 from rfl]; exact hg0_ok)
      have h_g016 : (g0 - 16 : UInt32).toNat = g0.toNat - 16 :=
        UInt32.toNat_sub_of_le g0 16 hge16
      have hframe_add : (16 : UInt32) + (g0 - 16 : UInt32) = g0 := by
        apply UInt32.toNat_inj.mp
        simp only [UInt32.toNat_add, h_g016,
                   show (16 : UInt32).toNat = 16 from by decide,
                   show (2 : Nat) ^ 32 = 4294967296 from by norm_num]
        have hlt : g0.toNat < 4294967296 := UInt32.toNat_lt_size g0
        omega
      have hg0_pre : ({ st with globals :=
              { globals := st.globals.globals.set 0 (.i32 (g0 - 16)) } } : Store Unit).globals.globals[0]? =
          some (.i32 (g0 - 16)) := by
        cases h : st.globals.globals with
        | nil => simp [h] at hg0
        | cons _ _ => simp [h, List.set_cons_zero]
      have hglob_restore : (st.globals.globals.set 0 (.i32 (g0 - 16))).set 0 (.i32 g0) =
          st.globals.globals := by
        cases h : st.globals.globals with
        | nil => simp [h] at hg0
        | cons v rest =>
          have hv : v = .i32 g0 := by
            simp only [h, List.getElem?_cons_zero] at hg0; exact Option.some.inj hg0
          subst hv; simp [List.set_cons_zero]
      have hglob_eta : { globals := st.globals.globals } = st.globals := by
        cases st.globals; rfl
      have h_plen : (0 + 1 + 1 : Nat) = 2 := rfl
      have h_llen : (0 + 1 + 1 + 1 + 1 + 1 + 1 : Nat) = 6 := rfl
      -- n ≥ 2 consequences
      have hbase' : 2 ≤ n := by omega
      have hn_lt_u32 : n < 4294967296 := by
        have hbound := UInt32.toNat_lt_size ptr; linarith [hptr]
      have hnotleU : ¬ UInt32.ofNat n ≤ (1 : UInt32) := by
        intro hle
        have h2 := UInt32.le_iff_toNat_le.mp hle
        have h3 : (UInt32.ofNat n).toNat = n := by
          show n % UInt32.size = n
          exact Nat.mod_eq_of_lt hn_lt_u32
        rw [h3, show (1 : UInt32).toNat = 1 from rfl] at h2
        omega
      -- Frame and pre-state (preamble sets global0 := g0 - 16)
      let frame : UInt32 := g0 - 16
      let st_pre : Store Unit :=
        { st with globals := { globals := st.globals.globals.set 0 (.i32 frame) } }
      -- g0 ≤ pages * 65536 (for bounds checks)
      have hg0_lt_pages : g0.toNat ≤ st.mem.pages * 65536 :=
        le_trans hg0_le (by linarith [hpg])
      -- Apply func10_spec to partition the array
      have hf10 : TerminatesWith {} «module» 10 st_pre
          [.i32 (UInt32.ofNat n), .i32 ptr]
          (fun st' vs =>
            ∃ pivot_idx : UInt32,
              vs = [.i32 pivot_idx] ∧ pivot_idx.toNat < n ∧
              ∃ arr : List UInt32,
                arr.length = n ∧ wordsAt st'.mem ptr n = arr ∧ arr.Perm xs ∧
                (∀ k < pivot_idx.toNat, arr[k]! ≤ arr[pivot_idx.toNat]!) ∧
                (∀ k, pivot_idx.toNat < k → k < n → arr[k]! > arr[pivot_idx.toNat]!) ∧
                st'.globals = st_pre.globals ∧ st'.mem.pages = st.mem.pages) := by
        have h := func10_spec st_pre ptr xs frame
          (by rw [hlen]; omega)
          (by rw [hlen]; exact hpg)
          (by linarith [hptr, hbase'])
          hg0_pre
          (by simp only [frame, h_g016]; sorry)  -- 52 ≤ g0.toNat - 16 (needs g0 ≥ 68)
          (by simp only [frame, h_g016]; omega)
          (by rw [hlen]; exact hmem)
        rwa [hlen] at h
      obtain ⟨N10, hN10⟩ := hf10
      obtain ⟨vs10, st10, hrun10, pivot_idx, hvs10_eq, hpivot_lt, arr,
          harr_len, harr_mem, harr_perm, harr_left, harr_right, hglob10, hpages10⟩ :=
        hN10 N10 le_rfl
      subst hvs10_eq
      -- Apply func1_terminates to write left-slice header [frame, frame+8)
      have hf1 : TerminatesWith {} «module» 1 st10
          [.i32 (1048664 : UInt32), .i32 (UInt32.ofNat n), .i32 ptr, .i32 pivot_idx, .i32 frame]
          (fun st' _ =>
            st'.mem.read32 frame = ptr ∧ st'.mem.read32 (frame + 4) = pivot_idx ∧
            st'.globals = st10.globals ∧ st'.mem.pages = st10.mem.pages) :=
        func1_terminates st10 frame pivot_idx ptr (UInt32.ofNat n) 1048664
      obtain ⟨N1, hN1⟩ := hf1
      obtain ⟨vs1, st1, hrun1, h_frame_ptr, h_frame_piv, hglob1, hpages1⟩ := hN1 N1 le_rfl
      have hvs1_nil : vs1 = [] := by sorry  -- func1 has 0 results
      rw [hvs1_nil] at hrun1
      -- Pages and global chain through func10 + func1
      have hpages_st1 : st1.mem.pages = st.mem.pages := by rw [hpages1, hpages10]
      have hg0_st1 : st1.globals.globals[0]? = some (.i32 frame) := by
        rw [hglob1, hglob10]; exact hg0_pre
      -- Left-half memory after func1 (framing: func1 writes [frame, frame+16), disjoint from array)
      have hmem_left : wordsAt st1.mem ptr pivot_idx.toNat = arr.take pivot_idx.toNat := by
        sorry
      -- Apply IH to sort the left half
      have hf11L : TerminatesWith {} «module» 11 st1
          [.i32 pivot_idx, .i32 ptr]
          (fun stL _ =>
            ∃ ys_left : List UInt32,
              wordsAt stL.mem ptr pivot_idx.toNat = ys_left ∧
              ys_left.Pairwise (· ≤ ·) ∧ ys_left.Perm (arr.take pivot_idx.toNat) ∧
              stL.globals = st1.globals ∧ stL.mem.pages = st1.mem.pages) := by
        have hIH := IH pivot_idx.toNat hpivot_lt
            st1 ptr (arr.take pivot_idx.toNat) frame
            (by rw [List.length_take, harr_len, Nat.min_eq_left (Nat.le_of_lt hpivot_lt)])
            (by rw [hpages_st1]; linarith [hpg, hpivot_lt])
            (by rw [hpages_st1]; exact hpg_min)
            (by linarith [hptr, hpivot_lt])
            hg0_st1
            (by simp only [frame, h_g016]; omega)
            (by simp only [frame, h_g016]; sorry)  -- 16 ≤ g0.toNat - 16 (needs g0 ≥ 32)
            hmem_left
        simp only [UInt32.ofNat_toNat] at hIH
        exact hIH
      obtain ⟨NL, hNL⟩ := hf11L
      obtain ⟨vsL, stL, hrunL, ys_left, hysL_mem, hysL_sorted, hysL_perm, hglobL, hpagesL⟩ :=
        hNL NL le_rfl
      have hvsL_nil : vsL = [] := by sorry  -- func11 has 0 results
      rw [hvsL_nil] at hrunL
      have hpages_stL : stL.mem.pages = st.mem.pages := by rw [hpagesL, hpages_st1]
      have hg0_stL : stL.globals.globals[0]? = some (.i32 frame) := by
        rw [hglobL]; exact hg0_st1
      -- Apply func2_terminates to write right-slice header [frame+8, frame+16)
      have hf2 : TerminatesWith {} «module» 2 stL
          [.i32 (1048680 : UInt32), .i32 (UInt32.ofNat n), .i32 ptr,
           .i32 (pivot_idx + 1), .i32 (frame + 8)]
          (fun st' _ =>
            st'.mem.read32 (frame + 8) = ptr + 4 * (pivot_idx + 1) ∧
            st'.mem.read32 (frame + 12) = UInt32.ofNat n - (pivot_idx + 1) ∧
            st'.globals = stL.globals ∧ st'.mem.pages = stL.mem.pages) :=
        func2_terminates stL frame pivot_idx ptr (UInt32.ofNat n) 1048680
          (by
            rw [UInt32.le_iff_toNat_le]
            simp only [UInt32.toNat_add, show (1:UInt32).toNat = 1 from rfl,
                       show UInt32.size = 4294967296 from rfl]
            have : (UInt32.ofNat n).toNat = n := Nat.mod_eq_of_lt hn_lt_u32
            omega)
          (by
            rw [hpages_stL]
            have hft2' : frame.toNat + 16 = g0.toNat := by
              simp only [frame, h_g016]; omega
            linarith [hg0_le, hpg])
      obtain ⟨N2, hN2⟩ := hf2
      obtain ⟨vs2, st2, hrun2, h_frame2_ptr, h_frame2_len, hglob2, hpages2⟩ := hN2 N2 le_rfl
      have hvs2_nil : vs2 = [] := by sorry  -- func2 has 0 results
      rw [hvs2_nil] at hrun2
      have hpages_st2 : st2.mem.pages = st.mem.pages := by rw [hpages2, hpages_stL]
      -- Right-half address/length
      let n_right : UInt32 := UInt32.ofNat n - (pivot_idx + 1)
      let ptr_right : UInt32 := ptr + 4 * (pivot_idx + 1)
      have hn_right_lt : n_right.toNat < n := by sorry  -- n - pivot_idx.toNat - 1 < n
      have hg0_st2 : st2.globals.globals[0]? = some (.i32 frame) := by
        rw [hglob2, hglobL]; exact hg0_st1
      -- Right-half memory after func2 (framing)
      have hmem_right : wordsAt st2.mem ptr_right n_right.toNat =
          arr.drop (pivot_idx.toNat + 1) := by
        sorry
      -- Apply IH to sort the right half
      have hf11R : TerminatesWith {} «module» 11 st2
          [.i32 n_right, .i32 ptr_right]
          (fun stR _ =>
            ∃ ys_right : List UInt32,
              wordsAt stR.mem ptr_right n_right.toNat = ys_right ∧
              ys_right.Pairwise (· ≤ ·) ∧ ys_right.Perm (arr.drop (pivot_idx.toNat + 1)) ∧
              stR.globals = st2.globals ∧ stR.mem.pages = st2.mem.pages) := by
        have hIH := IH n_right.toNat hn_right_lt
            st2 ptr_right (arr.drop (pivot_idx.toNat + 1)) frame
            (by sorry)  -- arr.drop.length = n_right.toNat
            (by sorry)  -- ptr_right.toNat + 4 * n_right.toNat ≤ pages * 65536
            (by rw [hpages_st2]; exact hpg_min)
            (by sorry)  -- 64 * (n_right.toNat + 1) ≤ ptr_right.toNat
            hg0_st2
            (by sorry)  -- frame.toNat ≤ ptr_right.toNat
            (by simp only [frame, h_g016]; sorry)  -- 16 ≤ g0.toNat - 16
            hmem_right
        simp only [UInt32.ofNat_toNat] at hIH
        exact hIH
      obtain ⟨NR, hNR⟩ := hf11R
      obtain ⟨vsR, stR, hrunR, ys_right, hysR_mem, hysR_sorted, hysR_perm, hglobR, hpagesR⟩ :=
        hNR NR le_rfl
      have hvsR_nil : vsR = [] := by sorry  -- func11 has 0 results
      rw [hvsR_nil] at hrunR
      have hpages_stR : stR.mem.pages = st.mem.pages := by rw [hpagesR, hpages_st2]
      -- Lift all runs to common fuel Nmax (block body executes at fuel Nmax-1,
      -- so define Nmax with +1 on each Ni to ensure Nmax-1 ≥ each Ni)
      let Nmax := max (N10 + 1) (max (N1 + 1) (max (NL + 1) (max (N2 + 1) (NR + 1))))
      have hNmax_pos : 0 < Nmax := by
        have : N10 + 1 ≤ Nmax := Nat.le_max_left _ _; omega
      have hN10_le : N10 ≤ Nmax - 1 := by
        have h : N10 + 1 ≤ Nmax := Nat.le_max_left _ _; omega
      have hN1_le : N1 ≤ Nmax - 1 := by
        have h : N1 + 1 ≤ Nmax :=
          (Nat.le_max_left _ _).trans (Nat.le_max_right _ _); omega
      have hNL_le : NL ≤ Nmax - 1 := by
        have h : NL + 1 ≤ Nmax :=
          ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans
            (Nat.le_max_right _ _); omega
      have hN2_le : N2 ≤ Nmax - 1 := by
        have h : N2 + 1 ≤ Nmax :=
          (((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans
            (Nat.le_max_right _ _)).trans (Nat.le_max_right _ _); omega
      have hNR_le : NR ≤ Nmax - 1 := by
        have h : NR + 1 ≤ Nmax :=
          ((((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans
            (Nat.le_max_right _ _)).trans (Nat.le_max_right _ _)); omega
      -- Run results at fuel Nmax-1 (the fuel available to calls inside the block body)
      have h_run10_Nm1 : run (Nmax - 1) «module» 10 st_pre
          [.i32 (UInt32.ofNat n), .i32 ptr] {} = .Success [.i32 pivot_idx] st10 :=
        (run_fuel_mono hN10_le (by rw [hrun10]; simp)).trans hrun10
      have h_run1_Nm1 : run (Nmax - 1) «module» 1 st10
          [.i32 (1048664 : UInt32), .i32 (UInt32.ofNat n), .i32 ptr,
           .i32 pivot_idx, .i32 frame] {} = .Success [] st1 :=
        (run_fuel_mono hN1_le (by rw [hrun1]; simp)).trans hrun1
      have h_runL_Nm1 : run (Nmax - 1) «module» 11 st1
          [.i32 pivot_idx, .i32 ptr] {} = .Success [] stL :=
        (run_fuel_mono hNL_le (by rw [hrunL]; simp)).trans hrunL
      have h_run2_Nm1 : run (Nmax - 1) «module» 2 stL
          [.i32 (1048680 : UInt32), .i32 (UInt32.ofNat n), .i32 ptr,
           .i32 (pivot_idx + 1), .i32 (frame + 8)] {} = .Success [] st2 :=
        (run_fuel_mono hN2_le (by rw [hrun2]; simp)).trans hrun2
      have h_runR_Nm1 : run (Nmax - 1) «module» 11 st2
          [.i32 n_right, .i32 ptr_right] {} = .Success [] stR :=
        (run_fuel_mono hNR_le (by rw [hrunR]; simp)).trans hrunR
      -- Globals chain: stR.globals = { globals := st.globals.globals.set 0 (.i32 frame) }
      have hstR_g : stR.globals = { globals := st.globals.globals.set 0 (.i32 frame) } := by
        rw [hglobR, hglob2, hglobL, hglob1, hglob10]
      have hstR_gg : stR.globals.globals = st.globals.globals.set 0 (.i32 frame) :=
        congr_arg Globals.globals hstR_g
      -- g0 in stR = frame (needed for epilogue's globalSet 0 g0)
      have hg0_stR : stR.globals.globals[0]? = some (.i32 frame) := by
        rw [hstR_gg]
        cases h : st.globals.globals with
        | nil => simp [h] at hg0
        | cons _ _ => simp [h, List.set_cons_zero]
      -- Out-of-bounds checks for load32 at frame+{0,4,8,12}
      have hft : frame.toNat = g0.toNat - 16 := h_g016
      -- Convert hge16 (UInt32) to Nat form so linarith can use it
      have hg0_nat_ok : 16 ≤ g0.toNat := by
        have h := UInt32.le_iff_toNat_le.mp hge16
        simpa only [show (16 : UInt32).toNat = 16 from rfl] using h
      -- Sum form of hft (avoids Nat subtraction in linarith)
      have hft2 : frame.toNat + 16 = g0.toNat := by
        clear_value frame; rw [hft]; exact Nat.sub_add_cancel hg0_nat_ok
      -- Out-of-bounds checks for load32 at frame+{0,4,8,12}
      -- All four follow from frame + 16 = g0 ≤ ptr ≤ pages*65536 - 4*n and n ≥ 2
      have hload4_ok : ¬ (st1.mem.pages * 65536 < frame.toNat + 4 + 4) := by
        intro h; rw [hpages_st1] at h; linarith [hft2, hg0_le, hpg, hbase']
      have hload0_ok : ¬ (st1.mem.pages * 65536 < frame.toNat + 0 + 4) := by
        intro h; rw [hpages_st1] at h; linarith [hft2, hg0_le, hpg, hbase']
      have hload12_ok : ¬ (st2.mem.pages * 65536 < frame.toNat + 12 + 4) := by
        intro h; rw [hpages_st2] at h; linarith [hft2, hg0_le, hpg, hbase']
      have hload8_ok : ¬ (st2.mem.pages * 65536 < frame.toNat + 8 + 4) := by
        intro h; rw [hpages_st2] at h; linarith [hft2, hg0_le, hpg, hbase']
      -- Arithmetic helper: frame + 0 = frame
      have hframe0 : frame + (0 : UInt32) = frame := by simp
      -- Postcondition: ys = ys_left ++ [pivot] ++ ys_right
      let ys := ys_left ++ [arr[pivot_idx.toNat]!] ++ ys_right
      -- Final globals after epilogue (globalSet 0 g0 restores original)
      have hstR_final_globals :
          ({ stR with globals :=
               { globals := stR.globals.globals.set 0 (.i32 g0) } } : Store Unit).globals =
          st.globals := by
        show { globals := stR.globals.globals.set 0 (.i32 g0) } = st.globals
        rw [hstR_gg, show frame = g0 - 16 from rfl, hglob_restore]
      have hys_sorted : ys.Pairwise (· ≤ ·) := by
        sorry  -- sorted_of_sorted_split + perm from hysL_perm/hysR_perm + harr_left/harr_right
      have hys_perm : ys.Perm xs := by
        sorry  -- harr_perm + hysL_perm + hysR_perm + list-split perm
      have hmem_ys : wordsAt stR.mem ptr n = ys := by
        sorry  -- combined memory: ys_left ++ [pivot] ++ ys_right occupies [ptr, ptr+4*n)
      -- Big exec: func11 body at fuel Nmax terminates
      -- (sorry: br_if NOT-taken match + 5 calls at fuel Nmax-1 via h_run*_Nm1)
      have h_exec : exec Nmax «module» st
          (func11Def.toLocals ([.i32 (UInt32.ofNat n), .i32 ptr].take func11Def.numParams).reverse)
          func11Def.body {} =
          .Return
            { stR with globals := { globals := stR.globals.globals.set 0 (.i32 g0) } }
            [] := by
        sorry
      -- Close wp_wasm_prop
      unfold wp_wasm_prop
      refine ⟨Nmax, ?_⟩
      rw [h_exec]
      exact ⟨ys,
             show wordsAt ({ stR with globals := _ } : Store Unit).mem ptr n = ys from hmem_ys,
             hys_sorted, hys_perm, hstR_final_globals, hpages_stR⟩
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
    (hlen      : xs.length = len.toNat)
    (hpg       : ptr.toNat + 4 * xs.length ≤ st.mem.pages * 65536)
    (hpg_min   : (1048576 : Nat) ≤ st.mem.pages * 65536)
    (hptr      : 64 * (xs.length + 1) ≤ ptr.toNat)
    (hptr_high : (1048576 : Nat) ≤ ptr.toNat)
    (hg0       : st.globals.globals[0]? = some (.i32 (1048576 : UInt32))) :
    TerminatesWith {} «module» 12 st [.i32 len, .i32 ptr]
      (fun st' _ =>
        ∃ ys : List UInt32,
          wordsAt st'.mem ptr ys.length = ys ∧
          ys.Pairwise (· ≤ ·) ∧
          ys.Perm xs) := by
  sorry

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
          | nil => simp only [exec]
          | cons _ _ => simp only [exec, execOne.eq_def]
        · intro m hm id st args env
          have hImp : m.imports[id]? = none := by simp [hm]
          have irrelExecZero : ∀ (st : Store Unit) (s : Locals) (p : Program),
              exec 0 m st s p env = exec 0 m st s p {} := by
            intro st s p; cases p with
            | nil => simp only [exec]
            | cons _ _ => simp only [exec, execOne.eq_def]
          conv_lhs => rw [run_eq hImp]
          conv_rhs => rw [run_eq hImp]
          rcases m.funcs[id - m.imports.length]? with _ | f
          · rfl
          · simp only [irrelExecZero, runTail]
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
          | nil => simp only [exec]
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
  intro env st ptr len xs hlen hpg hpg_min hptr hptr_high hg0
  apply terminatesWith_env_irrel (by native_decide) env
  exact func12_spec st ptr len xs hlen hpg hpg_min hptr (by sorry) hptr_high

end Project.Quicksort.QuicksortSepLogic
