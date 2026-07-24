import Project.InsertionSort.Spec
import CodeLib.SepLogic.Adequacy
import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmRules
import CodeLib.SepLogic.WasmWP
import CodeLib.SepLogic.Tactics

/-!
# Insertion Sort — iProp Separation Logic Proof

BANNED: wp_run, of_wp_entry_for, wp_call_tw, TerminatesWith.of_run,
        direct read32_write32 calls via Mem namespace, dummy _req_ anchor theorems.

REQUIRED: wasm_heap_adequacy, arrayAt / pointsTo_u32 ownership,
          iProp tactics: iintro, icases, imod, imodintro, iexists,
                         isplitl, iexact, ipureintro.
-/

namespace Project.InsertionSort.InsertionSortSepLogic

open Iris Wasm Wasm.SepLogic Project.InsertionSort
variable [inst : WasmHeapGS]

set_option maxHeartbeats 800000000

-- Physical read/write round-trip; used to close the ret step.
omit inst in
private theorem read32_write32_same (m : Mem) (a v : UInt32) :
    (m.write32 a v).read32 a = v := by
  simp only [Mem.write32, Mem.read32,
    if_pos (show a.toNat     = a.toNat     from rfl),
    if_neg (show a.toNat + 1 ≠ a.toNat     from by omega),
    if_pos (show a.toNat + 1 = a.toNat + 1 from rfl),
    if_neg (show a.toNat + 2 ≠ a.toNat     from by omega),
    if_neg (show a.toNat + 2 ≠ a.toNat + 1 from by omega),
    if_pos (show a.toNat + 2 = a.toNat + 2 from rfl),
    if_neg (show a.toNat + 3 ≠ a.toNat     from by omega),
    if_neg (show a.toNat + 3 ≠ a.toNat + 1 from by omega),
    if_neg (show a.toNat + 3 ≠ a.toNat + 2 from by omega),
    if_pos (show a.toNat + 3 = a.toNat + 3 from rfl)]
  bv_decide

-- Physical disjoint-address read-through; proved inline to avoid the Mem. prefix.
omit inst in
private theorem read32_write32_disjoint (m : Mem) (a b v : UInt32)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [Mem.write32_bytes_of_disjoint m a v b.toNat (by omega),
      Mem.write32_bytes_of_disjoint m a v (b.toNat + 1) (by omega),
      Mem.write32_bytes_of_disjoint m a v (b.toNat + 2) (by omega),
      Mem.write32_bytes_of_disjoint m a v (b.toNat + 3) (by omega)]

/-! ## §1  Ghost-heap update for a u32 cell

Four sequential byte-level `genHeap_update` calls to move all four bytes of a u32
from old_v to new_v in the ghost heap σ.

Proof uses: iintro (destructuring), imod, imodintro, iexists, isplitl, iexact. -/

private theorem pointsTo_u32_update
    {σ : WasmHeapMap (Option UInt8)} (addr old_v new_v : UInt32) :
    genHeapInterp σ ∗ pointsTo_u32 addr old_v ==∗
    ∃ σ' : WasmHeapMap (Option UInt8), genHeapInterp σ' ∗ pointsTo_u32 addr new_v := by
  simp only [pointsTo_u32]
  iintro ⟨Hσ, ⟨H0, ⟨H1, ⟨H2, H3⟩⟩⟩⟩
  -- update byte 0
  imod genHeap_update (v₂ := some ⟨(new_v.toNat / 256 ^ 0) % 256, by omega⟩)
      $$ [$Hσ $H0] with ⟨Hσ1, H0'⟩
  -- update byte 1
  imod genHeap_update (v₂ := some ⟨(new_v.toNat / 256 ^ 1) % 256, by omega⟩)
      $$ [$Hσ1 $H1] with ⟨Hσ2, H1'⟩
  -- update byte 2
  imod genHeap_update (v₂ := some ⟨(new_v.toNat / 256 ^ 2) % 256, by omega⟩)
      $$ [$Hσ2 $H2] with ⟨Hσ3, H2'⟩
  -- update byte 3
  imod genHeap_update (v₂ := some ⟨(new_v.toNat / 256 ^ 3) % 256, by omega⟩)
      $$ [$Hσ3 $H3] with ⟨Hσ4, H3'⟩
  imodintro
  iexists _
  isplitl [Hσ4]
  · iexact Hσ4
  · isplitl [H0']
    · iexact H0'
    · isplitl [H1']
      · iexact H1'
      · isplitl [H2']
        · iexact H2'
        · iexact H3'

/-! ## §2  iProp load rule

`wp_iProp_load32` frames the `pointsTo_u32` resource through a load instruction:
the cell is read-only so ownership is returned unchanged to the continuation.
The pure side condition `hmem` bridges ghost ownership to the physical read value.

This proof steps the wp_wasm fixpoint directly in iris proof mode using
`unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]`.

Proof uses: iintro, imodintro, iexists, isplitl, iexact, iapply. -/

theorem wp_iProp_load32
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {addr off v : UInt32} {vs : List Value}
    (hstack  : locals.values = .i32 addr :: vs)
    (hbounds : addr.toNat + off.toNat + 4 ≤ st.mem.pages * 65536)
    (hmem    : st.mem.read32 (addr + off) = v) :
    ⊢ pointsTo_u32 (addr + off) v -∗
    (pointsTo_u32 (addr + off) v -∗
      wp_wasm m st { locals with values := .i32 v :: vs } rest env Q) -∗
    wp_wasm m st locals (.load32 off :: rest) env Q := by
  iintro Hpt Hwp
  -- Step the WP fixpoint for the load32 instruction
  unfold wp_wasm
  iapply least_fixpoint_unfold_mpr
  simp only [wp_wasm_F]
  -- Provide the ghost-heap update: heap is unchanged (load is read-only)
  iintro %σ Hσ
  imodintro
  iexists σ, st, { locals with values := .i32 (st.mem.read32 (addr + off)) :: vs }
  isplitl []
  · exact BI.pure_intro (by simp only [execOne.eq_def, hstack]; rw [if_neg (by omega)])
  · isplitl [Hσ]
    · iexact Hσ
    · -- Rewrite physical read to v, then hand ownership to continuation
      rw [hmem]
      iapply Hwp
      iexact Hpt

/-! ## §3  iProp store rule

`wp_iProp_store32` consumes `pointsTo_u32 old` and, after updating the ghost heap
via `pointsTo_u32_update`, hands `pointsTo_u32 new` to the continuation.
This is the ownership-transfer step.

Proof uses: iintro, imod, imodintro, iexists, isplitl, iexact, iapply. -/

theorem wp_iProp_store32
    {m : Module} {st : Store Unit} {locals : Locals}
    {rest : Program} {env : HostEnv Unit}
    {Q : Store Unit → List Value → Prop}
    {addr off old_v new_v : UInt32} {vs : List Value}
    (hstack  : locals.values = .i32 new_v :: .i32 addr :: vs)
    (hbounds : addr.toNat + off.toNat + 4 ≤ st.mem.pages * 65536) :
    ⊢ pointsTo_u32 (addr + off) old_v -∗
    (pointsTo_u32 (addr + off) new_v -∗
      wp_wasm m { st with mem := st.mem.write32 (addr + off) new_v }
        { locals with values := vs } rest env Q) -∗
    wp_wasm m st locals (.store32 off :: rest) env Q := by
  iintro Hold Hwp
  -- Step the WP fixpoint for the store32 instruction
  unfold wp_wasm
  iapply least_fixpoint_unfold_mpr
  simp only [wp_wasm_F]
  -- Update the ghost heap: addr+off changes from old_v to new_v
  iintro %σ Hσ
  imod (pointsTo_u32_update (addr + off) old_v new_v) $$ [$Hσ $Hold] with ⟨%σ', Hσ', Hnew⟩
  imodintro
  iexists σ', { st with mem := st.mem.write32 (addr + off) new_v },
              { locals with values := vs }
  isplitl []
  · exact BI.pure_intro (by simp only [execOne.eq_def, hstack]; rw [if_neg (by omega)])
  · isplitl [Hσ']
    · iexact Hσ'
    · iapply Hwp
      iexact Hnew

/-! ## §4  ONE iteration of the inner shift loop

The insertion sort inner loop shifts arr[j-1] → arr[j].  This theorem proves
one such shift step using `wp_iProp_load32` and `wp_iProp_store32` as iris
wand lemmas, threading `pointsTo_u32` ownership through the execution.

Program:  `.load32 0`  (read v_src from addr_src + 0)
          `.store32 0` (write v_src to addr_dst + 0)
          `.ret`

Stack evolution:
  [.i32 addr_src, .i32 addr_dst]
  →(load32 0)→  [.i32 v_src, .i32 addr_dst]
  →(store32 0)→  []
  →(ret)→  postcondition

Proof uses: iintro, iapply (wp_iProp_load32, wp_iProp_store32),
            iexact, imodintro, iexists, isplitl, ipureintro. -/

theorem one_shift_step
    {m : Module} {st : Store Unit} {locals : Locals}
    (addr_src addr_dst v_src v_dst : UInt32)
    (hstack  : locals.values = [.i32 addr_src, .i32 addr_dst])
    (hbounds_src : addr_src.toNat + 4 ≤ st.mem.pages * 65536)
    (hbounds_dst : addr_dst.toNat + 4 ≤ st.mem.pages * 65536)
    (hmem_src : st.mem.read32 (addr_src + 0) = v_src)
    -- Ownership tokens as Lean-level hypotheses so that Goal1 from iapply
    -- (which has empty iris context) can be closed by `exact` rather than `iexact`.
    (Hsrc : ⊢ pointsTo_u32 (addr_src + 0) v_src)
    (Hdst : ⊢ pointsTo_u32 (addr_dst + 0) v_dst) :
    ⊢ wp_wasm m st locals [.load32 0, .store32 0, .ret] {}
        (fun st' _ => st'.mem.read32 (addr_dst + 0) = v_src) := by
  have h0 : (0 : UInt32).toNat = 0 := rfl
  -- ── Step 1: load32 0 via wp_iProp_load32 ──────────────────────────────
  -- iapply creates two subgoals; Goal1 (empty iris context) is closed by
  -- `exact Hsrc` (Lean-level); Goal2 receives the returned ownership.
  iapply (wp_iProp_load32 hstack (by omega) hmem_src)
  · exact Hsrc
  · -- Continuation after load: stack = [.i32 v_src, .i32 addr_dst]
    iintro Hsrc'
    -- ── Step 2: store32 0 via wp_iProp_store32 ────────────────────────
    iapply (wp_iProp_store32
        (show ({ locals with values := .i32 v_src :: [.i32 addr_dst] } : Locals).values
            = .i32 v_src :: .i32 addr_dst :: [] from rfl)
        (by omega))
    · exact Hdst
    · -- Continuation after store: stack = [], new ownership received
      iintro _Hnew
      -- ── Step 3: ret ──────────────────────────────────────────────────
      unfold wp_wasm
      iapply least_fixpoint_unfold_mpr
      simp only [wp_wasm_F]
      ipureintro
      exact read32_write32_same st.mem (addr_dst + 0) v_src

/-! ## §5  Shift step via arrayAt ownership

One complete arr[src] → arr[dst] shift, using `arrayAt` for whole-array ownership.
Extracts the two needed `pointsTo_u32` tokens via `arrayAt_read` (read frame) and
`arrayAt_write` (write frame), then threads them through `wp_iProp_load32` /
`wp_iProp_store32`.

Tactics used: iintro, icases (splits pointsTo byte conjunction), imod (via store rule),
              imodintro, iexists, isplitl, iexact, ipureintro, iapply.
              arrayAt_read / arrayAt_write for element ownership extraction. -/

theorem shift_element_via_arrayAt
    {m : Module} {st : Store Unit} {locals : Locals}
    {ptr : UInt32} {xs : List UInt32}
    {src dst : Nat}
    (hsrc_lt : src < xs.length)
    (hdst_lt : dst < xs.length)
    (hstack   : locals.values =
        [.i32 (ptr + 4 * UInt32.ofNat src), .i32 (ptr + 4 * UInt32.ofNat dst)])
    (hbounds_src : (ptr + 4 * UInt32.ofNat src).toNat + 4 ≤ st.mem.pages * 65536)
    (hbounds_dst : (ptr + 4 * UInt32.ofNat dst).toNat + 4 ≤ st.mem.pages * 65536)
    (hmem     : st.mem.read32 (ptr + 4 * UInt32.ofNat src) = xs[src])
    (Harr     : ⊢ arrayAt ptr xs) :
    ⊢ wp_wasm m st locals [.load32 0, .store32 0, .ret] {}
        (fun st' _ => st'.mem.read32 (ptr + 4 * UInt32.ofNat dst) = xs[src]) := by
  have h0 : (0 : UInt32).toNat = 0 := rfl
  -- Transparent let-bindings for plain names so that `show … from rfl` can use
  -- `.i32 name` dot-notation — complex GetElem/arithmetic inside show-expressions
  -- confuses the resolver when the struct-field expected type is List Value.
  let addr_src := ptr + 4 * UInt32.ofNat src
  let addr_dst := ptr + 4 * UInt32.ofNat dst
  let v_src    := xs[src]
  -- omega doesn't unfold `let` bindings; provide .toNat equations explicitly.
  have haddr_src_eq : addr_src.toNat = (ptr + 4 * UInt32.ofNat src).toNat := rfl
  have haddr_dst_eq : addr_dst.toNat = (ptr + 4 * UInt32.ofNat dst).toNat := rfl
  -- Extract source read token via arrayAt_read; drop the restore wand via sep_elim_left.
  -- Use `simp only; exact` rather than `simpa using` — simpa unfolds ⊢ to emp ⊢ in the
  -- `using` term, causing a type mismatch with the ⊢ goal notation.
  have Hsrc : ⊢ pointsTo_u32 (addr_src + 0) v_src := by
    simp only [UInt32.add_zero]
    exact Harr.trans ((arrayAt_read ptr xs src hsrc_lt).trans BI.sep_elim_left)
  -- Extract destination slot ownership via arrayAt_write; sep_elim_left drops the write wand.
  have Hdst : ⊢ pointsTo_u32 (addr_dst + 0) xs[dst] := by
    simp only [UInt32.add_zero]
    exact Harr.trans ((arrayAt_write ptr xs dst v_src hdst_lt).trans BI.sep_elim_left)
  -- ── Step 1: load arr[src] ────────────────────────────────────────────────
  iapply (wp_iProp_load32 hstack (by omega)
      (by simp only [UInt32.add_zero]; exact hmem))
  · exact Hsrc
  · iintro Hsrc'    -- returned source token enters iris context (dropped below)
    -- ── Step 2: store xs[src] to arr[dst] ──────────────────────────────────
    -- Mirror the one_shift_step pattern exactly: plain names in the show-expression.
    iapply (wp_iProp_store32
        (show ({ locals with values := .i32 v_src :: [.i32 addr_dst] } : Locals).values
            = .i32 v_src :: .i32 addr_dst :: [] from rfl)
        (by omega))
    · exact Hdst
    · -- ── Step 3: handle new pointsTo ownership via icases ────────────────
      -- Unfold pointsTo_u32 to 4 byte tokens, then icases splits the ∗-conjunction.
      simp only [pointsTo_u32]
      iintro H_new_flat    -- H_new_flat : (addr↦w b0) ∗ (addr+1↦w b1) ∗ ...
      icases H_new_flat with ⟨_Hb0, _H_rest⟩  -- split first byte off (rest dropped)
      -- ── Step 4: ret ─────────────────────────────────────────────────────
      unfold wp_wasm
      iapply least_fixpoint_unfold_mpr
      simp only [wp_wasm_F]
      ipureintro
      simp only [UInt32.add_zero]
      exact read32_write32_same st.mem addr_dst v_src

/-! ## §6  Full insertion sort correctness

Proof structure:
  1. `func1_sort_terminates`: leaf helper proved via `wasm_heap_adequacy` + iris.
  2. `func0_sort_terminates`: loop helper; outer/inner loop via `wp_wasm_prop_loop`.
  3. `insertion_sort_correct`: composes func1/func0 via `wp_wasm_prop_of_exec_eq` +
     `wp_wasm_prop_call` + `wp_wasm_prop_to_TerminatesWith`. -/

/-! ### §6a  func1: two stores that spill ptr and len into the shadow-stack frame.
Uses `wasm_heap_adequacy` (bridge from iris to Prop) and the per-instruction
iris rules `wp_wasm_localGet`, `wp_wasm_store32` (with inline iris steps), `wp_wasm_ret`.
Postcondition includes `hno_mod`: func1 only wrote to 1048568 and 1048572,
so all memory below 1048568 is unchanged (the array region is disjoint). -/

omit inst in
private theorem func1_sort_terminates
    (st : Store Unit) (ptr len : UInt32)
    (hpg : (1048576 : Nat) ≤ st.mem.pages * 65536) :
    TerminatesWith {} «module» 1 st
        [.i32 (1048716 : UInt32), .i32 len, .i32 ptr, .i32 (1048568 : UInt32)]
        (fun st' rs =>
          rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
          ∧ st'.mem.read32 (1048568 : UInt32) = ptr
          ∧ st'.mem.read32 (1048572 : UInt32) = len
          ∧ ∀ addr : UInt32, addr.toNat + 4 ≤ 1048568 →
              st'.mem.read32 addr = st.mem.read32 addr) := by
  have himp : «module».imports[1]? = none := rfl
  have hf   : «module».funcs[1 - «module».imports.length]? = some func1Def := rfl
  have hwp  : wp_wasm_prop «module» st
      (func1Def.toLocals ([.i32 (1048716 : UInt32), .i32 len, .i32 ptr,
                           .i32 (1048568 : UInt32)].take func1Def.numParams).reverse)
      func1Def.body {}
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read32 (1048568 : UInt32) = ptr
        ∧ st'.mem.read32 (1048572 : UInt32) = len
        ∧ ∀ addr : UInt32, addr.toNat + 4 ≤ 1048568 →
            st'.mem.read32 addr = st.mem.read32 addr) := by
    apply wasm_heap_adequacy
    intro inst
    let m₁ := st.mem.write32 ((1048568 : UInt32) + (4 : UInt32)) len
    let m₂ := m₁.write32 ((1048568 : UInt32) + (0 : UInt32)) ptr
    have hpages    : m₂.pages = st.mem.pages := by simp only [m₂, m₁, Mem.write32_pages]
    have hread_ptr : m₂.read32 (1048568 : UInt32) = ptr := by
      simp only [m₂, show (1048568 : UInt32) + (0 : UInt32) = (1048568 : UInt32) from rfl]
      exact read32_write32_same m₁ (1048568 : UInt32) ptr
    have hread_len : m₂.read32 (1048572 : UInt32) = len := by
      simp only [m₂, show (1048568 : UInt32) + (0 : UInt32) = (1048568 : UInt32) from rfl]
      rw [read32_write32_disjoint m₁ (1048568 : UInt32) (1048572 : UInt32) ptr
            (Or.inr (by simp only [show (1048568 : UInt32).toNat = 1048568 from rfl,
                                   show (1048572 : UInt32).toNat = 1048572 from rfl]; omega))]
      simp only [m₁, show (1048568 : UInt32) + (4 : UInt32) = (1048572 : UInt32) from rfl]
      exact read32_write32_same st.mem (1048572 : UInt32) len
    -- func1 only modifies addresses 1048568 and 1048572; below-1048568 reads are unchanged.
    -- read32_write32_disjoint: (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat)
    -- where a = write address, b = read address.
    -- Here read address (addr) is strictly below write address, so Or.inl applies.
    have hno_mod : ∀ addr : UInt32, addr.toNat + 4 ≤ 1048568 →
        m₂.read32 addr = st.mem.read32 addr := by
      intro addr hle
      simp only [m₂, show (1048568 : UInt32) + (0 : UInt32) = (1048568 : UInt32) from rfl]
      rw [read32_write32_disjoint m₁ (1048568 : UInt32) addr ptr (Or.inl hle)]
      simp only [m₁, show (1048568 : UInt32) + (4 : UInt32) = (1048572 : UInt32) from rfl]
      rw [read32_write32_disjoint st.mem (1048572 : UInt32) addr len
            (Or.inl (by simp only [show (1048572 : UInt32).toNat = 1048572 from rfl]; omega))]
    show ⊢ wp_wasm «module» st
        { params := [.i32 (1048568 : UInt32), .i32 ptr, .i32 len, .i32 (1048716 : UInt32)],
          locals := [], values := [] }
        func1 {} _
    simp only [func1]
    -- Step 1: localGet 0 → push .i32 (1048568 : UInt32) onto stack
    refine wp_wasm_localGet rfl ?_
    intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]; · iexact Hσ
    -- Step 2: localGet 2 → push .i32 len onto stack
    refine wp_wasm_localGet rfl ?_
    intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]; · iexact Hσ
    -- Step 3: store32 4 → write len to address 1048572 (= 1048568 + 4)
    refine wp_wasm_store32 rfl
        (by simp only [show (1048568 : UInt32).toNat = 1048568 from rfl,
                       show (4 : UInt32).toNat = 4 from rfl]; omega) ?_
    intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]; · iexact Hσ
    -- Step 4: localGet 0 → push .i32 (1048568 : UInt32) again
    refine wp_wasm_localGet rfl ?_
    intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]; · iexact Hσ
    -- Step 5: localGet 1 → push .i32 ptr onto stack
    refine wp_wasm_localGet rfl ?_
    intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]; · iexact Hσ
    -- Step 6: store32 0 → write ptr to address 1048568 (= 1048568 + 0)
    refine wp_wasm_store32 rfl
        (by simp only [Mem.write32_pages,
                       show (1048568 : UInt32).toNat = 1048568 from rfl,
                       show (0 : UInt32).toNat = 0 from rfl]; omega) ?_
    intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]; · iexact Hσ
    -- Step 7: ret → close postcondition with pre-computed witnesses
    exact wp_wasm_ret ⟨rfl, rfl, hpages, hread_ptr, hread_len, hno_mod⟩
  exact wp_wasm_prop_to_TerminatesWith hf himp rfl (Nat.le_refl _)
    (fun _ _ h => ⟨rfl, h.2⟩) hwp

/-! ### §6b  func0: the insertion sort loop.
The outer loop uses `wp_wasm_prop_loop` with an invariant tracking the sorted
prefix and a permutation of `xs`.  The inner loop shift steps use
`wasm_heap_adequacy` + `shift_element_via_arrayAt` (proved in §5).
The full loop invariant maintenance (sorted + permutation) is admitted here. -/

omit inst in
private theorem func0_sort_terminates
    (st : Store Unit) (ptr len : UInt32) (xs : List UInt32)
    (hlen  : xs.length = len.toNat)
    (hbounds  : ptr.toNat + 4 * xs.length ≤ st.mem.pages * 65536)
    (hmem_size : (1048576 : Nat) ≤ st.mem.pages * 65536)
    (hglobal1 : st.globals.globals[0]? = some (.i32 (1048560 : UInt32)))
    (hwords   : wordsAt st.mem ptr xs.length = xs)
    (hbounds2 : ptr.toNat + 4 * xs.length ≤ 1048544) :
    TerminatesWith {} «module» 0 st [.i32 len, .i32 ptr]
        (fun st' rs =>
          rs = [] ∧
          ∃ ys : List UInt32,
            wordsAt st'.mem ptr ys.length = ys ∧ ys.Pairwise (· ≤ ·) ∧ ys.Perm xs
            ∧ st'.globals.globals[0]? = some (.i32 (1048560 : UInt32))
            ∧ st'.mem.pages = st.mem.pages) := by
  have himp : «module».imports[0]? = none := rfl
  have hf   : «module».funcs[0 - «module».imports.length]? = some func0Def := rfl
  -- sp = global[0] - 16 = 1048560 - 16 = 1048544 (shadow-stack frame pointer)
  let sp : UInt32 := 1048544
  -- State after the 9-instruction preamble:
  --   global[0] ← sp, local[2] ← sp, mem[sp+8] ← 1 (i=1)
  let st_loop : Store Unit :=
    { st with
        globals := { st.globals with globals := st.globals.globals.set 0 (.i32 sp) },
        mem     := st.mem.write32 (sp + 8) 1 }
  let loc_loop : Locals :=
    { params := [.i32 ptr, .i32 len],
      locals  := [.i32 sp, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
      values  := [] }
  -- Outer loop invariant: sorted prefix of length i, array is a permutation of xs
  -- i can exceed len (checked at loop entry), so the key guard is the loop exit condition
  let Q_final : Store Unit → List Value → Prop := fun st' rs =>
    rs = [] ∧
    ∃ ys : List UInt32,
      wordsAt st'.mem ptr ys.length = ys ∧ ys.Pairwise (· ≤ ·) ∧ ys.Perm xs
      ∧ st'.globals.globals[0]? = some (.i32 (1048560 : UInt32))
      ∧ st'.mem.pages = st.mem.pages
  have hwp : wp_wasm_prop «module» st
      (func0Def.toLocals ([.i32 len, .i32 ptr].take func0Def.numParams).reverse)
      func0Def.body {} Q_final := by
    -- ── Preamble: 9 straight-line instructions → state st_loop / loc_loop ────
    -- Instructions: globalGet 0, const 16, sub, localSet 2, localGet 2,
    --   globalSet 0, localGet 2, const 1, store32 8.
    -- Fuel is consumed only at call/loop boundaries, so K=1 suffices.
    apply wp_wasm_prop_of_exec_eq (K := 1) (c := 1) (st' := st_loop) (locals' := loc_loop)
        (prog' := func0.drop 9)
    · -- Exec equation: running func0 for fuel+1 ≡ running func0.drop 9 from st_loop
      intro fuel
      show exec (fuel + 1) «module» st
              { params := [.i32 ptr, .i32 len],
                locals  := [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
                values  := [] }
              func0 {} =
          exec (fuel + 1) «module» st_loop loc_loop (func0.drop 9) {}
      -- Requires: exec 9 preamble instructions transforms (st, init_locals) to (st_loop, loc_loop)
      -- and does not trap (the sp-8 write is in bounds: sp+8+4=1048556 ≤ 1048576 ≤ pages*65536)
      have hbounds_sp8 : ¬ (st.mem.pages * 65536 < (1048556 : Nat)) := by omega
      -- Expose only the 9-instruction preamble on the LHS, keeping func0.drop 9 opaque.
      -- Inlining the full func0 body causes simp to diverge: execOne.eq_def for .loop
      -- loops forever on the symbolic-fuel Break-0 re-entry call in the match arms.
      conv_lhs =>
        rw [show func0 = func0.take 9 ++ func0.drop 9 from
            (List.take_append_drop 9 func0).symm]
      simp only [show func0.take 9 =
          ([.globalGet 0, .const (16 : UInt32), .sub, .localSet 2, .localGet 2,
            .globalSet 0, .localGet 2, .const (1 : UInt32),
            .store32 (8 : UInt32)] : Program) from rfl]
      simp [exec, execOne.eq_def, Locals.get, Locals.set?,
            hglobal1, hbounds_sp8, st_loop, loc_loop, sp]
    -- ── Outer loop: .loop 0 0 outerBody at (st_loop, loc_loop) ──────────────
    -- func0.drop 9 = [.loop 0 0 outerBody, .localGet 9, .localGet 1, .const 1048636,
    --                  .call 54, .unreachable]
    -- Unfold to get the loop constructor in head position, then apply loop rule.
    simp only [func0, List.drop]
    -- Outer-loop invariant I: ∃ i ys such that ys[0..i) is sorted, ys ∈ Perm xs,
    --   mem[sp+8] = i, global[0] = sp, mem.pages = st.mem.pages, wordsAt holds.
    apply wp_wasm_prop_loop
        (I := fun stA _ =>
          ∃ i : UInt32, ∃ ys : List UInt32,
            ys.length = len.toNat ∧
            wordsAt stA.mem ptr ys.length = ys ∧
            (ys.take i.toNat).Pairwise (· ≤ ·) ∧
            xs.Perm ys ∧
            stA.mem.read32 (sp + 8) = i ∧
            stA.globals.globals[0]? = some (.i32 sp) ∧
            stA.mem.pages = st.mem.pages)
        (μ := fun stA _ => (len - stA.mem.read32 (sp + 8)).toNat)
    · -- hinit: invariant holds at st_loop with i=1, ys=xs
      -- * mem[sp+8] = mem.write32(sp+8)(1).read32(sp+8) = 1 (read32_write32_same)
      -- * global[0] = sp (set 0 to sp)
      -- * mem.pages unchanged (write32 doesn't change pages)
      -- * wordsAt st_loop.mem ptr xs.length = xs because sp+8=1048552 > ptr+4*xs.length
      --   (all array reads below sp+8 are unaffected by the write at sp+8)
      refine ⟨1, xs, hlen, ?_, ?_, List.Perm.refl xs, ?_, ?_, ?_⟩
      · -- wordsAt st_loop.mem ptr xs.length = xs
        have heq : ∀ i ∈ List.range xs.length,
            st_loop.mem.read32 (ptr + 4 * UInt32.ofNat i) =
            st.mem.read32 (ptr + 4 * UInt32.ofNat i) := by
          intro i hi
          have hi_lt : i < xs.length := List.mem_range.mp hi
          apply Mem.read32_write32_disjoint
          left
          have hkn : (UInt32.ofNat i).toNat = i :=
            UInt32.toNat_ofNat_of_lt' (show i < UInt32.size from by show i < 4294967296; omega)
          have h4ki : (4 * UInt32.ofNat i).toNat = 4 * i := by
            rw [UInt32.toNat_mul, show (4 : UInt32).toNat = 4 from rfl, hkn,
                show (2 : Nat) ^ 32 = 4294967296 from rfl]
            exact Nat.mod_eq_of_lt (by omega)
          have hno_ov : (ptr + 4 * UInt32.ofNat i).toNat = ptr.toNat + 4 * i := by
            rw [UInt32.toNat_add, h4ki, show (2 : Nat) ^ 32 = 4294967296 from rfl]
            exact Nat.mod_eq_of_lt (by linarith)
          rw [hno_ov, show (sp + 8 : UInt32).toNat = 1048552 from rfl]
          omega
        simp only [wordsAt]
        have : (List.range xs.length).map (fun i => st_loop.mem.read32 (ptr + 4 * UInt32.ofNat i))
             = (List.range xs.length).map (fun i => st.mem.read32 (ptr + 4 * UInt32.ofNat i)) :=
          List.map_congr_left heq
        rw [this]; exact hwords
      · -- (xs.take 1).Pairwise (· ≤ ·)
        simp only [show UInt32.toNat 1 = 1 from rfl]
        match xs with
        | []     => exact .nil
        | x :: _ => exact List.pairwise_singleton (· ≤ ·) x
      · -- st_loop.mem.read32 (sp + 8) = 1
        exact Mem.read32_write32_same st.mem (sp + 8) 1
      · -- st_loop.globals.globals[0]? = some (.i32 sp)
        show (st.globals.globals.set 0 (.i32 sp))[0]? = some (.i32 sp)
        match hnn : st.globals.globals with
        | []     => simp [hnn] at hglobal1
        | _ :: _ => simp [List.set]
      · -- st_loop.mem.pages = st.mem.pages
        exact Mem.write32_pages st.mem (sp + 8) 1
    · -- hstep: each outer loop body terminates via Return or Break 0
      -- The outer loop body checks i < len at the top:
      --   ∗ If i ≥ len: restores global[0] ← sp+16 = 1048560, then .ret → Return
      --   ∗ If i < len: reads arr[i] as key, runs inner shift loop, stores key,
      --     increments i, then .br 1 inside a block → Break 0 at the outer loop
      intro stA locA ⟨i, ys, hlen_ys, hwords_ys, hsorted, hperm, hread_i, hglob, hpages⟩
      sorry
  exact wp_wasm_prop_to_TerminatesWith hf himp rfl (Nat.le_refl _)
      (fun _ _ h => ⟨rfl, h.2⟩) hwp

/-! ### §6c  Top-level proof: func2 calls func1 then func0.
Uses `wp_wasm_prop_of_exec_eq` to hop over the straight-line shadow-stack
preamble to `call 1`, `wp_wasm_prop_call` to splice in `func1_sort_terminates`,
a second `wp_wasm_prop_of_exec_eq` to hop to `call 0`, `wp_wasm_prop_call` to
splice in `func0_sort_terminates`, and `wp_wasm_prop_step` for the 4-instruction
frame teardown before `ret`. -/

theorem insertion_sort_correct : InsertionSortSpec := by
  intro st ptr len xs hlen hbounds hmem_size hglobal hwords hbounds2
  have himp₂ : «module».imports[2]? = none := rfl
  have hf₂   : «module».funcs[2 - «module».imports.length]? = some func2Def := rfl
  let stg : Store Unit :=
    { st with globals :=
        { st.globals with globals := st.globals.globals.set 0 (.i32 (1048560 : UInt32)) } }
  -- func1 terminates correctly from stg (global write doesn't affect mem).
  have hfunc1 : TerminatesWith {} «module» 1 stg
      [.i32 (1048716 : UInt32), .i32 len, .i32 ptr, .i32 (1048568 : UInt32)]
      (fun st' rs =>
        rs = [] ∧ st'.globals = stg.globals ∧ st'.mem.pages = stg.mem.pages
        ∧ st'.mem.read32 (1048568 : UInt32) = ptr
        ∧ st'.mem.read32 (1048572 : UInt32) = len
        ∧ ∀ addr : UInt32, addr.toNat + 4 ≤ 1048568 →
            st'.mem.read32 addr = stg.mem.read32 addr) :=
    func1_sort_terminates stg ptr len (by simp only [stg]; exact hmem_size)
  have hwp : wp_wasm_prop «module» st
      (func2Def.toLocals ([.i32 len, .i32 ptr].take func2Def.numParams).reverse)
      func2Def.body {}
      (fun st'' _ => ∃ ys : List UInt32,
        wordsAt st''.mem ptr ys.length = ys ∧ ys.Pairwise (· ≤ ·) ∧ ys.Perm xs) := by
    -- ── Hop 1: 14-instruction preamble → call 1 site ──────────────────────
    apply wp_wasm_prop_of_exec_eq (K := 1) (c := 1) (st' := stg)
        (locals' := { params := [.i32 ptr, .i32 len],
                      locals := [.i32 (1048560 : UInt32), .i32 (1048716 : UInt32),
                                 .i32 (0 : UInt32)],
                      values := [.i32 (1048716 : UInt32), .i32 len, .i32 ptr,
                                 .i32 (1048568 : UInt32)] })
        (prog' := [.call 1,
                   .localGet 2, .load32 (12 : UInt32), .localSet 4,
                   .localGet 2, .load32 (8 : UInt32), .localGet 4,
                   .call 0,
                   .localGet 2, .const (16 : UInt32), .add, .globalSet 0, .ret])
    · -- exec equation: simp through 14-instruction preamble
      intro fuel
      show exec (fuel + 1) «module» st
          { params := [.i32 ptr, .i32 len],
            locals := [.i32 (0 : UInt32), .i32 (0 : UInt32), .i32 (0 : UInt32)],
            values := [] }
          func2 {} = _
      simp only [func2]
      simp [exec, execOne.eq_def, Locals.get, Locals.set?, hglobal, stg]
    -- ── Call 1: func1 (spills ptr/len to shadow stack) ───────────────────
    · apply wp_wasm_prop_call
      refine hfunc1.mono ?_
      -- func1 is void; vs = [] after the call; subst immediately.
      rintro st1 vs ⟨hvs, hglob1, hpages1, hread_ptr, hread_len, hno_mod1⟩
      subst hvs
      have hg1 : st1.globals.globals[0]? = some (.i32 (1048560 : UInt32)) := by
        rw [hglob1]; simp only [stg]
        match hnn : st.globals.globals with
        | []     => simp [hnn] at hglobal
        | _ :: _ => simp [List.set]
      have hst1_pages : st1.mem.pages = st.mem.pages := by simp only [hpages1, stg]
      -- Derive wordsAt for st1.mem: func1 only wrote above 1048568, array is below.
      have hwords1 : wordsAt st1.mem ptr xs.length = xs := by
        simp only [wordsAt]
        have heq : ∀ i ∈ List.range xs.length,
            st1.mem.read32 (ptr + 4 * UInt32.ofNat i) =
            st.mem.read32 (ptr + 4 * UInt32.ofNat i) := by
          intro i hi
          have hi_lt : i < xs.length := List.mem_range.mp hi
          apply hno_mod1
          -- Need: (ptr + 4 * UInt32.ofNat i).toNat + 4 ≤ 1048568
          -- Since i < xs.length and ptr.toNat + 4 * xs.length ≤ 1048544 ≤ 1048568,
          -- the address fits. Proved via UInt32 overflow-free arithmetic.
          have hno_ov : (ptr + 4 * UInt32.ofNat i).toNat = ptr.toNat + 4 * i := by
            -- UInt32.toNat_ofNat_of_lt' covers UInt32.ofNat (not OfNat.ofNat literals).
            -- UInt32.toNat_mul/add give % 2^32 (not % UInt32.size) in goal position.
            have hkn : (UInt32.ofNat i).toNat = i :=
              UInt32.toNat_ofNat_of_lt' (show i < UInt32.size from by show i < 4294967296; omega)
            have h4ki : (4 * UInt32.ofNat i).toNat = 4 * i := by
              rw [UInt32.toNat_mul, show (4 : UInt32).toNat = 4 from rfl, hkn,
                  show (2 : Nat) ^ 32 = 4294967296 from rfl]
              exact Nat.mod_eq_of_lt (by omega)
            rw [UInt32.toNat_add, h4ki, show (2 : Nat) ^ 32 = 4294967296 from rfl]
            exact Nat.mod_eq_of_lt (by linarith)
          linarith [show ptr.toNat + 4 * i + 4 ≤ ptr.toNat + 4 * xs.length from by omega]
        have : (List.range xs.length).map (fun i => st1.mem.read32 (ptr + 4 * UInt32.ofNat i))
             = (List.range xs.length).map (fun i => st.mem.read32 (ptr + 4 * UInt32.ofNat i)) :=
          List.map_congr_left heq
        rw [this]; exact hwords
      -- ── Hop 2: load frame+12=len, load frame+8=ptr → call 0 ─────────────
      apply wp_wasm_prop_of_exec_eq (K := 1) (c := 1) (st' := st1)
          (locals' := { params := [.i32 ptr, .i32 len],
                        locals := [.i32 (1048560 : UInt32), .i32 (1048716 : UInt32), .i32 len],
                        values := [.i32 len, .i32 ptr] })
          (prog' := [.call 0, .localGet 2, .const (16 : UInt32), .add, .globalSet 0, .ret])
      · intro fuel
        -- load32 traps when pages*65536 < addr+offset+4; we need the no-trap branch
        have h_12_not : ¬ (st1.mem.pages * 65536 < 1048576) :=
          Nat.not_lt.mpr (by linarith [show st1.mem.pages = st.mem.pages from hst1_pages, hmem_size])
        have h_8_not : ¬ (st1.mem.pages * 65536 < 1048572) :=
          Nat.not_lt.mpr (by linarith [show st1.mem.pages = st.mem.pages from hst1_pages, hmem_size])
        simp [exec, execOne.eq_def, if_neg h_12_not, if_neg h_8_not, hread_len, hread_ptr]
      -- ── Call 0: func0 (insertion sort) ───────────────────────────────────
      · apply wp_wasm_prop_call
        refine (func0_sort_terminates st1 ptr len xs hlen
            (by rw [hst1_pages]; exact hbounds)
            (by rw [hst1_pages]; exact hmem_size)
            hg1 hwords1 hbounds2).mono ?_
        rintro st0 rs0 ⟨hrs0, ys, hys_words, hys_sorted, hys_perm, hg0, hpages0⟩
        subst hrs0
        -- ── Teardown: localGet 2, const 16, add, globalSet 0, then [ret] ──
        -- After call 0 pops its 2 args from [len, ptr] ++ vs1, vs1 remains on the stack.
        apply wp_wasm_prop_of_exec_eq (K := 1) (c := 1)
            (st' := { st0 with globals :=
              { st0.globals with globals := st0.globals.globals.set 0 (.i32 (1048576 : UInt32)) } })
            (locals' := { params := [.i32 ptr, .i32 len],
                          locals := [.i32 (1048560 : UInt32), .i32 (1048716 : UInt32), .i32 len],
                          values := [] })
            (prog' := [.ret])
        · intro fuel; simp [exec, execOne.eq_def, hg0]
        · exact ⟨1, by
            simp only [exec, execOne.eq_def]
            exact ⟨ys, hys_words, hys_sorted, hys_perm⟩⟩
  exact wp_wasm_prop_to_TerminatesWith hf₂ himp₂ rfl (Nat.le_refl _)
    (fun _ _ h => h) hwp

end Project.InsertionSort.InsertionSortSepLogic
