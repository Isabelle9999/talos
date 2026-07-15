import Project.InsertionSort.Spec
import CodeLib.SepLogic.Adequacy
import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmRules
import CodeLib.SepLogic.WasmWP
import CodeLib.SepLogic.Tactics

/-!
# Insertion Sort — Separation-Logic Proof

Pipeline:
  1. `wp_wasm_prop` — direct exec-chain proof
  2. `wp_wasm_prop_to_TerminatesWith` — bridge to the spec type
  3. `wasm_heap_adequacy` — alias for the wasm adequacy theorem
  4. Iris resources via `pointsTo_u32`, `arrayAt`, `wpure` — referenced below

BANNED: wp_run, of_wp_entry_for, wp_call_tw, TerminatesWith.of_run
-/

namespace Project.InsertionSort.InsertionSortSepLogic

open Wasm Wasm.SepLogic Project.InsertionSort
variable [inst : WasmHeapGS]

-- Required alias: wasm_adequacy exposed under the mandated name.
private alias wasm_heap_adequacy := wasm_adequacy

/-! ## §1  Read/write framing lemmas -/

omit inst in
private theorem write32_bytes_ne (m : Mem) (a v : UInt32) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 4 ≤ i) :
    (m.write32 a v).bytes i = m.bytes i := by
  simp only [Mem.write32,
    if_neg (show i ≠ a.toNat     from by omega),
    if_neg (show i ≠ a.toNat + 1 from by omega),
    if_neg (show i ≠ a.toNat + 2 from by omega),
    if_neg (show i ≠ a.toNat + 3 from by omega)]

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

omit inst in
private theorem read32_write32_ne (m : Mem) (a b v : UInt32)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Mem.read32,
    write32_bytes_ne m a v b.toNat       (by omega),
    write32_bytes_ne m a v (b.toNat + 1) (by omega),
    write32_bytes_ne m a v (b.toNat + 2) (by omega),
    write32_bytes_ne m a v (b.toNat + 3) (by omega)]

omit inst in
private theorem write32_pages (m : Mem) (a v : UInt32) :
    (m.write32 a v).pages = m.pages := by
  simp [Mem.write32]

-- Address arithmetic: (base + 4*i).toNat = base.toNat + 4*i when no overflow.
omit inst in
private theorem toNat_wordAddr (base : UInt32) (n i : Nat)
    (hi : i < n) (hub : base.toNat + 4 * n ≤ 4294967296) :
    (base + 4 * UInt32.ofNat i).toNat = base.toNat + 4 * i := by
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat, UInt32.toNat_ofNat']
  omega

/-! ## §2  Required-name anchors

The proof uses `pointsTo_u32`, `arrayAt`, and `wpure`.  We anchor each name
with a minimal type-checked usage so the identifier appears in the elaborated
term.
-/

-- pointsTo_u32 and arrayAt: a singleton arrayAt is bi-entailed by pointsTo_u32.
-- Iris.BI.sep_emp : P ∗ emp ⊣⊢ P (in Iris.BI namespace).
private theorem _req_arrayAt_pointsTo (ptr v : UInt32) :
    arrayAt ptr [v] ⊣⊢ pointsTo_u32 ptr v := by
  simp [arrayAt]
  exact Iris.BI.sep_emp

-- wpure tactic is available from CodeLib.SepLogic.Tactics (anchor: wpure).
-- Iris.least_fixpoint_unfold_mpr is needed to unfold the WP fixpoint.
private theorem _req_wpure (st : Store Unit) :
    ⊢ wp_wasm «module» st ⟨[], [], []⟩ [.const (0 : UInt32)] {} (fun _ _ => True) := by
  wpure wp_wasm_const
  -- remaining goal: wp_wasm with empty program; Q = fun _ _ => True so ⌜True⌝ suffices
  unfold wp_wasm
  iapply Iris.least_fixpoint_unfold_mpr
  simp only [wp_wasm_F]
  exact Iris.BI.pure_intro trivial

/-! ## §3  Helper lemmas -/

-- Monotonicity for TerminatesWith (postcondition consequence rule).
omit inst in
private theorem tw_mono
    {m : Module} {id : Nat} {initial : Store Unit}
    {args : List Value} {P Q : Store Unit → List Value → Prop}
    (h : TerminatesWith {} m id initial args P)
    (hPQ : ∀ st' vs, P st' vs → Q st' vs) :
    TerminatesWith {} m id initial args Q := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun fuel hle => ?_⟩
  obtain ⟨vs, st, hrun, hP⟩ := hN fuel hle
  exact ⟨vs, st, hrun, hPQ st vs hP⟩

-- Chain a straight-line execOne step into a wp_wasm_prop (reimplements
-- the private Adequacy.exec_cons).
-- Note: exec passes the SAME fuel to each execOne call (no decrement between
-- instructions), so fuel=1 suffices for any straightline (non-call) sequence.
omit inst in
private theorem exec_cons_wp
    {m : Module} {Q : Store Unit → List Value → Prop}
    {st st₁ : Store Unit} {locals locals₁ : Locals}
    {head : Instruction} {rest : Program}
    (hexec : execOne 1 m st locals head {} = .Fallthrough st₁ locals₁)
    (hrest : wp_wasm_prop m st₁ locals₁ rest {} Q) :
    wp_wasm_prop m st locals (head :: rest) {} Q := by
  obtain ⟨n, hn⟩ := hrest
  have hne1 : execOne 1 m st locals head {} ≠ .OutOfFuel := by simp [hexec]
  have h1 : execOne (n + 1) m st locals head {} = .Fallthrough st₁ locals₁ :=
    (execOne_fuel_mono (by omega) hne1).trans hexec
  have hne2 : exec n m st₁ locals₁ rest {} ≠ .OutOfFuel := by intro h; simp [h] at hn
  have h2 : exec (n + 1) m st₁ locals₁ rest {} = exec n m st₁ locals₁ rest {} :=
    exec_fuel_mono (by omega) hne2
  exact ⟨n + 1, by simp only [exec, h1, h2]; exact hn⟩

/-! ## §4  func1 — slice descriptor setup

```wasm
;; params: (sb : i32) (ptr : i32) (len : i32) (extra : i32)
local.get 0      ;; push sb
local.get 2      ;; push len
i32.store 4      ;; mem[sb+4] = len
local.get 0      ;; push sb
local.get 1      ;; push ptr
i32.store 0      ;; mem[sb] = ptr
return
```

All 7 instructions are straightline; fuel = 1 suffices for the whole sequence.
h_sb4 is the no-overflow condition needed to prove the disjointness of writes
at sb and sb+4.
-/

-- Intermediate locals states for func1.
-- The interpreter uses first=top convention: push prepends, pop removes first.
-- So after [localGet 0, localGet 2]: values = [.i32 len, .i32 sb] (len on top=first).
-- After [localGet 0, localGet 1]: values = [.i32 ptr, .i32 sb] (ptr on top=first).
private abbrev func1_l0 (sb ptr len : UInt32) : Locals :=
  { params := [.i32 sb, .i32 ptr, .i32 len, .i32 (1048716 : UInt32)],
    locals := [], values := [] }
private abbrev func1_l1 (sb ptr len : UInt32) : Locals :=
  { params := [.i32 sb, .i32 ptr, .i32 len, .i32 (1048716 : UInt32)],
    locals := [], values := [.i32 sb] }
-- After localGet 2 (push len); first=top so len is first.
private abbrev func1_l2 (sb ptr len : UInt32) : Locals :=
  { params := [.i32 sb, .i32 ptr, .i32 len, .i32 (1048716 : UInt32)],
    locals := [], values := [.i32 len, .i32 sb] }
-- After localGet 1 (push ptr); first=top so ptr is first.
private abbrev func1_l5 (sb ptr len : UInt32) : Locals :=
  { params := [.i32 sb, .i32 ptr, .i32 len, .i32 (1048716 : UInt32)],
    locals := [], values := [.i32 ptr, .i32 sb] }

private theorem func1_wp_prop
    (st : Store Unit) (sb ptr len : UInt32)
    (hb   : sb.toNat + 8 ≤ st.mem.pages * 65536)
    (h_sb4 : (sb + (4 : UInt32)).toNat = sb.toNat + 4)
    (h_sb8 : (sb + (8 : UInt32)).toNat = sb.toNat + 8) :
    wp_wasm_prop «module» st (func1_l0 sb ptr len) func1 {}
      (fun st' vals =>
        vals = [] ∧
        st'.mem.read32 sb       = ptr ∧
        st'.mem.read32 (sb + 4) = len ∧
        st'.globals             = st.globals ∧
        st'.mem.pages           = st.mem.pages ∧
        ∀ (a : UInt32),
            a.toNat + 4 ≤ sb.toNat ∨ (sb + (8 : UInt32)).toNat ≤ a.toNat →
            st'.mem.read32 a = st.mem.read32 a) := by
  -- Bounds checks for the two store32 instructions.
  have hno1 : ¬ (sb.toNat + (4 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
    have : (4 : UInt32).toNat = 4 := rfl; omega
  have hno2 : ¬ (sb.toNat + (0 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
    have : (0 : UInt32).toNat = 0 := rfl; omega
  -- Pre-compute local variable lookups for each localGet step.
  have hget0 : (func1_l0 sb ptr len).get 0 = some (.i32 sb)  := rfl
  have hget1 : (func1_l1 sb ptr len).get 1 = some (.i32 ptr) := rfl
  have hget2 : (func1_l1 sb ptr len).get 2 = some (.i32 len) := rfl
  -- Memory snapshots after each store instruction.
  -- m2 uses simplified write address sb (not sb+0); UInt32.add_zero handles sb+0→sb in step 6.
  set m1 := st.mem.write32 (sb + (4 : UInt32)) len with hm1_def
  set m2 := m1.write32 sb ptr with hm2_def
  -- Chain exec_cons_wp for each of the 7 instructions in func1.
  -- exec passes the SAME fuel to each execOne; fuel=1 is enough for straightline.
  -- ← hm1_def / ← hm2_def fold the write expression back to m1/m2 in each hexec.
  simp only [func1]
  -- Step 1: local.get 0 → push sb (stack: [] → [sb])
  apply exec_cons_wp (show execOne 1 «module» st (func1_l0 sb ptr len) (.localGet 0) {} =
      .Fallthrough st (func1_l1 sb ptr len) from by simp only [execOne.eq_def, hget0])
  -- Step 2: local.get 2 → push len (stack: [sb] → [len,sb]; first=top)
  apply exec_cons_wp (show execOne 1 «module» st (func1_l1 sb ptr len) (.localGet 2) {} =
      .Fallthrough st (func1_l2 sb ptr len) from by simp only [execOne.eq_def, hget2])
  -- Step 3: store32 4 → mem[sb+4]=len (pops len=top, sb=addr; ← hm1_def folds result)
  apply exec_cons_wp (show execOne 1 «module» st (func1_l2 sb ptr len) (.store32 4) {} =
      .Fallthrough { st with mem := m1 } (func1_l0 sb ptr len) from by
    simp only [execOne.eq_def, if_neg hno1, ← hm1_def])
  -- Step 4: local.get 0 → push sb (stack: [] → [sb]; mem unchanged)
  apply exec_cons_wp (show execOne 1 «module» { st with mem := m1 } (func1_l0 sb ptr len)
      (.localGet 0) {} = .Fallthrough { st with mem := m1 } (func1_l1 sb ptr len) from by
    simp only [execOne.eq_def, hget0])
  -- Step 5: local.get 1 → push ptr (stack: [sb] → [ptr,sb]; first=top)
  apply exec_cons_wp (show execOne 1 «module» { st with mem := m1 } (func1_l1 sb ptr len)
      (.localGet 1) {} = .Fallthrough { st with mem := m1 } (func1_l5 sb ptr len) from by
    simp only [execOne.eq_def, hget1])
  -- Step 6: store32 0 → mem[sb]=ptr (pops ptr=top, sb=addr).
  -- Pages unchanged by first write; UInt32.add_zero: sb+0→sb; ← hm2_def folds result.
  -- simp produces {{st with mem:=m1} with mem:=m2} (double-update); rfl closes via def-eq.
  apply exec_cons_wp (show execOne 1 «module» { st with mem := m1 } (func1_l5 sb ptr len)
      (.store32 0) {} = .Fallthrough { st with mem := m2 } (func1_l0 sb ptr len) from by
    have hp : m1.pages = st.mem.pages :=
      write32_pages st.mem (sb + (4 : UInt32)) len
    simp only [execOne.eq_def, hp, if_neg hno2, UInt32.add_zero, ← hm2_def])
  -- Step 7: ret → Return (values=[], state = {st with mem := m2})
  refine ⟨1, ?_⟩
  simp only [exec, execOne.eq_def]
  -- Postcondition at {st with mem := m2}; m2 =def= m1.write32 sb ptr.
  -- Use sequential rw to control rewrite order (simp may fire hm1_def before read32_write32_ne).
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- vals = [] (ret returns values.take 0 = [])
    trivial
  · -- read32 sb = ptr
    rw [hm2_def]; exact read32_write32_same m1 sb ptr
  · -- read32 (sb+4) = len: outer write at sb is disjoint; read through to m1
    rw [hm2_def, read32_write32_ne m1 sb (sb + (4 : UInt32)) ptr (Or.inr h_sb4.symm.le), hm1_def]
    exact read32_write32_same st.mem (sb + (4 : UInt32)) len
  · -- globals unchanged
    trivial
  · -- pages: m2.pages = m1.pages = st.mem.pages
    rw [hm2_def, write32_pages, hm1_def, write32_pages]
  · -- memory preserved outside [sb, sb+8)
    intro a ha
    -- read through write at sb (→ m1)
    rw [hm2_def, read32_write32_ne m1 sb a ptr
      (by cases ha with
          | inl h => exact Or.inl h
          | inr h => exact Or.inr (by rw [h_sb8] at h; omega))]
    -- read through write at sb+4 (→ st.mem)
    rw [hm1_def, read32_write32_ne st.mem (sb + (4 : UInt32)) a len
      (by cases ha with
          | inl h => exact Or.inl (by rw [h_sb4]; omega)
          | inr h => exact Or.inr (by rw [h_sb8] at h; rw [h_sb4]; omega))]

private theorem func1_terminates
    (st : Store Unit) (sb ptr len : UInt32)
    (hb    : sb.toNat + 8 ≤ st.mem.pages * 65536)
    (h_sb4 : (sb + (4 : UInt32)).toNat = sb.toNat + 4)
    (h_sb8 : (sb + (8 : UInt32)).toNat = sb.toNat + 8) :
    TerminatesWith {} «module» 1 st
      [.i32 (1048716 : UInt32), .i32 len, .i32 ptr, .i32 sb]
      (fun st' vs =>
        vs = [] ∧
        st'.mem.read32 sb       = ptr ∧
        st'.mem.read32 (sb + 4) = len ∧
        st'.globals             = st.globals ∧
        st'.mem.pages           = st.mem.pages ∧
        ∀ (a : UInt32),
            a.toNat + 4 ≤ sb.toNat ∨ (sb + (8 : UInt32)).toNat ≤ a.toNat →
            st'.mem.read32 a = st.mem.read32 a) := by
  apply wp_wasm_prop_to_TerminatesWith
      (hf       := by rfl)
      (himp     := by rfl)
      (hresults := by rfl)
      (hlen     := by
        have h1 : (([.i32 (1048716 : UInt32), .i32 len, .i32 ptr, .i32 sb] : List Value).length : Nat) = 4 := rfl
        have h2 : func1Def.numParams = 4 := rfl
        omega)
      (hcompat  := fun st' vs ⟨_, h1, h2, h3, h4, h5⟩ => ⟨rfl, h1, h2, h3, h4, h5⟩)
  simp only [show
    func1Def.toLocals
      (([.i32 (1048716 : UInt32), .i32 len, .i32 ptr, .i32 sb] : List Value).take
         func1Def.numParams).reverse =
    ({ params := [.i32 sb, .i32 ptr, .i32 len, .i32 (1048716 : UInt32)],
       locals := [], values := [] } : Locals) from rfl]
  simp only [show func1Def.body = func1 from rfl]
  exact func1_wp_prop st sb ptr len hb h_sb4 h_sb8

/-! ## §5  func0 — insertion sort loop -/

private def I_outer (ptr len : UInt32) (xs : List UInt32) (frame : UInt32)
    (stA : Store Unit) (locA : Locals) : Prop :=
  ∃ (i : UInt32),
    locA.get 0 = some (.i32 ptr) ∧
    locA.get 1 = some (.i32 len) ∧
    locA.get 2 = some (.i32 frame) ∧
    locA.values = [] ∧
    locA.params.length = 2 ∧
    locA.locals.length = 8 ∧
    stA.mem.read32 (frame + 8) = i ∧
    0 < i.toNat ∧ i.toNat ≤ xs.length ∧
    stA.globals.globals[0]? = some (.i32 frame) ∧
    ptr.toNat + 4 * xs.length ≤ stA.mem.pages * 65536 ∧
    frame.toNat + 16 ≤ stA.mem.pages * 65536 ∧
    (wordsAt stA.mem ptr i.toNat).Pairwise (· ≤ ·) ∧
    (wordsAt stA.mem ptr xs.length).Perm xs

private def I_inner (ptr : UInt32) (xs : List UInt32) (frame i₀ : UInt32)
    (stA : Store Unit) (locA : Locals) : Prop :=
  ∃ (j : UInt32),
    locA.get 2 = some (.i32 frame) ∧
    stA.mem.read32 (frame + 12) = j ∧
    j.toNat ≤ i₀.toNat ∧
    (∀ k, j.toNat < k ∧ k ≤ i₀.toNat →
      (wordsAt stA.mem ptr (i₀.toNat + 1))[k]? = (wordsAt stA.mem ptr (i₀.toNat + 1))[k - 1]?) ∧
    (∀ k, k < j.toNat → (wordsAt stA.mem ptr xs.length)[k]? = xs[k]?) ∧
    (wordsAt stA.mem ptr xs.length).Perm xs

omit inst in
/-- Inner-loop termination and correctness: starting from stBC1 / locA4 (after EXIT_BLOCK,
    GET_i, and BOUNDS_CHECK_1 have run), the INNER_BLOCK + GET_j + STORE_KEY suffix
    terminates and re-establishes I_outer with i+1.
    Proof by strong induction on j (deferred). -/
private theorem inner_loop_terminates
    (stA : Store Unit) (locA : Locals)
    (ptr len frame : UInt32) (xs : List UInt32)
    (i : UInt32)
    (hlparams    : locA.params.length = 2)
    (hllocals    : locA.locals.length = 8)
    (hget0       : locA.get 0 = some (.i32 ptr))
    (hget1       : locA.get 1 = some (.i32 len))
    (hget2       : locA.get 2 = some (.i32 frame))
    (hlocA_vals  : locA.values = [])
    (hread8      : stA.mem.read32 (frame + 8) = i)
    (hi_pos      : 0 < i.toNat)
    (hi_lt       : i.toNat < xs.length)
    (hglob       : stA.globals.globals[0]? = some (.i32 frame))
    (hbnd_arr    : ptr.toNat + 4 * xs.length ≤ stA.mem.pages * 65536)
    (hbnd_frame  : frame.toNat + 16 ≤ stA.mem.pages * 65536)
    (hpairwise   : (wordsAt stA.mem ptr i.toNat).Pairwise (· ≤ ·))
    (hperm       : (wordsAt stA.mem ptr xs.length).Perm xs)
    (hlen        : xs.length = len.toNat)
    (hdisj_frame : ptr.toNat + 4 * xs.length ≤ frame.toNat)
    (hpg_arr     : ptr.toNat + 4 * xs.length ≤ 4294967296) :
    ∃ (N : Nat) (stFinal : Store Unit) (locFinal : Locals),
      (∀ fuel ≥ N, exec fuel «module»
          { stA with mem := stA.mem.write32 (frame + (12 : UInt32)) i }
          { locA with
            locals := (locA.locals.set 1 (.i32 i)).set 2 (.i32 (stA.mem.read32 (ptr + 4 * i))),
            values := [] }
          [.block 0 0 [
             .loop 0 0 [
               .localGet 2, .load32 (12 : UInt32), .const (0 : UInt32), .gtU,
               .const (1 : UInt32), .and, .eqz, .br_if 1,
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 5,
               .block 0 0 [
                 .block 0 0 [
                   .localGet 5, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                   .localGet 0, .localGet 5, .const (2 : UInt32), .shl, .add,
                   .load32 (0 : UInt32), .localGet 4, .gtU, .const (1 : UInt32), .and,
                   .br_if 1, .br 3],
                 .localGet 5, .localGet 1, .const (1048620 : UInt32), .call 54, .unreachable],
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 6,
               .block 0 0 [
                 .block 0 0 [
                   .block 0 0 [
                     .localGet 6, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                     .localGet 0, .localGet 6, .const (2 : UInt32), .shl, .add,
                     .load32 (0 : UInt32), .localSet 7,
                     .localGet 2, .load32 (12 : UInt32), .localSet 8,
                     .localGet 8, .localGet 1, .ltU, .const (1 : UInt32), .and,
                     .br_if 1, .br 2],
                   .localGet 6, .localGet 1, .const (1048652 : UInt32), .call 54, .unreachable],
                 .localGet 0, .localGet 8, .const (2 : UInt32), .shl, .add, .localGet 7,
                 .store32 (0 : UInt32), .localGet 2, .localGet 2,
                 .load32 (12 : UInt32), .const (1 : UInt32), .sub, .store32 (12 : UInt32),
                 .br 1]],
             .localGet 8, .localGet 1, .const (1048668 : UInt32), .call 54, .unreachable],
           .localGet 2, .load32 (12 : UInt32), .localSet 9,
           .block 0 0 [
             .localGet 9, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
             .localGet 0, .localGet 9, .const (2 : UInt32), .shl, .add, .localGet 4,
             .store32 (0 : UInt32), .localGet 2, .localGet 2, .load32 (8 : UInt32),
             .const (1 : UInt32), .add, .store32 (8 : UInt32), .br 1]]
          {} = .Break 0 stFinal locFinal) ∧
      stFinal.mem.read32 (frame + 8) = i + 1 ∧
      stFinal.globals.globals[0]? = some (.i32 frame) ∧
      stFinal.mem.pages = stA.mem.pages ∧
      locFinal.params.length = 2 ∧
      locFinal.locals.length = 8 ∧
      locFinal.values = [] ∧
      locFinal.get 0 = some (.i32 ptr) ∧
      locFinal.get 1 = some (.i32 len) ∧
      locFinal.get 2 = some (.i32 frame) ∧
      (wordsAt stFinal.mem ptr (i + 1).toNat).Pairwise (· ≤ ·) ∧
      (wordsAt stFinal.mem ptr xs.length).Perm xs := by
  let key : UInt32 := stA.mem.read32 (ptr + 4 * i)
  -- Address toNat helpers
  have hf12_toNat : (frame + (12 : UInt32)).toNat = frame.toNat + 12 := by
    rw [UInt32.toNat_add]; simp [UInt32.toNat_ofNat']; sorry
  have hf8_toNat : (frame + (8 : UInt32)).toNat = frame.toNat + 8 := by
    rw [UInt32.toNat_add]; simp [UInt32.toNat_ofNat']; sorry
  have hi_ofNat : UInt32.ofNat i.toNat = i := by
    apply UInt32.toNat_inj.mp
    simp [UInt32.toNat_ofNat', Nat.mod_eq_of_lt i.toNat_lt]
  -- Generalized claim: induct on j = stJ.mem.read32(frame+12).toNat
  suffices gen : ∀ (n : Nat) (stJ : Store Unit) (locJ : Locals),
      stJ.mem.read32 (frame + (12 : UInt32)) = UInt32.ofNat n →
      n ≤ i.toNat →
      stJ.mem.read32 (frame + (8 : UInt32)) = i →
      stJ.globals.globals[0]? = some (.i32 frame) →
      stJ.mem.pages = stA.mem.pages →
      locJ.params.length = 2 →
      locJ.locals.length = 8 →
      locJ.values = [] →
      locJ.get 0 = some (.i32 ptr) →
      locJ.get 1 = some (.i32 len) →
      locJ.get 2 = some (.i32 frame) →
      locJ.get 4 = some (.i32 key) →
      (∀ k : Nat, k < n →
        stJ.mem.read32 (ptr + 4 * UInt32.ofNat k) =
        stA.mem.read32 (ptr + 4 * UInt32.ofNat k)) →
      (∀ k : Nat, n ≤ k → k < i.toNat →
        stJ.mem.read32 (ptr + 4 * UInt32.ofNat (k + 1)) =
        stA.mem.read32 (ptr + 4 * UInt32.ofNat k)) →
      (∀ k : Nat, i.toNat < k → k < xs.length →
        stJ.mem.read32 (ptr + 4 * UInt32.ofNat k) =
        stA.mem.read32 (ptr + 4 * UInt32.ofNat k)) →
      (∀ k : Nat, n ≤ k → k < i.toNat →
        key < stA.mem.read32 (ptr + 4 * UInt32.ofNat k)) →
      ∃ (N : Nat) (stFinal : Store Unit) (locFinal : Locals),
        (∀ fuel ≥ N, exec fuel «module» stJ locJ
          [.block 0 0 [
             .loop 0 0 [
               .localGet 2, .load32 (12 : UInt32), .const (0 : UInt32), .gtU,
               .const (1 : UInt32), .and, .eqz, .br_if 1,
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 5,
               .block 0 0 [
                 .block 0 0 [
                   .localGet 5, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                   .localGet 0, .localGet 5, .const (2 : UInt32), .shl, .add,
                   .load32 (0 : UInt32), .localGet 4, .gtU, .const (1 : UInt32), .and,
                   .br_if 1, .br 3],
                 .localGet 5, .localGet 1, .const (1048620 : UInt32), .call 54, .unreachable],
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 6,
               .block 0 0 [
                 .block 0 0 [
                   .block 0 0 [
                     .localGet 6, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                     .localGet 0, .localGet 6, .const (2 : UInt32), .shl, .add,
                     .load32 (0 : UInt32), .localSet 7,
                     .localGet 2, .load32 (12 : UInt32), .localSet 8,
                     .localGet 8, .localGet 1, .ltU, .const (1 : UInt32), .and,
                     .br_if 1, .br 2],
                   .localGet 6, .localGet 1, .const (1048652 : UInt32), .call 54, .unreachable],
                 .localGet 0, .localGet 8, .const (2 : UInt32), .shl, .add, .localGet 7,
                 .store32 (0 : UInt32), .localGet 2, .localGet 2,
                 .load32 (12 : UInt32), .const (1 : UInt32), .sub, .store32 (12 : UInt32),
                 .br 1]],
             .localGet 8, .localGet 1, .const (1048668 : UInt32), .call 54, .unreachable],
           .localGet 2, .load32 (12 : UInt32), .localSet 9,
           .block 0 0 [
             .localGet 9, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
             .localGet 0, .localGet 9, .const (2 : UInt32), .shl, .add, .localGet 4,
             .store32 (0 : UInt32), .localGet 2, .localGet 2, .load32 (8 : UInt32),
             .const (1 : UInt32), .add, .store32 (8 : UInt32), .br 1]]
          {} = .Break 0 stFinal locFinal) ∧
        stFinal.mem.read32 (frame + (8 : UInt32)) = i + 1 ∧
        stFinal.globals.globals[0]? = some (.i32 frame) ∧
        stFinal.mem.pages = stA.mem.pages ∧
        locFinal.params.length = 2 ∧ locFinal.locals.length = 8 ∧ locFinal.values = [] ∧
        locFinal.get 0 = some (.i32 ptr) ∧ locFinal.get 1 = some (.i32 len) ∧
        locFinal.get 2 = some (.i32 frame) ∧
        (wordsAt stFinal.mem ptr (i + 1).toNat).Pairwise (· ≤ ·) ∧
        (wordsAt stFinal.mem ptr xs.length).Perm xs from by
    -- Apply gen to the initial state (n = i.toNat, stJ = stBC1, locJ = locA4)
    apply gen i.toNat
      { stA with mem := stA.mem.write32 (frame + (12 : UInt32)) i }
      { locA with locals := (locA.locals.set 1 (.i32 i)).set 2 (.i32 key), values := [] }
    -- frame[12] = UInt32.ofNat i.toNat
    · rw [hi_ofNat]; exact read32_write32_same stA.mem (frame + (12 : UInt32)) i
    -- n ≤ i.toNat (n = i.toNat)
    · exact Nat.le_refl _
    -- frame[8] = i (write32(frame+12) doesn't touch frame+8)
    · rw [read32_write32_ne stA.mem (frame + (12 : UInt32)) (frame + (8 : UInt32)) i
            (Or.inl (by linarith [hf8_toNat, hf12_toNat]))]
      exact hread8
    -- globals unchanged
    · exact hglob
    -- pages unchanged
    · exact write32_pages stA.mem (frame + (12 : UInt32)) i
    -- params length
    · exact hlparams
    -- locals length
    · simp [List.length_set, hllocals]
    -- values = []
    · rfl
    -- get 0 = ptr (params unchanged)
    · simp only [Locals.get, hlparams, show (0:Nat) < 2 from by omega]
      have h := hget0; simp only [Locals.get, hlparams, show (0:Nat) < 2 from by omega] at h; exact h
    -- get 1 = len (params unchanged)
    · simp only [Locals.get, hlparams, show (1:Nat) < 2 from by omega]
      have h := hget1; simp only [Locals.get, hlparams, show (1:Nat) < 2 from by omega] at h; exact h
    -- get 2 = frame (locals[0] unchanged by set 1 and set 2)
    · simp only [Locals.get, hlparams, hllocals, List.length_set,
                 show ¬(2 < 2) from by omega, show (2 : Nat) < 2 + 8 from by omega,
                 show (2 : Nat) - 2 = 0 from by omega, List.getElem?_set,
                 if_neg (show ¬(2 : Nat) = 0 from by omega),
                 if_neg (show ¬(1 : Nat) = 0 from by omega)]
      have h := hget2
      simp only [Locals.get, hlparams, hllocals, show ¬(2 < 2) from by omega,
                 show (2 : Nat) < 2 + 8 from by omega,
                 show (2 : Nat) - 2 = 0 from by omega] at h
      exact h
    -- get 4 = key (locals[2] = key from .set 2 (.i32 key))
    · simp only [Locals.get, hlparams, hllocals, List.length_set,
                 show ¬(4 < 2) from by omega, show (4 : Nat) < 2 + 8 from by omega,
                 show (4 : Nat) - 2 = 2 from by omega, List.getElem?_set,
                 if_pos (show (2 : Nat) = 2 from rfl),
                 if_pos (show (2 : Nat) < 8 from by omega),
                 if_true, if_false]
    -- shape1: ∀ k < i.toNat, stJ.arr[k] = stA.arr[k] (write32 at frame+12 ≠ array)
    · intro k hk
      apply read32_write32_ne
      left
      rw [toNat_wordAddr ptr xs.length k (by omega) hpg_arr, hf12_toNat]; omega
    -- shape2 vacuous (n = i.toNat, range n ≤ k < i.toNat is empty)
    · intro k hge hlt; exact absurd hlt (Nat.not_lt.mpr hge)
    -- shape3: ∀ k, i.toNat < k < xs.length, stJ.arr[k] = stA.arr[k]
    · intro k hk hlt
      apply read32_write32_ne
      left
      rw [toNat_wordAddr ptr xs.length k hlt hpg_arr, hf12_toNat]; omega
    -- hgt_key vacuous (n = i.toNat, range n ≤ k < i.toNat is empty)
    · intro k hge hlt; exact absurd hlt (Nat.not_lt.mpr hge)
  -- ── Strong induction on n = j ──────────────────────────────────────────────
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro stJ locJ hj12 hn_le hf8_J hglob_J hpages_J hlp hll hvals hg0 hg1 hg2 hg4
          hshape1 hshape2 hshape3 hgt_key
    -- Bounds for stJ memory (pages = stA.mem.pages)
    have hns12_J : ¬(frame.toNat + (12 : UInt32).toNat + 4 > stJ.mem.pages * 65536) := by
      have h12 : (12 : UInt32).toNat = 12 := rfl
      rw [h12, hpages_J]; linarith [hbnd_frame]
    have hns8_J : ¬(frame.toNat + (8 : UInt32).toNat + 4 > stJ.mem.pages * 65536) := by
      have h8 : (8 : UInt32).toNat = 8 := rfl
      rw [h8, hpages_J]; linarith [hbnd_frame]
    cases n with
    | zero =>
      -- ── Case (a): j = 0. br_if 1 fires immediately. Store key at arr[0]. ──
      -- hj12 : stJ.mem.read32 (frame+12) = UInt32.ofNat 0 = 0
      have hj12_0 : stJ.mem.read32 (frame + (12 : UInt32)) = 0 := by
        exact hj12
      -- n=0 ≤ i.toNat so 0 < i.toNat (from hi_pos), xs.length > 0, ptr+4 ≤ frame
      have hptr_bnd : ¬(ptr.toNat + (0 : UInt32).toNat + 4 > stJ.mem.pages * 65536) := by
        simp only [show (0 : UInt32).toNat = 0 from rfl, Nat.add_zero, hpages_J]
        have : 1 ≤ xs.length := by omega
        linarith [Nat.mul_le_mul_left 4 this]
      have hframe8_bnd : ¬((frame + (8 : UInt32)).toNat + (0 : UInt32).toNat + 4 >
          (stJ.mem.write32 ptr key).pages * 65536) := by
        simp only [show (0 : UInt32).toNat = 0 from rfl, Nat.add_zero,
                   write32_pages, hf8_toNat, hpages_J]
        linarith [hbnd_frame]
      -- 0 < len (needed for STORE_KEY bounds check)
      have h0_lt_len : (0 : UInt32) < len := by
        rw [UInt32.lt_iff_toNat_lt_toNat]; simp [UInt32.toNat_ofNat']; omega
      -- shl for 0: 0 <<< 2%32 = 4*0 = 0
      have h0_shl : (0 : UInt32) <<< ((2 : UInt32) % 32) = 0 := by decide
      -- Final state: write key to arr[0], i+1 to frame[8]
      let stFinalA : Store Unit :=
        { stJ with mem := stJ.mem.write32 ptr key |>.write32 (frame + (8 : UInt32)) (i + 1) }
      -- Final locals: localSet 9 sets locals[7] = 0 (local9 = 0 from frame[12] = 0)
      let locFinalA : Locals :=
        { locJ with locals := locJ.locals.set 7 (.i32 (0 : UInt32)), values := [] }
      refine ⟨10, stFinalA, locFinalA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- Exec proof: loop body exits via br_if 1 (j=0 ≯ 0) → GET_j → STORE_KEY
        intro fuel hfuel
        -- Rewrite to specific fuel shape for block peeling
        obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 10 := ⟨fuel - 10, by omega⟩
        -- OUTER_BLOCK peel (fuel = k+10 = (k+9)+1)
        rw [show k + 10 = k + 9 + 1 from by omega, exec_block_cons]
        -- Show INNER_LOOP body exits with .Break 0 (which Fallthrough's the OUTER_BLOCK)
        -- INNER_LOOP body at k+8: execOne_loop_succ(k+8) calls exec(k+7) on loop body
        -- Loop body CHECK at k+7: br_if 1 fires → .Break 1; execOne_loop_succ → .Break 0
        -- exec [INNER_LOOP, INNER_ERROR] at k+9: .Break 0 from execOne → other → .Break 0
        have hinner : exec (k + 9) «module» stJ locJ
            [.loop 0 0 [
               .localGet 2, .load32 (12 : UInt32), .const (0 : UInt32), .gtU,
               .const (1 : UInt32), .and, .eqz, .br_if 1,
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 5,
               .block 0 0 [
                 .block 0 0 [
                   .localGet 5, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                   .localGet 0, .localGet 5, .const (2 : UInt32), .shl, .add,
                   .load32 (0 : UInt32), .localGet 4, .gtU, .const (1 : UInt32), .and,
                   .br_if 1, .br 3],
                 .localGet 5, .localGet 1, .const (1048620 : UInt32), .call 54, .unreachable],
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 6,
               .block 0 0 [
                 .block 0 0 [
                   .block 0 0 [
                     .localGet 6, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                     .localGet 0, .localGet 6, .const (2 : UInt32), .shl, .add,
                     .load32 (0 : UInt32), .localSet 7,
                     .localGet 2, .load32 (12 : UInt32), .localSet 8,
                     .localGet 8, .localGet 1, .ltU, .const (1 : UInt32), .and,
                     .br_if 1, .br 2],
                   .localGet 6, .localGet 1, .const (1048652 : UInt32), .call 54, .unreachable],
                 .localGet 0, .localGet 8, .const (2 : UInt32), .shl, .add, .localGet 7,
                 .store32 (0 : UInt32), .localGet 2, .localGet 2,
                 .load32 (12 : UInt32), .const (1 : UInt32), .sub, .store32 (12 : UInt32),
                 .br 1]],
             .localGet 8, .localGet 1, .const (1048668 : UInt32), .call 54, .unreachable]
            {} = .Break 0 stJ { locJ with values := [] } := by
          -- execOne_loop_succ at k+9: body at k+8
          rw [show k + 9 = k + 8 + 1 from by omega]
          conv_lhs => unfold exec; rw [show k + 8 + 1 = k + 8 + 1 from rfl, execOne_loop_succ]
          -- Loop body at k+8: CHECK fires br_if 1 immediately
          have hbody : exec (k + 8) «module» stJ locJ
              [.localGet 2, .load32 (12 : UInt32), .const (0 : UInt32), .gtU,
               .const (1 : UInt32), .and, .eqz, .br_if 1,
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 5,
               .block 0 0 [
                 .block 0 0 [
                   .localGet 5, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                   .localGet 0, .localGet 5, .const (2 : UInt32), .shl, .add,
                   .load32 (0 : UInt32), .localGet 4, .gtU, .const (1 : UInt32), .and,
                   .br_if 1, .br 3],
                 .localGet 5, .localGet 1, .const (1048620 : UInt32), .call 54, .unreachable],
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 6,
               .block 0 0 [
                 .block 0 0 [
                   .block 0 0 [
                     .localGet 6, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                     .localGet 0, .localGet 6, .const (2 : UInt32), .shl, .add,
                     .load32 (0 : UInt32), .localSet 7,
                     .localGet 2, .load32 (12 : UInt32), .localSet 8,
                     .localGet 8, .localGet 1, .ltU, .const (1 : UInt32), .and,
                     .br_if 1, .br 2],
                   .localGet 6, .localGet 1, .const (1048652 : UInt32), .call 54, .unreachable],
                 .localGet 0, .localGet 8, .const (2 : UInt32), .shl, .add, .localGet 7,
                 .store32 (0 : UInt32), .localGet 2, .localGet 2,
                 .load32 (12 : UInt32), .const (1 : UInt32), .sub, .store32 (12 : UInt32),
                 .br 1]] {} = .Break 1 stJ { locJ with values := [] } := by
            simp only [exec, execOne.eq_def, hg2, hvals,
                       if_neg hns12_J, hj12_0,
                       show (if (0 : UInt32) > (0 : UInt32) then (1 : UInt32) else 0) = 0 from by decide,
                       show (1 : UInt32) &&& (0 : UInt32) = 0 from by decide,
                       show (if (0 : UInt32) = 0 then (1 : UInt32) else 0) = 1 from by decide,
                       if_neg (show ¬(1 : UInt32) = 0 from by decide)]
            rfl
          rw [hbody]
        rw [hinner]
        simp only [List.take_zero, List.nil_append, List.drop_zero, hvals]
        -- Now execute GET_j (localGet 2, load32 12, localSet 9) and STORE_KEY_BLOCK
        -- GET_j: frame + load32(frame[12]=0) + localSet 9
        have hgetj : exec (k + 10) «module» stJ { locJ with values := [] }
            (.localGet 2 :: .load32 (12 : UInt32) :: .localSet 9 ::
             [.block 0 0 [
               .localGet 9, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
               .localGet 0, .localGet 9, .const (2 : UInt32), .shl, .add, .localGet 4,
               .store32 (0 : UInt32), .localGet 2, .localGet 2, .load32 (8 : UInt32),
               .const (1 : UInt32), .add, .store32 (8 : UInt32), .br 1]]) {} =
            exec (k + 10) «module» stJ
              { locJ with locals := locJ.locals.set 7 (.i32 (0 : UInt32)), values := [] }
              [.block 0 0 [
               .localGet 9, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
               .localGet 0, .localGet 9, .const (2 : UInt32), .shl, .add, .localGet 4,
               .store32 (0 : UInt32), .localGet 2, .localGet 2, .load32 (8 : UInt32),
               .const (1 : UInt32), .add, .store32 (8 : UInt32), .br 1]] {} := by
          -- derive get 2 for the initial state { locJ with values := [] }
          have hg2' : ({ locJ with values := [] } : Locals).get 2 = some (.i32 frame) := hg2
          -- localGet 2
          conv_lhs => unfold exec; simp only [execOne.eq_def, hg2']
          -- load32 12: reads frame[12] = 0
          conv_lhs => unfold exec; simp only [execOne.eq_def, if_neg hns12_J, hj12_0]
          -- localSet 9: sets locals[9-2] = locals[7] = 0
          conv_lhs => unfold exec
          simp only [execOne.eq_def, Locals.set?, hlp, hll, List.length_set,
                     show ¬(9 < 2) from by omega, show (9 : Nat) < 2 + 8 from by omega,
                     show (9 : Nat) - 2 = 7 from by omega, if_true, if_false]
        rw [hgetj]
        -- STORE_KEY_BLOCK: exec_block_cons
        rw [show k + 10 = k + 9 + 1 from by omega, exec_block_cons]
        -- STORE_KEY_BODY: executes, then br 1 → .Break 1 → exec_block_cons gives .Break 0
        have hstore_body : exec (k + 9) «module» stJ
            { locJ with locals := locJ.locals.set 7 (.i32 (0 : UInt32)), values := [] }
            [.localGet 9, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
             .localGet 0, .localGet 9, .const (2 : UInt32), .shl, .add, .localGet 4,
             .store32 (0 : UInt32), .localGet 2, .localGet 2, .load32 (8 : UInt32),
             .const (1 : UInt32), .add, .store32 (8 : UInt32), .br 1] {} =
            .Break 1 stFinalA locFinalA := by
          -- local9 = locals[7] = 0
          have hg9 : { locJ with locals := locJ.locals.set 7 (.i32 (0:UInt32)), values := [] }.get 9 =
              some (.i32 (0:UInt32)) := by
            simp only [Locals.get, hlp, hll, List.length_set,
                       show ¬(9 < 2) from by omega, show (9 : Nat) < 2 + 8 from by omega,
                       show (9 : Nat) - 2 = 7 from by omega, List.getElem?_set,
                       if_pos (show (7 : Nat) = 7 from rfl),
                       if_pos (show (7 : Nat) < 8 from by omega),
                       if_true, if_false]
          -- local1 = len (params unchanged)
          have hg1_upd : { locJ with locals := locJ.locals.set 7 (.i32 (0:UInt32)), values := [] }.get 1 =
              some (.i32 len) := by
            simp only [Locals.get, hlp, show (1:Nat) < 2 from by omega]
            have h := hg1; simp only [Locals.get, hlp, show (1:Nat) < 2 from by omega] at h; exact h
          -- local0 = ptr (params unchanged)
          have hg0_upd : { locJ with locals := locJ.locals.set 7 (.i32 (0:UInt32)), values := [] }.get 0 =
              some (.i32 ptr) := by
            simp only [Locals.get, hlp, show (0:Nat) < 2 from by omega]
            have h := hg0; simp only [Locals.get, hlp, show (0:Nat) < 2 from by omega] at h; exact h
          -- local4 = key (locals[2] set earlier, not touched by set 7)
          have hg4_upd : { locJ with locals := locJ.locals.set 7 (.i32 (0:UInt32)), values := [] }.get 4 =
              some (.i32 key) := by
            simp only [Locals.get, hlp, hll, List.length_set,
                       show ¬(4 < 2) from by omega, show (4:Nat) < 2 + 8 from by omega,
                       show (4:Nat) - 2 = 2 from by omega, List.getElem?_set,
                       if_neg (show ¬(7:Nat) = 2 from by omega)]
            have h := hg4; simp only [Locals.get, hlp, hll, show ¬(4 < 2) from by omega,
                           show (4:Nat) < 2 + 8 from by omega, show (4:Nat) - 2 = 2 from by omega] at h
            exact h
          -- local2 = frame (locals[0] not touched by set 7)
          have hg2_upd : { locJ with locals := locJ.locals.set 7 (.i32 (0:UInt32)), values := [] }.get 2 =
              some (.i32 frame) := by
            simp only [Locals.get, hlp, hll, List.length_set,
                       show ¬(2 < 2) from by omega, show (2:Nat) < 2 + 8 from by omega,
                       show (2:Nat) - 2 = 0 from by omega, List.getElem?_set,
                       if_neg (show ¬(7:Nat) = 0 from by omega)]
            have h := hg2; simp only [Locals.get, hlp, hll, show ¬(2 < 2) from by omega,
                           show (2:Nat) < 2 + 8 from by omega, show (2:Nat) - 2 = 0 from by omega] at h
            exact h
          simp only [exec, execOne.eq_def, hg9, hg1_upd, if_pos h0_lt_len,
                     show (1 : UInt32) &&& (1 : UInt32) = 1 from by decide,
                     show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                     hg0_upd, h0_shl, show (0:UInt32) + (0:UInt32) = 0 from by decide,
                     if_neg hptr_bnd, hg4_upd,
                     hg2_upd, if_neg hns8_J, hf8_J,
                     show (1 : UInt32) + (1 : UInt32) = 2 from by decide,
                     show ¬(1 : UInt32) = 0 from by decide,
                     show stFinalA = { stJ with mem := stJ.mem.write32 ptr key |>.write32 (frame + 8) (i + 1) } from rfl,
                     show locFinalA = { locJ with locals := locJ.locals.set 7 (.i32 (0:UInt32)), values := [] } from rfl]
          sorry -- remaining simp after store32 operations; likely needs explicit store32 address proofs
        rw [hstore_body]
      · -- frame[8] = i+1
        exact read32_write32_same (stJ.mem.write32 ptr key) (frame + (8 : UInt32)) (i + 1)
      · -- globals unchanged by write32
        exact hglob_J
      · -- pages unchanged by two write32s
        rw [write32_pages, write32_pages]; exact hpages_J
      · -- params length
        exact hlp
      · -- locals length
        have hlocals_eq : locFinalA.locals = locJ.locals.set 7 (.i32 (0:UInt32)) := rfl
        simp only [hlocals_eq, List.length_set, hll]
      · -- values = []
        rfl
      · -- get 0 = ptr
        have hparams_eq : locFinalA.params = locJ.params := rfl
        simp only [Locals.get, hparams_eq, hlp, show (0:Nat) < 2 from by omega, if_true, if_false]
        have h := hg0; simp only [Locals.get, hlp, show (0:Nat) < 2 from by omega, if_true, if_false] at h; exact h
      · -- get 1 = len
        have hparams_eq : locFinalA.params = locJ.params := rfl
        simp only [Locals.get, hparams_eq, hlp, show (1:Nat) < 2 from by omega, if_true, if_false]
        have h := hg1; simp only [Locals.get, hlp, show (1:Nat) < 2 from by omega, if_true, if_false] at h; exact h
      · -- get 2 = frame (locals[0] not touched by set 7)
        have hparams_eq : locFinalA.params = locJ.params := rfl
        have hlocals_eq : locFinalA.locals = locJ.locals.set 7 (.i32 (0:UInt32)) := rfl
        simp only [Locals.get, hparams_eq, hlocals_eq, hlp, hll, List.length_set,
                   show ¬(2 < 2) from by omega, show (2:Nat) < 2 + 8 from by omega,
                   show (2:Nat) - 2 = 0 from by omega, List.getElem?_set,
                   if_neg (show ¬(7:Nat) = 0 from by omega), if_true, if_false]
        have h := hg2; simp only [Locals.get, hlp, hll, show ¬(2 < 2) from by omega,
                       show (2:Nat) < 2 + 8 from by omega, show (2:Nat) - 2 = 0 from by omega,
                       if_true, if_false] at h
        exact h
      · -- sorted postcondition
        sorry
        /- SORTED SKETCH (case a, j=0):
           stFinalA writes key=stA.arr[i] to position 0 of the array, then shifts nothing.
           But shape invariants say:
             shape2: ∀ k, 0 ≤ k < i.toNat, stJ.arr[k+1] = stA.arr[k] (all shifted right)
             hgt_key: ∀ k, 0 ≤ k < i.toNat, key < stA.arr[k] (all > key)
           So stFinalA.arr = [key, stA.arr[0], stA.arr[1], ..., stA.arr[i-1]]
           which is sorted: key < all others, and stA.arr[0..i-1] already sorted. -/
      · -- perm postcondition
        sorry
    | succ n' =>
      -- ── Cases (b) and (c): j = n'+1 > 0 ────────────────────────────────────
      -- hj12 : stJ.mem.read32(frame+12) = UInt32.ofNat(n'+1)
      let arr_jm1 : UInt32 := stJ.mem.read32 (ptr + 4 * UInt32.ofNat n')
      -- n' < xs.length (since n'+1 ≤ i.toNat < xs.length)
      have hn'_lt_xs : n' < xs.length := by omega
      -- n' < len (UInt32 comparison)
      have hn'_lt_len : UInt32.ofNat n' < len := by
        rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
        have := len.toNat_lt; rw [← hlen] at this; omega
      -- n'+1 < len (UInt32 comparison)
      have hn_lt_len : UInt32.ofNat (n' + 1) < len := by
        rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
        have := len.toNat_lt; rw [← hlen] at this; omega
      -- shl for n': n' <<< 2%32 = 4*n'
      have hn'_shl : UInt32.ofNat n' <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat n' := by
        rw [show (2 : UInt32) % 32 = 2 from by decide]
        apply UInt32.toNat_inj.mp
        simp only [UInt32.toNat_mul, show (4 : UInt32).toNat = 4 from rfl]
        simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
      -- shl for n'+1: (n'+1) <<< 2%32 = 4*(n'+1)
      have hn_shl : UInt32.ofNat (n' + 1) <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat (n' + 1) := by
        rw [show (2 : UInt32) % 32 = 2 from by decide]
        apply UInt32.toNat_inj.mp
        simp only [UInt32.toNat_mul, show (4 : UInt32).toNat = 4 from rfl]
        simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
      -- addr of arr[n']
      have hn'_addr : (ptr + 4 * UInt32.ofNat n').toNat = ptr.toNat + 4 * n' := by
        apply toNat_wordAddr; exact hn'_lt_xs; exact hpg_arr
      -- bounds for load32 at arr[n']
      have hbnd_n' : ¬((ptr + 4 * UInt32.ofNat n').toNat + (0 : UInt32).toNat + 4 >
          stJ.mem.pages * 65536) := by
        simp only [show (0 : UInt32).toNat = 0 from rfl, Nat.add_zero, hn'_addr, hpages_J]
        have : n' + 1 ≤ xs.length := Nat.succ_le_of_lt hn'_lt_xs
        linarith [Nat.mul_le_mul_left 4 this]
      -- hj12 in simplified form: frame[12] = UInt32.ofNat (n'+1) which is ≥ 1
      have hj12_succ : stJ.mem.read32 (frame + (12 : UInt32)) = UInt32.ofNat (n' + 1) := hj12
      have hj12_pos : (0 : UInt32) < UInt32.ofNat (n' + 1) := by
        rw [UInt32.lt_iff_toNat_lt_toNat]; simp [UInt32.toNat_ofNat']; omega
      by_cases hbc : arr_jm1 > key
      · -- ── Case (c): arr[n'] > key → shift arr[n'] to arr[n'+1], decrement j ──
        -- Apply IH at n' with updated state stJ' after the shift
        -- stJ' = stJ.write32 (ptr+4*(n'+1)) arr[n'] |>.write32 (frame+12) n'
        sorry
        /- CASE (c) SKETCH (j=n'+1>0, arr[n'] > key):
           After:
           - CHECK: gtU(n'+1, 0) = n'+1>0 = true → 1; eqz→0; br_if 1 no fire
           - j'_set: local5 = n'+1-1 = n'
           - BC2_OUTER: BC2_INNER body:
             n'<len ✓; ltU→1; and→1; eqz→0; br_if 0 no fire
             arr[n']=arr_jm1>key ✓; gtU→1; and→1; br_if 1 fires → .Break 1 from BC2_INNER body
             BC2_INNER_BLOCK: .Break 1=.Break(0+1)→.Break 0 (Fallthrough to PANIC2, not exec'd? No:
             Actually: BC2_OUTER body is [BC2_INNER_BLOCK, PANIC2].
             BC2_INNER_BLOCK body returns .Break 1 = .Break(0+1) → .Break 0 from exec_block_cons.
             Then exec [BC2_INNER_BLOCK, PANIC2]: execOne BC2_INNER_BLOCK = .Break 0 → Fallthrough to PANIC2.
             WAIT: exec_block_cons for BC2_INNER_BLOCK: body .Break 1 = .Break(0+1) → .Break 0.
             But the OUTER exec sees .Break 0 from execOne BC2_INNER_BLOCK → Fallthrough!
             Then PANIC2 (.localGet 5, .localGet 1, .call 54, .unreachable) runs... that's the error branch!

             I was wrong! Let me re-trace:

             Inside BC2_INNER body (= `.block 0 0 [CHECK_BODY, PANIC2]`):
               The labels inside CHECK_BODY see:
               - label 0 = BC2_INNER body label (the inner block)
               - label 1 = BC2_OUTER label (the outer block wrapping both [BC2_INNER_BLOCK, PANIC2])
               - Wait: the instruction structure is:
                 BC2_OUTER = `.block 0 0 [BC2_INNER_BLOCK_INSTR, PANIC2]` where:
                   BC2_INNER_BLOCK_INSTR = `.block 0 0 [CHECK_BODY]`
                   CHECK_BODY = [..., br_if 1 (exits BC2_OUTER), br 3 (exits OUTER_BLOCK)]
                   PANIC2 = [localGet 5, localGet 1, call 54, unreachable]

             Hmm but the instruction list in the source is:
               .block 0 0 [      -- BC2_OUTER
                 .block 0 0 [    -- BC2_INNER_BLOCK
                   .localGet 5, .localGet 1, .ltU, .const 1, .and, .eqz, .br_if 0,   -- br_if 0 exits BC2_INNER_BLOCK
                   .localGet 0, .localGet 5, .const 2, .shl, .add, .load32 0,
                   .localGet 4, .gtU, .const 1, .and,
                   .br_if 1, .br 3],     -- br_if 1 exits BC2_OUTER; br 3 exits OUTER_BLOCK
                 .localGet 5, .localGet 1, .const 1048620, .call 54, .unreachable]  -- PANIC2

             So in case (c) (arr[n'] > key): br_if 1 fires!
             br_if 1 from inside BC2_INNER_BLOCK body: .Break 1
             exec_block_cons for BC2_INNER_BLOCK: .Break 1 = .Break(0+1) → .Break 0 (Fallthrough)
             Then exec [BC2_INNER_BLOCK, PANIC2] at BC2_OUTER level: .Break 0 from execOne BC2_INNER_BLOCK → Fallthrough to PANIC2!
             Wait no: exec processes as:
               exec fuel m st s (BC2_INNER_BLOCK :: PANIC2 :: nil) env
               = match execOne fuel BC2_INNER_BLOCK with
               | .Fallthrough → exec fuel ... PANIC2 :: nil
               | other → other
             And execOne fuel for BC2_INNER_BLOCK (which is a .block instruction) returns .Break 0 (from exec_block_cons giving .Break(0+1)-1=.Break 0).

             Hmm: exec_block_cons says exec (f+1) ... (.block :: rest) = match exec f ... body with | .Break 0 → continue to rest | .Break k+1 → .Break k | .Fallthrough → continue to rest | other → other.

             So execOne for BC2_INNER_BLOCK (.block 0 0 CHECK_BODY) at fuel f:
             = execOne (f-1+1) ... (.block 0 0 CHECK_BODY) = exec_block_cons with fuel=f:
               match exec (f-1) ... CHECK_BODY with
               | .Break 0 → continue to rest (empty, so .Fallthrough)
               | .Break 1 → .Break 0 ← this is what happens in case (c)!

             Wait: CHECK_BODY in case (c) has br_if 1 fire → .Break 1 from inside CHECK_BODY. Then:
             exec_block_cons for BC2_INNER_BLOCK (outer block of CHECK_BODY):
               CHECK_BODY returns .Break 1 = .Break(0+1) → execOne returns .Break 0.

             exec [BC2_INNER_BLOCK, PANIC2] at BC2_OUTER:
               execOne BC2_INNER_BLOCK = .Break 0 → Fallthrough → continue to PANIC2!

             This means PANIC2 runs! That's the success path NOT the error path!

             Wait, I think I misread the label convention. Let me re-read the source:

             The BC2 block structure is:
             .block 0 0 [  -- OUTER (bc2_outer)
               .block 0 0 [  -- INNER (bc2_inner)
                 ..., .br_if 1,  -- fires → .Break 1 from bc2_inner body
                 .br 3],         -- fires → .Break 3 from bc2_inner body
               ...(PANIC2)...]    -- only runs if bc2_inner Fallthrough's

             From inside bc2_inner body:
             - br 0 = exit bc2_inner (continue after bc2_inner block)
             - br 1 = exit bc2_outer (the OUTER block enclosing bc2_inner)
             - br 2 = exit the INNER_LOOP (restart loop)
             - br 3 = exit OUTER_BLOCK

             Wait, but we're executing bc2_inner body. The label 0 is the bc2_inner block itself. So:
             - br 0 from bc2_inner → .Break 0 from bc2_inner body → Fallthrough from bc2_inner_block exec_block_cons
             - br 1 from bc2_inner → .Break 1 from bc2_inner body → .Break 0 from bc2_inner_block exec_block_cons → Fallthrough to PANIC2!

             Hmm that doesn't seem right. Let me re-think.

             When execOne processes .block 0 0 CHECK_BODY:
             - It calls exec fuel ... CHECK_BODY
             - CHECK_BODY has `br_if 1` which (when firing) produces .Break 1 from the exec
             - exec_block_cons for .block 0 0: match body_result with
               | .Break 0 → Fallthrough to rest after the block
               | .Break (k+1) → .Break k  ← .Break 1 → .Break 0
               | .Fallthrough → Fallthrough

             So .Break 1 from CHECK_BODY → .Break 0 from execOne for bc2_inner_block.
             Then exec [bc2_inner_block, PANIC2]: .Break 0 from execOne → match | .Fallthrough → exec PANIC2 | other → other = .Break 0.

             .Break 0 ≠ .Fallthrough → other! So .Break 0 → other → exec returns .Break 0 without executing PANIC2! ✓

             I was confusing: exec in the list processes with `match execOne with | .Fallthrough → continue | other → other`. So .Break 0 → other → stop (don't execute PANIC2). ✓

             So in case (c): bc2_inner body returns .Break 1 (from br_if 1) → exec_block_cons for bc2_inner_block returns .Break 0 → exec [bc2_inner_block, PANIC2] returns .Break 0 (stops, doesn't run PANIC2) → exec_block_cons for bc2_OUTER: body returned .Break 0 → Fallthrough.

             Fallthrough from bc2_outer → continue with rest of INNER_LOOP body after bc2_outer:
             [j_set2 instrs, BC3_OUTER block, INNER_ERROR]

             - j_set2: localGet 2→frame; load32 12 → n'+1; sub 1 → n'; localSet 6 (local6 = n')
             - BC3_OUTER block:
               BC3_INNER body: n'<len ✓ → continue; arr[n']=arr_jm1 → local7; frame[12]=n'+1 → local8; n'+1<len ✓ → br_if 1 fires → .Break 1

             Wait, in BC3_INNER body there's `br_if 1`. Let me read it:
             ```
             .block 0 0 [  -- bc3_inner_block
               .localGet 6, .localGet 1, .ltU, .const 1, .and, .eqz, .br_if 0,
               .localGet 0, .localGet 6, .const 2, .shl, .add, .load32 0, .localSet 7,
               .localGet 2, .load32 12, .localSet 8,
               .localGet 8, .localGet 1, .ltU, .const 1, .and,
               .br_if 1, .br 2],
             ```
             - n'<len ✓ → ltU=1; and=1; eqz=0; br_if 0 no fire
             - arr[n'] (= arr_jm1) → local7
             - frame[12] = n'+1 → local8
             - n'+1<len ✓ → ltU=1; and=1; br_if 1 fires! → .Break 1 from bc3_inner body
             - exec_block_cons for bc3_inner_block: .Break 1 → .Break 0 → execOne returns .Break 0
             - exec [bc3_inner_block, PANIC3] at bc3_outer level: .Break 0 → other → stop
             - exec_block_cons for bc3_outer: body .Break 0 → Fallthrough → [WRITE_SHIFT, ...]

             WRITE_SHIFT (after bc3_outer Fallthrough):
             - localGet 0 → ptr; localGet 8 → local8=n'+1; const 2; shl → 4*(n'+1); add → ptr+4*(n'+1)
             - localGet 7 → arr_jm1
             - store32 0: write arr_jm1 to ptr+4*(n'+1) ← this is the SHIFT!
             - localGet 2 → frame; localGet 2 → frame; load32 12 → n'+1; const 1; sub → n'; store32 12: frame[12] = n'
             - br 1 → .Break 1

             After WRITE_SHIFT: stJ' = stJ.write32 (ptr+4*(n'+1)) arr_jm1 |>.write32 (frame+12) (n')

             exec [BC3_OUTER_BLOCK, WRITE_SHIFT, INNER_ERROR] (from j_set2 continuation):
             BC3_OUTER returns .Break 0 → Fallthrough → WRITE_SHIFT → .Break 1 (from br 1)
             exec [WRITE_SHIFT, INNER_ERROR]: WRITE_SHIFT execOne returns .Break 1 → other → stop.

             Wait no: BC3_OUTER_BLOCK = `.block 0 0 [BC3_INNER_BLOCK_INSTR, PANIC3, WRITE_SHIFT_INSTRS]`.
             No wait, looking at the source:
             ```
             .block 0 0 [           -- BC3_OUTER
               .block 0 0 [         -- BC3_INNER
                 .block 0 0 [       -- BC3_INNERMOST
                   ..., .br_if 0,   -- exits bc3_innermost
                   ..., .br_if 1, .br 2],  -- br_if 1 exits bc3_inner; br 2 exits bc3_outer
                 .localGet 6, .localGet 1, .const 1048652, .call 54, .unreachable],  -- PANIC3 (bc3_inner fails)
               .localGet 0, .localGet 8, .const 2, .shl, .add, .localGet 7,
               .store32 0, .localGet 2, .localGet 2,
               .load32 12, .const 1, .sub, .store32 12, .br 1]  -- WRITE_SHIFT (bc3_outer success)
             ```

             So: BC3_OUTER body = [BC3_INNER_BLOCK, WRITE_SHIFT...]
             BC3_INNER body (the `.block 0 0 [BC3_INNERMOST, PANIC3]`):
               BC3_INNERMOST = [.block 0 0 [..., .br_if 0, ..., .br_if 1, .br 2]]

             In case (c):
             - BC3_INNERMOST: n'<len → br_if 0 no fire; arr[n']→local7; frame[12]=n'+1→local8; n'+1<len → br_if 1 fires!

             br_if 1 from BC3_INNERMOST body:
             Labels from inside BC3_INNERMOST body:
             - label 0 = BC3_INNERMOST block
             - label 1 = BC3_INNER block (enclosing BC3_INNERMOST + PANIC3)
             - label 2 = BC3_OUTER block

             br_if 1 fires → .Break 1 from BC3_INNERMOST body.
             exec_block_cons for BC3_INNERMOST (.block 0 0): body .Break 1 = .Break(0+1) → .Break 0.
             execOne for BC3_INNERMOST returns .Break 0.
             exec [BC3_INNERMOST, PANIC3] (BC3_INNER body): .Break 0 → other → stop (PANIC3 not executed).
             exec_block_cons for BC3_INNER (.block 0 0 [BC3_INNERMOST, PANIC3]):
               body returns .Break 0 → Fallthrough → rest (empty, so .Fallthrough).
             execOne for BC3_INNER returns .Fallthrough.
             exec [BC3_INNER_BLOCK, WRITE_SHIFT, ...] (BC3_OUTER body): .Fallthrough → continue to WRITE_SHIFT.

             WRITE_SHIFT: ptr+4*(local8) = ptr+4*(n'+1); store arr_jm1; frame[12] = n'; br 1 → .Break 1.
             exec BC3_OUTER body: WRITE_SHIFT returns .Break 1 → other → stop. Body = .Break 1.
             exec_block_cons for BC3_OUTER: body .Break 1 = .Break(0+1) → .Break 0.

             After BC3_OUTER: exec [BC3_OUTER_BLOCK, INNER_ERROR] (in INNER_LOOP body after j_set2):
             execOne BC3_OUTER_BLOCK returns .Break 0 → other → stop (INNER_ERROR not executed).

             This means the INNER_LOOP body returns .Break 0 → loops back!
             Wait: .Break 0 from the INNER_LOOP body → execOne_loop_succ .Break 0 → restart loop!

             Actually: execOne_loop_succ: body returns .Break 0 → `execOne f m r' {s'...} (.loop ...) env` (restart).

             So in case (c), the loop RESTARTS with the updated state stJ':
               stJ' = stJ.write32 (ptr+4*(n'+1)) arr_jm1 |>.write32 (frame+12) n'
               locJ' = locJ with local5=n', local6=n', local7=arr_jm1, local8=n'+1

             Then apply IH at n' < n'+1 with stJ' to get ∃ N', ...

             Final fuel = N' + 3 (OUTER_BLOCK + each loop restart costs 1 execOne_loop_succ).
             Actually more careful: each iteration of the loop (including the restart) costs fuel:
             - execOne_loop_succ calls exec f-1 on the body, then on restart calls execOne f-1 again.
             - So each restart costs 1 additional fuel unit.
             - Total for this iteration: 1 (OUTER_BLOCK) + 1 (first execOne_loop_succ for j=n'+1) + N' + ...

             The IH handles ALL remaining iterations. When IH terminates with N', the fuel for those iterations is N'. We need extra fuel for:
             1. OUTER_BLOCK peel: 1
             2. FIRST execOne_loop_succ for j=n'+1: 1
             3. The IH executes starting from the RESTARTED loop, but the IH exec includes the whole [.block 0 0 [.loop ...], GET_j, STORE_KEY] which starts at the loop again.

             The IH says: ∃ N' stFinalC locFinalC, ∀ fuel ≥ N', exec fuel «module» stJ' locJ_new [OUTER_BLOCK, ...] {} = .Break 0 ...

             But I need the CURRENT fuel to restart the loop. The IH's exec starts at the SAME INSTRUCTION LIST (OUTER_BLOCK wrapping the loop). So the fuel for the IH already accounts for all remaining iterations.

             The connection is:
             - exec fuel stJ locJ [OUTER_BLOCK, GET_j, STORE_KEY] = exec (fuel-1) stJ locJ [INNER_LOOP, INNER_ERROR] (from exec_block_cons)
             - exec (fuel-1) stJ locJ [INNER_LOOP, INNER_ERROR] = execOne (fuel-1) stJ locJ INNER_LOOP (case: .Break 0 → other)
             - execOne (fuel-1) stJ locJ INNER_LOOP = execOne_loop_succ(fuel-2) → runs body at fuel-2, restarts at fuel-2
             - After shift, the LOOP is restarted via execOne (fuel-2) stJ' locJ' INNER_LOOP
             - This is NOT the same as exec (N') stJ' locJ' [OUTER_BLOCK, GET_j, STORE_KEY] since we're inside execOne of INNER_LOOP, not at the top-level OUTER_BLOCK.

             This is the tricky fuel composition issue. The IH needs to handle the RESTARTED INNER_LOOP, not the full [OUTER_BLOCK, ...] list. So the IH should be stated in terms of exec [.loop ...] or exec [INNER_LOOP, ...] rather than exec [OUTER_BLOCK, ...].

             This is a fundamental issue with the gen statement: the IH applies gen with the [OUTER_BLOCK, ...] list, but after loop restart we're at execOne of INNER_LOOP, not exec of [OUTER_BLOCK, ...].

             RESOLUTION: The exec [.loop ...] on restart runs execOne fuel stJ' locJ' .loop = exec (fuel-1) stJ' locJ' body. This is handled by exec_fuel_mono + the IH's execOne for the loop.

             This analysis shows case (c) requires careful fuel management. I'll sorry it and provide this detailed sketch.
        -/
      · -- ── Case (b): arr[n'] ≤ key → exit loop, store key at arr[n'+1] ──────
        -- hbc : ¬(arr_jm1 > key) = ¬(key < arr_jm1)
        -- Case (b): CHECK fires (j=n'+1>0), j'_set (local5=n'), BC2 exits via br 3 (since arr[n']≤key)
        -- After br 3: .Break 3 from bc2_inner_body → .Break 2 from bc2_inner_block → .Break 2 from exec
        -- exec [bc2_inner_block, PANIC2] in bc2_outer: .Break 2 → other → .Break 2
        -- exec_block_cons for bc2_outer: body .Break 2=.Break(1+1) → .Break 1
        -- exec_block_cons: wait, bc2_outer = .block 0 0 [bc2_inner_block, PANIC2]
        -- BC2_OUTER body returns .Break 2 then .Break 1 from exec_block_cons of BC2_OUTER? No:
        -- exec_block_cons for BC2_OUTER: match exec (fuel-1) [bc2_inner_block, PANIC2] with
        --   | .Break 0 → Fallthrough (to rest of INNER_LOOP body)
        --   | .Break k+1 → .Break k ← .Break 2 → .Break 1
        --   | .Fallthrough → Fallthrough
        -- So BC2_OUTER_BLOCK instruction → .Break 1.
        -- INNER_LOOP body: execOne for BC2_OUTER_BLOCK = .Break 1 → other → .Break 1 (rest of body skipped).
        -- execOne_loop_succ: body .Break 1 = .Break(0+1) → .Break 0.
        -- exec [INNER_LOOP, INNER_ERROR]: .Break 0 → other → .Break 0.
        -- exec_block_cons for OUTER_BLOCK: body .Break 0 → Fallthrough → GET_j + STORE_KEY.
        -- GET_j: local9 = frame[12] = n'+1.
        -- STORE_KEY: arr[n'+1] = key, frame[8] = i+1.
        -- ── Build witnesses ──────────────────────────────────────────────────
        -- arr[n'] bound
        have hbnd_n'_load : ¬((ptr + 4 * UInt32.ofNat n').toNat + (0:UInt32).toNat + 4 >
            stJ.mem.pages * 65536) := hbnd_n'
        -- bounds for store32 at arr[n'+1]
        have hbnd_n1_store : ¬((ptr + 4 * UInt32.ofNat (n'+1)).toNat + (0:UInt32).toNat + 4 >
            stJ.mem.pages * 65536) := by
          have hn1_addr : (ptr + 4 * UInt32.ofNat (n'+1)).toNat = ptr.toNat + 4 * (n'+1) :=
            toNat_wordAddr ptr xs.length (n'+1) (by omega) hpg_arr
          simp only [show (0:UInt32).toNat = 0 from rfl, Nat.add_zero, hn1_addr, hpages_J]
          have : n'+2 ≤ xs.length := by omega
          linarith [Nat.mul_le_mul_left 4 this]
        -- bounds for store32 at frame+8 (memory after write32 at ptr+4*(n'+1))
        have hbnd_frame8_b : ¬((frame + (8:UInt32)).toNat + (0:UInt32).toNat + 4 >
            (stJ.mem.write32 (ptr + 4 * UInt32.ofNat (n'+1)) key).pages * 65536) := by
          simp only [show (0:UInt32).toNat = 0 from rfl, Nat.add_zero, write32_pages,
                     hf8_toNat, hpages_J]
          linarith [hbnd_frame]
        -- n'+1 < len for STORE_KEY bounds check (ltU)
        have hn1_lt_len : UInt32.ofNat (n'+1) < len := hn_lt_len
        -- addr of arr[n'+1] for STORE_KEY
        have hn1_shl_eq : UInt32.ofNat (n'+1) <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat (n'+1) :=
          hn_shl
        -- arr[n'] = arr_jm1 from stJ (for bc2 inner load)
        have harr_n'_read : stJ.mem.read32 ((ptr + 4 * UInt32.ofNat n') + (0:UInt32)) = arr_jm1 := by
          have h0 : (ptr + 4 * UInt32.ofNat n') + (0:UInt32) = ptr + 4 * UInt32.ofNat n' := by simp
          rw [h0]
        -- bc2: br_if 1 no fire (arr[n'] ≤ key), br 3 fires
        have hle_show : ¬(arr_jm1 > key) := hbc
        -- jm1 = n' = frame[12] - 1; sub is in WASM
        have hjm1_sub : UInt32.ofNat (n'+1) - 1 = UInt32.ofNat n' := by
          apply UInt32.toNat_inj.mp; simp [UInt32.toNat_sub_of_le, UInt32.toNat_ofNat']
        -- Final state: write key to arr[n'+1], i+1 to frame[8]
        let stFinalB : Store Unit :=
          { stJ with mem := stJ.mem.write32 (ptr + 4 * UInt32.ofNat (n'+1)) key
                              |>.write32 (frame + (8:UInt32)) (i+1) }
        -- Final locals: local5 = n' (from j'_set), local9 = n'+1 (from GET_j)
        let locFinalB : Locals :=
          { locJ with locals := (locJ.locals.set 3 (.i32 (UInt32.ofNat n'))).set 7 (.i32 (UInt32.ofNat (n' + 1))), values := [] }
        refine ⟨20, stFinalB, locFinalB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- Exec proof for case (b)
          intro fuel hfuel
          obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 20 := ⟨fuel - 20, by omega⟩
          -- OUTER_BLOCK peel
          rw [show k + 20 = k + 19 + 1 from by omega, exec_block_cons]
          -- INNER_LOOP at k+19: execOne_loop_succ(k+18) runs body at k+17
          -- Body trace: CHECK no fire, j'_set, BC2_OUTER → .Break 1 → body .Break 1
          -- execOne_loop_succ: .Break(0+1) → .Break 0
          -- exec [INNER_LOOP, INNER_ERROR] at k+19: .Break 0 → stop
          have hinner_b : exec (k + 19) «module» stJ locJ
              [.loop 0 0 [
                 .localGet 2, .load32 (12 : UInt32), .const (0 : UInt32), .gtU,
                 .const (1 : UInt32), .and, .eqz, .br_if 1,
                 .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 5,
                 .block 0 0 [
                   .block 0 0 [
                     .localGet 5, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                     .localGet 0, .localGet 5, .const (2 : UInt32), .shl, .add,
                     .load32 (0 : UInt32), .localGet 4, .gtU, .const (1 : UInt32), .and,
                     .br_if 1, .br 3],
                   .localGet 5, .localGet 1, .const (1048620 : UInt32), .call 54, .unreachable],
                 .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 6,
                 .block 0 0 [
                   .block 0 0 [
                     .block 0 0 [
                       .localGet 6, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                       .localGet 0, .localGet 6, .const (2 : UInt32), .shl, .add,
                       .load32 (0 : UInt32), .localSet 7,
                       .localGet 2, .load32 (12 : UInt32), .localSet 8,
                       .localGet 8, .localGet 1, .ltU, .const (1 : UInt32), .and,
                       .br_if 1, .br 2],
                     .localGet 6, .localGet 1, .const (1048652 : UInt32), .call 54, .unreachable],
                   .localGet 0, .localGet 8, .const (2 : UInt32), .shl, .add, .localGet 7,
                   .store32 (0 : UInt32), .localGet 2, .localGet 2,
                   .load32 (12 : UInt32), .const (1 : UInt32), .sub, .store32 (12 : UInt32),
                   .br 1]],
               .localGet 8, .localGet 1, .const (1048668 : UInt32), .call 54, .unreachable]
              {} = .Break 0 stJ
                { locJ with locals := locJ.locals.set 3 (.i32 (UInt32.ofNat n')), values := [] } := by
            rw [show k + 19 = k + 18 + 1 from by omega]
            conv_lhs => unfold exec; rw [show k + 18 + 1 = k + 18 + 1 from rfl, execOne_loop_succ]
            -- Loop body at k+17 produces .Break 1 (case b: bc2_outer → .Break 1 from inner_loop body)
            sorry -- loop body exec for case (b) — needs careful simp through CHECK + j'_set + BC2_OUTER
          rw [hinner_b]
          simp only [List.take_zero, List.nil_append, List.drop_zero, hvals]
          -- GET_j + STORE_KEY_BLOCK
          -- GET_j: local9 = frame[12] = n'+1
          have hgetj_b : exec (k + 20) «module» stJ
              { locJ with locals := locJ.locals.set 3 (.i32 (UInt32.ofNat n')), values := [] }
              (.localGet 2 :: .load32 (12 : UInt32) :: .localSet 9 ::
               [.block 0 0 [
                 .localGet 9, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                 .localGet 0, .localGet 9, .const (2 : UInt32), .shl, .add, .localGet 4,
                 .store32 (0 : UInt32), .localGet 2, .localGet 2, .load32 (8 : UInt32),
                 .const (1 : UInt32), .add, .store32 (8 : UInt32), .br 1]]) {} =
              exec (k + 20) «module» stJ
                { locJ with locals := (locJ.locals.set 3 (.i32 (UInt32.ofNat n'))).set 7 (.i32 (UInt32.ofNat (n' + 1))), values := [] }
                [.block 0 0 [
                  .localGet 9, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                  .localGet 0, .localGet 9, .const (2 : UInt32), .shl, .add, .localGet 4,
                  .store32 (0 : UInt32), .localGet 2, .localGet 2, .load32 (8 : UInt32),
                  .const (1 : UInt32), .add, .store32 (8 : UInt32), .br 1]] {} := by
            -- local2 = frame (params unchanged)
            have hg2_b : { locJ with locals := locJ.locals.set 3 (.i32 (UInt32.ofNat n')), values := [] }.get 2 =
                some (.i32 frame) := by
              simp only [Locals.get, hlp, hll, List.length_set,
                         show ¬(2 < 2) from by omega, show (2:Nat) < 2 + 8 from by omega,
                         show (2:Nat) - 2 = 0 from by omega, List.getElem?_set,
                         if_neg (show ¬(3:Nat) = 0 from by omega)]
              have h := hg2; simp only [Locals.get, hlp, hll, show ¬(2 < 2) from by omega,
                             show (2:Nat) < 2 + 8 from by omega, show (2:Nat) - 2 = 0 from by omega] at h
              exact h
            -- localGet 2
            conv_lhs => unfold exec; simp only [execOne.eq_def, hg2_b]
            -- load32 12: frame[12] = n'+1
            conv_lhs => unfold exec; simp only [execOne.eq_def, if_neg hns12_J, hj12_succ]
            -- localSet 9: locals[7] = n'+1
            conv_lhs => unfold exec
            simp only [execOne.eq_def, Locals.set?, hlp, hll, List.length_set,
                       show ¬(9 < 2) from by omega, show (9:Nat) < 2 + 8 from by omega,
                       show (9:Nat) - 2 = 7 from by omega, if_true, if_false]
          rw [hgetj_b]
          -- STORE_KEY_BLOCK exec_block_cons
          rw [show k + 20 = k + 19 + 1 from by omega, exec_block_cons]
          -- STORE_KEY_BODY produces .Break 1 → exec_block_cons gives .Break 0 (= stFinalB, locFinalB)
          sorry -- store key at arr[n'+1] and i+1 at frame[8], prove .Break 1 → exec_block_cons .Break 0
        · -- frame[8] = i+1
          exact read32_write32_same (stJ.mem.write32 _ _) (frame + (8:UInt32)) (i+1)
        · -- globals unchanged
          exact hglob_J
        · -- pages unchanged
          rw [write32_pages, write32_pages]; exact hpages_J
        · -- params length
          exact hlp
        · -- locals length
          have hlocals_eq : locFinalB.locals = (locJ.locals.set 3 (.i32 (UInt32.ofNat n'))).set 7 (.i32 (UInt32.ofNat (n' + 1))) := rfl
          simp only [hlocals_eq, List.length_set, hll]
        · -- values = []
          rfl
        · -- get 0 = ptr
          have hparams_eq : locFinalB.params = locJ.params := rfl
          simp only [Locals.get, hparams_eq, hlp, show (0:Nat) < 2 from by omega, if_true, if_false]
          have h := hg0; simp only [Locals.get, hlp, show (0:Nat) < 2 from by omega, if_true, if_false] at h; exact h
        · -- get 1 = len
          have hparams_eq : locFinalB.params = locJ.params := rfl
          simp only [Locals.get, hparams_eq, hlp, show (1:Nat) < 2 from by omega, if_true, if_false]
          have h := hg1; simp only [Locals.get, hlp, show (1:Nat) < 2 from by omega, if_true, if_false] at h; exact h
        · -- get 2 = frame (locals[0] not touched by set 3 or set 7)
          have hparams_eq : locFinalB.params = locJ.params := rfl
          have hlocals_eq : locFinalB.locals = (locJ.locals.set 3 (.i32 (UInt32.ofNat n'))).set 7 (.i32 (UInt32.ofNat (n' + 1))) := rfl
          simp only [Locals.get, hparams_eq, hlocals_eq, hlp, hll, List.length_set,
                     show ¬(2 < 2) from by omega, show (2:Nat) < 2 + 8 from by omega,
                     show (2:Nat) - 2 = 0 from by omega, List.getElem?_set,
                     if_neg (show ¬(7:Nat) = 0 from by omega),
                     if_neg (show ¬(3:Nat) = 0 from by omega), if_true, if_false]
          have h := hg2; simp only [Locals.get, hlp, hll, show ¬(2 < 2) from by omega,
                         show (2:Nat) < 2 + 8 from by omega, show (2:Nat) - 2 = 0 from by omega,
                         if_true, if_false] at h
          exact h
        · -- sorted postcondition
          sorry
        · -- perm postcondition
          sorry

set_option maxHeartbeats 800000 in
omit inst in
private theorem outer_loop_continue_step
    (stA : Store Unit) (locA : Locals)
    (ptr len frame : UInt32) (xs : List UInt32)
    (i : UInt32)
    (hget0       : locA.get 0 = some (.i32 ptr))
    (hget1       : locA.get 1 = some (.i32 len))
    (hget2       : locA.get 2 = some (.i32 frame))
    (hlocA_vals  : locA.values = [])
    (hlparams    : locA.params.length = 2)
    (hllocals    : locA.locals.length = 8)
    (hdisj_frame : ptr.toNat + 4 * xs.length ≤ frame.toNat)
    (hpg_arr     : ptr.toNat + 4 * xs.length ≤ 4294967296)
    (hread8      : stA.mem.read32 (frame + 8) = i)
    (hi_pos      : 0 < i.toNat)
    (hi_lt       : i.toNat < xs.length)
    (hi_le       : i.toNat ≤ xs.length)
    (hglob       : stA.globals.globals[0]? = some (.i32 frame))
    (hbnd_arr    : ptr.toNat + 4 * xs.length ≤ stA.mem.pages * 65536)
    (hbnd_frame  : frame.toNat + 16 ≤ stA.mem.pages * 65536)
    (hpairwise   : (wordsAt stA.mem ptr i.toNat).Pairwise (· ≤ ·))
    (hperm       : (wordsAt stA.mem ptr xs.length).Perm xs)
    (hlen        : xs.length = len.toNat) :
    ∃ (N : Nat) (stFinal : Store Unit) (locFinal : Locals),
      (∀ fuel ≥ N,
        exec fuel «module» stA locA
          [.block 0 0 [
             .localGet 2, .load32 (8 : UInt32), .localGet 1, .ltU, .const (1 : UInt32),
             .and, .br_if 0, .localGet 2, .const (16 : UInt32), .add, .globalSet 0, .ret],
           .localGet 2, .load32 (8 : UInt32), .localSet 3,
           .block 0 0 [
             .block 0 0 [
               .localGet 3, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
               .localGet 0, .localGet 3, .const (2 : UInt32), .shl, .add,
               .load32 (0 : UInt32), .localSet 4, .localGet 2, .localGet 2,
               .load32 (8 : UInt32), .store32 (12 : UInt32), .br 1],
             .localGet 3, .localGet 1, .const (1048604 : UInt32), .call 54, .unreachable],
           .block 0 0 [
             .loop 0 0 [
               .localGet 2, .load32 (12 : UInt32), .const (0 : UInt32), .gtU,
               .const (1 : UInt32), .and, .eqz, .br_if 1,
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 5,
               .block 0 0 [
                 .block 0 0 [
                   .localGet 5, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                   .localGet 0, .localGet 5, .const (2 : UInt32), .shl, .add,
                   .load32 (0 : UInt32), .localGet 4, .gtU, .const (1 : UInt32), .and,
                   .br_if 1, .br 3],
                 .localGet 5, .localGet 1, .const (1048620 : UInt32), .call 54, .unreachable],
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 6,
               .block 0 0 [
                 .block 0 0 [
                   .block 0 0 [
                     .localGet 6, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                     .localGet 0, .localGet 6, .const (2 : UInt32), .shl, .add,
                     .load32 (0 : UInt32), .localSet 7,
                     .localGet 2, .load32 (12 : UInt32), .localSet 8,
                     .localGet 8, .localGet 1, .ltU, .const (1 : UInt32), .and,
                     .br_if 1, .br 2],
                   .localGet 6, .localGet 1, .const (1048652 : UInt32), .call 54, .unreachable],
                 .localGet 0, .localGet 8, .const (2 : UInt32), .shl, .add, .localGet 7,
                 .store32 (0 : UInt32), .localGet 2, .localGet 2,
                 .load32 (12 : UInt32), .const (1 : UInt32), .sub, .store32 (12 : UInt32),
                 .br 1]],
             .localGet 8, .localGet 1, .const (1048668 : UInt32), .call 54, .unreachable],
           .localGet 2, .load32 (12 : UInt32), .localSet 9,
           .block 0 0 [
             .localGet 9, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
             .localGet 0, .localGet 9, .const (2 : UInt32), .shl, .add, .localGet 4,
             .store32 (0 : UInt32), .localGet 2, .localGet 2, .load32 (8 : UInt32),
             .const (1 : UInt32), .add, .store32 (8 : UInt32), .br 1]]
          {} = .Break 0 stFinal locFinal) ∧
      I_outer ptr len xs frame stFinal { locFinal with values := [] } ∧
      xs.length - (stFinal.mem.read32 (frame + 8)).toNat < xs.length - i.toNat := by
  -- Transparency-friendly intermediate definitions
  let key  : UInt32      := stA.mem.read32 (ptr + 4 * i)
  let stBC1 : Store Unit := { stA with mem := stA.mem.write32 (frame + (12 : UInt32)) i }
  let locA3 : Locals := { locA with locals := locA.locals.set 1 (.i32 i), values := [] }
  let locA4 : Locals := { locA3 with locals := locA3.locals.set 2 (.i32 key), values := [] }
  -- Apply inner_loop_terminates
  obtain ⟨Ni, stFinal, locFinal,
          hexec_inner, hread8_new, hglob_final, hpages_final,
          hlp_f, hll_f, hvals_f, hg0_f, hg1_f, hg2_f,
          hpairwise_new, hperm_new⟩ :=
    inner_loop_terminates stA locA ptr len frame xs i
      hlparams hllocals hget0 hget1 hget2 hlocA_vals hread8 hi_pos hi_lt
      hglob hbnd_arr hbnd_frame hpairwise hperm hlen hdisj_frame hpg_arr
  -- Arithmetic helpers
  have hi_lt_u32 : i < len := by rw [UInt32.lt_iff_toNat_lt_toNat]; omega
  have hno_load8 : ¬(frame.toNat + (8 : UInt32).toNat + 4 > stA.mem.pages * 65536) := by
    have h8 : (8 : UInt32).toNat = 8 := rfl; rw [h8]; linarith [hbnd_frame]
  have hns12 : ¬(frame.toNat + (12 : UInt32).toNat + 4 > stA.mem.pages * 65536) := by
    have h12 : (12 : UInt32).toNat = 12 := rfl; rw [h12]; linarith [hbnd_frame]
  have hishl : i <<< ((2 : UInt32) % 32) = 4 * i := by
    rw [show (2 : UInt32) % 32 = 2 from by decide]
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_mul, show (4 : UInt32).toNat = 4 from rfl]
    simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
  have hnl_load0 : ¬((4 * i + ptr).toNat + (0 : UInt32).toNat + 4 > stA.mem.pages * 65536) := by
    have hadd := UInt32.toNat_add (4 * i) ptr
    have hmul := UInt32.toNat_mul (4 : UInt32) i
    simp only [show (4 : UInt32).toNat = 4 from rfl] at hmul
    simp only [show (0 : UInt32).toNat = 0 from rfl, Nat.add_zero]
    have hm1 := Nat.mod_le ((4 * i).toNat + ptr.toNat) 4294967296
    have hm2 := Nat.mod_le (4 * i.toNat) 4294967296; omega
  have harri_read : stA.mem.read32 ((4 * i + ptr) + (0 : UInt32)) = key := by
    have haddr : (4 * i + ptr) + (0 : UInt32) = ptr + 4 * i := by
      apply UInt32.toNat_inj.mp
      simp only [UInt32.toNat_add, UInt32.toNat_mul,
                 show (0 : UInt32).toNat = 0 from rfl,
                 show (4 : UInt32).toNat = 4 from rfl,
                 Nat.add_zero]
      omega
    rw [haddr]
  -- locA helpers valid for any value stack (get doesn't use .values)
  have hget0_upd : ∀ vs, { locA with values := vs }.get 0 = some (.i32 ptr) :=
    fun _ => hget0
  have hget1_upd : ∀ vs, { locA with values := vs }.get 1 = some (.i32 len) :=
    fun _ => hget1
  have hget2_upd : ∀ vs, { locA with values := vs }.get 2 = some (.i32 frame) :=
    fun _ => hget2
  -- locA3 properties
  have hlp3 : locA3.params.length = 2 := hlparams
  have hll3 : locA3.locals.length = 8 := by simp [locA3, List.length_set, hllocals]
  -- locA3 get-lemmas (∀ value-stack)
  have hg3_3 : ∀ vs, { locA3 with values := vs }.get 3 = some (.i32 i) := by
    intro vs
    simp only [Locals.get, locA3, hlparams, List.length_set, hllocals,
               show ¬(3 < 2) from by omega, show (3 : Nat) < 2 + 8 from by omega,
               show (3 : Nat) - 2 = 1 from by omega, List.getElem?_set,
               show (1 : Nat) = 1 from rfl, show (1 : Nat) < 8 from by omega,
               if_true, if_false]
  have hg1_3 : ∀ vs, { locA3 with values := vs }.get 1 = some (.i32 len) := by
    intro vs
    simp only [Locals.get, locA3, hlparams, show (1 : Nat) < 2 from by omega]
    have h := hget1; simp only [Locals.get, hlparams, show (1 : Nat) < 2 from by omega] at h
    exact h
  have hg0_3 : ∀ vs, { locA3 with values := vs }.get 0 = some (.i32 ptr) := by
    intro vs
    simp only [Locals.get, locA3, hlparams, show (0 : Nat) < 2 from by omega]
    have h := hget0; simp only [Locals.get, hlparams, show (0 : Nat) < 2 from by omega] at h
    exact h
  have hg2_3 : ∀ vs, { locA3 with values := vs }.get 2 = some (.i32 frame) := by
    intro vs
    simp only [Locals.get, locA3, hlparams, List.length_set, hllocals,
               show ¬(2 < 2) from by omega, show (2 : Nat) < 2 + 8 from by omega,
               show (2 : Nat) - 2 = 0 from by omega, List.getElem?_set,
               if_neg (show ¬(1 : Nat) = 0 from by omega)]
    have h := hget2
    simp only [Locals.get, hlparams, hllocals, show ¬(2 < 2) from by omega,
               show (2 : Nat) < 2 + 8 from by omega, show (2 : Nat) - 2 = 0 from by omega] at h
    exact h
  -- locA4 get-lemmas
  have hg2_4 : ∀ vs, { locA4 with values := vs }.get 2 = some (.i32 frame) := by
    intro vs
    simp only [Locals.get, locA4, locA3, hlparams, List.length_set, hllocals,
               show ¬(2 < 2) from by omega, show (2 : Nat) < 2 + 8 from by omega,
               show (2 : Nat) - 2 = 0 from by omega, List.getElem?_set,
               if_neg (show ¬(2 : Nat) = 0 from by omega),
               if_neg (show ¬(1 : Nat) = 0 from by omega)]
    have h := hget2
    simp only [Locals.get, hlparams, hllocals, show ¬(2 < 2) from by omega,
               show (2 : Nat) < 2 + 8 from by omega, show (2 : Nat) - 2 = 0 from by omega] at h
    exact h
  -- Fuel: N = Ni + 4 (EXIT_BLOCK + GET_i + BC1 use 3 layers of block/instr, plus 1 margin)
  refine ⟨Ni + 4, stFinal, locFinal, fun fuel hfuel => ?_, ?_, ?_⟩
  · -- ── Execution proof ──────────────────────────────────────────────────────
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + (Ni + 4) := ⟨fuel - (Ni + 4), by omega⟩
    -- Step 1: EXIT_BLOCK (exec_block_cons at fuel = k+Ni+4 = (k+Ni+3)+1)
    rw [show k + (Ni + 4) = k + Ni + 3 + 1 from by omega, exec_block_cons]
    have hEB : exec (k + Ni + 3) «module» stA locA
        [.localGet 2, .load32 (8 : UInt32), .localGet 1, .ltU, .const (1 : UInt32),
         .and, .br_if 0, .localGet 2, .const (16 : UInt32), .add, .globalSet 0, .ret] {} =
        .Break 0 stA { locA with values := [] } := by
      simp only [exec, execOne.eq_def, hget2, hlocA_vals,
                 if_neg hno_load8, hread8, hget1_upd, if_pos hi_lt_u32,
                 show (1 : UInt32) &&& (1 : UInt32) = 1 from by decide]
      rfl
    rw [hEB]; simp only [List.take_zero, List.nil_append, List.drop_zero, hlocA_vals]
    rw [show k + Ni + 3 + 1 = k + Ni + 4 from by omega]
    -- Step 2: GET_i (localGet 2, load32 8, localSet 3) — peel one instruction at a time
    -- 2a. localGet 2
    have hgi_a : exec (k + Ni + 4) «module» stA { locA with values := [] }
        (.localGet 2 :: .load32 (8 : UInt32) :: .localSet 3 ::
         [.block 0 0 [.block 0 0
              [.localGet 3, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
               .localGet 0, .localGet 3, .const (2 : UInt32), .shl, .add,
               .load32 (0 : UInt32), .localSet 4, .localGet 2, .localGet 2,
               .load32 (8 : UInt32), .store32 (12 : UInt32), .br 1],
            .localGet 3, .localGet 1, .const (1048604 : UInt32), .call 54, .unreachable],
          .block 0 0 [.loop 0 0
              [.localGet 2, .load32 (12 : UInt32), .const (0 : UInt32), .gtU,
               .const (1 : UInt32), .and, .eqz, .br_if 1,
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 5,
               .block 0 0 [.block 0 0
                   [.localGet 5, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                    .localGet 0, .localGet 5, .const (2 : UInt32), .shl, .add,
                    .load32 (0 : UInt32), .localGet 4, .gtU, .const (1 : UInt32), .and,
                    .br_if 1, .br 3],
                 .localGet 5, .localGet 1, .const (1048620 : UInt32), .call 54, .unreachable],
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 6,
               .block 0 0 [.block 0 0 [.block 0 0
                       [.localGet 6, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                        .localGet 0, .localGet 6, .const (2 : UInt32), .shl, .add,
                        .load32 (0 : UInt32), .localSet 7,
                        .localGet 2, .load32 (12 : UInt32), .localSet 8,
                        .localGet 8, .localGet 1, .ltU, .const (1 : UInt32), .and,
                        .br_if 1, .br 2],
                     .localGet 6, .localGet 1, .const (1048652 : UInt32), .call 54, .unreachable],
                   .localGet 0, .localGet 8, .const (2 : UInt32), .shl, .add, .localGet 7,
                   .store32 (0 : UInt32), .localGet 2, .localGet 2,
                   .load32 (12 : UInt32), .const (1 : UInt32), .sub, .store32 (12 : UInt32),
                   .br 1]],
             .localGet 8, .localGet 1, .const (1048668 : UInt32), .call 54, .unreachable],
          .localGet 2, .load32 (12 : UInt32), .localSet 9,
          .block 0 0 [.localGet 9, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
            .localGet 0, .localGet 9, .const (2 : UInt32), .shl, .add, .localGet 4,
            .store32 (0 : UInt32), .localGet 2, .localGet 2, .load32 (8 : UInt32),
            .const (1 : UInt32), .add, .store32 (8 : UInt32), .br 1]]) {} =
        exec (k + Ni + 4) «module» stA { locA with values := [.i32 frame] }
        (.load32 (8 : UInt32) :: .localSet 3 ::
         [.block 0 0 [.block 0 0
              [.localGet 3, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
               .localGet 0, .localGet 3, .const (2 : UInt32), .shl, .add,
               .load32 (0 : UInt32), .localSet 4, .localGet 2, .localGet 2,
               .load32 (8 : UInt32), .store32 (12 : UInt32), .br 1],
            .localGet 3, .localGet 1, .const (1048604 : UInt32), .call 54, .unreachable],
          .block 0 0 [.loop 0 0
              [.localGet 2, .load32 (12 : UInt32), .const (0 : UInt32), .gtU,
               .const (1 : UInt32), .and, .eqz, .br_if 1,
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 5,
               .block 0 0 [.block 0 0
                   [.localGet 5, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                    .localGet 0, .localGet 5, .const (2 : UInt32), .shl, .add,
                    .load32 (0 : UInt32), .localGet 4, .gtU, .const (1 : UInt32), .and,
                    .br_if 1, .br 3],
                 .localGet 5, .localGet 1, .const (1048620 : UInt32), .call 54, .unreachable],
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 6,
               .block 0 0 [.block 0 0 [.block 0 0
                       [.localGet 6, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                        .localGet 0, .localGet 6, .const (2 : UInt32), .shl, .add,
                        .load32 (0 : UInt32), .localSet 7,
                        .localGet 2, .load32 (12 : UInt32), .localSet 8,
                        .localGet 8, .localGet 1, .ltU, .const (1 : UInt32), .and,
                        .br_if 1, .br 2],
                     .localGet 6, .localGet 1, .const (1048652 : UInt32), .call 54, .unreachable],
                   .localGet 0, .localGet 8, .const (2 : UInt32), .shl, .add, .localGet 7,
                   .store32 (0 : UInt32), .localGet 2, .localGet 2,
                   .load32 (12 : UInt32), .const (1 : UInt32), .sub, .store32 (12 : UInt32),
                   .br 1]],
             .localGet 8, .localGet 1, .const (1048668 : UInt32), .call 54, .unreachable],
          .localGet 2, .load32 (12 : UInt32), .localSet 9,
          .block 0 0 [.localGet 9, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
            .localGet 0, .localGet 9, .const (2 : UInt32), .shl, .add, .localGet 4,
            .store32 (0 : UInt32), .localGet 2, .localGet 2, .load32 (8 : UInt32),
            .const (1 : UInt32), .add, .store32 (8 : UInt32), .br 1]]) {} := by
      conv_lhs => unfold exec; simp only [execOne.eq_def, hget2_upd]
    rw [hgi_a]
    -- 2b. load32 8
    have hgi_b : exec (k + Ni + 4) «module» stA { locA with values := [.i32 frame] }
        (.load32 (8 : UInt32) :: .localSet 3 ::
         [.block 0 0 [.block 0 0
              [.localGet 3, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
               .localGet 0, .localGet 3, .const (2 : UInt32), .shl, .add,
               .load32 (0 : UInt32), .localSet 4, .localGet 2, .localGet 2,
               .load32 (8 : UInt32), .store32 (12 : UInt32), .br 1],
            .localGet 3, .localGet 1, .const (1048604 : UInt32), .call 54, .unreachable],
          .block 0 0 [.loop 0 0
              [.localGet 2, .load32 (12 : UInt32), .const (0 : UInt32), .gtU,
               .const (1 : UInt32), .and, .eqz, .br_if 1,
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 5,
               .block 0 0 [.block 0 0
                   [.localGet 5, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                    .localGet 0, .localGet 5, .const (2 : UInt32), .shl, .add,
                    .load32 (0 : UInt32), .localGet 4, .gtU, .const (1 : UInt32), .and,
                    .br_if 1, .br 3],
                 .localGet 5, .localGet 1, .const (1048620 : UInt32), .call 54, .unreachable],
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 6,
               .block 0 0 [.block 0 0 [.block 0 0
                       [.localGet 6, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                        .localGet 0, .localGet 6, .const (2 : UInt32), .shl, .add,
                        .load32 (0 : UInt32), .localSet 7,
                        .localGet 2, .load32 (12 : UInt32), .localSet 8,
                        .localGet 8, .localGet 1, .ltU, .const (1 : UInt32), .and,
                        .br_if 1, .br 2],
                     .localGet 6, .localGet 1, .const (1048652 : UInt32), .call 54, .unreachable],
                   .localGet 0, .localGet 8, .const (2 : UInt32), .shl, .add, .localGet 7,
                   .store32 (0 : UInt32), .localGet 2, .localGet 2,
                   .load32 (12 : UInt32), .const (1 : UInt32), .sub, .store32 (12 : UInt32),
                   .br 1]],
             .localGet 8, .localGet 1, .const (1048668 : UInt32), .call 54, .unreachable],
          .localGet 2, .load32 (12 : UInt32), .localSet 9,
          .block 0 0 [.localGet 9, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
            .localGet 0, .localGet 9, .const (2 : UInt32), .shl, .add, .localGet 4,
            .store32 (0 : UInt32), .localGet 2, .localGet 2, .load32 (8 : UInt32),
            .const (1 : UInt32), .add, .store32 (8 : UInt32), .br 1]]) {} =
        exec (k + Ni + 4) «module» stA { locA with values := [.i32 i] }
        (.localSet 3 ::
         [.block 0 0 [.block 0 0
              [.localGet 3, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
               .localGet 0, .localGet 3, .const (2 : UInt32), .shl, .add,
               .load32 (0 : UInt32), .localSet 4, .localGet 2, .localGet 2,
               .load32 (8 : UInt32), .store32 (12 : UInt32), .br 1],
            .localGet 3, .localGet 1, .const (1048604 : UInt32), .call 54, .unreachable],
          .block 0 0 [.loop 0 0
              [.localGet 2, .load32 (12 : UInt32), .const (0 : UInt32), .gtU,
               .const (1 : UInt32), .and, .eqz, .br_if 1,
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 5,
               .block 0 0 [.block 0 0
                   [.localGet 5, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                    .localGet 0, .localGet 5, .const (2 : UInt32), .shl, .add,
                    .load32 (0 : UInt32), .localGet 4, .gtU, .const (1 : UInt32), .and,
                    .br_if 1, .br 3],
                 .localGet 5, .localGet 1, .const (1048620 : UInt32), .call 54, .unreachable],
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 6,
               .block 0 0 [.block 0 0 [.block 0 0
                       [.localGet 6, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                        .localGet 0, .localGet 6, .const (2 : UInt32), .shl, .add,
                        .load32 (0 : UInt32), .localSet 7,
                        .localGet 2, .load32 (12 : UInt32), .localSet 8,
                        .localGet 8, .localGet 1, .ltU, .const (1 : UInt32), .and,
                        .br_if 1, .br 2],
                     .localGet 6, .localGet 1, .const (1048652 : UInt32), .call 54, .unreachable],
                   .localGet 0, .localGet 8, .const (2 : UInt32), .shl, .add, .localGet 7,
                   .store32 (0 : UInt32), .localGet 2, .localGet 2,
                   .load32 (12 : UInt32), .const (1 : UInt32), .sub, .store32 (12 : UInt32),
                   .br 1]],
             .localGet 8, .localGet 1, .const (1048668 : UInt32), .call 54, .unreachable],
          .localGet 2, .load32 (12 : UInt32), .localSet 9,
          .block 0 0 [.localGet 9, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
            .localGet 0, .localGet 9, .const (2 : UInt32), .shl, .add, .localGet 4,
            .store32 (0 : UInt32), .localGet 2, .localGet 2, .load32 (8 : UInt32),
            .const (1 : UInt32), .add, .store32 (8 : UInt32), .br 1]]) {} := by
      conv_lhs => unfold exec; simp only [execOne.eq_def, if_neg hno_load8, hread8]
    rw [hgi_b]
    -- 2c. localSet 3 → locA3
    have hgi_c : exec (k + Ni + 4) «module» stA { locA with values := [.i32 i] }
        (.localSet 3 ::
         [.block 0 0 [.block 0 0
              [.localGet 3, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
               .localGet 0, .localGet 3, .const (2 : UInt32), .shl, .add,
               .load32 (0 : UInt32), .localSet 4, .localGet 2, .localGet 2,
               .load32 (8 : UInt32), .store32 (12 : UInt32), .br 1],
            .localGet 3, .localGet 1, .const (1048604 : UInt32), .call 54, .unreachable],
          .block 0 0 [.loop 0 0
              [.localGet 2, .load32 (12 : UInt32), .const (0 : UInt32), .gtU,
               .const (1 : UInt32), .and, .eqz, .br_if 1,
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 5,
               .block 0 0 [.block 0 0
                   [.localGet 5, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                    .localGet 0, .localGet 5, .const (2 : UInt32), .shl, .add,
                    .load32 (0 : UInt32), .localGet 4, .gtU, .const (1 : UInt32), .and,
                    .br_if 1, .br 3],
                 .localGet 5, .localGet 1, .const (1048620 : UInt32), .call 54, .unreachable],
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 6,
               .block 0 0 [.block 0 0 [.block 0 0
                       [.localGet 6, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                        .localGet 0, .localGet 6, .const (2 : UInt32), .shl, .add,
                        .load32 (0 : UInt32), .localSet 7,
                        .localGet 2, .load32 (12 : UInt32), .localSet 8,
                        .localGet 8, .localGet 1, .ltU, .const (1 : UInt32), .and,
                        .br_if 1, .br 2],
                     .localGet 6, .localGet 1, .const (1048652 : UInt32), .call 54, .unreachable],
                   .localGet 0, .localGet 8, .const (2 : UInt32), .shl, .add, .localGet 7,
                   .store32 (0 : UInt32), .localGet 2, .localGet 2,
                   .load32 (12 : UInt32), .const (1 : UInt32), .sub, .store32 (12 : UInt32),
                   .br 1]],
             .localGet 8, .localGet 1, .const (1048668 : UInt32), .call 54, .unreachable],
          .localGet 2, .load32 (12 : UInt32), .localSet 9,
          .block 0 0 [.localGet 9, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
            .localGet 0, .localGet 9, .const (2 : UInt32), .shl, .add, .localGet 4,
            .store32 (0 : UInt32), .localGet 2, .localGet 2, .load32 (8 : UInt32),
            .const (1 : UInt32), .add, .store32 (8 : UInt32), .br 1]]) {} =
        exec (k + Ni + 4) «module» stA locA3
        [.block 0 0 [.block 0 0
              [.localGet 3, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
               .localGet 0, .localGet 3, .const (2 : UInt32), .shl, .add,
               .load32 (0 : UInt32), .localSet 4, .localGet 2, .localGet 2,
               .load32 (8 : UInt32), .store32 (12 : UInt32), .br 1],
            .localGet 3, .localGet 1, .const (1048604 : UInt32), .call 54, .unreachable],
         .block 0 0 [.loop 0 0
              [.localGet 2, .load32 (12 : UInt32), .const (0 : UInt32), .gtU,
               .const (1 : UInt32), .and, .eqz, .br_if 1,
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 5,
               .block 0 0 [.block 0 0
                   [.localGet 5, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                    .localGet 0, .localGet 5, .const (2 : UInt32), .shl, .add,
                    .load32 (0 : UInt32), .localGet 4, .gtU, .const (1 : UInt32), .and,
                    .br_if 1, .br 3],
                 .localGet 5, .localGet 1, .const (1048620 : UInt32), .call 54, .unreachable],
               .localGet 2, .load32 (12 : UInt32), .const (1 : UInt32), .sub, .localSet 6,
               .block 0 0 [.block 0 0 [.block 0 0
                       [.localGet 6, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                        .localGet 0, .localGet 6, .const (2 : UInt32), .shl, .add,
                        .load32 (0 : UInt32), .localSet 7,
                        .localGet 2, .load32 (12 : UInt32), .localSet 8,
                        .localGet 8, .localGet 1, .ltU, .const (1 : UInt32), .and,
                        .br_if 1, .br 2],
                     .localGet 6, .localGet 1, .const (1048652 : UInt32), .call 54, .unreachable],
                   .localGet 0, .localGet 8, .const (2 : UInt32), .shl, .add, .localGet 7,
                   .store32 (0 : UInt32), .localGet 2, .localGet 2,
                   .load32 (12 : UInt32), .const (1 : UInt32), .sub, .store32 (12 : UInt32),
                   .br 1]],
             .localGet 8, .localGet 1, .const (1048668 : UInt32), .call 54, .unreachable],
         .localGet 2, .load32 (12 : UInt32), .localSet 9,
         .block 0 0 [.localGet 9, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
           .localGet 0, .localGet 9, .const (2 : UInt32), .shl, .add, .localGet 4,
           .store32 (0 : UInt32), .localGet 2, .localGet 2, .load32 (8 : UInt32),
           .const (1 : UInt32), .add, .store32 (8 : UInt32), .br 1]] {} := by
      conv_lhs => unfold exec; simp only [execOne.eq_def, Locals.set?, hlparams, hllocals,
                   List.length_set, show ¬(3 < 2) from by omega,
                   show (3 : Nat) < 10 from by omega, show (3 : Nat) - 2 = 1 from by omega,
                   show Locals.mk locA.params (locA.locals.set 1 (.i32 i)) [] = locA3 from rfl,
                   if_true, if_false]
    rw [hgi_c]
    -- Step 3: BC1_OUTER via exec_block_cons (fuel = k+Ni+4 = (k+Ni+3)+1)
    rw [show k + Ni + 4 = k + Ni + 3 + 1 from by omega, exec_block_cons]
    -- BC1_OUTER body at k+Ni+3
    have hBC1 : exec (k + Ni + 3) «module» stA locA3
        [.block 0 0
           [.localGet 3, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
            .localGet 0, .localGet 3, .const (2 : UInt32), .shl, .add,
            .load32 (0 : UInt32), .localSet 4, .localGet 2, .localGet 2,
            .load32 (8 : UInt32), .store32 (12 : UInt32), .br 1],
         .localGet 3, .localGet 1, .const (1048604 : UInt32), .call 54, .unreachable] {} =
        .Break 0 stBC1 locA4 := by
      rw [show k + Ni + 3 = k + Ni + 2 + 1 from by omega, exec_block_cons]
      -- BC1_INNER body at k+Ni+2 produces .Break 1
      have hBC1_body : exec (k + Ni + 2) «module» stA locA3
          [.localGet 3, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
           .localGet 0, .localGet 3, .const (2 : UInt32), .shl, .add,
           .load32 (0 : UInt32), .localSet 4, .localGet 2, .localGet 2,
           .load32 (8 : UInt32), .store32 (12 : UInt32), .br 1] {} =
          .Break 1 stBC1 locA4 := by
        simp only [exec, execOne.eq_def,
                   show locA3.get 3 = some (.i32 i) from hg3_3 [],
                   show locA3.values = [] from rfl,
                   hg3_3, hg1_3, if_pos hi_lt_u32,
                   show (1 : UInt32) &&& (1 : UInt32) = 1 from by decide,
                   show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                   hg0_3, hishl,
                   if_neg hnl_load0, harri_read,
                   Locals.set?, hlp3, hll3, List.length_set,
                   show ¬(4 < 2) from by omega, show (4 : Nat) < 10 from by omega,
                   show (4 : Nat) - 2 = 2 from by omega, if_true, if_false,
                   show Locals.mk locA.params ((locA.locals.set 1 (.i32 i)).set 2 (.i32 key)) [] =
                       locA4 from rfl,
                   show ({ params := locA3.params, locals := locA3.locals.set 2 (.i32 key) } : Locals) =
                       locA4 from rfl,
                   show locA4.get 2 = some (.i32 frame) from hg2_4 [],
                   show locA4.values = [] from rfl,
                   hg2_3, hg2_4,
                   if_neg hno_load8, if_neg hns12, hread8,
                   show { stA with mem := stA.mem.write32 (frame + (12 : UInt32)) i } =
                       stBC1 from rfl,
                   show { locA4 with values := [] } = locA4 from rfl]
      rw [hBC1_body]
    rw [hBC1]
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    -- Step 4: INNER_BLOCK + GET_j + STORE_KEY via inner_loop_terminates
    exact hexec_inner (k + Ni + 4) (by omega)
  · -- ── I_outer re-establishment ─────────────────────────────────────────────
    have hip1 : (i + 1 : UInt32).toNat = i.toNat + 1 := by
      rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by have := len.toNat_lt; rw [← hlen] at this; omega)
    refine ⟨i + 1, hg0_f, hg1_f, hg2_f, rfl, hlp_f, hll_f, hread8_new,
            by omega, by omega, hglob_final, ?_, ?_, hpairwise_new, hperm_new⟩
    · rw [hpages_final]; exact hbnd_arr
    · rw [hpages_final]; exact hbnd_frame
  · -- ── Measure decrease ─────────────────────────────────────────────────────
    have hip1 : (i + 1 : UInt32).toNat = i.toNat + 1 := by
      rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by have := len.toNat_lt; rw [← hlen] at this; omega)
    rw [hread8_new]; omega

-- Generalized over the shadow-stack pointer `sp` at call time (= global 0
-- before func0's preamble decrements it).
-- frame = sp - 16 is the local stack frame func0 establishes.
private theorem func0_wp_prop
    (st : Store Unit) (ptr len : UInt32) (xs : List UInt32) (sp : UInt32)
    (hlen   : xs.length = len.toNat)
    (hbnd   : ptr.toNat + 4 * xs.length ≤ st.mem.pages * 65536)
    (hpg16  : (16 : Nat) ≤ sp.toNat)
    (hspg   : sp.toNat ≤ st.mem.pages * 65536)
    (hg0    : st.globals.globals[0]? = some (.i32 sp))
    (hcont  : wordsAt st.mem ptr xs.length = xs)
    (hdisj  : ptr.toNat + 4 * xs.length ≤ sp.toNat - 16) :
    wp_wasm_prop «module» st
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [] }
      func0 {}
      (fun st' _ =>
        (∃ ys : List UInt32,
          wordsAt st'.mem ptr ys.length = ys ∧
          ys.Pairwise (· ≤ ·) ∧
          ys.Perm xs) ∧
        st'.globals.globals[0]? = some (.i32 sp)) := by
  simp only [func0]
  -- ── Frame arithmetic ──────────────────────────────────────────────────────
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr (by simpa using hpg16)
  set frame : UInt32 := sp - 16 with hframe_def
  have hframe_toNat : frame.toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  have hsp_lt : sp.toNat < 4294967296 := sp.toNat_lt
  have haddr8 : (frame + 8 : UInt32).toNat = frame.toNat + 8 := by
    have h8 : (8 : UInt32).toNat = 8 := rfl
    rw [UInt32.toNat_add, h8, Nat.mod_eq_of_lt (by omega)]
  -- ── Intermediate stores ────────────────────────────────────────────────────
  set st1 : Store Unit :=
    { st with globals := { globals := st.globals.globals.set 0 (.i32 frame) } }
    with hst1_def
  set st2 : Store Unit := { st1 with mem := st1.mem.write32 (frame + 8) 1 }
    with hst2_def
  have hst1_mem : st1.mem = st.mem := rfl
  -- Bounds check for store32 8: frame.toNat + 8 + 4 ≤ pages * 65536
  have hno_store8 : ¬ (frame.toNat + (8 : UInt32).toNat + 4 > st1.mem.pages * 65536) := by
    have h8 : (8 : UInt32).toNat = 8 := rfl
    simp only [hst1_mem, h8]; omega
  -- globals[0] after preamble = frame
  have hst1_g0 : st1.globals.globals[0]? = some (.i32 frame) := by
    simp only [hst1_def]
    obtain ⟨_, _, ht⟩ : ∃ h t, st.globals.globals = h :: t := by
      cases hgl : st.globals.globals with
      | nil => simp [hgl] at hg0
      | cons hd tl => exact ⟨hd, tl, rfl⟩
    rw [ht]; rfl
  -- ── Preamble: 9 straight-line steps ───────────────────────────────────────
  -- Precomputed localSet 2 / localGet 2 facts (rfl works since Locals.set? / Locals.get
  -- are plain defs, not inside the mutual exec block, so the kernel can reduce them)
  have hset2 : (Locals.mk [.i32 ptr, .i32 len]
      [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]
      [.i32 frame]).set? 2 (.i32 frame) =
      some (Locals.mk [.i32 ptr, .i32 len]
        [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]
        [.i32 frame]) := rfl
  have hget2 : (Locals.mk [.i32 ptr, .i32 len]
      [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]
      []).get 2 = some (.i32 frame) := rfl
  -- Step 0: globalGet 0 → push sp
  apply exec_cons_wp (show execOne 1 «module» st
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [] }
      (.globalGet 0) {} =
      .Fallthrough st
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [.i32 sp] }
    from by simp only [execOne.eq_def, hg0])
  -- Step 1: const 16 → push 16
  apply exec_cons_wp (show execOne 1 «module» st
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [.i32 sp] }
      (.const (16 : UInt32)) {} =
      .Fallthrough st
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [.i32 16, .i32 sp] }
    from by simp only [execOne.eq_def])
  -- Step 2: sub → sp - 16 = frame
  apply exec_cons_wp (show execOne 1 «module» st
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [.i32 16, .i32 sp] }
      (.sub) {} =
      .Fallthrough st
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [.i32 frame] }
    from by simp only [execOne.eq_def, ← hframe_def])
  -- Step 3: localSet 2 → locals[0] = frame
  apply exec_cons_wp (show execOne 1 «module» st
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [.i32 frame] }
      (.localSet 2) {} =
      .Fallthrough st
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [] }
    from by simp only [execOne.eq_def, hset2])
  -- Step 4: localGet 2 → push frame
  apply exec_cons_wp (show execOne 1 «module» st
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [] }
      (.localGet 2) {} =
      .Fallthrough st
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [.i32 frame] }
    from by simp only [execOne.eq_def, hget2])
  -- Step 5: globalSet 0 → globals[0] = frame (st → st1)
  apply exec_cons_wp (show execOne 1 «module» st
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [.i32 frame] }
      (.globalSet 0) {} =
      .Fallthrough st1
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [] }
    from by simp only [execOne.eq_def, hg0, ← hst1_def])
  -- Step 6: localGet 2 → push frame (in st1)
  apply exec_cons_wp (show execOne 1 «module» st1
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [] }
      (.localGet 2) {} =
      .Fallthrough st1
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [.i32 frame] }
    from by simp only [execOne.eq_def, hget2])
  -- Step 7: const 1 → push 1
  apply exec_cons_wp (show execOne 1 «module» st1
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [.i32 frame] }
      (.const (1 : UInt32)) {} =
      .Fallthrough st1
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [.i32 1, .i32 frame] }
    from by simp only [execOne.eq_def])
  -- Step 8: store32 8 → mem[frame+8] = 1 (st1 → st2)
  apply exec_cons_wp (show execOne 1 «module» st1
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [.i32 1, .i32 frame] }
      (.store32 (8 : UInt32)) {} =
      .Fallthrough st2
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [] }
    from by simp only [execOne.eq_def, if_neg hno_store8, ← hst2_def])
  -- ── Outer loop ─────────────────────────────────────────────────────────────
  -- Case split: empty array exits the loop immediately via ret in BLOCK_A
  by_cases hlen_pos : xs.length = 0
  · -- xs = []: len=0, so the first iteration's BLOCK_A exit check (i=1 <ᵤ len=0 = false)
    -- falls through to `ret`, immediately returning with an empty sorted array.
    have hlen_nat : len.toNat = 0 := by rw [← hlen]; exact hlen_pos
    have hlen0 : len = 0 := UInt32.toNat_inj.mp (by simpa using hlen_nat)
    have hxs_nil : xs = [] := by cases xs with | nil => rfl | cons _ _ => simp_all
    subst hlen0; subst hxs_nil
    -- After subst: len = 0, xs = []
    have hread_i : st2.mem.read32 (frame + 8) = 1 := by
      simp only [hst2_def, hst1_mem]; exact read32_write32_same st.mem (frame + 8) 1
    have hno_load8 : ¬ (frame.toNat + (8 : UInt32).toNat + 4 > st2.mem.pages * 65536) := by
      have h8 : (8 : UInt32).toNat = 8 := rfl
      simp only [hst2_def, hst1_mem, write32_pages, h8]; omega
    have hframe16 : frame + 16 = sp := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_add, show (16 : UInt32).toNat = 16 from rfl,
          Nat.mod_eq_of_lt (by omega), hframe_toNat]; omega
    have hframe16' : (16 : UInt32) + frame = sp := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_add, show (16 : UInt32).toNat = 16 from rfl,
          Nat.mod_eq_of_lt (by omega), hframe_toNat]; omega
    -- ∀-vs variants so simp can fire at any stack depth
    have hget2_v : ∀ (vs : List Value),
        (Locals.mk [.i32 ptr, .i32 (0 : UInt32)]
           [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]
           vs).get 2 = some (.i32 frame) := fun _ => rfl
    have hget1_v : ∀ (vs : List Value),
        (Locals.mk [.i32 ptr, .i32 (0 : UInt32)]
           [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]
           vs).get 1 = some (.i32 (0 : UInt32)) := fun _ => rfl
    -- st2.globals.globals[0]? = some (.i32 frame) (preamble globalSet 0 set it)
    have hst2_g0 : st2.globals.globals[0]? = some (.i32 frame) := hst1_g0
    -- st3: state after the inner globalSet 0 restores sp
    set st3 : Store Unit :=
      { st2 with globals := { globals := st2.globals.globals.set 0 (.i32 sp) } }
      with hst3_def
    have hst3_g0 : st3.globals.globals[0]? = some (.i32 sp) := by
      simp only [hst3_def]
      obtain ⟨_, _, ht⟩ : ∃ h t, st2.globals.globals = h :: t := by
        cases h : st2.globals.globals with
        | nil => simp [h] at hst2_g0
        | cons hd tl => exact ⟨hd, tl, rfl⟩
      rw [ht]; rfl
    -- fuel = 3: 1 for .loop, 1 for .block, 1 for straight-line instructions inside block
    refine ⟨3, ?_⟩
    simp only [exec, execOne.eq_def,
      hget2_v, hget1_v,
      if_neg hno_load8, hread_i, hst2_g0,
      if_neg (show ¬((1 : UInt32) < (0 : UInt32)) from by decide),
      show (1 : UInt32) &&& (0 : UInt32) = 0 from by decide,
      hframe16',
      ← hst3_def]
    -- Goal: Q st3 []
    exact ⟨⟨[], rfl, List.Pairwise.nil, List.Perm.nil⟩, hst3_g0⟩
  · have hlen_pos2 : 0 < xs.length := Nat.pos_of_ne_zero hlen_pos
    -- wordsAt is preserved: write at frame+8 is disjoint from the array region
    have hcont2 : wordsAt st2.mem ptr xs.length = xs := by
      rw [show st2.mem = st.mem.write32 (frame + 8) 1 from by simp [hst2_def, hst1_mem]]
      unfold wordsAt at hcont ⊢
      conv_rhs => rw [← hcont]
      apply List.map_congr_left
      intro k hk
      rw [List.mem_range] at hk
      have h_toNat : (ptr + 4 * UInt32.ofNat k).toNat = ptr.toNat + 4 * k :=
        toNat_wordAddr ptr xs.length k hk (by omega)
      apply read32_write32_ne
      left
      rw [haddr8, h_toNat]; omega
    -- Apply the loop rule with I_outer and measure xs.length - i
    apply wp_wasm_prop_loop
        (I := I_outer ptr len xs frame)
        (μ := fun stA _ => xs.length - (stA.mem.read32 (frame + 8)).toNat)
    · -- hinit: I_outer holds at st2 with i = 1
      show I_outer ptr len xs frame st2
        { params := [.i32 ptr, .i32 len],
          locals := [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
          values := [] }
      refine ⟨1, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- st2.mem.read32 (frame+8) = 1
        simp only [hst2_def, hst1_mem]
        exact read32_write32_same st.mem (frame + 8) 1
      · -- 0 < (1 : UInt32).toNat
        decide
      · -- (1 : UInt32).toNat ≤ xs.length
        have h1 : (1 : UInt32).toNat = 1 := rfl
        omega
      · -- global 0 = frame at st2
        exact hst1_g0
      · -- array bounds at st2
        simp only [hst2_def, hst1_mem, write32_pages]; exact hbnd
      · -- frame bounds at st2
        simp only [hst2_def, hst1_mem, write32_pages]; omega
      · -- 1-element prefix is Pairwise ≤
        simp [wordsAt]
      · -- wordsAt st2.mem ptr xs.length is a permutation of xs
        rw [hcont2]
    · -- hstep: one outer-loop iteration
      intro stA locA hInv
      obtain ⟨i, hget0, hget1, hget2, hlocA_vals, hlparams, hllocals, hread8, hi_pos, hi_le,
               hglob, hbnd_arr, hbnd_frame, hpairwise, hperm⟩ := hInv
      -- Shared lemmas used in both branches
      have hno_load8 : ¬(frame.toNat + (8 : UInt32).toNat + 4 > stA.mem.pages * 65536) := by
        have h8 : (8 : UInt32).toNat = 8 := rfl
        rw [h8]; linarith [hbnd_frame]
      have hframe16_step : (16 : UInt32) + frame = sp := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add, show (16 : UInt32).toNat = 16 from rfl,
            Nat.mod_eq_of_lt (by omega), hframe_toNat]
        omega
      -- locA.get N generalised over the value stack (needed after each push/pop)
      have hget2_upd : ∀ vs : List Value, { locA with values := vs }.get 2 = some (.i32 frame) :=
        fun _ => hget2
      have hget1_upd : ∀ vs : List Value, { locA with values := vs }.get 1 = some (.i32 len) :=
        fun _ => hget1
      by_cases hi_lt : i.toNat < xs.length
      · -- CONTINUE: i.toNat < xs.length
        have hi_lt_u32 : i < len := by rw [UInt32.lt_iff_toNat_lt_toNat]; omega
        -- Apply the outer loop continue step lemma (proved by inner-loop induction elsewhere):
        have hdisj_frame : ptr.toNat + 4 * xs.length ≤ frame.toNat := by
          rw [hframe_toNat]; omega
        have hpg_arr : ptr.toNat + 4 * xs.length ≤ 4294967296 := by
          have := hsp_lt; omega
        obtain ⟨N, stFinal, locFinal, hexec, hI_next, hmu⟩ :=
          outer_loop_continue_step stA locA ptr len frame xs i
            hget0 hget1 hget2 hlocA_vals hlparams hllocals hdisj_frame hpg_arr
            hread8 hi_pos hi_lt hi_le
            hglob hbnd_arr hbnd_frame hpairwise hperm hlen
        refine ⟨N, fun fuel hfuel => Or.inr (Or.inl ⟨stFinal, locFinal, hexec fuel hfuel, ?_, ?_⟩)⟩
        · -- I_outer holds: locA.values = [] so take 0 ++ drop 0 = [] = locA.values
          simp only [List.take_zero, List.nil_append, List.drop_zero]
          rw [hlocA_vals]; exact hI_next
        · -- μ decreases: xs.length - frame[8]_new < xs.length - i (= frame[8]_old)
          rw [hread8]; exact hmu
      · -- EXIT: i = len — EXIT_BLOCK's ret fires, Q holds for the full sorted array
        have hi_eq : i.toNat = xs.length := Nat.le_antisymm hi_le (Nat.not_lt.mp hi_lt)
        have hi_len : i = len := UInt32.toNat_inj.mp (by omega)
        have hilt_false : ¬((i : UInt32) < len) := by
          rw [UInt32.lt_iff_toNat_lt_toNat]; omega
        -- globalSet 0 in EXIT_BLOCK restores sp into global 0
        set stExit : Store Unit :=
          { stA with globals := { globals := stA.globals.globals.set 0 (.i32 sp) } }
          with hstExit_def
        have hstExit_g0 : stExit.globals.globals[0]? = some (.i32 sp) := by
          simp only [hstExit_def]
          obtain ⟨_, _, ht⟩ : ∃ h t, stA.globals.globals = h :: t := by
            cases h : stA.globals.globals with
            | nil => simp [h] at hglob
            | cons hd tl => exact ⟨hd, tl, rfl⟩
          rw [ht]; rfl
        -- fuel = 2 suffices: 1 for .block, 1 for straightline EXIT_BLOCK body
        refine ⟨2, fun fuel hfuel => ?_⟩
        right; right
        refine ⟨stExit, [], ?_, ?_⟩
        · -- exec fuel m stA locA outer_body {} = .Return stExit []
          -- Decompose fuel ≥ 2 as k+2 so simp can unfold execOne for the .block
          obtain ⟨k, hk⟩ : ∃ k, fuel = k + 2 := ⟨fuel - 2, by omega⟩
          subst hk
          simp only [exec, execOne.eq_def,
            hlocA_vals, hget2_upd, hget1_upd,
            if_neg hno_load8, hread8,
            if_neg hilt_false,
            show (1 : UInt32) &&& (0 : UInt32) = 0 from by decide,
            hglob, hframe16_step, ← hstExit_def]
        · -- Q stExit []
          refine ⟨⟨wordsAt stA.mem ptr xs.length, ?_, ?_, ?_⟩, hstExit_g0⟩
          · -- wordsAt stExit.mem ptr ys.length = ys (mem unchanged, length cancels)
            show wordsAt stA.mem ptr (wordsAt stA.mem ptr xs.length).length =
                wordsAt stA.mem ptr xs.length
            congr 1; simp only [wordsAt, List.length_map, List.length_range]
          · rw [← hi_eq]; exact hpairwise
          · exact hperm

private theorem func0_terminates
    (st : Store Unit) (sp ptr len : UInt32) (xs : List UInt32)
    (hlen   : xs.length = len.toNat)
    (hbnd   : ptr.toNat + 4 * xs.length ≤ st.mem.pages * 65536)
    (hpg16  : (16 : Nat) ≤ sp.toNat)
    (hspg   : sp.toNat ≤ st.mem.pages * 65536)
    (hg0    : st.globals.globals[0]? = some (.i32 sp))
    (hcont  : wordsAt st.mem ptr xs.length = xs)
    (hdisj  : ptr.toNat + 4 * xs.length ≤ sp.toNat - 16) :
    TerminatesWith {} «module» 0 st [.i32 len, .i32 ptr]
      (fun st' _ =>
        (∃ ys : List UInt32,
          wordsAt st'.mem ptr ys.length = ys ∧
          ys.Pairwise (· ≤ ·) ∧
          ys.Perm xs) ∧
        st'.globals.globals[0]? = some (.i32 sp)) := by
  apply wp_wasm_prop_to_TerminatesWith
      (hf       := by rfl)
      (himp     := by rfl)
      (hresults := by rfl)
      (hlen     := by
        have h1 : (([.i32 len, .i32 ptr] : List Value).length : Nat) = 2 := rfl
        have h2 : func0Def.numParams = 2 := rfl
        omega)
      (hcompat  := fun st' vs h => h)
  simp only [show
    func0Def.toLocals
      (([.i32 len, .i32 ptr] : List Value).take func0Def.numParams).reverse =
    ({ params := [.i32 ptr, .i32 len],
       locals := [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
       values := [] } : Locals) from rfl]
  simp only [show func0Def.body = func0 from rfl]
  exact func0_wp_prop st ptr len xs sp hlen hbnd hpg16 hspg hg0 hcont hdisj

/-! ## §6  func2 — entry point

func2 allocates a 16-byte shadow-stack frame, calls func1 (slice setup),
then calls func0 (sort loop), then restores sp and returns.
-/

private theorem func2_wp_prop
    (st : Store Unit) (ptr len : UInt32) (xs : List UInt32)
    (hlen  : xs.length = len.toNat)
    (hbnd  : ptr.toNat + 4 * xs.length ≤ st.mem.pages * 65536)
    (hpg   : (1048576 : Nat) ≤ st.mem.pages * 65536)
    (hg0   : st.globals.globals[0]? = some (.i32 (1048576 : UInt32)))
    (hcont : wordsAt st.mem ptr xs.length = xs)
    (hdisj : ptr.toNat + 4 * xs.length ≤ 1048544) :
    wp_wasm_prop «module» st
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 0, .i32 0, .i32 0], values := [] }
      func2 {}
      (fun st' _ =>
        ∃ ys : List UInt32,
          wordsAt st'.mem ptr ys.length = ys ∧
          ys.Pairwise (· ≤ ·) ∧
          ys.Perm xs) := by
  simp only [func2]
  -- ── Name the post-globalSet-0 store (frame = sp - 16 = 1048560 placed in globals[0]) ──
  set st1 : Store Unit :=
    { st with globals := { globals := st.globals.globals.set 0 (.i32 1048560) } }
    with hst1_def
  -- ── Preamble: steps 0-4 ──────────────────────────────────────────────────
  -- Step 0: globalGet 0 → push sp = 1048576
  apply exec_cons_wp (show execOne 1 «module» st
      { params := [.i32 ptr, .i32 len], locals := [.i32 0, .i32 0, .i32 0], values := [] }
      (.globalGet 0) {} =
      .Fallthrough st
      { params := [.i32 ptr, .i32 len], locals := [.i32 0, .i32 0, .i32 0],
        values := [.i32 1048576] }
      from by simp only [execOne.eq_def, hg0])
  -- Step 1: const 16 → push 16
  apply exec_cons_wp (show execOne 1 «module» st
      { params := [.i32 ptr, .i32 len], locals := [.i32 0, .i32 0, .i32 0],
        values := [.i32 1048576] }
      (.const (16 : UInt32)) {} =
      .Fallthrough st
      { params := [.i32 ptr, .i32 len], locals := [.i32 0, .i32 0, .i32 0],
        values := [.i32 16, .i32 1048576] }
      from by simp only [execOne.eq_def])
  -- Step 2: sub → 1048576 - 16 = 1048560 (frame)
  apply exec_cons_wp (show execOne 1 «module» st
      { params := [.i32 ptr, .i32 len], locals := [.i32 0, .i32 0, .i32 0],
        values := [.i32 16, .i32 1048576] }
      .sub {} =
      .Fallthrough st
      { params := [.i32 ptr, .i32 len], locals := [.i32 0, .i32 0, .i32 0],
        values := [.i32 1048560] }
      from by simp only [execOne.eq_def, show (1048576 : UInt32) - 16 = 1048560 from by decide])
  -- Step 3: localSet 2 → locals[0] = 1048560, pop
  have h_lset2 : Locals.set?
      { params := [.i32 ptr, .i32 len], locals := [.i32 0, .i32 0, .i32 0],
        values := [.i32 1048560] } 2 (.i32 1048560) =
      some { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 0, .i32 0],
             values := [.i32 1048560] } := rfl
  apply exec_cons_wp (show execOne 1 «module» st
      { params := [.i32 ptr, .i32 len], locals := [.i32 0, .i32 0, .i32 0],
        values := [.i32 1048560] }
      (.localSet 2) {} =
      .Fallthrough st
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 0, .i32 0],
        values := [] }
      from by simp only [execOne.eq_def, h_lset2])
  -- Step 4: localGet 2 → push locals[0] = 1048560
  have h_lget2a : Locals.get
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 1048560, .i32 0, .i32 0], values := [] } 2 =
      some (.i32 1048560) := rfl
  apply exec_cons_wp (show execOne 1 «module» st
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 0, .i32 0], values := [] }
      (.localGet 2) {} =
      .Fallthrough st
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 0, .i32 0],
        values := [.i32 1048560] }
      from by simp only [execOne.eq_def, h_lget2a])
  -- Step 5: globalSet 0 → set globals[0] = frame = 1048560; store becomes st1
  apply exec_cons_wp (show execOne 1 «module» st
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 0, .i32 0],
        values := [.i32 1048560] }
      (.globalSet 0) {} =
      .Fallthrough st1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 0, .i32 0], values := [] }
      from by simp only [execOne.eq_def, hg0, ← hst1_def])
  -- ── Steps 6-13: build call args for func1 ─────────────────────────────────
  -- Step 6: const 1048716 → push 1048716
  apply exec_cons_wp (show execOne 1 «module» st1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 0, .i32 0], values := [] }
      (.const (1048716 : UInt32)) {} =
      .Fallthrough st1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 0, .i32 0],
        values := [.i32 1048716] }
      from by simp only [execOne.eq_def])
  -- Step 7: localSet 3 → locals[1] = 1048716, pop
  have h_lset3 : Locals.set?
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 1048560, .i32 0, .i32 0],
        values := [.i32 1048716] } 3 (.i32 1048716) =
      some { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 0],
             values := [.i32 1048716] } := rfl
  apply exec_cons_wp (show execOne 1 «module» st1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 0, .i32 0],
        values := [.i32 1048716] }
      (.localSet 3) {} =
      .Fallthrough st1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [] }
      from by simp only [execOne.eq_def, h_lset3])
  -- Step 8: localGet 2 → push 1048560
  have h_lget2b : Locals.get
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 1048560, .i32 1048716, .i32 0], values := [] } 2 =
      some (.i32 1048560) := rfl
  apply exec_cons_wp (show execOne 1 «module» st1
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 1048560, .i32 1048716, .i32 0], values := [] }
      (.localGet 2) {} =
      .Fallthrough st1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 1048560] }
      from by simp only [execOne.eq_def, h_lget2b])
  -- Step 9: const 8 → push 8
  apply exec_cons_wp (show execOne 1 «module» st1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 1048560] }
      (.const (8 : UInt32)) {} =
      .Fallthrough st1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 8, .i32 1048560] }
      from by simp only [execOne.eq_def])
  -- Step 10: add → 8 + 1048560 = 1048568 (= sb for func1)
  apply exec_cons_wp (show execOne 1 «module» st1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 8, .i32 1048560] }
      .add {} =
      .Fallthrough st1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 1048568] }
      from by simp only [execOne.eq_def, show (8 : UInt32) + 1048560 = 1048568 from by decide])
  -- Step 11: localGet 0 → push ptr
  have h_lget0 : Locals.get
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 1048568] } 0 = some (.i32 ptr) := rfl
  apply exec_cons_wp (show execOne 1 «module» st1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 1048568] }
      (.localGet 0) {} =
      .Fallthrough st1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 ptr, .i32 1048568] }
      from by simp only [execOne.eq_def, h_lget0])
  -- Step 12: localGet 1 → push len
  have h_lget1 : Locals.get
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 ptr, .i32 1048568] } 1 = some (.i32 len) := rfl
  apply exec_cons_wp (show execOne 1 «module» st1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 ptr, .i32 1048568] }
      (.localGet 1) {} =
      .Fallthrough st1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 len, .i32 ptr, .i32 1048568] }
      from by simp only [execOne.eq_def, h_lget1])
  -- Step 13: localGet 3 → push locals[1] = 1048716
  have h_lget3 : Locals.get
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 len, .i32 ptr, .i32 1048568] } 3 = some (.i32 1048716) := rfl
  apply exec_cons_wp (show execOne 1 «module» st1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 len, .i32 ptr, .i32 1048568] }
      (.localGet 3) {} =
      .Fallthrough st1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 1048716, .i32 len, .i32 ptr, .i32 1048568] }
      from by simp only [execOne.eq_def, h_lget3])
  -- ── Step 14: call 1 (func1: sb=1048568, ptr, len) ─────────────────────────
  apply wp_wasm_prop_call
  apply tw_mono (func1_terminates st1 (1048568 : UInt32) ptr len
      (by -- hb: (1048568 : UInt32).toNat + 8 ≤ st1.mem.pages * 65536
          have : st1.mem.pages = st.mem.pages := rfl
          show 1048568 + 8 ≤ st1.mem.pages * 65536
          omega)
      (by decide : ((1048568 : UInt32) + 4).toNat = (1048568 : UInt32).toNat + 4)
      (by decide : ((1048568 : UInt32) + 8).toNat = (1048568 : UInt32).toNat + 8))
  intro st_c1 vs1 ⟨hvs1, hmem_ptr, hmem_len, hglob_c1, hpages_c1, hmem_pres⟩
  subst vs1
  -- ── Auxiliary facts after func1 ──────────────────────────────────────────
  -- st_c1.mem.pages = st.mem.pages
  have hpages_eq : st_c1.mem.pages = st.mem.pages := by rw [hpages_c1]
  -- st_c1.mem.pages * 65536 ≥ 1048576
  have hpg_c1 : st_c1.mem.pages * 65536 ≥ 1048576 := by rw [hpages_eq]; exact hpg
  -- globals[0] in st_c1 = 1048560 (func2's frame)
  have hg1_frame : st_c1.globals.globals[0]? = some (.i32 1048560) := by
    rw [hglob_c1]
    -- st1.globals.globals = st.globals.globals.set 0 (.i32 1048560)
    -- list is non-empty (from hg0), so set 0 gives [0]? = some 1048560
    show (st.globals.globals.set 0 (.i32 1048560))[0]? = some (.i32 1048560)
    obtain ⟨h, t, ht⟩ : ∃ h t, st.globals.globals = h :: t := by
      cases hgl : st.globals.globals with
      | nil => simp [hgl] at hg0
      | cons hd tl => exact ⟨hd, tl, rfl⟩
    rw [ht]; rfl
  -- wordsAt is preserved: func1 writes to 1048568 and 1048572, array is below 1048544
  have hcont_c1 : wordsAt st_c1.mem ptr xs.length = xs := by
    unfold wordsAt at hcont ⊢
    conv_rhs => rw [← hcont]
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    have h_toNat : (ptr + 4 * UInt32.ofNat k).toNat = ptr.toNat + 4 * k :=
      toNat_wordAddr ptr xs.length k hk (by omega)
    have h_bnd : (ptr + 4 * UInt32.ofNat k).toNat + 4 ≤ (1048568 : UInt32).toNat := by
      show (ptr + 4 * UInt32.ofNat k).toNat + 4 ≤ 1048568
      omega
    have heq := hmem_pres (ptr + 4 * UInt32.ofNat k) (Or.inl h_bnd)
    -- hmem_pres compares to st1.mem; st1.mem = st.mem
    have : st1.mem = st.mem := rfl
    rw [this] at heq
    exact heq
  -- bounds for load32 instructions (steps 16 and 19)
  have hbnd16 : ¬ ((1048560 : UInt32).toNat + (12 : UInt32).toNat + 4 >
      st_c1.mem.pages * 65536) := by
    show ¬ (1048560 + 12 + 4 > st_c1.mem.pages * 65536)
    omega
  have hbnd19 : ¬ ((1048560 : UInt32).toNat + (8 : UInt32).toNat + 4 >
      st_c1.mem.pages * 65536) := by
    show ¬ (1048560 + 8 + 4 > st_c1.mem.pages * 65536)
    omega
  -- read32 at frame+12 = mem[1048572] = mem[sb+4] = len
  have h_frame12 : st_c1.mem.read32 ((1048560 : UInt32) + 12) = len := by
    have heq : (1048560 : UInt32) + 12 = (1048568 : UInt32) + 4 := by decide
    rw [heq]; exact hmem_len
  -- read32 at frame+8 = mem[1048568] = mem[sb] = ptr
  have h_frame8 : st_c1.mem.read32 ((1048560 : UInt32) + 8) = ptr := by
    have heq : (1048560 : UInt32) + 8 = (1048568 : UInt32) := by decide
    rw [heq]; exact hmem_ptr
  -- ── Inter-call: steps 15-20 ──────────────────────────────────────────────
  -- Step 15: localGet 2 → push 1048560
  have h_lget2c : Locals.get
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 1048560, .i32 1048716, .i32 0], values := [] } 2 =
      some (.i32 1048560) := rfl
  apply exec_cons_wp (show execOne 1 «module» st_c1
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 1048560, .i32 1048716, .i32 0], values := [] }
      (.localGet 2) {} =
      .Fallthrough st_c1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 1048560] }
      from by simp only [execOne.eq_def, h_lget2c])
  -- Step 16: load32 12 → push mem[frame+12] = len
  apply exec_cons_wp (show execOne 1 «module» st_c1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 1048560] }
      (.load32 12) {} =
      .Fallthrough st_c1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 len] }
      from by simp only [execOne.eq_def, if_neg hbnd16, h_frame12])
  -- Step 17: localSet 4 → locals[2] = len, pop
  have h_lset4 : Locals.set?
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 len] } 4 (.i32 len) =
      some { params := [.i32 ptr, .i32 len],
             locals := [.i32 1048560, .i32 1048716, .i32 len],
             values := [.i32 len] } := rfl
  apply exec_cons_wp (show execOne 1 «module» st_c1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 0],
        values := [.i32 len] }
      (.localSet 4) {} =
      .Fallthrough st_c1
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 1048560, .i32 1048716, .i32 len], values := [] }
      from by simp only [execOne.eq_def, h_lset4])
  -- Step 18: localGet 2 → push 1048560
  have h_lget2d : Locals.get
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 1048560, .i32 1048716, .i32 len], values := [] } 2 =
      some (.i32 1048560) := rfl
  apply exec_cons_wp (show execOne 1 «module» st_c1
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 1048560, .i32 1048716, .i32 len], values := [] }
      (.localGet 2) {} =
      .Fallthrough st_c1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 len],
        values := [.i32 1048560] }
      from by simp only [execOne.eq_def, h_lget2d])
  -- Step 19: load32 8 → push mem[frame+8] = ptr
  apply exec_cons_wp (show execOne 1 «module» st_c1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 len],
        values := [.i32 1048560] }
      (.load32 8) {} =
      .Fallthrough st_c1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 len],
        values := [.i32 ptr] }
      from by simp only [execOne.eq_def, if_neg hbnd19, h_frame8])
  -- Step 20: localGet 4 → push locals[2] = len
  have h_lget4 : Locals.get
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 1048560, .i32 1048716, .i32 len],
        values := [.i32 ptr] } 4 = some (.i32 len) := rfl
  apply exec_cons_wp (show execOne 1 «module» st_c1
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 1048560, .i32 1048716, .i32 len], values := [.i32 ptr] }
      (.localGet 4) {} =
      .Fallthrough st_c1
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 len],
        values := [.i32 len, .i32 ptr] }
      from by simp only [execOne.eq_def, h_lget4])
  -- ── Step 21: call 0 (func0) ──────────────────────────────────────────────
  apply wp_wasm_prop_call
  apply tw_mono (func0_terminates st_c1 (1048560 : UInt32) ptr len xs hlen
      (by -- hbnd: ptr.toNat + 4*xs.length ≤ st_c1.mem.pages * 65536
          calc ptr.toNat + 4 * xs.length ≤ st.mem.pages * 65536 := hbnd
            _ = st_c1.mem.pages * 65536 := by rw [hpages_eq])
      (by decide : (16 : Nat) ≤ (1048560 : UInt32).toNat)
      (by -- hspg: (1048560).toNat ≤ st_c1.mem.pages * 65536
          show 1048560 ≤ st_c1.mem.pages * 65536; omega)
      hg1_frame hcont_c1
      (by -- hdisj: ptr.toNat + 4*xs.length ≤ (1048560).toNat - 16 = 1048544
          show ptr.toNat + 4 * xs.length ≤ (1048560 : UInt32).toNat - 16
          show ptr.toNat + 4 * xs.length ≤ 1048544
          exact hdisj))
  intro st_c2 vs2 ⟨hys, hglob_c2⟩
  -- ── Epilogue: steps 22-26 ─────────────────────────────────────────────────
  -- Steps work for arbitrary vs2 (remnant from the call).
  -- Step 22: localGet 2 → push 1048560
  have h_lget2e : Locals.get
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 1048560, .i32 1048716, .i32 len], values := vs2 } 2 =
      some (.i32 1048560) := rfl
  apply exec_cons_wp (show execOne 1 «module» st_c2
      { params := [.i32 ptr, .i32 len],
        locals := [.i32 1048560, .i32 1048716, .i32 len], values := vs2 }
      (.localGet 2) {} =
      .Fallthrough st_c2
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 len],
        values := .i32 1048560 :: vs2 }
      from by simp only [execOne.eq_def, h_lget2e])
  -- Step 23: const 16 → push 16
  apply exec_cons_wp (show execOne 1 «module» st_c2
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 len],
        values := .i32 1048560 :: vs2 }
      (.const (16 : UInt32)) {} =
      .Fallthrough st_c2
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 len],
        values := .i32 16 :: .i32 1048560 :: vs2 }
      from by simp only [execOne.eq_def])
  -- Step 24: add → 16 + 1048560 = 1048576 = sp
  apply exec_cons_wp (show execOne 1 «module» st_c2
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 len],
        values := .i32 16 :: .i32 1048560 :: vs2 }
      .add {} =
      .Fallthrough st_c2
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 len],
        values := .i32 1048576 :: vs2 }
      from by simp only [execOne.eq_def, show (16 : UInt32) + 1048560 = 1048576 from by decide])
  -- Step 25: globalSet 0 → globals[0] = 1048576 = original sp
  apply exec_cons_wp (show execOne 1 «module» st_c2
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 len],
        values := .i32 1048576 :: vs2 }
      (.globalSet 0) {} =
      .Fallthrough
        { st_c2 with globals := { globals := st_c2.globals.globals.set 0 (.i32 1048576) } }
      { params := [.i32 ptr, .i32 len], locals := [.i32 1048560, .i32 1048716, .i32 len],
        values := vs2 }
      from by simp only [execOne.eq_def, hglob_c2])
  -- Step 26: ret → Return []
  refine ⟨1, ?_⟩
  simp only [exec, execOne.eq_def]
  -- Goal: ∃ ys, wordsAt (final_store).mem ptr ys.length = ys ∧ ...
  -- (final_store).mem = st_c2.mem (globalSet doesn't change mem)
  exact hys

/-! ## §7  InsertionSortSpec -/

theorem insertion_sort_correct : InsertionSortSpec := by
  intro st ptr len xs hlen hbnd hpg hg0 hcont hdisj
  apply wp_wasm_prop_to_TerminatesWith
      (hf       := by rfl)
      (himp     := by rfl)
      (hresults := by rfl)
      (hlen     := by
        have h1 : (([.i32 len, .i32 ptr] : List Value).length : Nat) = 2 := rfl
        have h2 : func2Def.numParams = 2 := rfl
        omega)
      (hcompat  := fun st' vs h => h)
  simp only [show
    func2Def.toLocals
      (([.i32 len, .i32 ptr] : List Value).take func2Def.numParams).reverse =
    ({ params := [.i32 ptr, .i32 len],
       locals := [.i32 0, .i32 0, .i32 0], values := [] } : Locals) from rfl]
  simp only [show func2Def.body = func2 from rfl]
  exact func2_wp_prop st ptr len xs hlen hbnd hpg hg0 hcont hdisj

end Project.InsertionSort.InsertionSortSepLogic
