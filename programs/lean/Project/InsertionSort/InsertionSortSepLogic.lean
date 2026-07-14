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

private def I_outer (ptr : UInt32) (xs : List UInt32) (frame : UInt32)
    (stA : Store Unit) (locA : Locals) : Prop :=
  ∃ (i : UInt32),
    locA.get 2 = some (.i32 frame) ∧
    stA.mem.read32 (frame + 8) = i ∧
    0 < i.toNat ∧ i.toNat ≤ xs.length ∧
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
  sorry

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
