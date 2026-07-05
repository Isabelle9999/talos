import Project.SwapElements.Program
import Project.SwapElements.Spec
import CodeLib.SepLogic.Adequacy
import CodeLib.SepLogic.WasmWP
import CodeLib.Entry
import CodeLib.RustStd.Frame

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

/-! ## Memory framing lemmas

Read-after-write algebra for 64-bit reads after disjoint 64-bit or 32-bit writes.
Needed to prove memory postconditions after the load/store chain. -/

omit inst in
private theorem write64_bytes_ne (m : Mem) (a : UInt32) (v : UInt64) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 8 ≤ i) : (m.write64 a v).bytes i = m.bytes i := by
  simp only [Mem.write64]
  have h0 : i ≠ a.toNat := by omega
  have h1 : i ≠ a.toNat + 1 := by omega
  have h2 : i ≠ a.toNat + 2 := by omega
  have h3 : i ≠ a.toNat + 3 := by omega
  have h4 : i ≠ a.toNat + 4 := by omega
  have h5 : i ≠ a.toNat + 5 := by omega
  have h6 : i ≠ a.toNat + 6 := by omega
  have h7 : i ≠ a.toNat + 7 := by omega
  simp [h0, h1, h2, h3, h4, h5, h6, h7]

omit inst in
private theorem read64_write64_ne (m : Mem) (a b : UInt32) (v : UInt64)
    (h : b.toNat + 8 ≤ a.toNat ∨ a.toNat + 8 ≤ b.toNat) :
    (m.write64 a v).read64 b = m.read64 b := by
  simp only [Mem.read64]
  rw [write64_bytes_ne m a v b.toNat (by omega),
      write64_bytes_ne m a v (b.toNat + 1) (by omega),
      write64_bytes_ne m a v (b.toNat + 2) (by omega),
      write64_bytes_ne m a v (b.toNat + 3) (by omega),
      write64_bytes_ne m a v (b.toNat + 4) (by omega),
      write64_bytes_ne m a v (b.toNat + 5) (by omega),
      write64_bytes_ne m a v (b.toNat + 6) (by omega),
      write64_bytes_ne m a v (b.toNat + 7) (by omega)]

omit inst in
private theorem write32_bytes_ne (m : Mem) (a v : UInt32) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 4 ≤ i) : (m.write32 a v).bytes i = m.bytes i := by
  simp only [Mem.write32]
  have h0 : i ≠ a.toNat := by omega
  have h1 : i ≠ a.toNat + 1 := by omega
  have h2 : i ≠ a.toNat + 2 := by omega
  have h3 : i ≠ a.toNat + 3 := by omega
  simp [h0, h1, h2, h3]

omit inst in
private theorem read64_write32_ne (m : Mem) (a b : UInt32) (v : UInt32)
    (h : b.toNat + 8 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v).read64 b = m.read64 b := by
  simp only [Mem.read64]
  rw [write32_bytes_ne m a v b.toNat (by omega),
      write32_bytes_ne m a v (b.toNat + 1) (by omega),
      write32_bytes_ne m a v (b.toNat + 2) (by omega),
      write32_bytes_ne m a v (b.toNat + 3) (by omega),
      write32_bytes_ne m a v (b.toNat + 4) (by omega),
      write32_bytes_ne m a v (b.toNat + 5) (by omega),
      write32_bytes_ne m a v (b.toNat + 6) (by omega),
      write32_bytes_ne m a v (b.toNat + 7) (by omega)]

omit inst in
private theorem read32_write32_ne (m : Mem) (a b : UInt32) (v : UInt32)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [write32_bytes_ne m a v b.toNat (by omega),
      write32_bytes_ne m a v (b.toNat + 1) (by omega),
      write32_bytes_ne m a v (b.toNat + 2) (by omega),
      write32_bytes_ne m a v (b.toNat + 3) (by omega)]

/-! ## Function termination lemmas

Call chain: func4 → func0 → func1 → func2.
Each is proved with TerminatesWith and composed via wp_call_of_terminates.

Key memory facts after the swap:
  final_mem = (st.mem
    .write32(1048568, ptr)         -- func3: ptr spill
    .write32(1048572, len)         -- func3: len spill
    .write64(1048552, vA)          -- func2: temp = *ptr_a
    .write64(ptr + 8*i, vB)       -- func2: *ptr_a = *ptr_b
    .write64(ptr + 8*j, vA))      -- func2: *ptr_b = temp
  where vA = st.mem.read64(ptr + 8*i), vB = st.mem.read64(ptr + 8*j).

The framing lemmas show that addresses ≥ 1048576 other than ptr+8*i and ptr+8*j
are unchanged by all these writes.

Spec gap: SwapElementsSpec does not require st.globals.globals[0]? = some (.i32 1048576).
Without that precondition, func4's globalGet 0 may trap and TerminatesWith is false
for those stores. The main sorry in swap_spec_sep is exactly that gap. -/

-- func3 spills ptr/len into the 8-byte slot at [1048568, 1048575]
-- body: write32(1048572, len) then write32(1048568, ptr)
omit inst in
private theorem func3_terminates (env : HostEnv Unit) (st : Store Unit)
    (ptr len : UInt32)
    (hpg : (1048576 : Nat) ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 3 st
      [.i32 (1048652 : UInt32), .i32 len, .i32 ptr, .i32 (1048568 : UInt32)]
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read32 (1048568 : UInt32) = ptr
        ∧ st'.mem.read32 (1048572 : UInt32) = len
        ∧ ∀ a : UInt32, (1048576 : Nat) ≤ a.toNat →
            st'.mem.read64 a = st.mem.read64 a) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32], [], func3, [], none⟩) rfl
  -- of_wp_entry_for passes args.take(numParams).reverse as locals.
  -- wp_run doesn't have List.reverse, so evaluate the reversed args via rfl first.
  simp only [show (⟨[.i32, .i32, .i32, .i32], [], func3, [], none⟩ : Wasm.Function).toLocals
      ([.i32 (1048652 : UInt32), .i32 len, .i32 ptr, .i32 (1048568 : UInt32)].take
        (⟨[.i32, .i32, .i32, .i32], [], func3, [], none⟩ : Wasm.Function).numParams).reverse =
      { params := [.i32 (1048568 : UInt32), .i32 ptr, .i32 len, .i32 (1048652 : UInt32)],
        locals := [], values := [] } from rfl]
  unfold func3
  -- wp_run includes Locals.get and evaluates all localGet steps.
  -- Bounds checks produce if-expressions (hpg is not in the simp set).
  wp_run
  sorry

-- func2: the actual swap via scratch at 1048552 (global0 = 1048560 at call time)
set_option maxHeartbeats 4000000 in
private theorem func2_terminates (env : HostEnv Unit) (st : Store Unit)
    (ptr_a ptr_b : UInt32)
    (hg0 : st.globals.globals[0]? = some (.i32 (1048560 : UInt32)))
    (hpg_scratch : (1048560 : Nat) ≤ st.mem.pages * 65536)
    (hpg_a : ptr_a.toNat + 8 ≤ st.mem.pages * 65536)
    (hpg_b : ptr_b.toNat + 8 ≤ st.mem.pages * 65536)
    -- ptr_a and ptr_b are both above the scratch region [1048544,1048559]
    (hge_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hge_b : (1048560 : Nat) ≤ ptr_b.toNat)
    -- either equal or 8-byte disjoint (guaranteed by 8-byte array stride)
    (hdisj : ptr_a = ptr_b ∨
             ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat) :
    TerminatesWith env «module» 2 st [.i32 ptr_b, .i32 ptr_a]
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read64 ptr_a = st.mem.read64 ptr_b
        ∧ st'.mem.read64 ptr_b = st.mem.read64 ptr_a
        ∧ ∀ a : UInt32,
            (a.toNat + 8 ≤ ptr_a.toNat ∨ ptr_a.toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
            st'.mem.read64 a = st.mem.read64 a) := by
  have himp : «module».imports[2]? = none := rfl
  have hf : «module».funcs[2 - «module».imports.length]? = some func2Def := rfl
  have hwp : wp_wasm_prop «module» st
      (func2Def.toLocals ([.i32 ptr_b, .i32 ptr_a].take func2Def.numParams).reverse)
      func2Def.body env
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read64 ptr_a = st.mem.read64 ptr_b
        ∧ st'.mem.read64 ptr_b = st.mem.read64 ptr_a
        ∧ ∀ a : UInt32,
            (a.toNat + 8 ≤ ptr_a.toNat ∨ ptr_a.toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
            st'.mem.read64 a = st.mem.read64 a) := by
    apply wasm_heap_adequacy
    intro inst
    -- pre-prove memory postcondition on the exact write64 chain used by the wp steps
    -- addresses: 1048560-16+8, ptr_a+0, ptr_b+0 (offset immediates not yet reduced)
    have h1552_nat : (1048552 : UInt32).toNat = 1048552 := rfl
    have hne_a : (1048552 : UInt32).toNat + 8 ≤ ptr_a.toNat := by omega
    have hne_b : (1048552 : UInt32).toNat + 8 ≤ ptr_b.toNat := by omega
    have ha0 : ptr_a + (0 : UInt32) = ptr_a := by simp
    have hb0 : ptr_b + (0 : UInt32) = ptr_b := by simp
    have h1552eq : ((1048560 : UInt32) - 16 + 8) = (1048552 : UInt32) := rfl
    let m₁ := st.mem.write64 ((1048560 : UInt32) - 16 + 8) (st.mem.read64 (ptr_a + 0))
    let m₂ := m₁.write64 (ptr_a + 0) (m₁.read64 (ptr_b + 0))
    let m₃ := m₂.write64 (ptr_b + 0) (m₂.read64 ((1048560 : UInt32) - 16 + 8))
    have hm₁ : m₁ = st.mem.write64 ((1048560 : UInt32) - 16 + 8) (st.mem.read64 (ptr_a + 0)) := rfl
    have hm₂ : m₂ = m₁.write64 (ptr_a + 0) (m₁.read64 (ptr_b + 0)) := rfl
    have hm₃ : m₃ = m₂.write64 (ptr_b + 0) (m₂.read64 ((1048560 : UInt32) - 16 + 8)) := rfl
    have hpages : m₃.pages = st.mem.pages := by
      simp only [hm₃, hm₂, hm₁, Mem.write64_pages]
    have hread_a : m₃.read64 ptr_a = st.mem.read64 ptr_b := by
      simp only [hm₃, hm₂, hm₁, ha0, hb0, h1552eq]
      rcases hdisj with rfl | h | h
      · rw [Mem.read64_write64_same,
            read64_write64_ne _ ptr_a _ _ (Or.inl hne_a),
            Mem.read64_write64_same]
      · rw [read64_write64_ne _ ptr_b _ _ (Or.inl h),
            Mem.read64_write64_same,
            read64_write64_ne _ (1048552 : UInt32) _ _ (Or.inr hne_b)]
      · rw [read64_write64_ne _ ptr_b _ _ (Or.inr h),
            Mem.read64_write64_same,
            read64_write64_ne _ (1048552 : UInt32) _ _ (Or.inr hne_b)]
    have hread_b : m₃.read64 ptr_b = st.mem.read64 ptr_a := by
      simp only [hm₃, hm₂, hm₁, ha0, hb0, h1552eq]
      rw [Mem.read64_write64_same,
          read64_write64_ne _ ptr_a _ _ (Or.inl hne_a),
          Mem.read64_write64_same]
    have hread_ne : ∀ a : UInt32,
        (a.toNat + 8 ≤ ptr_a.toNat ∨ ptr_a.toNat + 8 ≤ a.toNat) →
        (a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ a.toNat) →
        (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
        m₃.read64 a = st.mem.read64 a := by
      intro a h1 h2 h3
      simp only [hm₃, hm₂, hm₁, ha0, hb0, h1552eq]
      rw [read64_write64_ne _ ptr_b _ _ h2,
          read64_write64_ne _ ptr_a _ _ h1,
          read64_write64_ne _ (1048552 : UInt32) _ _
            (by rcases h3 with h | h
                · exact Or.inl (by omega)
                · exact Or.inr (by omega))]
    show ⊢ wp_wasm «module» st
      { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (0 : UInt32)], values := [] }
      [.globalGet 0, .const (16 : UInt32), .sub, .localSet 2, .localGet 2, .localGet 0,
       .load64 (0 : UInt32), .store64 (8 : UInt32), .localGet 0, .localGet 1,
       .load64 (0 : UInt32), .store64 (0 : UInt32), .localGet 1, .localGet 2,
       .load64 (8 : UInt32), .store64 (0 : UInt32), .ret] env _
    apply wp_wasm_globalGet (hget := hg0)
    intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
    · iexact Hσ
    · apply wp_wasm_const (16 : UInt32)
      intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
      · iexact Hσ
      · apply wp_wasm_sub (hstack := rfl)
        intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
        · iexact Hσ
        · apply wp_wasm_localSet (hstack := rfl) (hset := rfl)
          intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
          · iexact Hσ
          · apply wp_wasm_localGet (hget := rfl)
            intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
            · iexact Hσ
            · apply wp_wasm_localGet (hget := rfl)
              intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
              · iexact Hσ
              · apply wp_wasm_load64 (hstack := rfl)
                    (hbounds := by
                      simp only [show (0 : UInt32).toNat = 0 from rfl]; omega)
                intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                · iexact Hσ
                · apply wp_wasm_store64 (hstack := rfl)
                      (hbounds := by
                        simp only [show (1048560 - 16 : UInt32).toNat = 1048544 from rfl,
                                   show (8 : UInt32).toNat = 8 from rfl]; omega)
                  intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                  · iexact Hσ
                  · apply wp_wasm_localGet (hget := rfl)
                    intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                    · iexact Hσ
                    · apply wp_wasm_localGet (hget := rfl)
                      intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                      · iexact Hσ
                      · apply wp_wasm_load64 (hstack := rfl)
                            (hbounds := by
                              simp only [Mem.write64_pages,
                                show (0 : UInt32).toNat = 0 from rfl]; omega)
                        intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                        · iexact Hσ
                        · apply wp_wasm_store64 (hstack := rfl)
                              (hbounds := by
                                simp only [Mem.write64_pages,
                                  show (0 : UInt32).toNat = 0 from rfl]; omega)
                          intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                          · iexact Hσ
                          · apply wp_wasm_localGet (hget := rfl)
                            intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                            · iexact Hσ
                            · apply wp_wasm_localGet (hget := rfl)
                              intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                              · iexact Hσ
                              · apply wp_wasm_load64 (hstack := rfl)
                                    (hbounds := by
                                      simp only [Mem.write64_pages,
                                        show (1048560 - 16 : UInt32).toNat = 1048544 from rfl,
                                        show (8 : UInt32).toNat = 8 from rfl]; omega)
                                intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                                · iexact Hσ
                                · apply wp_wasm_store64 (hstack := rfl)
                                      (hbounds := by
                                        simp only [Mem.write64_pages,
                                          show (0 : UInt32).toNat = 0 from rfl]; omega)
                                  intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                                  · iexact Hσ
                                  · -- ret
                                    unfold wp_wasm
                                    iapply least_fixpoint_unfold_mpr
                                    unfold wp_wasm_F
                                    dsimp only []
                                    exact BI.pure_intro ⟨rfl, rfl, hpages, hread_a, hread_b, hread_ne⟩
  obtain ⟨fuel₀, hwp_fuel⟩ := hwp
  have hresults : func2Def.results.length = 0 := rfl
  have hcr : ([.i32 ptr_b, .i32 ptr_a] : List Value).drop func2Def.numParams = [] := rfl
  cases hexec : exec fuel₀ «module» st
      (func2Def.toLocals ([.i32 ptr_b, .i32 ptr_a].take func2Def.numParams).reverse)
      func2Def.body env with
  | Fallthrough st' s' =>
    rw [hexec] at hwp_fuel; dsimp only at hwp_fuel
    exact TerminatesWith.of_run fuel₀ [] st'
      (by rw [run_eq himp]; simp [hf, hexec, hresults, hcr]) hwp_fuel
  | Return st' vals =>
    rw [hexec] at hwp_fuel; dsimp only at hwp_fuel
    exact TerminatesWith.of_run fuel₀ [] st'
      (by rw [run_eq himp]; simp [hf, hexec, hresults, hcr]) (hwp_fuel.1 ▸ hwp_fuel)
  | Break n st' s' => simp only [hexec] at hwp_fuel
  | Trap st' msg => simp only [hexec] at hwp_fuel
  | Invalid msg => simp only [hexec] at hwp_fuel
  | OutOfFuel => simp only [hexec] at hwp_fuel
  | ReturnCall fid st' vs => simp only [hexec] at hwp_fuel
  | Throwing tag targs st' s' => simp only [hexec] at hwp_fuel

-- func1: bounds-check i < len and j < len, compute addresses, call func2
-- called from func0 with args [.i32 1048604, .i32 j, .i32 i, .i32 len, .i32 ptr]
omit inst in
private theorem func1_terminates_sw (env : HostEnv Unit) (st : Store Unit)
    (ptr len i j : UInt32)
    (hi : i < len) (hj : j < len)
    (hpg : ptr.toNat + 8 * len.toNat ≤ st.mem.pages * 65536)
    (hptr : (1048576 : Nat) ≤ ptr.toNat)
    (hg0 : st.globals.globals[0]? = some (.i32 (1048560 : UInt32))) :
    TerminatesWith env «module» 1 st
      [.i32 (1048604 : UInt32), .i32 j, .i32 i, .i32 len, .i32 ptr]
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j)
        ∧ st'.mem.read64 (elemAddr ptr j) = st.mem.read64 (elemAddr ptr i)
        ∧ ∀ a : UInt32,
            (a.toNat + 8 ≤ (elemAddr ptr i).toNat ∨ (elemAddr ptr i).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (elemAddr ptr j).toNat ∨ (elemAddr ptr j).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
            st'.mem.read64 a = st.mem.read64 a) := by
  sorry

-- func0: simple wrapper that calls func1
omit inst in
private theorem func0_terminates_sw (env : HostEnv Unit) (st : Store Unit)
    (ptr len i j : UInt32)
    (hi : i < len) (hj : j < len)
    (hpg : ptr.toNat + 8 * len.toNat ≤ st.mem.pages * 65536)
    (hptr : (1048576 : Nat) ≤ ptr.toNat)
    (hg0 : st.globals.globals[0]? = some (.i32 (1048560 : UInt32))) :
    TerminatesWith env «module» 0 st
      [.i32 j, .i32 i, .i32 len, .i32 ptr]
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j)
        ∧ st'.mem.read64 (elemAddr ptr j) = st.mem.read64 (elemAddr ptr i)
        ∧ ∀ a : UInt32,
            (a.toNat + 8 ≤ (elemAddr ptr i).toNat ∨ (elemAddr ptr i).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (elemAddr ptr j).toNat ∨ (elemAddr ptr j).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
            st'.mem.read64 a = st.mem.read64 a) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32], [], func0, [], none⟩) rfl
  unfold func0; wp_run
  -- calls func1 with [1048604, j, i, len, ptr]
  apply wp_call_of_terminates
    (func1_terminates_sw env st ptr len i j hi hj hpg hptr hg0)
  rintro st' vs ⟨hrs, hglob, hpages, hrA, hrB, hother⟩
  subst hrs
  wp_run
  exact ⟨rfl, hglob, hpages, hrA, hrB, hother⟩

/-! ## Top-level spec -/

-- spec missing: st.globals.globals[0]? = some (.i32 1048576)
-- see comment above func1_terminates_sw
theorem swap_spec_sep : SwapElementsSpec := by
  intro env st ptr len i j hi hj hbound hptr
  -- without this, func4's globalGet 0 traps and TerminatesWith is false for those stores
  have hg0 : st.globals.globals[0]? = some (.i32 (1048576 : UInt32)) := by sorry
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32], [.i32, .i32, .i32], func4, [], none⟩) rfl
  unfold func4; wp_run
  simp only [hg0]
  -- global0 = 1048576 → fp = 1048560; func3(1048568, ptr, len, 1048652) → call func0
  -- then restore global0 = 1048576; ret
  -- pages ≥ 1048576/65536 = 16.0007... so pages ≥ 17 (from memory declaration)
  -- but spec only gives ptr + 8*len ≤ pages*65536 with ptr ≥ 1048576
  have hpg1576 : (1048576 : Nat) ≤ st.mem.pages * 65536 := by omega
  -- set global0 = 1048560 after func4's first globalSet
  -- then call func3 to spill ptr/len; then call func0 for the swap
  sorry

end Project.SwapElements.SwapSepLogic
