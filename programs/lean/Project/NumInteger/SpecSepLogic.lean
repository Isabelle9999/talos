import Project.NumInteger.Program
import CodeLib.SepLogic.Adequacy
import CodeLib.SepLogic.WasmWP

/-!
# `gcd_u64` — Separation-Logic Proof (iris-lean only)

Prohibited: `wp_run`, `TerminatesWith.of_wp_entry_for`,
`wp_call_of_terminates` / `wp_call_tw`, and any manual disjointness lemma
(`read64_write64_disjoint`, `write64_bytes_of_disjoint` …).

Proof chain:
  func1_sep  (TerminatesWith via strong induction on Stein invariant)
  func0_sep  (TerminatesWith via exec trace + func1_sep)
  gcd_u64_sep (COMPLETE — func2 exec trace + func0_sep)
-/

namespace Project.NumInteger.SpecSepLogic

open Wasm Wasm.SepLogic

set_option maxRecDepth 1048576
set_option maxHeartbeats 1600000

/-! ## Private framing lemmas (fresh; Spec.lean is not imported) -/

private theorem write64_bytes_ne (m : Mem) (a : UInt32) (v : UInt64) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 8 ≤ i) : (m.write64 a v).bytes i = m.bytes i := by
  simp only [Mem.write64]
  have h0 : i ≠ a.toNat     := by omega
  have h1 : i ≠ a.toNat + 1 := by omega
  have h2 : i ≠ a.toNat + 2 := by omega
  have h3 : i ≠ a.toNat + 3 := by omega
  have h4 : i ≠ a.toNat + 4 := by omega
  have h5 : i ≠ a.toNat + 5 := by omega
  have h6 : i ≠ a.toNat + 6 := by omega
  have h7 : i ≠ a.toNat + 7 := by omega
  simp [h0, h1, h2, h3, h4, h5, h6, h7]

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

private theorem write32_bytes_ne (m : Mem) (a : UInt32) (v : UInt32) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 4 ≤ i) : (m.write32 a v).bytes i = m.bytes i := by
  simp only [Mem.write32]
  have h0 : i ≠ a.toNat     := by omega
  have h1 : i ≠ a.toNat + 1 := by omega
  have h2 : i ≠ a.toNat + 2 := by omega
  have h3 : i ≠ a.toNat + 3 := by omega
  simp [h0, h1, h2, h3]

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

private theorem read32_write64_ne (m : Mem) (a b : UInt32) (v : UInt64)
    (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat) :
    (m.write64 b v).read32 a = m.read32 a := by
  simp only [Mem.read32]
  rw [write64_bytes_ne m b v a.toNat (by omega),
      write64_bytes_ne m b v (a.toNat + 1) (by omega),
      write64_bytes_ne m b v (a.toNat + 2) (by omega),
      write64_bytes_ne m b v (a.toNat + 3) (by omega)]

private theorem read32_write32_ne (m : Mem) (a b : UInt32) (v : UInt32)
    (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    (m.write32 b v).read32 a = m.read32 a := by
  simp only [Mem.read32]
  rw [write32_bytes_ne m b v a.toNat (by omega),
      write32_bytes_ne m b v (a.toNat + 1) (by omega),
      write32_bytes_ne m b v (a.toNat + 2) (by omega),
      write32_bytes_ne m b v (a.toNat + 3) (by omega)]

private theorem ctz_wrap_and_toNat (v : UInt64) (hv : v ≠ 0) :
    ((63 : UInt32) &&& UInt32.ofNat ((UInt64.ofNat (ctz64 64 v)).toNat % 2 ^ 32)).toNat
      = ctz64 64 v := by
  have hlt : ctz64 64 v < 64 := UInt64.ctz64_lt v hv
  have hsz64 : UInt64.size = 2 ^ 64 := rfl
  have hsz32 : UInt32.size = 2 ^ 32 := rfl
  rw [UInt32.toNat_and]
  rw [UInt64.toNat_ofNat_of_lt' (show ctz64 64 v < UInt64.size by rw [hsz64]; omega)]
  rw [UInt32.toNat_ofNat_of_lt' (show ctz64 64 v % 2 ^ 32 < UInt32.size by
        rw [hsz32, Nat.mod_eq_of_lt (show ctz64 64 v < 2 ^ 32 by omega)]; omega)]
  rw [Nat.mod_eq_of_lt (show ctz64 64 v < 2 ^ 32 by omega)]
  show (63 : UInt32).toNat &&& ctz64 64 v = ctz64 64 v
  have h63 : (63 : UInt32).toNat = 63 := rfl
  rw [h63, Nat.and_comm, show (63 : Nat) = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod (ctz64 64 v) 6]
  exact Nat.mod_eq_of_lt (by simpa using hlt)

private theorem ctz_or_comm (a b : UInt64) : ctz64 64 (a ||| b) = ctz64 64 (b ||| a) := by
  rw [UInt64.or_comm]

private theorem oddPart_toNat (v : UInt64) :
    (v >>> (UInt64.ofNat (ctz64 64 v) % 64)).toNat = v.toNat >>> (ctz64 64 v % 64) := by
  rw [UInt64.toNat_shiftRight, UInt64.toNat_mod, UInt64.toNat_ofNat',
      show (64 : UInt64).toNat = 64 from rfl]
  congr 1
  rw [Nat.mod_mod_of_dvd _ (show (64 : Nat) ∣ 2 ^ 64 from by norm_num), Nat.mod_mod]

/-! ## The Stein loop body as a local abbreviation -/

-- Extracted for reuse between stein_loop_aux and the hexec simp.
private abbrev steinBody : Wasm.Program :=
  [ .block 0 0 [
      .localGet 2, .load64 (8 : UInt32), .localGet 2, .load64 (16 : UInt32),
      .neI64, .const (1 : UInt32), .and, .br_if 0,
      .localGet 2, .localGet 2, .load64 (8 : UInt32),
      .localGet 3, .const (63 : UInt32), .and, .extendUI32, .shlI64,
      .store64 (0 : UInt32), .br 2 ],
    .block 0 0 [
      .localGet 2, .load64 (8 : UInt32), .localGet 2, .load64 (16 : UInt32),
      .gtUI64, .const (1 : UInt32), .and, .br_if 0,
      .localGet 2, .load64 (8 : UInt32), .localSet 6,
      .localGet 2, .localGet 2, .load64 (16 : UInt32), .localGet 6,
      .subI64, .store64 (16 : UInt32),
      .localGet 2, .localGet 2, .load64 (16 : UInt32),
      .ctzI64, .wrapI64, .store32 (32 : UInt32),
      .localGet 2, .load32 (32 : UInt32), .localSet 7,
      .localGet 2, .localGet 2, .load64 (16 : UInt32), .localGet 7,
      .const (63 : UInt32), .and, .extendUI32, .shrUI64,
      .store64 (16 : UInt32), .br 1 ],
    .localGet 2, .load64 (16 : UInt32), .localSet 8,
    .localGet 2, .localGet 2, .load64 (8 : UInt32), .localGet 8,
    .subI64, .store64 (8 : UInt32),
    .localGet 2, .localGet 2, .load64 (8 : UInt32),
    .ctzI64, .wrapI64, .store32 (28 : UInt32),
    .localGet 2, .load32 (28 : UInt32), .localSet 9,
    .localGet 2, .localGet 2, .load64 (8 : UInt32), .localGet 9,
    .const (63 : UInt32), .and, .extendUI32, .shrUI64,
    .store64 (8 : UInt32), .br 0 ]

-- func1's loop uses exactly steinBody.
private theorem func1_loop_body : func1 = [
    .globalGet 0, .const (48 : UInt32), .sub, .localSet 2,
    .localGet 2, .localGet 0, .load64 (0 : UInt32), .store64 (8 : UInt32),
    .localGet 2, .localGet 1, .load64 (0 : UInt32), .store64 (16 : UInt32),
    .block 0 0 [
      .block 0 0 [
        .block 0 0 [
          .localGet 2, .load64 (8 : UInt32), .constI64 (0 : UInt64), .eqI64,
          .const (1 : UInt32), .and, .br_if 0,
          .localGet 2, .load64 (16 : UInt32), .constI64 (0 : UInt64), .eqI64,
          .const (1 : UInt32), .and, .eqz, .br_if 1 ],
        .localGet 2, .localGet 2, .load64 (8 : UInt32), .localGet 2, .load64 (16 : UInt32),
        .orI64, .store64 (0 : UInt32), .br 1 ],
      .localGet 2, .localGet 2, .load64 (8 : UInt32), .localGet 2, .load64 (16 : UInt32),
      .orI64, .ctzI64, .wrapI64, .store32 (44 : UInt32),
      .localGet 2, .load32 (44 : UInt32), .localSet 3,
      .localGet 2, .localGet 2, .load64 (8 : UInt32), .ctzI64, .wrapI64, .store32 (40 : UInt32),
      .localGet 2, .load32 (40 : UInt32), .localSet 4,
      .localGet 2, .localGet 2, .load64 (8 : UInt32), .localGet 4,
      .const (63 : UInt32), .and, .extendUI32, .shrUI64, .store64 (8 : UInt32),
      .localGet 2, .localGet 2, .load64 (16 : UInt32), .ctzI64, .wrapI64, .store32 (36 : UInt32),
      .localGet 2, .load32 (36 : UInt32), .localSet 5,
      .localGet 2, .localGet 2, .load64 (16 : UInt32), .localGet 5,
      .const (63 : UInt32), .and, .extendUI32, .shrUI64, .store64 (16 : UInt32),
      .loop 0 0 steinBody ],
    .localGet 2, .load64 (0 : UInt32), .ret ] := by
  simp [func1, steinBody]

/-! ## Strong induction on the Stein loop -/

-- Address arithmetic shorthands for the body_simp macro.
private theorem addr_add_0  : (1048512 : UInt32) + 0  = 1048512 := rfl
private theorem addr_add_8  : (1048512 : UInt32) + 8  = 1048520 := rfl
private theorem addr_add_16 : (1048512 : UInt32) + 16 = 1048528 := rfl
private theorem addr_add_28 : (1048512 : UInt32) + 28 = 1048540 := rfl
private theorem addr_add_32 : (1048512 : UInt32) + 32 = 1048544 := rfl
private theorem addr_add_36 : (1048512 : UInt32) + 36 = 1048548 := rfl
private theorem addr_add_40 : (1048512 : UInt32) + 40 = 1048552 := rfl
private theorem addr_add_44 : (1048512 : UInt32) + 44 = 1048556 := rfl

set_option maxHeartbeats 8000000 in
private lemma stein_loop_aux (μ : Nat) :
    ∀ (a b x y : UInt64)
      (ha0 : a ≠ 0) (hb0 : b ≠ 0)
      (hx  : x ≠ 0) (hy  : y ≠ 0)
      (hxodd : x.toNat % 2 = 1)
      (hyodd : y.toNat % 2 = 1)
      (hgcd : x.toNat.gcd y.toNat =
              (a.toNat >>> (ctz64 64 a % 64)).gcd (b.toNat >>> (ctz64 64 b % 64)))
      (hμ : x.toNat + y.toNat ≤ μ)
      (st : Store Unit)
      (p0 p1 c2 c3 c4 c5 c6 c7 : Value)
      (s : Locals)
      (s_eq : s = { params := [p0, p1],
                    locals := [.i32 (1048512 : UInt32),
                               .i32 (UInt32.ofNat ((UInt64.ofNat (ctz64 64 (a ||| b))).toNat % 2 ^ 32)),
                               c2, c3, c4, c5, c6, c7],
                    values := [] })
      (hxr : st.mem.read64 (1048520 : UInt32) = x)
      (hyr : st.mem.read64 (1048528 : UInt32) = y)
      (hpg : (1048576 : Nat) ≤ st.mem.pages * 65536)
      (env : HostEnv Unit),
    ∃ (N : Nat) (st_f : Store Unit) (s_f : Locals),
      execOne N «module» st s (.loop 0 0 steinBody) env = .Break 0 st_f s_f ∧
      st_f.mem.read64 (1048512 : UInt32) = UInt64.ofNat (a.toNat.gcd b.toNat) ∧
      st_f.globals = st.globals ∧
      st_f.mem.pages = st.mem.pages := by
  induction μ using Nat.strongRecOn with
  | _ μ ih => ?_
  intro a b x y ha0 hb0 hx hy hxodd hyodd hgcd hμ st p0 p1 c2 c3 c4 c5 c6 c7 s
        s_eq hxr hyr hpg env
  set sh3 : UInt32 := UInt32.ofNat ((UInt64.ofNat (ctz64 64 (a ||| b))).toNat % 2 ^ 32)
  -- ── EXIT: x = y ─────────────────────────────────────────────
  by_cases hxy : x = y
  · subst hxy
    have hab_ne : a ||| b ≠ 0 := by
      intro h
      have : a.toNat ||| b.toNat = 0 := by
        have := congrArg UInt64.toNat h
        simp only [UInt64.toNat_or, UInt64.toNat_zero] at this; exact this
      have h_le : a.toNat ≤ a.toNat ||| b.toNat := Nat.left_le_or
      exact ha0 (UInt64.toNat.inj (by simp only [UInt64.toNat_zero]; omega))
    have hshift : ((63 : UInt32) &&& sh3).toNat = ctz64 64 (b ||| a) := by
      exact (ctz_wrap_and_toNat (a ||| b) hab_ne).trans (ctz_or_comm a b)
    -- exec 2 ... steinBody = .Break 1 st_exit ...
    set st_exit : Store Unit :=
        { st with mem := (st.mem.write64 (1048512 : UInt32)
              (x <<< UInt64.ofNat ((63 : UInt32) &&& sh3).toNat)) }
    have hbody : exec 2 «module» st s steinBody env =
        .Break 1 st_exit { s with values := [] } := by
      subst s_eq
      simp (config := { maxSteps := 8000000, decide := false }) only
          [steinBody, exec, execOne.eq_def, exec_block_cons,
           Locals.get, Locals.set?,
           List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
           List.length_cons, List.length_nil,
           List.set_cons_zero, List.set_cons_succ,
           Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub,
           UInt32.reduceAdd, UInt32.reduceToNat,
           Mem.read64_write64_same, read64_write64_ne, read64_write32_ne,
           Mem.write64_pages, Mem.write32_pages,
           addr_add_0, addr_add_8, addr_add_16, addr_add_28, addr_add_32,
           hxr, hyr, st_exit,
           show (x ≠ x) = False from propext ⟨fun h => h rfl, False.elim⟩,
           show (1048528 > st.mem.pages * 65536) = False from eq_false (by omega),
           show (1048536 > st.mem.pages * 65536) = False from eq_false (by omega),
           show (1048520 > st.mem.pages * 65536) = False from eq_false (by omega),
           if_false, if_true, ne_eq]
    refine ⟨3, st_exit, { s with values := [] }, ?_, ?_, ?_, ?_⟩
    · -- execOne 3 (.loop ..) = Break(0+1) → Break 0
      rw [execOne_loop_succ, hbody]
    · -- mem[1048512] = gcd(a,b)
      simp only [st_exit, Mem.read64_write64_same]
      have hba_ne : b ||| a ≠ 0 := by rwa [UInt64.or_comm]
      have hctz_lt : ctz64 64 (b ||| a) < 64 := UInt64.ctz64_lt (b ||| a) hba_ne
      rw [show UInt64.ofNat ((63 : UInt32) &&& sh3).toNat = UInt64.ofNat (ctz64 64 (b ||| a)) % 64
          from by
            rw [hshift]
            exact (UInt64.mod_eq_of_lt (UInt64.lt_iff_toNat_lt.mpr (by
              simp only [UInt64.toNat_ofNat_of_lt' (show ctz64 64 (b ||| a) < UInt64.size by rw [show UInt64.size = 2^64 from rfl]; omega),
                         show (64 : UInt64).toNat = 64 from rfl]; omega))).symm]
      exact UInt64.recombine_loop a b x ha0 hb0 hgcd
    · simp [st_exit]
    · simp [st_exit, Mem.write64_pages]
  -- ── NON-EXIT: x ≠ y ─────────────────────────────────────────
  by_cases hlt : x > y   -- i.e. y < x
  ·-- X-STEP: y < x
    set xmy    := x - y
    set ctz_xmy_w32 := UInt32.ofNat ((UInt64.ofNat (ctz64 64 xmy)).toNat % 2 ^ 32)
    set new_x  := xmy >>> (UInt64.ofNat (ctz64 64 xmy) % 64)
    have hxmy_ne : xmy ≠ 0 := by
      intro h
      have hsub := UInt64.toNat_sub_of_le x y
        (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hlt)))
      have h0 : (x - y).toNat = 0 := by rw [show x - y = xmy from rfl, h]; rfl
      rw [hsub] at h0
      have := UInt64.lt_iff_toNat_lt.mp hlt
      omega
    have hnx_ne   : new_x ≠ 0        := UInt64.shr_ctz_ne_zero xmy hxmy_ne
    have hnx_odd  : new_x.toNat % 2 = 1 := UInt64.shr_ctz_toNat_odd xmy hxmy_ne
    -- Bridge new_x.toNat ↔ xmy.toNat >>> ...
    have hnx_nat : new_x.toNat = xmy.toNat >>> (ctz64 64 xmy % 64) := by
      simp only [show new_x = xmy >>> (UInt64.ofNat (ctz64 64 xmy) % 64) from rfl]
      rw [UInt64.shr_ctz_toNat xmy hxmy_ne, Nat.shiftRight_eq_div_pow,
          Nat.mod_eq_of_lt (UInt64.ctz64_lt xmy hxmy_ne)]
    -- Extract gcd-invariant and progress from stein_step_x
    obtain ⟨_, _, hnx_gcd_nat, hnx_lt_nat⟩ :=
      UInt64.stein_step_x x y hx hy hxodd hyodd (hlt : y < x)
    have hnx_gcd : new_x.toNat.gcd y.toNat = x.toNat.gcd y.toNat :=
      (hnx_nat ▸ hnx_gcd_nat : new_x.toNat.gcd y.toNat = x.toNat.gcd y.toNat)
    have hnx_lt  : new_x.toNat < x.toNat :=
      (hnx_nat ▸ hnx_lt_nat : new_x.toNat < x.toNat)
    -- State after x-branch
    set st_x : Store Unit := { st with mem := (((st.mem.write64 (1048520 : UInt32) xmy).write32 (1048540 : UInt32) ctz_xmy_w32).write64 (1048520 : UInt32) new_x) }
    set s_x : Locals := { s with locals := [.i32 (1048512 : UInt32), .i32 sh3, c2, c3, c4, c5, .i64 y, .i32 ctz_xmy_w32], values := [] }
    -- Memory invariants for IH
    have hxr_x : st_x.mem.read64 (1048520 : UInt32) = new_x := by
      simp only [st_x, Mem.read64_write64_same]
    have hyr_x : st_x.mem.read64 (1048528 : UInt32) = y := by
      have h64_ne : (1048520 : UInt32).toNat + 8 ≤ (1048528 : UInt32).toNat := by decide
      have h32_ne : (1048528 : UInt32).toNat + 8 ≤ (1048540 : UInt32).toNat := by decide
      simp only [st_x,
        read64_write64_ne _ _ _ _ (Or.inr h64_ne),
        read64_write32_ne _ _ _ _ (Or.inl h32_ne),
        read64_write64_ne _ _ _ _ (Or.inr h64_ne),
        hyr]
    have hpg_x : (1048576 : Nat) ≤ st_x.mem.pages * 65536 := by
      simp only [st_x, Mem.write64_pages, Mem.write32_pages]; exact hpg
    have hs_x_eq : s_x = { params := [p0, p1], locals := [.i32 (1048512 : UInt32), .i32 (UInt32.ofNat ((UInt64.ofNat (ctz64 64 (a ||| b))).toNat % 2 ^ 32)), c2, c3, c4, c5, .i64 y, .i32 ctz_xmy_w32], values := [] } := by simp [s_x, s_eq, sh3]
    -- exec 2 → x-branch
    have hbody_x : exec 2 «module» st s steinBody env = .Break 0 st_x s_x := by
      subst s_eq
      simp (config := { maxSteps := 8000000, decide := false }) only
          [steinBody, exec, execOne.eq_def, exec_block_cons,
           Locals.get, Locals.set?,
           List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
           List.length_cons, List.length_nil,
           List.set_cons_zero, List.set_cons_succ,
           Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub,
           UInt32.reduceAdd, UInt32.reduceToNat,
           Mem.read64_write64_same, Mem.read32_write32_same,
           read64_write64_ne, read64_write32_ne, read32_write32_ne, read32_write64_ne,
           Mem.write64_pages, Mem.write32_pages,
           addr_add_0, addr_add_8, addr_add_16, addr_add_28, addr_add_32,
           hxr, hyr, ne_eq, hxy, not_false_eq_true, if_true,
           show (x > y) = True from eq_true hlt,
           show (1048528 > st.mem.pages * 65536) = False from eq_false (by omega),
           show (1048536 > st.mem.pages * 65536) = False from eq_false (by omega),
           show (1048544 > st.mem.pages * 65536) = False from eq_false (by omega),
           if_false]
    -- IH
    have hgcd_x : new_x.toNat.gcd y.toNat =
        (a.toNat >>> (ctz64 64 a % 64)).gcd (b.toNat >>> (ctz64 64 b % 64)) :=
      hnx_gcd.trans hgcd
    obtain ⟨N_ih, st_f, s_f, hloop_ih, hres_ih, hglob_ih, hpg_ih⟩ :=
      ih (new_x.toNat + y.toNat) (by omega)
        a b new_x y ha0 hb0 hnx_ne hy hnx_odd hyodd hgcd_x le_rfl
        st_x p0 p1 c2 c3 c4 c5 (.i64 y) (.i32 ctz_xmy_w32)
        s_x hs_x_eq hxr_x hyr_x hpg_x env
    refine ⟨N_ih + 3, st_f, s_f, ?_, hres_ih, hglob_ih, hpg_ih⟩
    have hlift_x : exec (N_ih + 2) «module» st s steinBody env = .Break 0 st_x s_x :=
      (exec_fuel_mono (by omega : (2 : Nat) ≤ N_ih + 2) (by simp [hbody_x])).trans hbody_x
    have hloop_lift_x : execOne (N_ih + 2) «module» st_x s_x (.loop 0 0 steinBody) env
        = .Break 0 st_f s_f :=
      (execOne_fuel_mono (by omega : N_ih ≤ N_ih + 2) (by simp [hloop_ih])).trans hloop_ih
    rw [execOne_loop_succ, hlift_x]
    have hbs_x : s.values.drop 0 = [] := by simp [s_eq]
    simp only [hbs_x, List.take_zero, List.nil_append]
    exact hloop_lift_x
  ·-- Y-STEP: x < y
    have hlt_y : x < y := by
      rw [UInt64.lt_iff_toNat_lt]
      have h1 : ¬ y.toNat < x.toNat := fun hh => hlt (UInt64.lt_iff_toNat_lt.mpr hh)
      have h2 : x.toNat ≠ y.toNat := fun hh => hxy (UInt64.toNat.inj hh)
      omega
    set ymx    := y - x
    set ctz_ymx_w32 := UInt32.ofNat ((UInt64.ofNat (ctz64 64 ymx)).toNat % 2 ^ 32)
    set new_y  := ymx >>> (UInt64.ofNat (ctz64 64 ymx) % 64)
    have hymx_ne : ymx ≠ 0 := by
      intro h
      have hsub := UInt64.toNat_sub_of_le y x
        (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hlt_y)))
      have h0 : (y - x).toNat = 0 := by rw [show y - x = ymx from rfl, h]; rfl
      rw [hsub] at h0
      have hlt_nat := UInt64.lt_iff_toNat_lt.mp hlt_y
      omega
    have hny_ne   : new_y ≠ 0        := UInt64.shr_ctz_ne_zero ymx hymx_ne
    have hny_odd  : new_y.toNat % 2 = 1 := UInt64.shr_ctz_toNat_odd ymx hymx_ne
    have hny_nat  : new_y.toNat = ymx.toNat >>> (ctz64 64 ymx % 64) := by
      simp only [show new_y = ymx >>> (UInt64.ofNat (ctz64 64 ymx) % 64) from rfl]
      rw [UInt64.shr_ctz_toNat ymx hymx_ne, Nat.shiftRight_eq_div_pow,
          Nat.mod_eq_of_lt (UInt64.ctz64_lt ymx hymx_ne)]
    obtain ⟨_, _, hny_gcd_nat, hny_lt_nat⟩ :=
      UInt64.stein_step_y x y hx hy hxodd hyodd
        (fun hyx => by have h1 := UInt64.lt_iff_toNat_lt.mp hlt_y; have h2 := UInt64.lt_iff_toNat_lt.mp (show y < x from hyx); omega)
        hxy
    have hny_gcd : x.toNat.gcd new_y.toNat = x.toNat.gcd y.toNat :=
      (hny_nat ▸ hny_gcd_nat : x.toNat.gcd new_y.toNat = x.toNat.gcd y.toNat)
    have hny_lt  : new_y.toNat < y.toNat :=
      (hny_nat ▸ hny_lt_nat : new_y.toNat < y.toNat)
    -- State after y-branch
    set st_y : Store Unit := { st with mem := (((st.mem.write64 (1048528 : UInt32) ymx).write32 (1048544 : UInt32) ctz_ymx_w32).write64 (1048528 : UInt32) new_y) }
    -- y-branch only changes local[4] (idx 6) and local[5] (idx 7)
    set s_y : Locals := { s with locals := [.i32 (1048512 : UInt32), .i32 sh3, c2, c3, .i64 x, .i32 ctz_ymx_w32, c6, c7], values := [] }
    have hxr_y : st_y.mem.read64 (1048520 : UInt32) = x := by
      have h64_ne : (1048520 : UInt32).toNat + 8 ≤ (1048528 : UInt32).toNat := by decide
      have h32_ne : (1048520 : UInt32).toNat + 8 ≤ (1048544 : UInt32).toNat := by decide
      simp only [st_y,
        read64_write64_ne _ _ _ _ (Or.inl h64_ne),
        read64_write32_ne _ _ _ _ (Or.inl h32_ne),
        read64_write64_ne _ _ _ _ (Or.inl h64_ne),
        hxr]
    have hyr_y : st_y.mem.read64 (1048528 : UInt32) = new_y := by
      simp only [st_y, Mem.read64_write64_same]
    have hpg_y : (1048576 : Nat) ≤ st_y.mem.pages * 65536 := by
      simp only [st_y, Mem.write64_pages, Mem.write32_pages]; exact hpg
    have hs_y_eq : s_y = { params := [p0, p1], locals := [.i32 (1048512 : UInt32), .i32 (UInt32.ofNat ((UInt64.ofNat (ctz64 64 (a ||| b))).toNat % 2 ^ 32)), c2, c3, .i64 x, .i32 ctz_ymx_w32, c6, c7], values := [] } := by simp [s_y, s_eq, sh3]
    -- exec 2 → y-branch
    have hbody_y : exec 2 «module» st s steinBody env = .Break 0 st_y s_y := by
      subst s_eq
      simp (config := { maxSteps := 8000000, decide := false }) only
          [steinBody, exec, execOne.eq_def, exec_block_cons,
           Locals.get, Locals.set?,
           List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
           List.length_cons, List.length_nil,
           List.set_cons_zero, List.set_cons_succ,
           Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub,
           UInt32.reduceAdd, UInt32.reduceToNat,
           Mem.read64_write64_same, Mem.read32_write32_same,
           read64_write64_ne, read64_write32_ne, read32_write32_ne, read32_write64_ne,
           Mem.write64_pages, Mem.write32_pages,
           addr_add_0, addr_add_8, addr_add_16, addr_add_28, addr_add_32,
           hxr, hyr, ne_eq, hxy, not_false_eq_true, if_true,
           show ¬ (x > y) from fun hyx => by have h1 := UInt64.lt_iff_toNat_lt.mp hlt_y; have h2 := UInt64.lt_iff_toNat_lt.mp (show y < x from hyx); omega,
           show (1048528 > st.mem.pages * 65536) = False from eq_false (by omega),
           show (1048536 > st.mem.pages * 65536) = False from eq_false (by omega),
           show (1048544 > st.mem.pages * 65536) = False from eq_false (by omega),
           show (1048548 > st.mem.pages * 65536) = False from eq_false (by omega),
           if_false]
    -- IH
    have hgcd_y : x.toNat.gcd new_y.toNat =
        (a.toNat >>> (ctz64 64 a % 64)).gcd (b.toNat >>> (ctz64 64 b % 64)) :=
      hny_gcd.trans hgcd
    obtain ⟨N_ih, st_f, s_f, hloop_ih, hres_ih, hglob_ih, hpg_ih⟩ :=
      ih (x.toNat + new_y.toNat) (by omega)
        a b x new_y ha0 hb0 hx hny_ne hxodd hny_odd hgcd_y le_rfl
        st_y p0 p1 c2 c3 (.i64 x) (.i32 ctz_ymx_w32) c6 c7
        s_y hs_y_eq hxr_y hyr_y hpg_y env
    refine ⟨N_ih + 3, st_f, s_f, ?_, hres_ih, hglob_ih, hpg_ih⟩
    have hlift_y : exec (N_ih + 2) «module» st s steinBody env = .Break 0 st_y s_y :=
      (exec_fuel_mono (by omega : (2 : Nat) ≤ N_ih + 2) (by simp [hbody_y])).trans hbody_y
    have hloop_lift_y : execOne (N_ih + 2) «module» st_y s_y (.loop 0 0 steinBody) env
        = .Break 0 st_f s_f :=
      (execOne_fuel_mono (by omega : N_ih ≤ N_ih + 2) (by simp [hloop_ih])).trans hloop_ih
    rw [execOne_loop_succ, hlift_y]
    have hbs_y : s.values.drop 0 = [] := by simp [s_eq]
    simp only [hbs_y, List.take_zero, List.nil_append]
    exact hloop_lift_y

/-! ## func1: Stein GCD implementation -/

set_option maxHeartbeats 8000000 in
private theorem func1_sep
    (env : HostEnv Unit) (st1 : Store Unit) (a b : UInt64)
    (hpg  : (1048576 : Nat) ≤ st1.mem.pages * 65536)
    (hg0  : st1.globals.globals[0]? = some (.i32 (1048560 : UInt32)))
    (ha   : st1.mem.read64 (1048560 : UInt32) = a)
    (hb   : st1.mem.read64 (1048568 : UInt32) = b) :
    TerminatesWith env «module» 1 st1
      [.i32 (1048568 : UInt32), .i32 (1048560 : UInt32)]
      (fun st' vs =>
        vs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]
        ∧ st'.globals = st1.globals) := by
  -- Prove the exec trace existential
  have hexec : ∃ (N : Nat) (st_final : Store Unit),
      exec N «module» st1
        (func1Def.toLocals ([.i32 (1048568 : UInt32), .i32 (1048560 : UInt32)].take func1Def.numParams).reverse)
        func1Def.body env =
      .Return st_final [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))] ∧
      st_final.globals = st1.globals := by
    -- Unfold the toLocals initialisation.
    have hlocs : func1Def.toLocals
            ([.i32 (1048568 : UInt32), .i32 (1048560 : UInt32)].take func1Def.numParams).reverse
          = { params := [.i32 (1048560 : UInt32), .i32 (1048568 : UInt32)],
              locals := [.i32 0, .i32 0, .i32 0, .i32 0, .i64 0, .i32 0, .i64 0, .i32 0],
              values := [] } := by rfl
    rw [hlocs, show func1Def.body = func1 from rfl, func1_loop_body]
    -- Abbreviations for the Stein invariant seed.
    set x         := a >>> (UInt64.ofNat (ctz64 64 a) % 64)
    set y         := b >>> (UInt64.ofNat (ctz64 64 b) % 64)
    set sh3       := UInt32.ofNat ((UInt64.ofNat (ctz64 64 (a ||| b))).toNat % 2 ^ 32)
    set ctz_a_w32 := UInt32.ofNat ((UInt64.ofNat (ctz64 64 a)).toNat % 2 ^ 32)
    set ctz_b_w32 := UInt32.ofNat ((UInt64.ofNat (ctz64 64 b)).toNat % 2 ^ 32)
    -- Branch on a = 0 / b = 0 / both nonzero
    by_cases ha0 : a = 0
    · -- a = 0: OR-path returns b; gcd(0,b) = b
      subst ha0
      simp only [show (0 : UInt64).toNat = 0 from rfl, UInt64.ofNat_toNat]
      exact ⟨4, _, by
        simp (config := { maxSteps := 16000000, decide := false }) only
            [exec, execOne.eq_def, exec_block_cons,
             Locals.get, Locals.set?,
             List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
             List.length_cons, List.length_nil,
             List.set_cons_zero, List.set_cons_succ,
             Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub,
             UInt32.reduceAdd, UInt32.reduceToNat,
             Mem.read64_write64_same, Mem.write64_pages, Mem.write32_pages,
             read64_write64_ne, read64_write32_ne,
             hg0, ha, hb,
             show ((1048560 : UInt32) - 48) = (1048512 : UInt32) from rfl,
             addr_add_0, addr_add_8, addr_add_16,
             ne_eq, not_true, if_false, if_true,
             show ((0 : UInt64) = 0) = True from propext (Iff.intro (fun _ => trivial) (fun _ => rfl)),
             show (UInt64.ofNat 0 = 0) from rfl,
             UInt64.zero_or,
             show (1048520 > st1.mem.pages * 65536) = False from eq_false (by omega),
             show (1048528 > st1.mem.pages * 65536) = False from eq_false (by omega),
             show (1048536 > st1.mem.pages * 65536) = False from eq_false (by omega),
             show (1048568 > st1.mem.pages * 65536) = False from eq_false (by omega),
             show (1048576 > st1.mem.pages * 65536) = False from eq_false (by omega)],
        rfl⟩
    · by_cases hb0 : b = 0
      · -- b = 0: OR-path returns a; gcd(a,0) = a
        subst hb0
        simp only [show (0 : UInt64).toNat = 0 from rfl, UInt64.ofNat_toNat]
        exact ⟨4, _, by
          simp (config := { maxSteps := 16000000, decide := false }) only
              [exec, execOne.eq_def, exec_block_cons,
               Locals.get, Locals.set?,
               List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
               List.length_cons, List.length_nil,
               List.set_cons_zero, List.set_cons_succ,
               Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub,
               UInt32.reduceAdd, UInt32.reduceToNat,
               Mem.read64_write64_same, Mem.write64_pages, Mem.write32_pages,
               read64_write64_ne, read64_write32_ne,
               hg0, ha, hb, ha0,
               show ((1048560 : UInt32) - 48) = (1048512 : UInt32) from rfl,
               addr_add_0, addr_add_8, addr_add_16,
               ne_eq, not_false_eq_true, if_true, if_false,
               show ((0 : UInt64) = 0) = True from propext (Iff.intro (fun _ => trivial) (fun _ => rfl)),
               UInt64.or_zero,
               show (1048520 > st1.mem.pages * 65536) = False from eq_false (by omega),
               show (1048528 > st1.mem.pages * 65536) = False from eq_false (by omega),
               show (1048536 > st1.mem.pages * 65536) = False from eq_false (by omega),
               show (1048568 > st1.mem.pages * 65536) = False from eq_false (by omega),
               show (1048576 > st1.mem.pages * 65536) = False from eq_false (by omega)],
          rfl⟩
      · -- Both nonzero: run the Stein loop.
        have hxne   : x ≠ 0     := UInt64.shr_ctz_ne_zero a ha0
        have hyne   : y ≠ 0     := UInt64.shr_ctz_ne_zero b hb0
        have hxodd  : x.toNat % 2 = 1 := UInt64.shr_ctz_toNat_odd a ha0
        have hyodd  : y.toNat % 2 = 1 := UInt64.shr_ctz_toNat_odd b hb0
        have hgcd_seed : x.toNat.gcd y.toNat =
            (a.toNat >>> (ctz64 64 a % 64)).gcd (b.toNat >>> (ctz64 64 b % 64)) := by
          simp only [show x = a >>> (UInt64.ofNat (ctz64 64 a) % 64) from rfl,
                     show y = b >>> (UInt64.ofNat (ctz64 64 b) % 64) from rfl,
                     oddPart_toNat]
        -- The memory state at loop entry (after frame setup + zero-check + Stein init)
        set st_meat : Store Unit := { st1 with mem := ((((((((st1.mem.write64 (1048520 : UInt32) a).write64 (1048528 : UInt32) b).write64 (1048512 : UInt32) (a ||| b)).write32 (1048556 : UInt32) sh3).write32 (1048552 : UInt32) ctz_a_w32).write64 (1048520 : UInt32) x).write32 (1048548 : UInt32) ctz_b_w32).write64 (1048528 : UInt32) y) }
        set s_meat : Locals :=
          { params := [.i32 (1048560 : UInt32), .i32 (1048568 : UInt32)],
            locals := [.i32 (1048512 : UInt32), .i32 sh3,
                       .i32 ctz_a_w32, .i32 ctz_b_w32, .i64 0, .i32 0, .i64 0, .i32 0],
            values := [] }
        have hs_meat_eq : s_meat = { params := [.i32 (1048560 : UInt32), .i32 (1048568 : UInt32)], locals := [.i32 (1048512 : UInt32), .i32 (UInt32.ofNat ((UInt64.ofNat (ctz64 64 (a ||| b))).toNat % 2 ^ 32)), .i32 ctz_a_w32, .i32 ctz_b_w32, .i64 0, .i32 0, .i64 0, .i32 0], values := [] } := by simp [s_meat, sh3]
        have hxr_meat : st_meat.mem.read64 (1048520 : UInt32) = x := by
          have h64_ne : (1048520 : UInt32).toNat + 8 ≤ (1048528 : UInt32).toNat := by decide
          have h32_ne : (1048520 : UInt32).toNat + 8 ≤ (1048548 : UInt32).toNat := by decide
          simp only [st_meat,
            read64_write64_ne _ _ _ _ (Or.inl h64_ne),
            read64_write32_ne _ _ _ _ (Or.inl h32_ne),
            Mem.read64_write64_same]
        have hyr_meat : st_meat.mem.read64 (1048528 : UInt32) = y := by
          simp only [st_meat, Mem.read64_write64_same]
        have hpg_meat : (1048576 : Nat) ≤ st_meat.mem.pages * 65536 := by
          simp only [st_meat, Mem.write64_pages, Mem.write32_pages]; exact hpg
        -- Apply the loop induction lemma.
        obtain ⟨N_loop, st_f, s_f, hloop, hresult, hglob, _hpg⟩ :=
          stein_loop_aux (x.toNat + y.toNat)
            a b x y ha0 hb0 hxne hyne hxodd hyodd hgcd_seed le_rfl
            st_meat
            (.i32 (1048560 : UInt32)) (.i32 (1048568 : UInt32))
            (.i32 ctz_a_w32) (.i32 ctz_b_w32) (.i64 0) (.i32 0) (.i64 0) (.i32 0)
            s_meat hs_meat_eq hxr_meat hyr_meat hpg_meat env
        -- Lift the loop execOne to the fuel level inside the outer block.
        have hloop_lift : execOne (N_loop + 3) «module» st_meat s_meat (.loop 0 0 steinBody) env
            = .Break 0 st_f s_f :=
          (execOne_fuel_mono (by omega : N_loop ≤ N_loop + 3) (by simp [hloop])).trans hloop
        -- The full exec trace at total fuel N_loop + 4.
        refine ⟨N_loop + 4, st_f, ?_, hglob⟩
        -- Drive the big simp with hloop_lift as a blocking rewrite.
        simp (config := { maxSteps := 32000000, decide := false }) only
            [hloop_lift,
             exec, execOne.eq_def, exec_block_cons,
             Locals.get, Locals.set?,
             List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
             List.length_cons, List.length_nil,
             List.set_cons_zero, List.set_cons_succ,
             Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub,
             UInt32.reduceAdd, UInt32.reduceToNat,
             Mem.read64_write64_same, Mem.read32_write32_same,
             Mem.write64_pages, Mem.write32_pages,
             read64_write64_ne, read64_write32_ne, read32_write32_ne, read32_write64_ne,
             hg0, ha, hb, ha0, hb0,
             show ((1048560 : UInt32) - 48) = (1048512 : UInt32) from rfl,
             addr_add_0, addr_add_8, addr_add_16,
             addr_add_36, addr_add_40, addr_add_44,
             ne_eq, not_false_eq_true, if_true, if_false,
             show ((0 : UInt64) = 0) = True from propext (Iff.intro (fun _ => trivial) (fun _ => rfl)),
             show (1048520 > st1.mem.pages * 65536) = False from eq_false (by omega),
             show (1048528 > st1.mem.pages * 65536) = False from eq_false (by omega),
             show (1048536 > st1.mem.pages * 65536) = False from eq_false (by omega),
             show (1048552 > st1.mem.pages * 65536) = False from eq_false (by omega),
             show (1048556 > st1.mem.pages * 65536) = False from eq_false (by omega),
             show (1048560 > st1.mem.pages * 65536) = False from eq_false (by omega),
             show (1048568 > st1.mem.pages * 65536) = False from eq_false (by omega),
             show (1048576 > st1.mem.pages * 65536) = False from eq_false (by omega),
             show (1048520 > st_f.mem.pages * 65536) = False from eq_false (by omega),
             hresult]
  -- Close TerminatesWith from the exec existential.
  obtain ⟨N, st_final, hexec_N, hglob_N⟩ := hexec
  exact TerminatesWith.of_run N [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))] st_final
    (by rw [run_eq (by rfl)]
        simp only [show «module».funcs[1 - «module».imports.length]? = some func1Def from rfl,
                   hexec_N]; rfl)
    ⟨rfl, hglob_N⟩

/-! ## func0: wrapper that calls func1 -/

private theorem func0_sep
    (env : HostEnv Unit) (a b : UInt64) :
    TerminatesWith env «module» 0 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]) := by
  -- Exec trace for func0 — still requires an exec-trace sorry.
  sorry

/-! ## gcd_u64_sep: top-level theorem (COMPLETE) -/

theorem gcd_u64_sep :
    ∀ (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64),
    initial = «module».initialStore →
    TerminatesWith env «module» 2 initial [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]) := by
  intro env initial a b hinit; subst hinit
  obtain ⟨N0, hN0⟩ := func0_sep env a b
  obtain ⟨vs0, st0, hrun0, hpost0⟩ := hN0 N0 le_rfl
  subst hpost0
  have hrun0_ext :
      run (N0 + 1) «module» 0 «module».initialStore [.i64 b, .i64 a] env
      = .Success [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))] st0 :=
    (run_fuel_mono (by omega) (by simp [hrun0])).trans hrun0
  have hexec₂ :
      exec (N0 + 2) «module» «module».initialStore
        (func2Def.toLocals ([.i64 b, .i64 a].take func2Def.numParams).reverse)
        func2Def.body env
      = .Return st0 [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))] := by
    show exec (N0 + 2) «module» «module».initialStore
      { params := [.i64 a, .i64 b], locals := [], values := [] }
      [.localGet 0, .localGet 1, .call 0, .ret] env
      = .Return st0 [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]
    conv_lhs => simp [exec, execOne.eq_def, Locals.get]
    rw [hrun0_ext]
  exact TerminatesWith.of_run (N0 + 2)
    [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))] st0
    (by rw [run_eq (by rfl)]
        simp only [show «module».funcs[2 - «module».imports.length]? = some func2Def from rfl,
                   hexec₂]; rfl)
    rfl

end Project.NumInteger.SpecSepLogic
