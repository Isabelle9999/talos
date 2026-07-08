import Project.MergeSort.MergeSepLogic
import Project.MergeSort.DrainSepLogic
import Project.MergeSort.Program
import CodeLib.SepLogic.Adequacy

namespace Wasm.SepLogic.MergeSort

open Wasm Project.MergeSort Project.MergeSort.Framing

variable [WasmHeapGS]

set_option maxHeartbeats 2000000 in
theorem func6_terminates
    (st : Store Unit)
    (left_ptr n_left right_ptr n_right out_ptr n_out sp : UInt32)
    (hsp    : st.globals.globals[0]? = some (.i32 sp))
    (hsp_lo : 32 ≤ sp.toNat)
    (hsp_hi : sp.toNat ≤ st.mem.pages * 65536)
    (hcap   : n_left.toNat + n_right.toNat ≤ n_out.toNat)
    (hL_bnd : left_ptr.toNat  + 4 * n_left.toNat  ≤ st.mem.pages * 65536)
    (hR_bnd : right_ptr.toNat + 4 * n_right.toNat ≤ st.mem.pages * 65536)
    (hO_bnd : out_ptr.toNat   + 4 * n_out.toNat   ≤ st.mem.pages * 65536)
    (hpages : st.mem.pages * 65536 ≤ 4294967296)
    (hLR_dj : left_ptr.toNat  + 4 * n_left.toNat  ≤ right_ptr.toNat ∨
              right_ptr.toNat + 4 * n_right.toNat ≤ left_ptr.toNat)
    (hLO_dj : left_ptr.toNat  + 4 * n_left.toNat  ≤ out_ptr.toNat ∨
              out_ptr.toNat   + 4 * n_out.toNat   ≤ left_ptr.toNat)
    (hRO_dj : right_ptr.toNat + 4 * n_right.toNat ≤ out_ptr.toNat ∨
              out_ptr.toNat   + 4 * n_out.toNat   ≤ right_ptr.toNat)
    (hFL_dj : (sp - 32).toNat + 20 ≤ left_ptr.toNat ∨
              left_ptr.toNat  + 4 * n_left.toNat  ≤ (sp - 32).toNat)
    (hFR_dj : (sp - 32).toNat + 20 ≤ right_ptr.toNat ∨
              right_ptr.toNat + 4 * n_right.toNat ≤ (sp - 32).toNat)
    (hFO_dj : (sp - 32).toNat + 20 ≤ out_ptr.toNat ∨
              out_ptr.toNat   + 4 * n_out.toNat   ≤ (sp - 32).toNat) :
    TerminatesWith {} «module» 6 st
      [.i32 n_out, .i32 out_ptr, .i32 n_right, .i32 right_ptr, .i32 n_left, .i32 left_ptr]
      (fun st' _ => True) := by
  apply wp_wasm_prop_to_TerminatesWith (f := func6Def)
  · rfl
  · rfl
  · rfl
  · simp [Function.numParams, func6Def]
  · intro _ _ _; trivial
  let frame   : UInt32  := sp - 32
  let loc_init : Locals :=
    func6Def.toLocals ([.i32 n_out, .i32 out_ptr, .i32 n_right, .i32 right_ptr,
                         .i32 n_left, .i32 left_ptr].take 6).reverse
  let loc₁    : Locals  :=
    { loc_init with locals := loc_init.locals.set 0 (.i32 frame) }
  let st₁     : Store Unit :=
    { st with
      globals := { st.globals with globals := st.globals.globals.set 0 (.i32 frame) }
      mem     := st.mem
                  |>.write32 (frame + 20) 0 |>.write32 (frame + 24) 0
                  |>.write32 (frame + 28) 0 |>.write32 (frame + 8)  0
                  |>.write32 (frame + 12) 0 |>.write32 (frame + 16) 0 }
  -- BLOCKER: MergeLoopInv / DrainInv are `private` in MergeSepLogic / DrainSepLogic.
  -- Constructing the invariant or applying main_merge_loop_spec / right_drain_spec
  -- from outside those files requires making those types public first.
  have h_main : wp_wasm_prop «module» st₁ loc₁ (func6.drop 27) {} (fun _ _ => True) := by
    sorry
  obtain ⟨N, hN⟩ := h_main
  have h_setup : exec (N + 27) «module» st
      (func6Def.toLocals (List.take func6Def.numParams
          [.i32 n_out, .i32 out_ptr, .i32 n_right, .i32 right_ptr,
           .i32 n_left, .i32 left_ptr]).reverse)
      func6Def.body {} =
      exec N «module» st₁ loc₁ (func6.drop 27) {} := by
    have hle32 : (32 : UInt32) ≤ sp :=
      UInt32.le_iff_toNat_le.mpr (by simpa using hsp_lo)
    have hfr : frame.toNat = sp.toNat - 32 :=
      UInt32.toNat_sub_of_le sp 32 hle32
    have haddr8  : (frame + 8).toNat  = frame.toNat + 8  := by
      have h : (8  : UInt32).toNat = 8  := rfl
      rw [UInt32.toNat_add, h]; omega
    have haddr12 : (frame + 12).toNat = frame.toNat + 12 := by
      have h : (12 : UInt32).toNat = 12 := rfl
      rw [UInt32.toNat_add, h]; omega
    have haddr16 : (frame + 16).toNat = frame.toNat + 16 := by
      have h : (16 : UInt32).toNat = 16 := rfl
      rw [UInt32.toNat_add, h]; omega
    have haddr20 : (frame + 20).toNat = frame.toNat + 20 := by
      have h : (20 : UInt32).toNat = 20 := rfl
      rw [UInt32.toNat_add, h]; omega
    have haddr24 : (frame + 24).toNat = frame.toNat + 24 := by
      have h : (24 : UInt32).toNat = 24 := rfl
      rw [UInt32.toNat_add, h]; omega
    have haddr28 : (frame + 28).toNat = frame.toNat + 28 := by
      have h : (28 : UInt32).toNat = 28 := rfl
      rw [UInt32.toNat_add, h]; omega
    have hfr_toNat : (sp - 32 : UInt32).toNat = frame.toNat := rfl
    have hb8  : ¬((sp - 32 : UInt32).toNat + (8  : UInt32).toNat + 4 > st.mem.pages * 65536) := by
      have : (8  : UInt32).toNat = 8  := rfl; omega
    have hb12 : ¬((sp - 32 : UInt32).toNat + (12 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
      have : (12 : UInt32).toNat = 12 := rfl; omega
    have hb16 : ¬((sp - 32 : UInt32).toNat + (16 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
      have : (16 : UInt32).toNat = 16 := rfl; omega
    have hb20 : ¬((sp - 32 : UInt32).toNat + (20 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
      have : (20 : UInt32).toNat = 20 := rfl; omega
    have hb24 : ¬((sp - 32 : UInt32).toNat + (24 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
      have : (24 : UInt32).toNat = 24 := rfl; omega
    have hb28 : ¬((sp - 32 : UInt32).toNat + (28 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
      have : (28 : UInt32).toNat = 28 := rfl; omega
    -- hrd: the address used in the preamble loads is sp-32 (= frame); use haddr lemmas to connect
    have hrd20 : (st.mem.write32 (sp - 32 + 20) 0 |>.write32 (sp - 32 + 24) 0
        |>.write32 (sp - 32 + 28) 0).read32 (sp - 32 + 20) = 0 := by
      rw [Mem.read32_write32_of_disjoint _ _ _ _ (Or.inr (by
            have h1 : (sp - 32 + 20 : UInt32).toNat = frame.toNat + 20 := haddr20
            have h2 : (sp - 32 + 28 : UInt32).toNat = frame.toNat + 28 := haddr28
            omega)),
          Mem.read32_write32_of_disjoint _ _ _ _ (Or.inr (by
            have h1 : (sp - 32 + 20 : UInt32).toNat = frame.toNat + 20 := haddr20
            have h2 : (sp - 32 + 24 : UInt32).toNat = frame.toNat + 24 := haddr24
            omega)),
          Mem.read32_write32_same]
    have hrd24 : (st.mem.write32 (sp - 32 + 20) 0 |>.write32 (sp - 32 + 24) 0
        |>.write32 (sp - 32 + 28) 0 |>.write32 (sp - 32 + 8) 0).read32 (sp - 32 + 24) = 0 := by
      rw [Mem.read32_write32_of_disjoint _ _ _ _ (Or.inl (by
            have h1 : (sp - 32 + 8  : UInt32).toNat = frame.toNat + 8  := haddr8
            have h2 : (sp - 32 + 24 : UInt32).toNat = frame.toNat + 24 := haddr24
            omega)),
          Mem.read32_write32_of_disjoint _ _ _ _ (Or.inr (by
            have h1 : (sp - 32 + 24 : UInt32).toNat = frame.toNat + 24 := haddr24
            have h2 : (sp - 32 + 28 : UInt32).toNat = frame.toNat + 28 := haddr28
            omega)),
          Mem.read32_write32_same]
    have hrd28 : (st.mem.write32 (sp - 32 + 20) 0 |>.write32 (sp - 32 + 24) 0
        |>.write32 (sp - 32 + 28) 0 |>.write32 (sp - 32 + 8) 0
        |>.write32 (sp - 32 + 12) 0).read32 (sp - 32 + 28) = 0 := by
      rw [Mem.read32_write32_of_disjoint _ _ _ _ (Or.inl (by
            have h1 : (sp - 32 + 12 : UInt32).toNat = frame.toNat + 12 := haddr12
            have h2 : (sp - 32 + 28 : UInt32).toNat = frame.toNat + 28 := haddr28
            omega)),
          Mem.read32_write32_of_disjoint _ _ _ _ (Or.inl (by
            have h1 : (sp - 32 + 8  : UInt32).toNat = frame.toNat + 8  := haddr8
            have h2 : (sp - 32 + 28 : UInt32).toNat = frame.toNat + 28 := haddr28
            omega)),
          Mem.read32_write32_same]
    have hlp : loc_init.params.length = 6 := rfl
    have hll : loc_init.locals.length = 16 := by
      show (func6Def.locals.map ValueType.zero).length = 16; native_decide
    have hlocals_init : loc_init.locals =
        [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
         .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0] := by
      show func6Def.locals.map ValueType.zero =
        [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
         .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]
      native_decide
    have hN_ne : exec N «module» st₁ loc₁ (func6.drop 27) {} ≠ .OutOfFuel := by
      intro heq; simp [heq] at hN
    suffices h_eq : exec (N + 27) «module» st loc_init func6 {} =
        exec (N + 27) «module» st₁ loc₁ (func6.drop 27) {} by
      exact h_eq.trans (exec_fuel_mono (Nat.le_add_right N 27) hN_ne)
    rw [← List.take_append_drop 27 func6,
        show func6.take 27 = [
            .globalGet 0, .const (32 : UInt32), .sub, .localSet 6,
            .localGet 6, .globalSet 0,
            .localGet 6, .const (0 : UInt32), .store32 (20 : UInt32),
            .localGet 6, .const (0 : UInt32), .store32 (24 : UInt32),
            .localGet 6, .const (0 : UInt32), .store32 (28 : UInt32),
            .localGet 6, .localGet 6, .load32 (20 : UInt32), .store32 (8  : UInt32),
            .localGet 6, .localGet 6, .load32 (24 : UInt32), .store32 (12 : UInt32),
            .localGet 6, .localGet 6, .load32 (28 : UInt32), .store32 (16 : UInt32)
          ] from rfl]
    conv_lhs =>
      simp only [List.cons_append, List.nil_append,
                 exec, execOne.eq_def,
                 hsp, hrd20, hrd24, hrd28,
                 hlocals_init, hlp, hll,
                 Locals.get, Locals.set?,
                 List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
                 List.set_cons_zero, List.set_cons_succ,
                 List.length_cons, List.length_nil, List.length_set,
                 Mem.read32_write32_same, Mem.write32_pages,
                 if_neg hb8, if_neg hb12, if_neg hb16,
                 if_neg hb20, if_neg hb24, if_neg hb28,
                 show ¬ ((6 : Nat) < 6) from by omega,
                 show (6 : Nat) < 6 + 16 from by omega,
                 show (6 - 6 : Nat) = 0 from by omega,
                 ite_true, ite_false]
    rfl
  exact ⟨N + 27, by rw [h_setup]; exact hN⟩

