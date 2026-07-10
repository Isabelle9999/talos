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
      (fun _ _ => True) := by
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
  -- Anonymous constructors elaborate against private types because Lean unfolds
  -- private defs when checking against an expected type from a public theorem.
  have h_main : wp_wasm_prop «module» st₁ loc₁ (func6.drop 27) {} (fun _ _ => True) := by
    -- address helpers for frame slots
    have hle32 : (32 : UInt32) ≤ sp :=
      UInt32.le_iff_toNat_le.mpr (by simpa using hsp_lo)
    have hframe_small : frame.toNat + 32 ≤ 4294967296 := by
      have h_eq : frame.toNat = (2 ^ 32 - (32 : UInt32).toNat + sp.toNat) % 2 ^ 32 :=
        UInt32.toNat_sub sp 32
      simp only [show (32 : UInt32).toNat = 32 from rfl,
                 show (2 : Nat) ^ 32 = 4294967296 from rfl] at h_eq
      have := hsp_lo
      have := hsp_hi
      have := hpages
      have := sp.toNat_lt
      omega
    have haddr8  : (frame + 8).toNat  = frame.toNat + 8  := by
      have : (8  : UInt32).toNat = 8  := rfl; rw [UInt32.toNat_add, this, Nat.mod_eq_of_lt (by omega)]
    have haddr12 : (frame + 12).toNat = frame.toNat + 12 := by
      have : (12 : UInt32).toNat = 12 := rfl; rw [UInt32.toNat_add, this, Nat.mod_eq_of_lt (by omega)]
    have haddr16 : (frame + 16).toNat = frame.toNat + 16 := by
      have : (16 : UInt32).toNat = 16 := rfl; rw [UInt32.toNat_add, this, Nat.mod_eq_of_lt (by omega)]
    -- initial invariant fields
    have hpages1 : st₁.mem.pages * 65536 ≤ 4294967296 := by
      simp only [st₁, Mem.write32_pages]; exact hpages
    have hframe20 : frame.toNat + 20 ≤ st₁.mem.pages * 65536 := by
      simp only [st₁, Mem.write32_pages]
      have hfr : frame.toNat = sp.toNat - 32 := UInt32.toNat_sub_of_le sp 32 hle32
      omega
    have hr8 : st₁.mem.read32 (frame + 8) = 0 := by
      show (st.mem |>.write32 (frame + 20) 0 |>.write32 (frame + 24) 0
           |>.write32 (frame + 28) 0 |>.write32 (frame + 8)  0
           |>.write32 (frame + 12) 0 |>.write32 (frame + 16) 0).read32 (frame + 8) = 0
      rw [Mem.read32_write32_of_disjoint _ _ _ 0 (Or.inr (by omega)),
          Mem.read32_write32_of_disjoint _ _ _ 0 (Or.inr (by omega)),
          Mem.read32_write32_same]
    have hr12 : st₁.mem.read32 (frame + 12) = 0 := by
      show (st.mem |>.write32 (frame + 20) 0 |>.write32 (frame + 24) 0
           |>.write32 (frame + 28) 0 |>.write32 (frame + 8)  0
           |>.write32 (frame + 12) 0 |>.write32 (frame + 16) 0).read32 (frame + 12) = 0
      rw [Mem.read32_write32_of_disjoint _ _ _ 0 (Or.inr (by omega)),
          Mem.read32_write32_same]
    have hr16 : st₁.mem.read32 (frame + 16) = 0 := by
      show (st.mem |>.write32 (frame + 20) 0 |>.write32 (frame + 24) 0
           |>.write32 (frame + 28) 0 |>.write32 (frame + 8)  0
           |>.write32 (frame + 12) 0 |>.write32 (frame + 16) 0).read32 (frame + 16) = 0
      rw [Mem.read32_write32_same]
    have hll1 : loc₁.locals.length = 16 := by
      change (func6Def.locals.map ValueType.zero).length = 16
      native_decide
    have hget6 : loc₁.get 6 = some (.i32 frame) := by
      simp only [Locals.get, show loc₁.params.length = 6 from rfl, hll1,
                 if_neg (show ¬((6 : Nat) < 6) from by omega),
                 if_pos (show (6 : Nat) < 6 + 16 from by omega),
                 show 6 - 6 = 0 from rfl]
      have hlen : 0 < loc_init.locals.length := by
        have : (loc_init.locals.set 0 (.i32 frame)).length = 16 := hll1
        rw [List.length_set] at this; omega
      exact List.getElem?_set_self hlen
    have hglobal1 : st₁.globals.globals[0]? = some (.i32 frame) := by
      show (st.globals.globals.set 0 (.i32 frame))[0]? = some (.i32 frame)
      have hlen : 0 < st.globals.globals.length := by
        rcases h : st.globals.globals with _ | ⟨hd, tl⟩
        · simp [h] at hsp
        · exact Nat.succ_pos _
      exact List.getElem?_set_self hlen
    -- phase 2: apply main_merge_loop_spec_exit
    obtain ⟨N₂, st₂, loc₂, h_exec₂, h_inv₂, hQ₂⟩ :=
      main_merge_loop_spec_exit (m := «module») (env := {}) st₁ loc₁
          frame out_ptr left_ptr right_ptr n_left n_right n_out 0 0 0
          ⟨0, 0,
           Nat.zero_le _, Nat.zero_le _,
           Nat.zero_le _, Nat.zero_le _,
           hr8, hr12, hr16,
           hget6, rfl, rfl, rfl, rfl, rfl, rfl,
           rfl, hll1,
           ⟨_, hglobal1⟩,
           fun _ _ => rfl, fun _ _ => rfl,
           hframe20,
           by omega,
           by simp only [st₁, Mem.write32_pages]; exact hL_bnd,
           by simp only [st₁, Mem.write32_pages]; exact hR_bnd,
           by simp only [st₁, Mem.write32_pages]; exact hO_bnd,
           hpages1, hLO_dj, hRO_dj, hLR_dj, hFL_dj, hFR_dj, hFO_dj⟩
    -- phase 3: drain from (st₂, loc₂)
    have h_drain : wp_wasm_prop «module» st₂ loc₂ (func6.drop 28) {} (fun _ _ => True) := by
      obtain ⟨i, j, _, hi_hi, _, hj_hi,
               hi_m, hj_m, hk_m,
               hf6, h0, h1, h2, h3, h4, h5,
               hlparams, hllocals, hglobal,
               hleft, hright,
               hpages, hk_global,
               hleft_global, hright_global, hout_global, hpages_u32,
               hleft_out_disj, hright_out_disj, hleft_right_disj,
               hframe_left_disj, hframe_right_disj, hframe_out_disj⟩ := h_inv₂
      obtain ⟨N_od, stR, vsR, h_loop⟩ :=
        outer_drain_exit (m := «module») (env := {}) st₂ loc₂
          frame out_ptr left_ptr right_ptr n_left n_right n_out i (i + j) j
          ⟨i, le_refl _, hi_hi, hj_hi,
           h0, h1, h2, h3, h4, h5, hf6,
           hlparams, hllocals, hglobal,
           hi_m, hj_m,
           by rw [hk_m]; congr 1; omega,
           fun _ h => by omega,
           fun _ _ => rfl, fun _ _ => rfl,
           hpages, by omega,
           hleft_global, hright_global, hout_global, hpages_u32,
           hleft_right_disj, hleft_out_disj, hright_out_disj,
           hframe_left_disj, hframe_right_disj, hframe_out_disj⟩
      have hloop_sing : ∀ F (stT : Store Unit) (locT : Locals),
          exec F «module» stT locT [.loop 0 0 outerDrainBody] {} =
          execOne F «module» stT locT (.loop 0 0 outerDrainBody) {} := fun F stT locT => by
        cases F with
        | zero => simp [exec, execOne]
        | succ f =>
          simp only [exec]
          rcases execOne (f + 1) «module» stT locT (.loop 0 0 outerDrainBody) {} with
            ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_⟩ | _ <;> rfl
      have h_eo_od : execOne N_od «module» st₂ loc₂ (.loop 0 0 outerDrainBody) {} =
          .Return stR vsR :=
        (hloop_sing N_od st₂ loc₂).symm.trans h_loop
      refine ⟨N_od, ?_⟩
      rw [show func6.drop 28 = .loop 0 0 outerDrainBody :: func6.drop 29 from rfl]
      simp only [exec, h_eo_od]
    obtain ⟨N₃, hN₃⟩ := h_drain
    -- compose phases 2 and 3
    refine ⟨N₂ + N₃ + 2, ?_⟩
    have hblock_sing : ∀ F (stT : Store Unit) (locT : Locals),
        exec F «module» stT locT [.block 0 0 [.loop 0 0 mainMergeBody]] {} =
        execOne F «module» stT locT (.block 0 0 [.loop 0 0 mainMergeBody]) {} := fun F stT locT => by
      cases F with
      | zero => simp [exec, execOne]
      | succ f =>
        simp only [exec]
        rcases execOne (f + 1) «module» stT locT (.block 0 0 [.loop 0 0 mainMergeBody]) {} with
          ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_⟩ | _ <;> rfl
    have h_eoN2 : execOne N₂ «module» st₁ loc₁ (.block 0 0 [.loop 0 0 mainMergeBody]) {} =
        .Fallthrough st₂ loc₂ :=
      (hblock_sing N₂ st₁ loc₁).symm.trans h_exec₂
    have h_eo_big : execOne (N₂ + N₃ + 2) «module» st₁ loc₁
        (.block 0 0 [.loop 0 0 mainMergeBody]) {} = .Fallthrough st₂ loc₂ :=
      (execOne_fuel_mono (by omega) (by rw [h_eoN2]; intro h; cases h)).trans h_eoN2
    have hN₃_ne : exec N₃ «module» st₂ loc₂ (func6.drop 28) {} ≠ .OutOfFuel := by
      intro h; simp [h] at hN₃
    have h28_big : exec (N₂ + N₃ + 2) «module» st₂ loc₂ (func6.drop 28) {} =
        exec N₃ «module» st₂ loc₂ (func6.drop 28) {} :=
      exec_fuel_mono (by omega) hN₃_ne
    have hcons : exec (N₂ + N₃ + 2) «module» st₁ loc₁
        (.block 0 0 [.loop 0 0 mainMergeBody] :: func6.drop 28) {} =
        exec (N₂ + N₃ + 2) «module» st₂ loc₂ (func6.drop 28) {} := by
      simp only [exec, h_eo_big]
    rw [show func6.drop 27 = .block 0 0 [.loop 0 0 mainMergeBody] :: func6.drop 28 from rfl,
        hcons, h28_big]
    exact hN₃
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
