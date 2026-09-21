import CodeLib.SepLogic.SmallStepOutcomeLanguage
import CodeLib.SepLogic.SmallStepTotalLifting

/-!
# `CodeLib.RustStd.Template`

Reusable contract for `_RNvNtCsebHcaeoSrxy_3std5alloc8rust_oom` (class `51821617ff5a`).

The body is identical across every crate that links Rust's `std`, modulo the
crate-specific call target `k`.  `rustOOMPrefix` captures the first 14
instructions; `template_rust_oom k` is the full body
`rustOOMPrefix ++ [.call k, .unreachable]`; `RustOOMContractAt` states the WP
contract; `rustOOM_instantiate` proves it holds for any SP ≥ 16.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open scoped Outcome

/-- The 14-instruction body prefix of `rust_oom`, ending just before the
    crate-specific `call k; unreachable` tail. -/
def rustOOMPrefix : Wasm.Program :=
  [ .globalGet 0                -- sp = global[0]
  , .const 16                   -- 16
  , .sub                        -- frame = sp - 16
  , .localTee 2                 -- local[2] = frame; stack: [frame]
  , .globalSet 0                -- global[0] = frame; stack: []
  , .localGet 2                 -- frame
  , .localGet 1                 -- len  (param 1)
  , .store32 12                 -- mem[frame + 12] = len  (= mem[sp - 4] = len)
  , .localGet 2                 -- frame
  , .localGet 0                 -- ptr  (param 0)
  , .store32 8                  -- mem[frame + 8]  = ptr  (= mem[sp - 8] = ptr)
  , .localGet 2                 -- frame
  , .const 8                    -- 8
  , .add                        -- frame + 8 = sp - 8
  ]

/-- The full body of `rust_oom` parameterised by the crate-specific call target.
    Consumers prove `func.body = template_rust_oom calleeAbsIdx` by `rfl`. -/
def template_rust_oom (k : Nat) : Wasm.Program :=
  rustOOMPrefix ++ [.call k, .unreachable]

/-- Contract for the body of `rust_oom`.

    Parameters `sp w1 w2` are the stack-pointer value on entry and the old
    contents of the two shadow-stack cells the function overwrites.  The
    caller supplies:
    - `globalPointsToAt 0 0 (.i32 sp)` — ownership of global 0 (the SP)
    - `pointsTo_u32 0 (sp - 4) w1` — ownership of the slot at `frame + 12 = sp - 4`
    - `pointsTo_u32 0 (sp - 8) w2` — ownership of the slot at `frame + 8  = sp - 8`
    - an abstract residual resource `R` forwarded unchanged to the callee

    `hcallee` is the WP for calling `calleeIdx` once the prefix has run;
    consumers supply it from the callee's own contract. -/
def RustOOMContractAt [WasmSmallStepGS hlc α]
    (calleeIdx : Nat) (sp w1 w2 : UInt32) : Prop :=
  ∀ (ptr len : UInt32)
    {R : IProp (WasmHeapGF α)}
    {v₀ : Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → IProp (WasmHeapGF α)},
    (globalPointsToAt 0 0 (.i32 (sp - 16)) ∗
       pointsTo_u32 0 (sp - 4) len ∗
       pointsTo_u32 0 (sp - 8) ptr ∗ R ⊢
       WP (Expr.running
             ⟨⟨[.i32 ptr, .i32 len], [.i32 (sp - 16)], [.i32 (sp - 8)]⟩,
               .call calleeIdx :: .unreachable :: code,
               arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) →
    globalPointsToAt 0 0 (.i32 sp) ∗
      pointsTo_u32 0 (sp - 4) w1 ∗
      pointsTo_u32 0 (sp - 8) w2 ∗ R ⊢
      WP (Expr.running
            ⟨⟨[.i32 ptr, .i32 len], [v₀], []⟩,
              template_rust_oom calleeIdx ++ code,
              arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]

-- ── Arithmetic helpers ────────────────────────────────────────────────────────

private theorem sp_sub16_toNat {sp : UInt32} (hsp : (16 : UInt32) ≤ sp) :
    (sp - 16 : UInt32).toNat = sp.toNat - 16 :=
  UInt32.toNat_sub_of_le sp 16 hsp

private theorem store_hnowrap12 {sp : UInt32} (hsp : (16 : UInt32) ≤ sp) :
    ((sp - 16) + 12 : UInt32).toNat = (sp - 16).toNat + 12 := by
  have hf := sp_sub16_toNat hsp
  rw [UInt32.toNat_add, show (12 : UInt32).toNat = 12 from rfl]
  apply Nat.mod_eq_of_lt
  have := sp.toNat_lt; rw [hf]; unfold UInt32.size at this; omega

private theorem store_h1_12 {sp : UInt32} (hsp : (16 : UInt32) ≤ sp) :
    (((sp - 16) + 12) + 1 : UInt32).toNat = ((sp - 16) + 12).toNat + 1 := by
  have hf := sp_sub16_toNat hsp
  have h12 := store_hnowrap12 hsp
  rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]
  apply Nat.mod_eq_of_lt
  have := sp.toNat_lt; rw [h12, hf]; unfold UInt32.size at this; omega

private theorem store_h2_12 {sp : UInt32} (hsp : (16 : UInt32) ≤ sp) :
    (((sp - 16) + 12) + 2 : UInt32).toNat = ((sp - 16) + 12).toNat + 2 := by
  have hf := sp_sub16_toNat hsp
  have h12 := store_hnowrap12 hsp
  rw [UInt32.toNat_add, show (2 : UInt32).toNat = 2 from rfl]
  apply Nat.mod_eq_of_lt
  have := sp.toNat_lt; rw [h12, hf]; unfold UInt32.size at this; omega

private theorem store_h3_12 {sp : UInt32} (hsp : (16 : UInt32) ≤ sp) :
    (((sp - 16) + 12) + 3 : UInt32).toNat = ((sp - 16) + 12).toNat + 3 := by
  have hf := sp_sub16_toNat hsp
  have h12 := store_hnowrap12 hsp
  rw [UInt32.toNat_add, show (3 : UInt32).toNat = 3 from rfl]
  apply Nat.mod_eq_of_lt
  have := sp.toNat_lt; rw [h12, hf]; unfold UInt32.size at this; omega

private theorem store_hnowrap8 {sp : UInt32} (hsp : (16 : UInt32) ≤ sp) :
    ((sp - 16) + 8 : UInt32).toNat = (sp - 16).toNat + 8 := by
  have hf := sp_sub16_toNat hsp
  rw [UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl]
  apply Nat.mod_eq_of_lt
  have := sp.toNat_lt; rw [hf]; unfold UInt32.size at this; omega

private theorem store_h1_8 {sp : UInt32} (hsp : (16 : UInt32) ≤ sp) :
    (((sp - 16) + 8) + 1 : UInt32).toNat = ((sp - 16) + 8).toNat + 1 := by
  have hf := sp_sub16_toNat hsp
  have h8 := store_hnowrap8 hsp
  rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]
  apply Nat.mod_eq_of_lt
  have := sp.toNat_lt; rw [h8, hf]; unfold UInt32.size at this; omega

private theorem store_h2_8 {sp : UInt32} (hsp : (16 : UInt32) ≤ sp) :
    (((sp - 16) + 8) + 2 : UInt32).toNat = ((sp - 16) + 8).toNat + 2 := by
  have hf := sp_sub16_toNat hsp
  have h8 := store_hnowrap8 hsp
  rw [UInt32.toNat_add, show (2 : UInt32).toNat = 2 from rfl]
  apply Nat.mod_eq_of_lt
  have := sp.toNat_lt; rw [h8, hf]; unfold UInt32.size at this; omega

private theorem store_h3_8 {sp : UInt32} (hsp : (16 : UInt32) ≤ sp) :
    (((sp - 16) + 8) + 3 : UInt32).toNat = ((sp - 16) + 8).toNat + 3 := by
  have hf := sp_sub16_toNat hsp
  have h8 := store_hnowrap8 hsp
  rw [UInt32.toNat_add, show (3 : UInt32).toNat = 3 from rfl]
  apply Nat.mod_eq_of_lt
  have := sp.toNat_lt; rw [h8, hf]; unfold UInt32.size at this; omega

/-- `(sp - 16) + 12 = sp - 4` when `sp ≥ 16`. -/
private theorem frame_add12_eq {sp : UInt32} (hsp : (16 : UInt32) ≤ sp) :
    (sp - 16 : UInt32) + 12 = sp - 4 := by
  apply UInt32.toNat.inj
  have hf := sp_sub16_toNat hsp
  have hlt : sp.toNat < UInt32.size := sp.toNat_lt
  have hge : 16 ≤ sp.toNat := by
    have := UInt32.le_iff_toNat_le.mp hsp; simp [UInt32.toNat_ofNat] at this; omega
  have h12 := store_hnowrap12 hsp
  have h4le : (4 : UInt32) ≤ sp := by
    have : (4 : UInt32).toNat ≤ sp.toNat := by
      simp [UInt32.toNat_ofNat]; omega
    exact UInt32.le_iff_toNat_le.mpr this
  have hs4 : (sp - 4 : UInt32).toNat = sp.toNat - 4 := UInt32.toNat_sub_of_le sp 4 h4le
  rw [h12, hf, hs4]
  omega

/-- `(sp - 16) + 8 = sp - 8` when `sp ≥ 16`. -/
private theorem frame_add8_eq {sp : UInt32} (hsp : (16 : UInt32) ≤ sp) :
    (sp - 16 : UInt32) + 8 = sp - 8 := by
  apply UInt32.toNat.inj
  have hf := sp_sub16_toNat hsp
  have hlt : sp.toNat < UInt32.size := sp.toNat_lt
  have hge : 16 ≤ sp.toNat := by
    have := UInt32.le_iff_toNat_le.mp hsp; simp [UInt32.toNat_ofNat] at this; omega
  have h8 := store_hnowrap8 hsp
  have h8le : (8 : UInt32) ≤ sp := by
    have : (8 : UInt32).toNat ≤ sp.toNat := by
      simp [UInt32.toNat_ofNat]; omega
    exact UInt32.le_iff_toNat_le.mpr this
  have hs8 : (sp - 8 : UInt32).toNat = sp.toNat - 8 := UInt32.toNat_sub_of_le sp 8 h8le
  rw [h8, hf, hs8]
  omega

/-- `8 + (sp - 16) = sp - 8` when `sp ≥ 16`.
    Needed because `twp_add` computes `rhs + lhs` (stack order: const 8 on top). -/
private theorem frame_8_add_eq {sp : UInt32} (hsp : (16 : UInt32) ≤ sp) :
    (8 : UInt32) + (sp - 16) = sp - 8 := by
  rw [UInt32.add_comm]; exact frame_add8_eq hsp

/-- The `RustOOMContractAt` holds for any `sp ≥ 16`.

    Proof: step the 14-instruction prefix with `twp_globalGet`, `twp_globalSet`,
    `twp_store32` (for the two frame writes), and `wasm_twp_pures` for the pure
    arithmetic; then apply `hcallee` with the updated resources.

    The pre-`iintro` `rw` converts the `sp - 4` / `sp - 8` form in the
    precondition to the natural `(sp - 16) + 12` / `(sp - 16) + 8` form
    that `twp_store32` expects; the post-step `simp` converts back. -/
theorem rustOOM_instantiate [WasmSmallStepGS hlc α]
    (calleeIdx : Nat) (sp w1 w2 : UInt32) (hsp : (16 : UInt32) ≤ sp) :
    RustOOMContractAt (α := α) (hlc := hlc) calleeIdx sp w1 w2 := by
  unfold RustOOMContractAt template_rust_oom rustOOMPrefix
  intro ptr len R v₀ code arity remainder controls calls s E Φ hcallee
  -- Convert precondition addresses to the form twp_store32 expects
  rw [← frame_add12_eq hsp, ← frame_add8_eq hsp]
  iintro ⟨Hglobal, H1, H2, HR⟩
  -- Flatten the ++ chain so each wasm_twp_* can see the next :: instruction
  simp only [List.cons_append, List.nil_append]
  -- global.get 0
  wasm_twp_bind twp_globalGet with Hglobal => Hglobal
  -- i32.const 16; i32.sub
  wasm_twp_pures [twp_const twp_sub]
  -- local.tee 2 (normalise List.set immediately so locals = [sp - 16])
  wasm_twp_localTee [List.length, List.set]
  -- global.set 0
  wasm_twp_bind twp_globalSet with Hglobal => Hglobal
  -- local.get 2; local.get 1
  wasm_twp_pures [twp_localGet twp_localGet]
  -- i32.store offset=12: mem[frame + 12] = len
  wasm_twp_bind (twp_store32 w1
    (store_hnowrap12 hsp) (store_h1_12 hsp) (store_h2_12 hsp) (store_h3_12 hsp)) with H1 => H1
  -- local.get 2; local.get 0
  wasm_twp_pures [twp_localGet twp_localGet]
  -- i32.store offset=8: mem[frame + 8] = ptr
  wasm_twp_bind (twp_store32 w2
    (store_hnowrap8 hsp) (store_h1_8 hsp) (store_h2_8 hsp) (store_h3_8 hsp)) with H2 => H2
  -- local.get 2; i32.const 8; i32.add → stack top = (sp - 16) + 8
  wasm_twp_pures [twp_localGet twp_const twp_add]
  -- Normalise addresses, stack value, and the List.set from localTee:
  --   (sp-16)+12 → sp-4, (sp-16)+8 → sp-8 (hypothesis addresses)
  --   8+(sp-16) → sp-8 (stack top from twp_add, which computes rhs+lhs)
  --   [v₀].set (2-(0+1+1)) x = [x]  (definitionally rfl, bridges iapply)
  simp only [frame_8_add_eq hsp, frame_add8_eq hsp, frame_add12_eq hsp,
             show [v₀].set (2 - (0 + 1 + 1)) (Value.i32 (sp - 16)) =
               [Value.i32 (sp - 16)] from rfl]
  -- Apply callee contract with updated resources
  iapply hcallee
  isplitl_exacts [Hglobal H1 H2]
  iexact HR

end Wasm.SmallStep
