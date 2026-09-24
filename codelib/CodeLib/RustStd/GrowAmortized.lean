import CodeLib.SepLogic.SmallStepOutcomeLanguage
import CodeLib.SepLogic.SmallStepTotalLifting
import CodeLib.RustStd.RawVec

/-!
# `CodeLib.RustStd.GrowAmortized`

Template and contract for `RawVec::grow_amortized`, the 5-parameter growth
routine shared by every Rust crate that links `std` for `u8` allocations.
It has two relocated call targets — the alloc-error handler and `finish_grow`
— captured as the parameters `kHandler` and `kFinishGrow`.

Consumers prove `func_N = template_grow_amortized a b` by `rfl`; the contract
`GrowAmortizedContractAt` then applies without re-running the proof.

**Parameters** at the start of the body (local indices 0–4):
- param 0 `ptr`        : pointer to the `RawVec` header (capacity at [0], data at [4])
- param 1 `length`     : current element count
- param 2 `additional` : number of additional elements requested
- param 3 `alignment`  : allocation alignment
- param 4 `elementSize`: element size in bytes (must be 1 for this contract)

**Local** 5 (zero-initialised by caller):
- local 5 : i32 shadow-frame pointer (`sp - 16`)
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open scoped Outcome

/-- The continuation of `grow_amortized` after `call kFinishGrow`:
    check the result tag, write the header, restore the shadow-stack pointer. -/
private def growAmortized_cont (kHandler : Nat) : Program :=
  [ .block 0 0
      [ .localGet 5, .load32 4, .const 1, .ne, .br_if 0
      , .localGet 5, .load32 8
      , .localGet 5, .load32 12
      , .call kHandler, .unreachable ]
  , .localGet 5, .load32 8, .localSet 4
  , .localGet 0, .localGet 2, .store32 0
  , .localGet 0, .localGet 4, .store32 4
  , .localGet 5, .const 16, .add, .globalSet 0 ]

/-- The body of `RawVec::grow_amortized`, parameterised by the two crate-specific
    call targets.  Consumers prove `func_N = template_grow_amortized a b` by `rfl`. -/
def template_grow_amortized (kHandler kFinishGrow : Nat) : Wasm.Program :=
  [ .globalGet 0, .const 16, .sub, .localTee 5, .globalSet 0
  , .block 0 0
      [ .localGet 2, .localGet 1, .add, .localTee 1
      , .localGet 2, .geU, .br_if 0
      , .const 0, .const 0, .call kHandler, .unreachable ]
  , .localGet 5, .const 4, .add
  , .localGet 0, .load32 0, .localTee 2
  , .localGet 0, .load32 4
  , .localGet 1
  , .localGet 2, .const 1, .shl, .localTee 2
  , .localGet 1, .localGet 2, .gtU, .select
  , .localTee 2
  , .const 8, .const 4, .localGet 4, .const 1, .eq, .select
  , .localTee 1
  , .localGet 2, .localGet 1, .gtU, .select
  , .localTee 2
  , .localGet 3, .localGet 4
  , .call kFinishGrow ]
  ++ growAmortized_cont kHandler

-- ── Arithmetic helpers ────────────────────────────────────────────────────────

private theorem ga_sp_sub16_toNat {sp : UInt32} (hsp : (16 : UInt32) ≤ sp) :
    (sp - 16 : UInt32).toNat = sp.toNat - 16 :=
  UInt32.toNat_sub_of_le sp 16 hsp

private theorem ga_hnowrap4 {sp : UInt32} (hsp : (16 : UInt32) ≤ sp) :
    ((sp - 16) + 4 : UInt32).toNat = (sp - 16).toNat + 4 := by
  have hf := ga_sp_sub16_toNat hsp
  rw [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]
  apply Nat.mod_eq_of_lt
  have := sp.toNat_lt; rw [hf]; omega

private theorem ga_frame_add4_eq {sp : UInt32} (hsp : (16 : UInt32) ≤ sp) :
    (sp - 16 : UInt32) + 4 = sp - 12 := by
  apply UInt32.toNat.inj
  have hf := ga_sp_sub16_toNat hsp
  have hlt : sp.toNat < UInt32.size := sp.toNat_lt
  have hge : 16 ≤ sp.toNat := by
    have := UInt32.le_iff_toNat_le.mp hsp; simp [UInt32.toNat_ofNat] at this; omega
  have h4 := ga_hnowrap4 hsp
  have h12le : (12 : UInt32) ≤ sp := by
    have : (12 : UInt32).toNat ≤ sp.toNat := by simp [UInt32.toNat_ofNat]; omega
    exact UInt32.le_iff_toNat_le.mpr this
  have hs12 : (sp - 12 : UInt32).toNat = sp.toNat - 12 := UInt32.toNat_sub_of_le sp 12 h12le
  rw [h4, hf, hs12]; omega

/-- `(4 : UInt32) + (sp - 16) = sp - 12` when `sp ≥ 16`.
    Needed because `twp_add` computes `const + local` (const is TOS). -/
private theorem ga_frame_4_add_eq {sp : UInt32} (hsp : (16 : UInt32) ≤ sp) :
    (4 : UInt32) + (sp - 16) = sp - 12 := by
  rw [UInt32.add_comm]; exact ga_frame_add4_eq hsp

-- ptr ± n no-wrap lemmas (hypothesis: ptr.toNat + 7 < UInt32.size)

private theorem ga_ptr_h1 {ptr : UInt32} (h : ptr.toNat + 7 < UInt32.size) :
    (ptr + 1 : UInt32).toNat = ptr.toNat + 1 := by
  rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]
  exact Nat.mod_eq_of_lt (by unfold UInt32.size at h; omega)

private theorem ga_ptr_h2 {ptr : UInt32} (h : ptr.toNat + 7 < UInt32.size) :
    (ptr + 2 : UInt32).toNat = ptr.toNat + 2 := by
  rw [UInt32.toNat_add, show (2 : UInt32).toNat = 2 from rfl]
  exact Nat.mod_eq_of_lt (by unfold UInt32.size at h; omega)

private theorem ga_ptr_h3 {ptr : UInt32} (h : ptr.toNat + 7 < UInt32.size) :
    (ptr + 3 : UInt32).toNat = ptr.toNat + 3 := by
  rw [UInt32.toNat_add, show (3 : UInt32).toNat = 3 from rfl]
  exact Nat.mod_eq_of_lt (by unfold UInt32.size at h; omega)

private theorem ga_ptr4_hnowrap {ptr : UInt32} (h : ptr.toNat + 7 < UInt32.size) :
    (ptr + 4 : UInt32).toNat = ptr.toNat + 4 := by
  rw [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]
  exact Nat.mod_eq_of_lt (by unfold UInt32.size at h; omega)

private theorem ga_ptr4_h1 {ptr : UInt32} (h : ptr.toNat + 7 < UInt32.size) :
    ((ptr + 4) + 1 : UInt32).toNat = (ptr + 4).toNat + 1 := by
  rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl, ga_ptr4_hnowrap h]
  exact Nat.mod_eq_of_lt (by unfold UInt32.size at h; omega)

private theorem ga_ptr4_h2 {ptr : UInt32} (h : ptr.toNat + 7 < UInt32.size) :
    ((ptr + 4) + 2 : UInt32).toNat = (ptr + 4).toNat + 2 := by
  rw [UInt32.toNat_add, show (2 : UInt32).toNat = 2 from rfl, ga_ptr4_hnowrap h]
  exact Nat.mod_eq_of_lt (by unfold UInt32.size at h; omega)

private theorem ga_ptr4_h3 {ptr : UInt32} (h : ptr.toNat + 7 < UInt32.size) :
    ((ptr + 4) + 3 : UInt32).toNat = (ptr + 4).toNat + 3 := by
  rw [UInt32.toNat_add, show (3 : UInt32).toNat = 3 from rfl, ga_ptr4_hnowrap h]
  exact Nat.mod_eq_of_lt (by unfold UInt32.size at h; omega)

/-- `(if P then 1 else 0 : UInt32) ≠ 0 ↔ P`. -/
private theorem ga_ite_one_zero_ne_zero {P : Prop} [Decidable P] :
    (if P then (1 : UInt32) else 0) ≠ 0 ↔ P := by
  split_ifs with h <;> simp [h]

-- ── Contract ─────────────────────────────────────────────────────────────────

/-- WP contract for `template_grow_amortized`, restricted to `elementSize = 1`
    (u8 allocations) so the new-capacity postcondition is `reserveNewCapacity`.

    Guard hypotheses:
    - `hsp`           : shadow stack has room for a 16-byte frame
    - `h_no_overflow` : `additional ≤ length + additional` (no wrap in required)
    - `hptr`          : the RawVec header fits in addressable memory

    Resources:
    - `globalPointsToAt 0 0 (.i32 sp)` — ownership of global 0
    - Frame slots at `sp - 12`, `sp - 8`, `sp - 4` — used by finish_grow
    - `pointsTo_u32 0 ptr oldCapacity`, `pointsTo_u32 0 (ptr + 4) oldData` — the header

    `hFinishGrow` is the WP goal at the `call kFinishGrow` site with continuation;
    consumers supply it by instantiating `FinishGrowContractAt` and stepping the
    result-check, header-write, and stack-restore continuation. -/
def GrowAmortizedContractAt [WasmSmallStepGS hlc α]
    (kHandler kFinishGrow : Nat) : Prop :=
  ∀ (ptr length additional alignment sp : UInt32)
    {v5 w1 w2 w3 oldCapacity oldData : UInt32}
    {R : IProp (WasmHeapGF α)}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → IProp (WasmHeapGF α)},
    (16 : UInt32) ≤ sp →
    additional ≤ length + additional →
    ptr.toNat + 7 < UInt32.size →
    (globalPointsToAt 0 0 (.i32 (sp - 16)) ∗
       pointsTo_u32 0 (sp - 12) w1 ∗
       pointsTo_u32 0 (sp - 8)  w2 ∗
       pointsTo_u32 0 (sp - 4)  w3 ∗
       pointsTo_u32 0 ptr       oldCapacity ∗
       pointsTo_u32 0 (ptr + 4) oldData ∗ R ⊢
       WP (Expr.running
             ⟨{ params :=
                    [ .i32 ptr, .i32 8
                    , .i32 (reserveNewCapacity length additional oldCapacity)
                    , .i32 alignment, .i32 1 ],
                 locals := [.i32 (sp - 16)],
                 values :=
                    [ .i32 1, .i32 alignment
                    , .i32 (reserveNewCapacity length additional oldCapacity)
                    , .i32 oldData, .i32 oldCapacity, .i32 (sp - 12) ] },
               .call kFinishGrow :: (growAmortized_cont kHandler ++ code),
               arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) →
    globalPointsToAt 0 0 (.i32 sp) ∗
       pointsTo_u32 0 (sp - 12) w1 ∗
       pointsTo_u32 0 (sp - 8)  w2 ∗
       pointsTo_u32 0 (sp - 4)  w3 ∗
       pointsTo_u32 0 ptr       oldCapacity ∗
       pointsTo_u32 0 (ptr + 4) oldData ∗ R ⊢
       WP (Expr.running
             ⟨{ params :=
                    [ .i32 ptr, .i32 length, .i32 additional
                    , .i32 alignment, .i32 1 ],
                 locals := [.i32 v5],
                 values := [] },
               template_grow_amortized kHandler kFinishGrow ++ code,
               arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]

-- ── Proof ─────────────────────────────────────────────────────────────────────

/-- `GrowAmortizedContractAt` holds for any two call targets. -/
theorem growAmortized_instantiate [WasmSmallStepGS hlc α]
    (kHandler kFinishGrow : Nat) :
    GrowAmortizedContractAt (α := α) (hlc := hlc) kHandler kFinishGrow := by
  unfold GrowAmortizedContractAt template_grow_amortized
  intro ptr length additional alignment sp v5 w1 w2 w3 oldCapacity oldData R
    code arity remainder controls calls s E Φ
    hsp h_no_overflow hptr hFinishGrow
  simp only [List.cons_append, List.nil_append]
  iintro ⟨Hglobal, Hfr1, Hfr2, Hfr3, Hcapacity, Hdata, HR⟩
  -- global.get 0 → sp
  wasm_twp_bind twp_globalGet with Hglobal => Hglobal
  -- i32.const 16; i32.sub → sp - 16
  wasm_twp_pures [twp_const twp_sub]
  -- local.tee 5: locals[0] := sp - 16
  wasm_twp_localTee [List.length, List.set]
  -- global.set 0: global[0] := sp - 16
  wasm_twp_bind twp_globalSet with Hglobal => Hglobal
  -- Overflow check block
  wasm_twp_pures [twp_block]
  -- local.get 2 (additional); local.get 1 (length); add → required
  wasm_twp_pures [twp_localGet twp_localGet twp_add]
  -- local.tee 1: params[1] := required = length + additional
  wasm_twp_localTee [List.set]
  -- local.get 2 (additional); ge_u: required ≥ additional
  wasm_twp_pures [twp_localGet]
  iapply twp_geU (result := 1) (by rw [if_pos h_no_overflow])
  -- br_if 0 taken → exit overflow block
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  -- local.get 5 (= sp - 16); i32.const 4; add → (sp - 16) + 4
  wasm_twp_pures [twp_localGet twp_const twp_add]
  -- local.get 0 (ptr); i32.load offset=0 → oldCapacity
  wasm_twp_pures [twp_localGet]
  wasm_twp_bind (twp_load32_addr oldCapacity
    (ga_ptr_h1 hptr) (ga_ptr_h2 hptr) (ga_ptr_h3 hptr)) with Hcapacity => Hcapacity
  -- local.tee 2: params[2] := oldCapacity
  wasm_twp_localTee [List.set]
  -- local.get 0 (ptr); i32.load offset=4 → oldData
  wasm_twp_pures [twp_localGet]
  wasm_twp_bind (twp_load32 oldData
    (ga_ptr4_hnowrap hptr) (ga_ptr4_h1 hptr) (ga_ptr4_h2 hptr) (ga_ptr4_h3 hptr)) with Hdata => Hdata
  -- local.get 1 (= required = length + additional)
  wasm_twp_pures [twp_localGet]
  -- local.get 2 (= oldCapacity); i32.const 1; i32.shl → oldCapacity <<< (1 % 32)
  wasm_twp_pures [twp_localGet twp_const twp_shl]
  -- Normalise shift amount: 1 % 32 = 1
  simp only [show (1 : UInt32) % 32 = 1 from by decide]
  -- local.tee 2: params[2] := doubled = oldCapacity <<< 1
  wasm_twp_localTee [List.set]
  -- Candidate selection: local.get 1; local.get 2; gt_u; select → reserveCandidate
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_gtU rfl
  iapply twp_select (selected := .i32 (reserveCandidate length additional oldCapacity)) (by
    simp only [ga_ite_one_zero_ne_zero]
    unfold reserveCandidate reserveRequired reserveDoubled
    split_ifs <;> rfl)
  -- local.tee 2: params[2] := candidate
  wasm_twp_localTee [List.set]
  -- Minimum selection: const 8; const 4; local.get 4 (= 1); const 1; eq → 1; select → 8
  wasm_twp_pures [twp_const twp_const twp_localGet twp_const twp_eq]
  iapply twp_select (selected := .i32 8) (by decide)
  -- local.tee 1: params[1] := 8
  wasm_twp_localTee [List.set]
  -- New-capacity selection: local.get 2 (candidate); local.get 1 (= 8); gt_u; select
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_gtU rfl
  iapply twp_select (selected := .i32 (reserveNewCapacity length additional oldCapacity)) (by
    simp only [ga_ite_one_zero_ne_zero]
    unfold reserveNewCapacity reserveCandidate reserveRequired reserveDoubled
    split_ifs <;> rfl)
  -- local.tee 2: params[2] := newCap
  wasm_twp_localTee [List.set]
  -- local.get 3 (alignment); local.get 4 (elementSize = 1)
  wasm_twp_pures [twp_localGet twp_localGet]
  -- Normalise (sp - 16) + 4 → sp - 12 in the values list
  simp only [ga_frame_4_add_eq hsp,
    show [Value.i32 v5].set (5 - (0 + 1 + 1 + 1 + 1 + 1)) (Value.i32 (sp - 16)) =
      [Value.i32 (sp - 16)] from rfl,
    show List.drop 0 ([] : List Value) = [] from rfl]
  -- Discharge to the consumer's finish_grow hypothesis
  iapply hFinishGrow
  isplitl_exacts [Hglobal Hfr1 Hfr2 Hfr3 Hcapacity Hdata]
  iexact HR

end Wasm.SmallStep
