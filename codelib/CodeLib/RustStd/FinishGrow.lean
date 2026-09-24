import CodeLib.SepLogic.SmallStepOutcomeLanguage
import CodeLib.SepLogic.SmallStepTotalLifting

/-!
# `CodeLib.RustStd.FinishGrow`

Template and contract for `RawVec::finish_grow`, the 6-parameter inner routine
shared by every Rust crate that links `std`.  It has three relocated call
targets — realloc, alloc-zeroed (the marker), and alloc — captured as the
parameters `kRealloc`, `kAllocZeroed`, and `kAlloc`.

Consumers prove `func_N = template_finish_grow a b c` by `rfl`; the contract
`FinishGrowContractAt` then applies without re-running the proof.

**Parameters** at the start of the body (local indices 0–5):
- param 0 `result`      : pointer to the `RawVec` output struct
- param 1 `oldCapacity` : old element count
- param 2 `oldPtr`      : old heap pointer
- param 3 `newCapacity` : requested new element count (overwritten by product)
- param 4 `alignment`   : allocation alignment
- param 5 `elementSize` : element size in bytes

**Locals** 6–8 (zero-initialised by callers):
- local 6 : i32 success flag (set to 1 on entry, cleared to 0 on success)
- local 7 : i32 error-capacity sentinel (set to 4/8 on error, new ptr on success)
- local 8 : i64 new-capacity × element-size product (before truncation)
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open scoped Outcome

/-- The body of `RawVec::finish_grow`, parameterised by the three crate-specific
    call targets.  Consumers prove `func_N = template_finish_grow a b c` by `rfl`. -/
def template_finish_grow (kRealloc kAllocZeroed kAlloc : Nat) : Wasm.Program :=
  [ .const 1,   .localSet 6
  , .const 4,   .localSet 7
  , .block 0 0
      [ -- overflow-1: high 32 bits of (newCapacity × elementSize) must be zero
        .block 0 0
          [ .localGet 5, .extendUI32, .localGet 3, .extendUI32, .mulI64, .localTee 8
          , .constI64 32, .shrUI64, .wrapI64, .eqz, .br_if 0
          , .const 0, .localSet 3, .br 1 ]
        -- overflow-2: product must fit in [0, 2^31 - alignment]
      , .block 0 0
          [ .localGet 8, .wrapI64, .localTee 3
          , .const 2147483648, .localGet 4, .sub, .leU, .br_if 0
          , .const 0, .localSet 3, .br 1 ]
        -- dispatch
      , .block 0 0
          [ .block 0 0
              [ .block 0 0
                  [ .block 0 0
                      [ .localGet 1, .eqz, .br_if 0
                      , .localGet 2, .localGet 5, .localGet 1, .mul
                      , .localGet 4, .localGet 3
                      , .call kRealloc, .localSet 7, .br 1 ]
                  , .block 0 0
                      [ .localGet 3, .br_if 0
                      , .localGet 4, .localSet 7, .br 2 ]
                  , .call kAllocZeroed
                  , .localGet 3, .localGet 4, .call kAlloc, .localSet 7 ]
              , .localGet 7, .br_if 0
              , .localGet 0, .localGet 4, .store32 4, .br 1 ]
          , .localGet 0, .localGet 7, .store32 4
          , .const 0, .localSet 6 ]
      , .const 8, .localSet 7 ]
  , .localGet 0, .localGet 7, .add, .localGet 3, .store32 0
  , .localGet 0, .localGet 6, .store32 0 ]

-- ── Control frames at the two call sites ──────────────────────────────────────
-- Each `body` field equals the FULL original block body set when the block was
-- entered; the interpreter does not update it as instructions are consumed.

/-- Frame for @5a (the realloc-path block inside @4). -/
private abbrev finishGrow_ctrl5 (kRealloc kAllocZeroed kAlloc : Nat) : ControlFrame :=
  { kind        := .block
    paramArity  := 0
    resultArity := 0
    body        :=
        [ .localGet 1, .eqz, .br_if 0
        , .localGet 2, .localGet 5, .localGet 1, .mul
        , .localGet 4, .localGet 3
        , .call kRealloc, .localSet 7, .br 1 ]
    continuation :=
        [ .block 0 0
            [ .localGet 3, .br_if 0
            , .localGet 4, .localSet 7, .br 2 ]
        , .call kAllocZeroed
        , .localGet 3, .localGet 4, .call kAlloc, .localSet 7 ]
    belowStack  := [] }

/-- Frame for the ptr-check block `@4` (contains @5a, @5b, and the alloc chain). -/
private abbrev finishGrow_ctrl4 (kRealloc kAllocZeroed kAlloc : Nat) : ControlFrame :=
  { kind        := .block
    paramArity  := 0
    resultArity := 0
    body        :=
        [ .block 0 0
            [ .localGet 1, .eqz, .br_if 0
            , .localGet 2, .localGet 5, .localGet 1, .mul
            , .localGet 4, .localGet 3
            , .call kRealloc, .localSet 7, .br 1 ]
        , .block 0 0
            [ .localGet 3, .br_if 0
            , .localGet 4, .localSet 7, .br 2 ]
        , .call kAllocZeroed
        , .localGet 3, .localGet 4, .call kAlloc, .localSet 7 ]
    continuation :=
        [ .localGet 7, .br_if 0
        , .localGet 0, .localGet 4, .store32 4, .br 1 ]
    belowStack  := [] }

/-- Frame for the result-write block `@3` (sits inside `@2c`). -/
private abbrev finishGrow_ctrl3 (kRealloc kAllocZeroed kAlloc : Nat) : ControlFrame :=
  { kind        := .block
    paramArity  := 0
    resultArity := 0
    body        :=
        [ .block 0 0
            [ .block 0 0
                [ .localGet 1, .eqz, .br_if 0
                , .localGet 2, .localGet 5, .localGet 1, .mul
                , .localGet 4, .localGet 3
                , .call kRealloc, .localSet 7, .br 1 ]
            , .block 0 0
                [ .localGet 3, .br_if 0
                , .localGet 4, .localSet 7, .br 2 ]
            , .call kAllocZeroed
            , .localGet 3, .localGet 4, .call kAlloc, .localSet 7 ]
        , .localGet 7, .br_if 0
        , .localGet 0, .localGet 4, .store32 4, .br 1 ]
    continuation :=
        [ .localGet 0, .localGet 7, .store32 4
        , .const 0, .localSet 6 ]
    belowStack  := [] }

/-- Frame for the dispatch-outer block `@2c` (sits inside `@1`). -/
private abbrev finishGrow_ctrl2 (kRealloc kAllocZeroed kAlloc : Nat) : ControlFrame :=
  { kind        := .block
    paramArity  := 0
    resultArity := 0
    body        :=
        [ .block 0 0
            [ .block 0 0
                [ .block 0 0
                    [ .localGet 1, .eqz, .br_if 0
                    , .localGet 2, .localGet 5, .localGet 1, .mul
                    , .localGet 4, .localGet 3
                    , .call kRealloc, .localSet 7, .br 1 ]
                , .block 0 0
                    [ .localGet 3, .br_if 0
                    , .localGet 4, .localSet 7, .br 2 ]
                , .call kAllocZeroed
                , .localGet 3, .localGet 4, .call kAlloc, .localSet 7 ]
            , .localGet 7, .br_if 0
            , .localGet 0, .localGet 4, .store32 4, .br 1 ]
        , .localGet 0, .localGet 7, .store32 4
        , .const 0, .localSet 6 ]
    continuation := [.const 8, .localSet 7]
    belowStack  := [] }

/-- Frame for the outer `block @1`.
    `continuation` holds the two final `i32.store` instructions plus `code`. -/
private abbrev finishGrow_ctrl1
    (kRealloc kAllocZeroed kAlloc : Nat) (code : Program) : ControlFrame :=
  { kind        := .block
    paramArity  := 0
    resultArity := 0
    body        :=
        [ .block 0 0
            [ .localGet 5, .extendUI32, .localGet 3, .extendUI32, .mulI64, .localTee 8
            , .constI64 32, .shrUI64, .wrapI64, .eqz, .br_if 0
            , .const 0, .localSet 3, .br 1 ]
        , .block 0 0
            [ .localGet 8, .wrapI64, .localTee 3
            , .const 2147483648, .localGet 4, .sub, .leU, .br_if 0
            , .const 0, .localSet 3, .br 1 ]
        , .block 0 0
            [ .block 0 0
                [ .block 0 0
                    [ .block 0 0
                        [ .localGet 1, .eqz, .br_if 0
                        , .localGet 2, .localGet 5, .localGet 1, .mul
                        , .localGet 4, .localGet 3
                        , .call kRealloc, .localSet 7, .br 1 ]
                    , .block 0 0
                        [ .localGet 3, .br_if 0
                        , .localGet 4, .localSet 7, .br 2 ]
                    , .call kAllocZeroed
                    , .localGet 3, .localGet 4, .call kAlloc, .localSet 7 ]
                , .localGet 7, .br_if 0
                , .localGet 0, .localGet 4, .store32 4, .br 1 ]
            , .localGet 0, .localGet 7, .store32 4
            , .const 0, .localSet 6 ]
        , .const 8, .localSet 7 ]
    continuation :=
        .localGet 0 :: .localGet 7 :: .add :: .localGet 3 :: .store32 0 ::
        .localGet 0 :: .localGet 6 :: .store32 0 :: code
    belowStack  := [] }

-- ── Public contract ────────────────────────────────────────────────────────────

/-- WP contract for `template_finish_grow`.

    The three guard hypotheses state:
    - `h_hi`    : `newCapacity × elementSize` fits in 32 bits (overflow-1 check)
    - `h_bound` : `product ≤ 2^31 - alignment`         (overflow-2 check)
    - `h_nz`    : `product ≠ 0`

    The two callee hypotheses are the WP goals at the two call sites that the
    consumer must discharge from the appropriate allocator contracts.  They are
    abstract: no mention of programs-specific heap types or host state. -/
def FinishGrowContractAt [WasmSmallStepGS hlc α]
    (kRealloc kAllocZeroed kAlloc : Nat) : Prop :=
  ∀ (result oldCapacity oldPtr newCapacity alignment elementSize : UInt32)
    {v6 v7 : UInt32} {v8 : UInt64}
    {R : IProp (WasmHeapGF α)}
    {code : Program} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → IProp (WasmHeapGF α)},
    ((UInt64.ofNat elementSize.toNat * UInt64.ofNat newCapacity.toNat) >>>
        (32 : UInt64) = 0) →
    (newCapacity * elementSize ≤ (2147483648 : UInt32) - alignment) →
    (newCapacity * elementSize ≠ 0) →
    (oldCapacity ≠ 0 →
      R ⊢ WP (Expr.running
            ⟨{ params :=
                    [ .i32 result, .i32 oldCapacity, .i32 oldPtr
                    , .i32 (newCapacity * elementSize), .i32 alignment
                    , .i32 elementSize ]
               locals :=
                    [ .i32 1, .i32 4
                    , .i64 (UInt64.ofNat elementSize.toNat *
                            UInt64.ofNat newCapacity.toNat) ]
               values :=
                    [ .i32 (newCapacity * elementSize), .i32 alignment
                    , .i32 (oldCapacity * elementSize), .i32 oldPtr ] },
              [.call kRealloc, .localSet 7, .br 1],
              0, remainder,
              finishGrow_ctrl5 kRealloc kAllocZeroed kAlloc ::
                finishGrow_ctrl4 kRealloc kAllocZeroed kAlloc ::
                finishGrow_ctrl3 kRealloc kAllocZeroed kAlloc ::
                finishGrow_ctrl2 kRealloc kAllocZeroed kAlloc ::
                finishGrow_ctrl1 kRealloc kAllocZeroed kAlloc code :: controls,
              calls⟩ : Expr α) @ s; E [{ Φ }]) →
    (oldCapacity = 0 →
      R ⊢ WP (Expr.running
            ⟨{ params :=
                    [ .i32 result, .i32 0, .i32 oldPtr
                    , .i32 (newCapacity * elementSize), .i32 alignment
                    , .i32 elementSize ]
               locals :=
                    [ .i32 1, .i32 4
                    , .i64 (UInt64.ofNat elementSize.toNat *
                            UInt64.ofNat newCapacity.toNat) ]
               values := [] },
              [.call kAllocZeroed, .localGet 3, .localGet 4, .call kAlloc,
               .localSet 7],
              0, remainder,
              finishGrow_ctrl4 kRealloc kAllocZeroed kAlloc ::
                finishGrow_ctrl3 kRealloc kAllocZeroed kAlloc ::
                finishGrow_ctrl2 kRealloc kAllocZeroed kAlloc ::
                finishGrow_ctrl1 kRealloc kAllocZeroed kAlloc code :: controls,
              calls⟩ : Expr α) @ s; E [{ Φ }]) →
    R ⊢ WP (Expr.running
          ⟨{ params :=
                  [ .i32 result, .i32 oldCapacity, .i32 oldPtr
                  , .i32 newCapacity, .i32 alignment, .i32 elementSize ]
             locals := [.i32 v6, .i32 v7, .i64 v8]
             values := [] },
            template_finish_grow kRealloc kAllocZeroed kAlloc ++ code,
            0, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]

-- ── Arithmetic helper ─────────────────────────────────────────────────────────

private theorem fg_hwrap {newCapacity elementSize : UInt32} :
    UInt32.ofNat
        ((UInt64.ofNat elementSize.toNat *
          UInt64.ofNat newCapacity.toNat).toNat % 2 ^ 32) =
      newCapacity * elementSize := by
  have hn : newCapacity.toNat < 4294967296 := newCapacity.toNat_lt
  have he : elementSize.toNat < 4294967296 := elementSize.toNat_lt
  simp only [UInt64.toNat_mul,
    show (UInt64.ofNat elementSize.toNat).toNat = elementSize.toNat % 18446744073709551616
      from rfl,
    show (UInt64.ofNat newCapacity.toNat).toNat = newCapacity.toNat % 18446744073709551616
      from rfl]
  have h1 : newCapacity.toNat ≤ 4294967295 := by omega
  have h2 : elementSize.toNat ≤ 4294967295 := by omega
  have hprod : elementSize.toNat * newCapacity.toNat < 18446744073709551616 := by
    have h3 := Nat.mul_le_mul h2 h1
    have h4 : (4294967295 : Nat) * 4294967295 < 18446744073709551616 := by decide
    omega
  have he64 : elementSize.toNat % 18446744073709551616 = elementSize.toNat :=
    Nat.mod_eq_of_lt (by omega)
  have hn64 : newCapacity.toNat % 18446744073709551616 = newCapacity.toNat :=
    Nat.mod_eq_of_lt (by omega)
  rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl,
      show (2 : Nat) ^ 32 = 4294967296 from rfl,
      he64, hn64,
      Nat.mod_eq_of_lt hprod,
      Nat.mul_comm elementSize.toNat newCapacity.toNat,
      show (4294967296 : Nat) = UInt32.size from rfl,
      ← UInt32.toNat_mul, UInt32.ofNat_toNat]

-- ── Proof ─────────────────────────────────────────────────────────────────────

/-- `FinishGrowContractAt` holds for any three call targets. -/
theorem finishGrow_instantiate [WasmSmallStepGS hlc α]
    (kRealloc kAllocZeroed kAlloc : Nat) :
    FinishGrowContractAt (α := α) (hlc := hlc) kRealloc kAllocZeroed kAlloc := by
  unfold FinishGrowContractAt template_finish_grow
  intro result oldCapacity oldPtr newCapacity alignment elementSize v6 v7 v8
    R code remainder controls calls s E Φ
    h_hi h_bound h_nz hRealloc hAllocZeroed
  simp only [List.cons_append, List.nil_append]
  iintro HR
  -- i32.const 1; local.set 6
  wasm_twp_pures [twp_const twp_localSet] using [List.length]
  -- i32.const 4; local.set 7
  wasm_twp_pures [twp_const twp_localSet] using [List.length]
  -- Enter @1; enter @2a
  wasm_twp_pures [twp_block twp_block]
  -- local.get 5 (elementSize); i64.extend; local.get 3 (newCapacity); i64.extend; i64.mul
  wasm_twp_pures [twp_localGet twp_extendUI32 twp_localGet twp_extendUI32 twp_mulI64]
  -- local.tee 8: saves product i64 to local[2], keeps on stack
  wasm_twp_localTee [List.length]
  -- i64.const 32; i64.shr_u
  wasm_twp_pures [twp_constI64 twp_shrUI64]
  rw [show (32 : UInt64) % 64 = 32 from by decide, h_hi]
  -- i32.wrap_i64 of 0; i32.eqz of 0 = 1
  wasm_twp_pures [twp_wrapI64 twp_eqz]
  -- br_if 0 taken (overflow check passed): exit @2a
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  -- Enter @2b; local.get 8 (prodI64); i32.wrap_i64; rewrite product
  have hwrap : UInt32.ofNat
      ((UInt64.ofNat elementSize.toNat *
        UInt64.ofNat newCapacity.toNat).toNat % 2 ^ 32) =
    newCapacity * elementSize := fg_hwrap
  wasm_twp_pures [twp_block twp_localGet twp_wrapI64] rewriting [hwrap]
  -- local.tee 3: params[3] := product
  wasm_twp_localTee [List.set]
  -- i32.const -2147483648; local.get 4 (alignment); i32.sub
  wasm_twp_pures [twp_const twp_localGet twp_sub]
  -- i32.le_u: product ≤ 2^31 - alignment (by h_bound)
  iapply twp_leU (result := 1) (by rw [if_pos h_bound])
  -- br_if 0 taken: exit @2b
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  -- Enter @2c > @3 > @4 > @5 (four nested blocks)
  wasm_twp_pures [twp_block twp_block twp_block twp_block]
  -- Case split: oldCapacity = 0 vs oldCapacity ≠ 0
  rcases Decidable.em (oldCapacity = 0) with h_zero | h_nonzero
  · -- ── alloc-zeroed path (oldCapacity = 0) ──
    subst h_zero
    -- local.get 1 (= 0); i32.eqz → 1; br_if 0 taken, exits @5
    wasm_twp_pures [twp_localGet twp_eqz]
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append]
    -- Enter @5b; local.get 3 (= product ≠ 0)
    wasm_twp_pures [twp_block twp_localGet]
    -- br_if 0 taken (product ≠ 0), exits @5b — the br 2 path is excluded by h_nz
    iapply twp_brIf h_nz (by rfl)
    simp only [List.take_zero, List.nil_append]
    -- Discharge to consumer at [call kAllocZeroed, ...]
    simp only [List.drop, List.set,
               show (6 : Nat) - (0 + 1 + 1 + 1 + 1 + 1 + 1) = 0 from by decide,
               show (7 : Nat) - (0 + 1 + 1 + 1 + 1 + 1 + 1) = 1 from by decide,
               show (8 : Nat) - (0 + 1 + 1 + 1 + 1 + 1 + 1) = 2 from by decide]
    iapply (hAllocZeroed rfl)
    iexact HR
  · -- ── realloc path (oldCapacity ≠ 0) ──
    -- local.get 1; i32.eqz → 0 (oldCapacity ≠ 0)
    wasm_twp_pures [twp_localGet]
    iapply twp_eqz (by rw [if_neg h_nonzero])
    -- br_if 0 NOT taken; local.get 2; local.get 5; local.get 1; i32.mul; local.get 4; local.get 3
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_localGet twp_mul]
    wasm_twp_pures [twp_localGet twp_localGet]
    -- Discharge to consumer at [call kRealloc, local.set 7, br 1]
    simp only [List.drop, List.set,
               show (6 : Nat) - (0 + 1 + 1 + 1 + 1 + 1 + 1) = 0 from by decide,
               show (7 : Nat) - (0 + 1 + 1 + 1 + 1 + 1 + 1) = 1 from by decide,
               show (8 : Nat) - (0 + 1 + 1 + 1 + 1 + 1 + 1) = 2 from by decide]
    iapply (hRealloc h_nonzero)
    iexact HR

end Wasm.SmallStep
