import CodeLib.SepLogic.SmallStepOutcomeLanguage
import CodeLib.SepLogic.SmallStepTotalLifting

/-!
# `CodeLib.RustStd.BumpAlloc`

Template and WP contract for the generated bump allocator shared by every Rust
crate compiled with `wasm32-unknown-unknown` and `talos_alloc`.

Three relocated immediates are captured as parameters:
- `cursorAddr` — memory address that holds the heap cursor
- `heapBase`   — fallback initial heap base when the cursor is zero
- `k`          — function index of the `talos.oom` import call

Consumers prove `func_N = template_bump_alloc a b c` by `rfl`;
`BumpAllocContractAt` then applies without re-running the proof.

**Local-index layout** (2 params, 2 zero-initialised locals):
- param 0 : `size`      — allocation size (bytes); overwritten with `currentPages` late
- param 1 : `alignment` — alignment; overwritten with `finish` early
- local  2 : `alignMask` then `base`
- local  3 : `storedCursor` → `adjustedFrontier` → `requiredPages`
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open scoped Outcome

-- ── Template pieces ─────────────────────────────────────────────────────────

private abbrev bumpAlloc_arithmeticPrefix (cursorAddr heapBase : UInt32) : Wasm.Program :=
  [ .localGet 1, .const 0xFFFFFFFF, .add, .localTee 2
  , .const 0, .load32 cursorAddr, .localTee 3
  , .const heapBase, .localGet 3, .select, .add, .localTee 3
  , .localGet 2, .ltU, .br_if 0
  , .localGet 3, .const 0, .localGet 1, .sub, .and, .localTee 2
  , .localGet 0, .add, .localTee 1
  , .localGet 2, .ltU, .br_if 0
  , .localGet 1, .const 0, .ltS, .br_if 0 ]

private abbrev bumpAlloc_growthTail : Wasm.Program :=
  [ .localGet 1, .const 65535, .add, .const 16, .shrU
  , .localTee 3, .memorySize, .localTee 0, .leU, .br_if 1
  , .localGet 3, .localGet 0, .sub, .memoryGrow
  , .const 0xFFFFFFFF, .ne, .br_if 1 ]

/-- The complete bump-allocator body, parameterised by `cursorAddr`, `heapBase`,
    and the OOM call index `k`.  Consumers prove `func_N = template_bump_alloc a b c`
    by `rfl`. -/
def template_bump_alloc (cursorAddr heapBase : UInt32) (k : Nat) : Wasm.Program :=
  [ .block 0 0
      ([ .block 0 0
           (bumpAlloc_arithmeticPrefix cursorAddr heapBase ++ bumpAlloc_growthTail) ]
       ++ [ .call k, .unreachable ]) ]
  ++ [ .const 0, .localGet 1, .store32 cursorAddr, .localGet 2 ]

-- ── Control frame at the OOM call site ──────────────────────────────────────

private abbrev bumpAlloc_outerCtrl
    (cursorAddr heapBase : UInt32) (k : Nat) (code : Program) : ControlFrame :=
  { kind        := .block
    paramArity  := 0
    resultArity := 0
    body        :=
        [ .block 0 0
            [ .localGet 1, .const 0xFFFFFFFF, .add, .localTee 2
            , .const 0, .load32 cursorAddr, .localTee 3
            , .const heapBase, .localGet 3, .select, .add, .localTee 3
            , .localGet 2, .ltU, .br_if 0
            , .localGet 3, .const 0, .localGet 1, .sub, .and, .localTee 2
            , .localGet 0, .add, .localTee 1
            , .localGet 2, .ltU, .br_if 0
            , .localGet 1, .const 0, .ltS, .br_if 0
            , .localGet 1, .const 65535, .add, .const 16, .shrU
            , .localTee 3, .memorySize, .localTee 0, .leU, .br_if 1
            , .localGet 3, .localGet 0, .sub, .memoryGrow
            , .const 0xFFFFFFFF, .ne, .br_if 1 ]
        , .call k, .unreachable ]
    continuation := .const 0 :: .localGet 1 :: .store32 cursorAddr :: .localGet 2 :: code
    belowStack  := [] }

-- ── Public contract ──────────────────────────────────────────────────────────

/-- WP contract for `template_bump_alloc`.

    The contract is parametrised over the module `m` (required by
    `twp_memorySize_tracked` / `twp_memoryGrow_tracked`); all crate-specific heap
    predicates live in the consumer's frame `R`.

    Guard hypotheses:
    - `hcursorBounds` — `cursorAddr + 3` stays within the 32-bit address space
    - `h_oom`         — any local state can reach `Φ(OOM)` from the OOM call site
    - `h_success`     — after committing the cursor, `base` on the stack reaches `Φ`
-/
def BumpAllocContractAt [WasmSmallStepGS hlc α]
    (m : Module) (_hmIs64 : m.memIs64 = false)
    (cursorAddr heapBase : UInt32) (k : Nat) : Prop :=
  ∀ (size alignment storedCursor : UInt32) (ownedPages : Nat)
    {R : IProp (WasmHeapGF α)}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → IProp (WasmHeapGF α)},
    (cursorAddr.toNat + 3 < UInt32.size) →
    (∀ (l0 l1 l2 l3 : UInt32),
       runtimeModuleOwn ⟨0⟩ m ∗ pointsTo_u32 0 cursorAddr storedCursor ∗
         memoryPagesOwn ownedPages ∗ R ⊢
       WP (Expr.running
             ⟨{ params := [.i32 l0, .i32 l1]
                locals := [.i32 l2, .i32 l3]
                values := [] },
               [.call k, .unreachable], arity, remainder,
               bumpAlloc_outerCtrl cursorAddr heapBase k code :: controls,
               calls⟩ : Expr α) @ s; E [{ Φ }]) →
    (∀ (base : UInt32) (newPages : Nat) (l0 l3 : UInt32),
       runtimeModuleOwn ⟨0⟩ m ∗ pointsTo_u32 0 cursorAddr (size + base) ∗
         memoryPagesOwn newPages ∗ R ⊢
       WP (Expr.running
             ⟨{ params := [.i32 l0, .i32 (size + base)]
                locals := [.i32 base, .i32 l3]
                values := [.i32 base] },
               code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) →
    runtimeModuleOwn ⟨0⟩ m ∗ pointsTo_u32 0 cursorAddr storedCursor ∗
      memoryPagesOwn ownedPages ∗ R ⊢
    WP (Expr.running
          ⟨{ params := [.i32 size, .i32 alignment]
             locals := [.i32 0, .i32 0]
             values := [] },
            template_bump_alloc cursorAddr heapBase k ++ code,
            arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]

-- ── Proof ────────────────────────────────────────────────────────────────────

theorem bumpAlloc_instantiate [WasmSmallStepGS hlc α]
    (m : Module) (hmIs64 : m.memIs64 = false)
    (cursorAddr heapBase : UInt32) (k : Nat) :
    BumpAllocContractAt (α := α) (hlc := hlc) m hmIs64 cursorAddr heapBase k := by
  unfold BumpAllocContractAt template_bump_alloc bumpAlloc_arithmeticPrefix bumpAlloc_growthTail
  intro size alignment storedCursor ownedPages R code arity remainder controls calls s E Φ
    hcursorBounds h_oom h_success
  simp only [List.cons_append, List.nil_append]
  iintro ⟨Hruntime, Hcursor, Hpages, HR⟩
  -- Enter outer block then inner block
  wasm_twp_pures [twp_block twp_block]
  -- ── Arithmetic prefix ─────────────────────────────────────────────────────
  -- local.get 1 (alignment); const 0xFFFFFFFF; add (alignMask)
  wasm_twp_pures [twp_localGet twp_const twp_add]
  -- local.tee 2 → locals[0] = alignMask
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set]
  -- const 0; load32 cursorAddr
  wasm_twp_pures [twp_const]
  ihave HcursorAt : pointsTo_u32 0 ((0 : UInt32) + cursorAddr) storedCursor $$ [Hcursor]
  · irw_exact [UInt32.zero_add cursorAddr] with Hcursor
  obtain ⟨hstep1, hstep2, hstep3⟩ := UInt32.addSteps4 cursorAddr
      (by have hcb := hcursorBounds; unfold UInt32.size at hcb; omega)
  wasm_twp_bind twp_load32 (address := 0) (offset := cursorAddr) storedCursor
      (by simp only [UInt32.zero_add, UInt32.toNat_zero, Nat.zero_add])
      (by simp only [UInt32.zero_add]; exact hstep1)
      (by simp only [UInt32.zero_add]; exact hstep2)
      (by simp only [UInt32.zero_add]; exact hstep3)
      with HcursorAt => Hcursor
  isimp only [UInt32.zero_add] at Hcursor
  -- local.tee 3 → locals[1] = storedCursor
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set]
  -- const heapBase; local.get 3 (storedCursor); select
  wasm_twp_pures [twp_const twp_localGet]
  let frontier := if storedCursor ≠ 0 then storedCursor else heapBase
  have h_sel : Value.i32 frontier = if storedCursor ≠ 0 then Value.i32 storedCursor else Value.i32 heapBase :=
      by simp only [frontier]; by_cases h : storedCursor ≠ 0 <;> simp [h]
  iapply twp_select (selected := .i32 frontier) h_sel
  -- add (frontier + alignMask = adjustedFrontier); local.tee 3 → locals[1]
  let alignMask : UInt32 := (0xFFFFFFFF : UInt32) + alignment
  let adjustedFrontier : UInt32 := frontier + alignMask
  wasm_twp_pures [twp_add]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set]
  -- local.get 2 (alignMask); lt_u; br_if 0 — overflow check 1
  wasm_twp_pures [twp_localGet]
  by_cases hov1 : adjustedFrontier < alignMask
  · -- OOM via overflow 1
    iapply twp_ltU (result := 1) (by exact (if_pos hov1).symm)
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    have hoom_inst := h_oom size alignment alignMask adjustedFrontier
    simp only [show alignMask = (4294967295 : UInt32) + alignment from rfl,
               show adjustedFrontier = frontier + ((4294967295 : UInt32) + alignment) from rfl] at hoom_inst
    iapply_frame hoom_inst using [Hruntime Hcursor Hpages HR]
  · -- No overflow 1
    iapply twp_ltU (result := 0) (by exact (if_neg hov1).symm)
    wasm_twp_pures [twp_brIfZero]
    -- local.get 3; const 0; local.get 1 (alignment); sub; and
    wasm_twp_pures [twp_localGet twp_const twp_localGet twp_sub twp_and]
    -- local.tee 2 → locals[0] = base
    let base : UInt32 := adjustedFrontier &&& (0 - alignment)
    wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set]
    -- local.get 0 (size); add (finish = base + size); local.tee 1 → params[1]
    let finish : UInt32 := size + base
    wasm_twp_pures [twp_localGet twp_add]
    wasm_twp_localTee [List.set]
    -- local.get 2 (base); lt_u; br_if 0 — overflow check 2
    wasm_twp_pures [twp_localGet]
    by_cases hov2 : finish < base
    · -- OOM via overflow 2
      iapply twp_ltU (result := 1) (by exact (if_pos hov2).symm)
      iapply twp_brIf (by decide) (by rfl)
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      have hoom_inst := h_oom size finish base adjustedFrontier
      simp only [show adjustedFrontier = frontier + ((4294967295 : UInt32) + alignment) from rfl,
                 show base = (frontier + ((4294967295 : UInt32) + alignment)) &&& ((0 : UInt32) - alignment) from rfl,
                 show finish = size + ((frontier + ((4294967295 : UInt32) + alignment)) &&& ((0 : UInt32) - alignment)) from rfl] at hoom_inst
      iapply_frame hoom_inst using [Hruntime Hcursor Hpages HR]
    · -- No overflow 2
      iapply twp_ltU (result := 0) (by exact (if_neg hov2).symm)
      wasm_twp_pures [twp_brIfZero]
      -- local.get 1 (finish); const 0; lt_s; br_if 0 — overflow check 3
      wasm_twp_pures [twp_localGet twp_const]
      by_cases hov3 : finish.toInt32 < (0 : UInt32).toInt32
      · -- OOM via overflow 3
        iapply twp_ltS (result := 1) (by exact (if_pos hov3).symm)
        iapply twp_brIf (by decide) (by rfl)
        simp only [List.take_zero, List.nil_append, List.drop_zero]
        have hoom_inst := h_oom size finish base adjustedFrontier
        simp only [show adjustedFrontier = frontier + ((4294967295 : UInt32) + alignment) from rfl,
                   show base = (frontier + ((4294967295 : UInt32) + alignment)) &&& ((0 : UInt32) - alignment) from rfl,
                   show finish = size + ((frontier + ((4294967295 : UInt32) + alignment)) &&& ((0 : UInt32) - alignment)) from rfl] at hoom_inst
        iapply_frame hoom_inst using [Hruntime Hcursor Hpages HR]
      · -- No overflow 3
        iapply twp_ltS (result := 0) (by exact (if_neg hov3).symm)
        wasm_twp_pures [twp_brIfZero]
        -- ── Growth tail ───────────────────────────────────────────────────
        -- local.get 1 (finish); const 65535; add; const 16; shr_u → requiredPages
        let requiredPages : UInt32 := ((65535 : UInt32) + finish) >>> 16
        wasm_twp_pures [twp_localGet twp_const twp_add twp_const twp_shrU]
            rewriting [show (16 : UInt32) % 32 = 16 from by decide]
        -- local.tee 3 → locals[1] = requiredPages
        wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set]
        -- memory.size (tracked)
        ihave HsizeFrame : iprop(
            pointsTo_u32 0 cursorAddr storedCursor ∗ memoryPagesOwn ownedPages ∗ R) $$
            [Hcursor Hpages HR]
        · iframe
        iapply twp_memorySize_tracked m ⟨0⟩ $$ HsizeFrame Hruntime
        iintro %pages HsizeFrame Hruntime Hmeasured
        icases HsizeFrame with ⟨Hcursor, Hpages, HR⟩
        simp only [show m.memIs64 = false from hmIs64, sizeValue,
          Bool.false_eq_true, ↓reduceIte]
        -- local.tee 0 → params[0] = pages.toUInt32
        wasm_twp_pures [twp_localTee]
        simp
        -- le_u (requiredPages ≤ pages.toUInt32?); br_if 1 — success if fits
        by_cases hfits : requiredPages ≤ pages.toUInt32
        · -- SUCCESS: memory already sufficient
          iapply twp_leU (result := 1) (by exact (if_pos hfits).symm)
          iapply twp_brIf (by decide) (by rfl)
          simp only [List.take_zero, List.nil_append]
          -- commit tail: const 0; local.get 1 (finish); store32 cursorAddr; local.get 2 (base)
          wasm_twp_pures [twp_const twp_localGet]
          ihave HcursorAt2 : pointsTo_u32 0 ((0 : UInt32) + cursorAddr) storedCursor $$ [Hcursor]
          · irw_exact [UInt32.zero_add cursorAddr] with Hcursor
          wasm_twp_bind twp_store32 (address := 0) (offset := cursorAddr)
              (value := size + ((frontier + ((4294967295 : UInt32) + alignment)) &&& (-alignment)))
              storedCursor
              (by simp only [UInt32.zero_add, UInt32.toNat_zero, Nat.zero_add])
              (by simp only [UInt32.zero_add]; exact hstep1)
              (by simp only [UInt32.zero_add]; exact hstep2)
              (by simp only [UInt32.zero_add]; exact hstep3)
              with HcursorAt2 => Hcursor
          isimp only [UInt32.zero_add] at Hcursor
          wasm_twp_pures [twp_localGet]
          have hsuccess_inst := h_success base pages pages.toUInt32 requiredPages
          simp only [show pages.toUInt32 = UInt32.ofNat pages from rfl,
                     show base = (frontier + ((4294967295 : UInt32) + alignment)) &&& (-alignment) from rfl,
                     show requiredPages = ((65535 : UInt32) + (size + ((frontier + ((4294967295 : UInt32) + alignment)) &&& (-alignment)))) >>> 16 from rfl] at hsuccess_inst
          iapply_frame hsuccess_inst using [Hruntime Hcursor Hmeasured HR]
        · -- Memory insufficient: try to grow
          iapply twp_leU (result := 0) (by exact (if_neg hfits).symm)
          wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_sub]
          -- memory.grow (tracked)
          ihave HgrowFrame : iprop(
              pointsTo_u32 0 cursorAddr storedCursor ∗ memoryPagesOwn ownedPages ∗ R) $$
              [Hcursor Hpages HR]
          · iframe
          iapply twp_memoryGrow_tracked m ⟨0⟩ pages
              (fun _actualPages _hmeasured => by
                iintro HgrowFrame Hruntime _HMeasured
                icases HgrowFrame with ⟨Hcursor, Hpages, HR⟩
                -- grow failed: result = -1 on stack
                wasm_twp_pures [twp_const]
                iapply twp_ne (result := 0) (by simp)
                wasm_twp_pures [twp_brIfZero twp_exitControl]
                    using [List.take_zero, List.nil_append, List.drop_zero]
                have hoom_inst := h_oom pages.toUInt32 finish base requiredPages
                simp only [show pages.toUInt32 = UInt32.ofNat pages from rfl,
                           show finish = size + ((frontier + ((4294967295 : UInt32) + alignment)) &&& (-alignment)) from rfl,
                           show base = (frontier + ((4294967295 : UInt32) + alignment)) &&& (-alignment) from rfl,
                           show requiredPages = ((65535 : UInt32) + (size + ((frontier + ((4294967295 : UInt32) + alignment)) &&& (-alignment)))) >>> 16 from rfl] at hoom_inst
                iapply_frame hoom_inst using [Hruntime Hcursor Hpages HR])
              (fun _oldPages previousPages newPages _hfacts _hmeasured => by
                iintro HgrowFrame Hruntime _HMeasured HnewPages
                icases HgrowFrame with ⟨Hcursor, Hpages, HR⟩
                -- grow returned previousPages
                wasm_twp_pures [twp_const]
                by_cases hsentinel : previousPages.toUInt32 = (0xFFFFFFFF : UInt32)
                · -- Sentinel value: treat as OOM
                  iapply twp_ne (result := 0) (by simp [hsentinel])
                  wasm_twp_pures [twp_brIfZero twp_exitControl]
                      using [List.take_zero, List.nil_append, List.drop_zero]
                  have hoom_inst := h_oom pages.toUInt32 finish base requiredPages
                  simp only [show pages.toUInt32 = UInt32.ofNat pages from rfl,
                             show finish = size + ((frontier + ((4294967295 : UInt32) + alignment)) &&& (-alignment)) from rfl,
                             show base = (frontier + ((4294967295 : UInt32) + alignment)) &&& (-alignment) from rfl,
                             show requiredPages = ((65535 : UInt32) + (size + ((frontier + ((4294967295 : UInt32) + alignment)) &&& (-alignment)))) >>> 16 from rfl] at hoom_inst
                  iapply_frame hoom_inst using [Hruntime Hcursor Hpages HR]
                · -- Genuine success
                  iapply twp_ne (result := 1) (by simp [hsentinel])
                  iapply twp_brIf (by decide) (by rfl)
                  simp only [List.take_zero, List.nil_append]
                  -- commit tail
                  wasm_twp_pures [twp_const twp_localGet]
                  ihave HcursorAt3 : pointsTo_u32 0 ((0 : UInt32) + cursorAddr)
                      storedCursor $$ [Hcursor]
                  · irw_exact [UInt32.zero_add cursorAddr] with Hcursor
                  obtain ⟨hstep1', hstep2', hstep3'⟩ := UInt32.addSteps4 cursorAddr
                      (by have hcb := hcursorBounds; unfold UInt32.size at hcb; omega)
                  wasm_twp_bind twp_store32 (address := 0) (offset := cursorAddr)
                      (value := size + ((frontier + ((4294967295 : UInt32) + alignment)) &&& (-alignment)))
                      storedCursor
                      (by simp only [UInt32.zero_add, UInt32.toNat_zero, Nat.zero_add])
                      (by simp only [UInt32.zero_add]; exact hstep1')
                      (by simp only [UInt32.zero_add]; exact hstep2')
                      (by simp only [UInt32.zero_add]; exact hstep3')
                      with HcursorAt3 => Hcursor
                  isimp only [UInt32.zero_add] at Hcursor
                  wasm_twp_pures [twp_localGet]
                  have hsuccess_inst := h_success base newPages pages.toUInt32 requiredPages
                  simp only [show pages.toUInt32 = UInt32.ofNat pages from rfl,
                             show base = (frontier + ((4294967295 : UInt32) + alignment)) &&& (-alignment) from rfl,
                             show requiredPages = ((65535 : UInt32) + (size + ((frontier + ((4294967295 : UInt32) + alignment)) &&& (-alignment)))) >>> 16 from rfl] at hsuccess_inst
                  iapply_frame hsuccess_inst using [Hruntime Hcursor HnewPages HR])
              $$ HgrowFrame Hruntime Hmeasured

end Wasm.SmallStep
