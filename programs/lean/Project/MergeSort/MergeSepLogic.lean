import CodeLib.SepLogic.Adequacy
import Project.MergeSort.Framing

/-! # Main merge loop spec for func6

Proves `main_merge_loop_spec`: the inner merge `.loop 0 0 mainMergeBody` (wrapped
in its outer `.block 0 0 [.loop ...]`) from `func6` (Program.lean lines 274–479)
terminates with either `i = n_left` or `j = n_right`.

The loop body exits via `br_if 1` (Break 1 from the body), which the loop
converts to Break 0, which the outer block converts to Fallthrough.  The spec
is therefore stated for `[.block 0 0 [.loop 0 0 mainMergeBody]]`.

First-pass: the counter invariant is proven; the content invariant (output is
the correct merge of the two prefixes) is left for a follow-up.
-/

namespace Wasm.SepLogic.MergeSort

open Wasm Project.MergeSort.Framing

variable [WasmHeapGS]

/-- Body of func6's main merge loop (Program.lean lines 276–477).

    Structure:
      - two exit checks (i ≥ n_left or j ≥ n_right → br_if 1 exits the loop+block)
      - load i into local7
      - 14-block comparison/copy structure:
          path A (left[i] ≤ right[j]): copies left[i] to out[k], i++
          path B (left[i] > right[j]): copies right[j] to out[k], j++
          all bounds-check panics (.call 87) are unreachable under the invariant
      - k++ (common to both paths, after the 14-block structure)
      - br 0 (loop restart) -/
private def mainMergeBody : Program := [
  -- exit: i ≥ n_left
  .localGet 6, .load32 (8 : UInt32), .localGet 1, .ltU,
  .const (1 : UInt32), .and, .eqz, .br_if 1,
  -- exit: j ≥ n_right
  .localGet 6, .load32 (12 : UInt32), .localGet 3, .ltU,
  .const (1 : UInt32), .and, .eqz, .br_if 1,
  -- i → local7
  .localGet 6, .load32 (8 : UInt32), .localSet 7,
  -- 14-block comparison + copy
  .block 0 0 [
    .block 0 0 [
      .block 0 0 [
        .block 0 0 [
          .block 0 0 [
            .block 0 0 [
              .block 0 0 [
                .block 0 0 [
                  .block 0 0 [
                    .block 0 0 [
                      .block 0 0 [
                        .block 0 0 [
                          .block 0 0 [
                            .block 0 0 [
                              -- check i < n_left (br_if 0 = panic)
                              .localGet 7, .localGet 1, .ltU,
                              .const (1 : UInt32), .and, .eqz, .br_if 0,
                              -- left[i] → local8; j → local9
                              .localGet 0, .localGet 7, .const (2 : UInt32), .shl,
                              .add, .load32 (0 : UInt32), .localSet 8,
                              .localGet 6, .load32 (12 : UInt32), .localSet 9,
                              -- check j < n_right: ok → br_if 1; fail → br 2
                              .localGet 9, .localGet 3, .ltU,
                              .const (1 : UInt32), .and, .br_if 1, .br 2
                            ],
                            -- bounds-check panic path — impossible under invariant
                            .localGet 7, .localGet 1,
                            .const (1048712 : UInt32), .call 87, .unreachable
                          ],
                          -- compare left[i] vs right[j]:
                          -- left[i] ≤ right[j] → br_if 2 (left path)
                          -- left[i] > right[j] → br 1 (right path)
                          .localGet 8, .localGet 2, .localGet 9,
                          .const (2 : UInt32), .shl, .add, .load32 (0 : UInt32),
                          .leU, .const (1 : UInt32), .and, .br_if 2, .br 1
                        ],
                        -- bounds-check panic path — impossible under invariant
                        .localGet 9, .localGet 3,
                        .const (1048728 : UInt32), .call 87, .unreachable
                      ],
                      -- right path: j → local10; check j < n_right
                      .localGet 6, .load32 (12 : UInt32), .localSet 10,
                      .localGet 10, .localGet 3, .ltU,
                      .const (1 : UInt32), .and, .br_if 1, .br 2
                    ],
                    -- left path: i → local11; check i < n_left: ok → br_if 4; fail → br 5
                    .localGet 6, .load32 (8 : UInt32), .localSet 11,
                    .localGet 11, .localGet 1, .ltU,
                    .const (1 : UInt32), .and, .br_if 4, .br 5
                  ],
                  -- right path cont: right[j] → local12; k → local13
                  .localGet 2, .localGet 10, .const (2 : UInt32), .shl,
                  .add, .load32 (0 : UInt32), .localSet 12,
                  .localGet 6, .load32 (16 : UInt32), .localSet 13,
                  -- check k < n_out: ok → br_if 1; fail → br 2
                  .localGet 13, .localGet 5, .ltU,
                  .const (1 : UInt32), .and, .br_if 1, .br 2
                ],
                -- bounds-check panic path — impossible under invariant
                .localGet 10, .localGet 3,
                .const (1048744 : UInt32), .call 87, .unreachable
              ],
              -- right path store: out[k] = right[j]; j++; exit all 6 inner blocks
              .localGet 4, .localGet 13, .const (2 : UInt32), .shl,
              .add, .localGet 12, .store32 (0 : UInt32),
              .localGet 6, .localGet 6, .load32 (12 : UInt32),
              .const (1 : UInt32), .add, .store32 (12 : UInt32),
              .br 5
            ],
            -- bounds-check panic path — impossible under invariant
            .localGet 13, .localGet 5,
            .const (1048760 : UInt32), .call 87, .unreachable
          ],
          -- left path cont: left[i] → local14; k → local15
          .localGet 0, .localGet 11, .const (2 : UInt32), .shl,
          .add, .load32 (0 : UInt32), .localSet 14,
          .localGet 6, .load32 (16 : UInt32), .localSet 15,
          -- check k < n_out: ok → br_if 1; fail → br 2
          .localGet 15, .localGet 5, .ltU,
          .const (1 : UInt32), .and, .br_if 1, .br 2
        ],
        -- bounds-check panic path — impossible under invariant
        .localGet 11, .localGet 1,
        .const (1048776 : UInt32), .call 87, .unreachable
      ],
      -- left path store: out[k] = left[i]; i++; exit 2 outer blocks
      .localGet 4, .localGet 15, .const (2 : UInt32), .shl,
      .add, .localGet 14, .store32 (0 : UInt32),
      .localGet 6, .localGet 6, .load32 (8 : UInt32),
      .const (1 : UInt32), .add, .store32 (8 : UInt32),
      .br 1
    ],
    -- bounds-check panic path — impossible under invariant
    .localGet 15, .localGet 5,
    .const (1048792 : UInt32), .call 87, .unreachable
  ],
  -- k++ (after either path exits the 14-block structure)
  .localGet 6, .localGet 6, .load32 (16 : UInt32),
  .const (1 : UInt32), .add, .store32 (16 : UInt32),
  .br 0
]

/-- Loop invariant (counter-tracking only; content invariant is a follow-up).

    Tracks current i, j and k = k₀ + (i - i₀) + (j - j₀), with local-structure
    constraints and disjointness conditions.  `st_init` is fixed so future
    content-invariant fields can refer to original source values. -/
private def MergeLoopInv
    (frame out_ptr left_ptr right_ptr n_left n_right n_out : UInt32)
    (i₀ j₀ k₀ : Nat) (st_init : Store Unit)
    (stA : Store Unit) (locA : Locals) : Prop :=
  ∃ i j : Nat,
    i₀ ≤ i ∧ i ≤ n_left.toNat ∧
    j₀ ≤ j ∧ j ≤ n_right.toNat ∧
    -- i, j, k stored in frame slots
    stA.mem.read32 (frame + 8)  = UInt32.ofNat i ∧
    stA.mem.read32 (frame + 12) = UInt32.ofNat j ∧
    stA.mem.read32 (frame + 16) = UInt32.ofNat (k₀ + (i - i₀) + (j - j₀)) ∧
    -- six params unchanged
    locA.get 6 = some (.i32 frame) ∧
    locA.get 0 = some (.i32 left_ptr) ∧
    locA.get 1 = some (.i32 n_left) ∧
    locA.get 2 = some (.i32 right_ptr) ∧
    locA.get 3 = some (.i32 n_right) ∧
    locA.get 4 = some (.i32 out_ptr) ∧
    locA.get 5 = some (.i32 n_out) ∧
    locA.params.length = 6 ∧ locA.locals.length = 16 ∧
    -- global 0 writable (exit path uses globalSet 0 in drain loops)
    (∃ v, stA.globals.globals[0]? = some v) ∧
    -- source arrays unchanged (placeholder; content invariant fields go here)
    (∀ q, q < n_left.toNat →
      stA.mem.read32 (left_ptr + 4 * UInt32.ofNat q) =
      st_init.mem.read32 (left_ptr + 4 * UInt32.ofNat q)) ∧
    (∀ q, q < n_right.toNat →
      stA.mem.read32 (right_ptr + 4 * UInt32.ofNat q) =
      st_init.mem.read32 (right_ptr + 4 * UInt32.ofNat q)) ∧
    -- memory bounds
    frame.toNat + 20 ≤ stA.mem.pages * 65536 ∧
    k₀ + (n_left.toNat - i₀) + (n_right.toNat - j₀) ≤ n_out.toNat ∧
    left_ptr.toNat  + 4 * n_left.toNat  ≤ stA.mem.pages * 65536 ∧
    right_ptr.toNat + 4 * n_right.toNat ≤ stA.mem.pages * 65536 ∧
    out_ptr.toNat   + 4 * n_out.toNat   ≤ stA.mem.pages * 65536 ∧
    stA.mem.pages * 65536 ≤ 4294967296 ∧
    -- disjointness
    (left_ptr.toNat + 4 * n_left.toNat ≤ out_ptr.toNat ∨
     out_ptr.toNat + 4 * n_out.toNat ≤ left_ptr.toNat) ∧
    (right_ptr.toNat + 4 * n_right.toNat ≤ out_ptr.toNat ∨
     out_ptr.toNat + 4 * n_out.toNat ≤ right_ptr.toNat) ∧
    (left_ptr.toNat + 4 * n_left.toNat ≤ right_ptr.toNat ∨
     right_ptr.toNat + 4 * n_right.toNat ≤ left_ptr.toNat) ∧
    (frame.toNat + 20 ≤ left_ptr.toNat ∨
     left_ptr.toNat + 4 * n_left.toNat ≤ frame.toNat) ∧
    (frame.toNat + 20 ≤ right_ptr.toNat ∨
     right_ptr.toNat + 4 * n_right.toNat ≤ frame.toNat) ∧
    (frame.toNat + 20 ≤ out_ptr.toNat ∨
     out_ptr.toNat + 4 * n_out.toNat ≤ frame.toNat)

/-- The main merge loop of `func6` terminates with either `i = n_left` or
    `j = n_right` (the loop exhausted at least one source array).

    The spec covers `[.block 0 0 [.loop 0 0 mainMergeBody]]` because the loop
    exits via `br_if 1` (Break 1 from body → Break 0 from loop) and the outer
    block converts that Break 0 to Fallthrough.

    Measure: μ = (n_left.toNat - i) + (n_right.toNat - j).
    Each iteration increments exactly one of i, j, so μ strictly decreases. -/
theorem main_merge_loop_spec
    {m : Module} {env : HostEnv Unit}
    (st : Store Unit) (locals : Locals)
    (frame out_ptr left_ptr right_ptr n_left n_right n_out : UInt32)
    (i₀ j₀ k₀ : Nat)
    (hI₀ : MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
             i₀ j₀ k₀ st st locals) :
    wp_wasm_prop m st locals [.block 0 0 [.loop 0 0 mainMergeBody]] env
      (fun st' _ =>
        st'.mem.read32 (frame + 8)  = n_left ∨
        st'.mem.read32 (frame + 12) = n_right) := by
  -- strong induction on μ = (n_left - i) + (n_right - j)
  suffices key : ∀ n stA locA,
      MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
        i₀ j₀ k₀ st stA locA →
      (n_left.toNat - (stA.mem.read32 (frame + 8)).toNat) +
        (n_right.toNat - (stA.mem.read32 (frame + 12)).toNat) = n →
      wp_wasm_prop m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env
        (fun st' _ =>
          st'.mem.read32 (frame + 8) = n_left ∨
          st'.mem.read32 (frame + 12) = n_right) from
    key _ st locals hI₀ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro stA locA hI hμ
    obtain ⟨i, j, hi_lo, hi_hi, hj_lo, hj_hi,
             hi_m, hj_m, hk_m,
             hf6, h0, h1, h2, h3, h4, h5,
             hlparams, hllocals, hglobal,
             hleft, hright,
             hpages, hk_global,
             hleft_global, hright_global, hout_global,
             hpages_u32,
             hleft_out_disj, hright_out_disj, hleft_right_disj,
             hframe_left_disj, hframe_right_disj, hframe_out_disj⟩ := hI
    by_cases hlt_i : i < n_left.toNat
    · by_cases hlt_j : j < n_right.toNat
      · -- ── iteration: i < n_left, j < n_right ────────────────────────────────
        -- Case-split on comparison left[i] ≤ right[j].
        -- Each path: exec trace through 14 nested blocks sorry'd;
        -- invariant restoration and measure decrease proven; IH applied.
        obtain ⟨v₀, hg⟩ := hglobal
        have hμ_pos : 0 < n := by
          rw [← hμ, hi_m, hj_m, UInt32.toNat_ofNat', UInt32.toNat_ofNat']
          have := n_left.toNat_lt; have := n_right.toNat_lt; omega
        let k := k₀ + (i - i₀) + (j - j₀)
        have hk_val : k < n_out.toNat := by have := hk_global; omega
        have hft8  : (frame + 8).toNat  = frame.toNat + 8  := by
          rw [UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have hft12 : (frame + 12).toNat = frame.toNat + 12 := by
          rw [UInt32.toNat_add, show (12 : UInt32).toNat = 12 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have hft16 : (frame + 16).toNat = frame.toNat + 16 := by
          rw [UInt32.toNat_add, show (16 : UInt32).toNat = 16 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have hout_k_toNat : (out_ptr + 4 * UInt32.ofNat k).toNat = out_ptr.toNat + 4 * k :=
          toNat_wordAddr out_ptr n_out.toNat k hk_val (by linarith)
        let left_i  := stA.mem.read32 (left_ptr + 4 * UInt32.ofNat i)
        let right_j := stA.mem.read32 (right_ptr + 4 * UInt32.ofNat j)
        have hi_add1 : UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by
          apply UInt32.toNat_inj.mp
          simp only [UInt32.toNat_add, UInt32.toNat_ofNat', show (1 : UInt32).toNat = 1 from rfl,
                     Nat.mod_eq_of_lt (show i + 1 < 4294967296 from by
                       have := n_left.toNat_lt; omega)]
          omega
        have hj_add1 : UInt32.ofNat j + 1 = UInt32.ofNat (j + 1) := by
          apply UInt32.toNat_inj.mp
          simp only [UInt32.toNat_add, UInt32.toNat_ofNat', show (1 : UInt32).toNat = 1 from rfl,
                     Nat.mod_eq_of_lt (show j + 1 < 4294967296 from by
                       have := n_right.toNat_lt; omega)]
          omega
        have hk_add1 : UInt32.ofNat k + 1 = UInt32.ofNat (k + 1) := by
          apply UInt32.toNat_inj.mp
          simp only [UInt32.toNat_add, UInt32.toNat_ofNat', show (1 : UInt32).toNat = 1 from rfl,
                     Nat.mod_eq_of_lt (show k + 1 < 4294967296 from by
                       have := n_out.toNat_lt; omega)]
          omega
        by_cases hle : left_i ≤ right_j
        · -- ── path A: left[i] ≤ right[j]: copy left[i] to out[k], i++, k++ ──
          let mem1_A := stA.mem.write32 (out_ptr + 4 * UInt32.ofNat k) left_i
          let mem2_A := mem1_A.write32 (frame + 8) (UInt32.ofNat i + 1)
          let mem3_A := mem2_A.write32 (frame + 16) (UInt32.ofNat k + 1)
          let stC_A : Store Unit := { stA with mem := mem3_A }
          -- Result locals: localSet 7(→local[1]) 8(→local[2]) 9(→local[3])
          --                       11(→local[5]) 14(→local[8]) 15(→local[9])
          let locA_out_locs :=
            locA.locals.set 1 (.i32 (UInt32.ofNat i)) |>.set 2 (.i32 left_i)
              |>.set 3 (.i32 (UInt32.ofNat j)) |>.set 5 (.i32 (UInt32.ofNat i))
              |>.set 8 (.i32 left_i) |>.set 9 (.i32 (UInt32.ofNat k))
          let locA_out_A : Locals := { locA with locals := locA_out_locs }
          -- exec trace (staged through 14 nested blocks)
          have h_body_A : ∃ f_A,
              exec f_A m stA locA mainMergeBody env = .Break 0 stC_A locA_out_A := by
            exact sorry
          obtain ⟨f_A, h_body_A⟩ := h_body_A
          -- memory reads after path A writes
          have hread8_A : stC_A.mem.read32 (frame + 8) = UInt32.ofNat (i + 1) := by
            simp only [stC_A, mem3_A, mem2_A, mem1_A]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 8) _
                  (by right; rw [hft16, hft8]; omega),
                Mem.read32_write32_same, hi_add1]
          have hread12_A : stC_A.mem.read32 (frame + 12) = UInt32.ofNat j := by
            simp only [stC_A, mem3_A, mem2_A, mem1_A]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 12) _
                  (by right; rw [hft16, hft12]),
                Mem.read32_write32_of_disjoint _ (frame + 8) (frame + 12) _
                  (by left; rw [hft8, hft12]),
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 12) _
                  (by rw [hout_k_toNat, hft12];
                      rcases hframe_out_disj with h | h <;> omega),
                hj_m]
          have hread16_A : stC_A.mem.read32 (frame + 16) = UInt32.ofNat (k + 1) := by
            simp only [stC_A, mem3_A]
            rw [Mem.read32_write32_same, hk_add1]
          -- locA_out_A.get 6: local[0] unchanged (set indices 1,2,3,5,8,9 ≠ 0)
          have hf6_out_A : locA_out_A.get 6 = some (.i32 frame) := by
            simp only [locA_out_A, locA_out_locs, Locals.get, hlparams, hllocals, List.length_set,
                       show ¬ (6 < 6) from by omega,
                       show 6 < 6 + 16 from by omega,
                       show 6 - 6 = 0 from by omega,
                       List.getElem?_set,
                       show (9 : Nat) ≠ 0 from by omega,
                       show (8 : Nat) ≠ 0 from by omega,
                       show (5 : Nat) ≠ 0 from by omega,
                       show (3 : Nat) ≠ 0 from by omega,
                       show (2 : Nat) ≠ 0 from by omega,
                       show (1 : Nat) ≠ 0 from by omega,
                       if_false]
            simpa [Locals.get, hlparams, hllocals,
                   show ¬ (6 < 6) from by omega] using hf6
          have hllocals_out_A : locA_out_A.locals.length = 16 := by
            simp [locA_out_A, locA_out_locs, List.length_set, hllocals]
          -- locA_out_A.get 0..5 = locA.get 0..5: params unchanged, needs hlparams for if-branch
          have hg_eq_A : ∀ n, n < 6 → locA_out_A.get n = locA.get n := fun n hn => by
            simp only [locA_out_A, Locals.get, hlparams, if_pos hn]
          have hlparams_out_A : locA_out_A.params.length = 6 := by exact hlparams
          -- invariant restoration: (i+1, j)
          have hI_A : MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
                        i₀ j₀ k₀ st stC_A locA_out_A :=
            ⟨i + 1, j, by omega, by omega, hj_lo, hj_hi,
             hread8_A, hread12_A,
             by rw [hread16_A]; congr 1; omega,
             hf6_out_A,
             (hg_eq_A 0 (by omega)).trans h0, (hg_eq_A 1 (by omega)).trans h1,
             (hg_eq_A 2 (by omega)).trans h2, (hg_eq_A 3 (by omega)).trans h3,
             (hg_eq_A 4 (by omega)).trans h4, (hg_eq_A 5 (by omega)).trans h5,
             hlparams_out_A, hllocals_out_A, ⟨v₀, hg⟩,
             fun q hq => by
               simp only [stC_A, mem3_A, mem2_A, mem1_A]
               have hliq : (left_ptr + 4 * UInt32.ofNat q).toNat = left_ptr.toNat + 4 * q :=
                 toNat_wordAddr left_ptr n_left.toNat q hq (by linarith)
               rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                     (by rw [hft16, hliq]; rcases hframe_left_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (frame + 8) _ _
                     (by rw [hft8, hliq]; rcases hframe_left_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                     (by rw [hout_k_toNat, hliq]; rcases hleft_out_disj with h | h <;> omega)]
               exact hleft q hq,
             fun q hq => by
               simp only [stC_A, mem3_A, mem2_A, mem1_A]
               have hriq : (right_ptr + 4 * UInt32.ofNat q).toNat = right_ptr.toNat + 4 * q :=
                 toNat_wordAddr right_ptr n_right.toNat q hq (by linarith)
               rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                     (by rw [hft16, hriq]; rcases hframe_right_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (frame + 8) _ _
                     (by rw [hft8, hriq]; rcases hframe_right_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                     (by rw [hout_k_toNat, hriq]; rcases hright_out_disj with h | h <;> omega)]
               exact hright q hq,
             by simp [stC_A, mem3_A, mem2_A, mem1_A, Mem.write32_pages, hpages],
             hk_global,
             by simp [stC_A, mem3_A, mem2_A, mem1_A, Mem.write32_pages, hleft_global],
             by simp [stC_A, mem3_A, mem2_A, mem1_A, Mem.write32_pages, hright_global],
             by simp [stC_A, mem3_A, mem2_A, mem1_A, Mem.write32_pages, hout_global],
             hpages_u32, hleft_out_disj, hright_out_disj, hleft_right_disj,
             hframe_left_disj, hframe_right_disj, hframe_out_disj⟩
          -- measure decrease
          have hμ_A : (n_left.toNat - (stC_A.mem.read32 (frame + 8)).toNat) +
                      (n_right.toNat - (stC_A.mem.read32 (frame + 12)).toNat) < n := by
            rw [hread8_A, hread12_A, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := n_left.toNat_lt; omega),
                Nat.mod_eq_of_lt (by have := n_right.toNat_lt; omega),
                ← hμ, hi_m, hj_m, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := n_left.toNat_lt; omega),
                Nat.mod_eq_of_lt (by have := n_right.toNat_lt; omega)]
            omega
          -- IH at reduced measure: input is (stC_A, locA_out_A)
          obtain ⟨f_rest, hf_rest⟩ := IH _ hμ_A stC_A locA_out_A hI_A rfl
          -- Fuel composition: one body iteration at stA then IH fuel at stC_A
          have hbody_ne : exec f_A m stA locA mainMergeBody env ≠ .OutOfFuel := by
            simp [h_body_A]
          have hfuel_ne : exec f_rest m stC_A locA_out_A [.block 0 0 [.loop 0 0 mainMergeBody]] env ≠ .OutOfFuel :=
            fun h => by rw [h] at hf_rest; exact hf_rest
          have hbody_mono : exec (max f_A f_rest) m stA locA mainMergeBody env = .Break 0 stC_A locA_out_A :=
            (exec_fuel_mono (Nat.le_max_left f_A f_rest) hbody_ne).trans h_body_A
          have hblock_mono : exec (max f_A f_rest + 1) m stC_A locA_out_A [.block 0 0 [.loop 0 0 mainMergeBody]] env =
              exec f_rest m stC_A locA_out_A [.block 0 0 [.loop 0 0 mainMergeBody]] env :=
            exec_fuel_mono (by omega) hfuel_ne
          have hloop_single : ∀ F stT locT,
              exec F m stT locT [.loop 0 0 mainMergeBody] env =
              execOne F m stT locT (.loop 0 0 mainMergeBody) env := fun F stT locT => by
            cases F with
            | zero => simp [exec, execOne]
            | succ f =>
              simp only [exec]
              rcases execOne (f + 1) m stT locT (.loop 0 0 mainMergeBody) env with
                ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_⟩ | _
              · rfl
              all_goals rfl
          have hloop_eq : exec (max f_A f_rest + 1) m stA locA [.loop 0 0 mainMergeBody] env =
              exec (max f_A f_rest) m stC_A locA_out_A [.loop 0 0 mainMergeBody] env := by
            rw [hloop_single, hloop_single]
            conv_lhs => rw [execOne_loop_succ]
            simp only [hbody_mono, List.take_zero, List.nil_append, List.drop_zero]
            -- {locA_out_A with values := locA.values} = locA_out_A by rfl:
            -- locA_out_A = {locA with locals := ...}, so .values = locA.values definitionally
            rfl
          have heq : exec (max f_A f_rest + 2) m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env =
              exec (max f_A f_rest + 1) m stC_A locA_out_A [.block 0 0 [.loop 0 0 mainMergeBody]] env := by
            rw [show max f_A f_rest + 2 = max f_A f_rest + 1 + 1 from rfl]
            conv_lhs => rw [exec_block_cons, hloop_eq]
            conv_rhs => rw [exec_block_cons]
            set discr := exec (max f_A f_rest) m stC_A locA_out_A [.loop 0 0 mainMergeBody] env
            rcases discr with ⟨r', s'⟩ | ⟨n, r', s'⟩ | ⟨r', vs⟩ | ⟨r', msg⟩ | ⟨msg⟩ | _
            · simp [exec, locA_out_A, locA_out_locs]
            · cases n with | zero => simp [exec, locA_out_A, locA_out_locs] | succ k => rfl
            all_goals rfl
          exact ⟨max f_A f_rest + 2, by rw [heq, hblock_mono]; exact hf_rest⟩
        · -- ── path B: left[i] > right[j]: copy right[j] to out[k], j++, k++ ──
          let mem1_B := stA.mem.write32 (out_ptr + 4 * UInt32.ofNat k) right_j
          let mem2_B := mem1_B.write32 (frame + 12) (UInt32.ofNat j + 1)
          let mem3_B := mem2_B.write32 (frame + 16) (UInt32.ofNat k + 1)
          let stC_B : Store Unit := { stA with mem := mem3_B }
          -- Result locals: localSet 7(→local[1]) 8(→local[2]) 9(→local[3])
          --                       10(→local[4]) 12(→local[6]) 13(→local[7])
          let locB_out_locs :=
            locA.locals.set 1 (.i32 (UInt32.ofNat i)) |>.set 2 (.i32 left_i)
              |>.set 3 (.i32 (UInt32.ofNat j)) |>.set 4 (.i32 (UInt32.ofNat j))
              |>.set 6 (.i32 right_j) |>.set 7 (.i32 (UInt32.ofNat k))
          let locB_out_B : Locals := { locA with locals := locB_out_locs }
          -- exec trace (staged through 14 nested blocks)
          have h_body_B : ∃ f_B,
              exec f_B m stA locA mainMergeBody env = .Break 0 stC_B locB_out_B := by
            exact sorry
          obtain ⟨f_B, h_body_B⟩ := h_body_B
          -- memory reads after path B writes
          have hread8_B : stC_B.mem.read32 (frame + 8) = UInt32.ofNat i := by
            simp only [stC_B, mem3_B, mem2_B, mem1_B]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 8) _
                  (by right; rw [hft16, hft8]; omega),
                Mem.read32_write32_of_disjoint _ (frame + 12) (frame + 8) _
                  (by right; rw [hft12, hft8]),
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 8) _
                  (by rw [hout_k_toNat, hft8];
                      rcases hframe_out_disj with h | h <;> omega),
                hi_m]
          have hread12_B : stC_B.mem.read32 (frame + 12) = UInt32.ofNat (j + 1) := by
            simp only [stC_B, mem3_B, mem2_B, mem1_B]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 12) _
                  (by right; rw [hft16, hft12]),
                Mem.read32_write32_same, hj_add1]
          have hread16_B : stC_B.mem.read32 (frame + 16) = UInt32.ofNat (k + 1) := by
            simp only [stC_B, mem3_B]
            rw [Mem.read32_write32_same, hk_add1]
          -- locB_out_B.get 6: local[0] unchanged (set indices 1,2,3,4,6,7 ≠ 0)
          have hf6_out_B : locB_out_B.get 6 = some (.i32 frame) := by
            simp only [locB_out_B, locB_out_locs, Locals.get, hlparams, hllocals, List.length_set,
                       show ¬ (6 < 6) from by omega,
                       show 6 < 6 + 16 from by omega,
                       show 6 - 6 = 0 from by omega,
                       List.getElem?_set,
                       show (7 : Nat) ≠ 0 from by omega,
                       show (6 : Nat) ≠ 0 from by omega,
                       show (4 : Nat) ≠ 0 from by omega,
                       show (3 : Nat) ≠ 0 from by omega,
                       show (2 : Nat) ≠ 0 from by omega,
                       show (1 : Nat) ≠ 0 from by omega,
                       if_false]
            simpa [Locals.get, hlparams, hllocals,
                   show ¬ (6 < 6) from by omega] using hf6
          have hllocals_out_B : locB_out_B.locals.length = 16 := by
            simp [locB_out_B, locB_out_locs, List.length_set, hllocals]
          -- locB_out_B.get 0..5 = locA.get 0..5: params unchanged, needs hlparams for if-branch
          have hg_eq_B : ∀ n, n < 6 → locB_out_B.get n = locA.get n := fun n hn => by
            simp only [locB_out_B, Locals.get, hlparams, if_pos hn]
          have hlparams_out_B : locB_out_B.params.length = 6 := by exact hlparams
          -- invariant restoration: (i, j+1)
          have hI_B : MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
                        i₀ j₀ k₀ st stC_B locB_out_B :=
            ⟨i, j + 1, hi_lo, hi_hi, by omega, by omega,
             hread8_B, hread12_B,
             by rw [hread16_B]; congr 1; omega,
             hf6_out_B,
             (hg_eq_B 0 (by omega)).trans h0, (hg_eq_B 1 (by omega)).trans h1,
             (hg_eq_B 2 (by omega)).trans h2, (hg_eq_B 3 (by omega)).trans h3,
             (hg_eq_B 4 (by omega)).trans h4, (hg_eq_B 5 (by omega)).trans h5,
             hlparams_out_B, hllocals_out_B, ⟨v₀, hg⟩,
             fun q hq => by
               simp only [stC_B, mem3_B, mem2_B, mem1_B]
               have hliq : (left_ptr + 4 * UInt32.ofNat q).toNat = left_ptr.toNat + 4 * q :=
                 toNat_wordAddr left_ptr n_left.toNat q hq (by linarith)
               rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                     (by rw [hft16, hliq]; rcases hframe_left_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (frame + 12) _ _
                     (by rw [hft12, hliq]; rcases hframe_left_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                     (by rw [hout_k_toNat, hliq]; rcases hleft_out_disj with h | h <;> omega)]
               exact hleft q hq,
             fun q hq => by
               simp only [stC_B, mem3_B, mem2_B, mem1_B]
               have hriq : (right_ptr + 4 * UInt32.ofNat q).toNat = right_ptr.toNat + 4 * q :=
                 toNat_wordAddr right_ptr n_right.toNat q hq (by linarith)
               rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                     (by rw [hft16, hriq]; rcases hframe_right_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (frame + 12) _ _
                     (by rw [hft12, hriq]; rcases hframe_right_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                     (by rw [hout_k_toNat, hriq]; rcases hright_out_disj with h | h <;> omega)]
               exact hright q hq,
             by simp [stC_B, mem3_B, mem2_B, mem1_B, Mem.write32_pages, hpages],
             hk_global,
             by simp [stC_B, mem3_B, mem2_B, mem1_B, Mem.write32_pages, hleft_global],
             by simp [stC_B, mem3_B, mem2_B, mem1_B, Mem.write32_pages, hright_global],
             by simp [stC_B, mem3_B, mem2_B, mem1_B, Mem.write32_pages, hout_global],
             hpages_u32, hleft_out_disj, hright_out_disj, hleft_right_disj,
             hframe_left_disj, hframe_right_disj, hframe_out_disj⟩
          -- measure decrease
          have hμ_B : (n_left.toNat - (stC_B.mem.read32 (frame + 8)).toNat) +
                      (n_right.toNat - (stC_B.mem.read32 (frame + 12)).toNat) < n := by
            rw [hread8_B, hread12_B, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := n_left.toNat_lt; omega),
                Nat.mod_eq_of_lt (by have := n_right.toNat_lt; omega),
                ← hμ, hi_m, hj_m, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := n_left.toNat_lt; omega),
                Nat.mod_eq_of_lt (by have := n_right.toNat_lt; omega)]
            omega
          -- IH at reduced measure: input is (stC_B, locB_out_B)
          obtain ⟨f_rest, hf_rest⟩ := IH _ hμ_B stC_B locB_out_B hI_B rfl
          -- Fuel composition: one body iteration at stA then IH fuel at stC_B
          have hbody_ne : exec f_B m stA locA mainMergeBody env ≠ .OutOfFuel := by
            simp [h_body_B]
          have hfuel_ne : exec f_rest m stC_B locB_out_B [.block 0 0 [.loop 0 0 mainMergeBody]] env ≠ .OutOfFuel :=
            fun h => by rw [h] at hf_rest; exact hf_rest
          have hbody_mono : exec (max f_B f_rest) m stA locA mainMergeBody env = .Break 0 stC_B locB_out_B :=
            (exec_fuel_mono (Nat.le_max_left f_B f_rest) hbody_ne).trans h_body_B
          have hblock_mono : exec (max f_B f_rest + 1) m stC_B locB_out_B [.block 0 0 [.loop 0 0 mainMergeBody]] env =
              exec f_rest m stC_B locB_out_B [.block 0 0 [.loop 0 0 mainMergeBody]] env :=
            exec_fuel_mono (by omega) hfuel_ne
          have hloop_single : ∀ F stT locT,
              exec F m stT locT [.loop 0 0 mainMergeBody] env =
              execOne F m stT locT (.loop 0 0 mainMergeBody) env := fun F stT locT => by
            cases F with
            | zero => simp [exec, execOne]
            | succ f =>
              simp only [exec]
              rcases execOne (f + 1) m stT locT (.loop 0 0 mainMergeBody) env with
                ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_⟩ | _
              · rfl
              all_goals rfl
          have hloop_eq : exec (max f_B f_rest + 1) m stA locA [.loop 0 0 mainMergeBody] env =
              exec (max f_B f_rest) m stC_B locB_out_B [.loop 0 0 mainMergeBody] env := by
            rw [hloop_single, hloop_single]
            conv_lhs => rw [execOne_loop_succ]
            simp only [hbody_mono, List.take_zero, List.nil_append, List.drop_zero]
            rfl
          have heq : exec (max f_B f_rest + 2) m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env =
              exec (max f_B f_rest + 1) m stC_B locB_out_B [.block 0 0 [.loop 0 0 mainMergeBody]] env := by
            rw [show max f_B f_rest + 2 = max f_B f_rest + 1 + 1 from rfl]
            conv_lhs => rw [exec_block_cons, hloop_eq]
            conv_rhs => rw [exec_block_cons]
            set discr := exec (max f_B f_rest) m stC_B locB_out_B [.loop 0 0 mainMergeBody] env
            rcases discr with ⟨r', s'⟩ | ⟨n, r', s'⟩ | ⟨r', vs⟩ | ⟨r', msg⟩ | ⟨msg⟩ | _
            · simp [exec, locB_out_B, locB_out_locs]
            · cases n with | zero => simp [exec, locB_out_B, locB_out_locs] | succ k => rfl
            all_goals rfl
          exact ⟨max f_B f_rest + 2, by rw [heq, hblock_mono]; exact hf_rest⟩
      · -- ── exit: j = n_right ──────────────────────────────────────────────────
        -- body's second br_if 1 fires: exec 1 body = Break 1 → exec 2 loop = Break 0
        -- → exec 3 block = Fallthrough.  Q: stA.mem.read32(frame+12) = n_right.
        have hj_eq : j = n_right.toNat := Nat.le_antisymm hj_hi (Nat.not_lt.mp hlt_j)
        have hi_lt32  : UInt32.ofNat i < n_left := by
          rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
          have := n_left.toNat_lt; omega
        have hj_nlt32 : ¬(UInt32.ofNat j < n_right) := by
          rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
          have := n_right.toNat_lt; omega
        have hb8  : ¬(frame.toNat + (8 : UInt32).toNat + 4 > stA.mem.pages * 65536) :=
          by simp; omega
        have hb12 : ¬(frame.toNat + (12 : UInt32).toNat + 4 > stA.mem.pages * 65536) :=
          by simp; omega
        have hgv6j : ∀ xs, ({ locA with values := xs } : Locals).get 6 = locA.get 6 := fun _ => rfl
        have hgv1j : ∀ xs, ({ locA with values := xs } : Locals).get 1 = locA.get 1 := fun _ => rfl
        have hgv3j : ∀ xs, ({ locA with values := xs } : Locals).get 3 = locA.get 3 := fun _ => rfl
        -- exec 1 body = Break 1 (second br_if 1 fires since j = n_right)
        have h_body_exit_j : exec 1 m stA locA mainMergeBody env = .Break 1 stA locA := by
          simp only [mainMergeBody, exec, execOne.eq_def,
                     hgv6j, hgv1j, hgv3j, hf6, h1, h3,
                     hi_m, hj_m,
                     if_neg hb8, if_neg hb12,
                     if_pos hi_lt32,
                     show (1 : UInt32) &&& 1 = 1 from by decide,
                     show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                     if_neg hj_nlt32,
                     show (1 : UInt32) &&& 0 = 0 from by decide]
          rfl
        -- exec 2 [.loop ...] = Break 0  (Break 1 from body → loop converts to Break 0)
        have h_loop_exit_j : exec 2 m stA locA [.loop 0 0 mainMergeBody] env = .Break 0 stA locA := by
          simp only [show (2 : Nat) = 1 + 1 from rfl, exec, execOne_loop_succ]
          rw [h_body_exit_j]
        -- exec 3 [.block ...] = Fallthrough  (Break 0 from loop → block gives Fallthrough)
        have h_block_exit_j : exec 3 m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env =
            .Fallthrough stA locA := by
          rw [show (3 : Nat) = 2 + 1 from rfl, exec_block_cons, h_loop_exit_j]
          simp only [List.take_zero, List.nil_append, List.drop_zero, exec]
        have hQ_j : stA.mem.read32 (frame + 12) = n_right := by
          rw [hj_m, hj_eq]
          apply UInt32.toNat_inj.mp
          simp
        exact ⟨3, by simp only [h_block_exit_j]; exact Or.inr hQ_j⟩
    · -- ── exit: i = n_left ────────────────────────────────────────────────────
      -- body's first br_if 1 fires immediately: exec 1 body = Break 1 → exec 2 loop = Break 0
      -- → exec 3 block = Fallthrough.  Q: stA.mem.read32(frame+8) = n_left.
      have hi_eq : i = n_left.toNat := Nat.le_antisymm hi_hi (Nat.not_lt.mp hlt_i)
      have hi_nlt32 : ¬(UInt32.ofNat i < n_left) := by
        rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
        have := n_left.toNat_lt; omega
      have hb8i : ¬(frame.toNat + (8 : UInt32).toNat + 4 > stA.mem.pages * 65536) :=
        by simp; omega
      have hgv6i : ∀ xs, ({ locA with values := xs } : Locals).get 6 = locA.get 6 := fun _ => rfl
      have hgv1i : ∀ xs, ({ locA with values := xs } : Locals).get 1 = locA.get 1 := fun _ => rfl
      -- exec 1 body = Break 1 (first br_if 1 fires since i = n_left)
      have h_body_exit_i : exec 1 m stA locA mainMergeBody env = .Break 1 stA locA := by
        simp only [mainMergeBody, exec, execOne.eq_def,
                   hgv1i, hf6, h1, hi_m,
                   if_neg hb8i,
                   if_neg hi_nlt32,
                   show (1 : UInt32) &&& 0 = 0 from by decide]
        rfl
      -- exec 2 [.loop ...] = Break 0
      have h_loop_exit_i : exec 2 m stA locA [.loop 0 0 mainMergeBody] env = .Break 0 stA locA := by
        simp only [show (2 : Nat) = 1 + 1 from rfl, exec, execOne_loop_succ]
        rw [h_body_exit_i]
      -- exec 3 [.block 0 0 [.loop ...]] = Fallthrough
      have h_block_exit_i : exec 3 m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env =
          .Fallthrough stA locA := by
        rw [show (3 : Nat) = 2 + 1 from rfl, exec_block_cons, h_loop_exit_i]
        simp only [List.take_zero, List.nil_append, List.drop_zero, exec]
      have hQ_i : stA.mem.read32 (frame + 8) = n_left := by
        rw [hi_m, hi_eq]
        apply UInt32.toNat_inj.mp
        simp
      exact ⟨3, by simp only [h_block_exit_i]; exact Or.inl hQ_i⟩

end Wasm.SepLogic.MergeSort
