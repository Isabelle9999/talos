import CodeLib.Tactics.Rule
import CodeLib.SepLogic.SmallStepTotalLifting
import CodeLib.SepLogic.SmallStepTotalLiftingBytes
import CodeLib.SepLogic.SmallStepLifting

/-!
# Wasm TWP and WP rule registry

Registers each `wasm_twp_pures` arm from `SmallStepTotalLifting.lean` and each
`wasm_wp_pures` arm from `SmallStepLifting.lean` into the `@[wasm_rule]`
environment extension so that `wasm_pure` / `wasm_pures` can select rules by
instruction head without an explicit name list.

The rule-to-constructor correspondence and the `rfl` flag match the
`macro_rules` arms in `SmallStepTotalLifting` (twp) and `SmallStepLifting` (wp).
-/

-- Forward syntax declaration so Pure.lean can quote `wasm_mem` before Mem.lean
-- defines its elaborator.  The `@[tactic wasm_mem]` attribute in Mem.lean wires
-- up the implementation; at Pure.lean's compile time, only the syntax is needed.
syntax (name := wasm_mem) "wasm_mem" ("using" "[" term,* "]")? : tactic

-- ─── TWP rules (modality `twp`, notation `[{ Φ }]`) ──────────────────────────

-- Rules whose arm is `iapply thm` (no rfl):
attribute [wasm_rule twp const]        Wasm.SmallStep.twp_const
attribute [wasm_rule twp add]          Wasm.SmallStep.twp_add
attribute [wasm_rule twp sub]          Wasm.SmallStep.twp_sub
attribute [wasm_rule twp mul]          Wasm.SmallStep.twp_mul
attribute [wasm_rule twp and]          Wasm.SmallStep.twp_and
attribute [wasm_rule twp or]           Wasm.SmallStep.twp_or
attribute [wasm_rule twp shl]          Wasm.SmallStep.twp_shl
attribute [wasm_rule twp shrU]         Wasm.SmallStep.twp_shrU
attribute [wasm_rule twp constI64]     Wasm.SmallStep.twp_constI64
attribute [wasm_rule twp subI64]       Wasm.SmallStep.twp_subI64
attribute [wasm_rule twp mulI64]       Wasm.SmallStep.twp_mulI64
attribute [wasm_rule twp orI64]        Wasm.SmallStep.twp_orI64
attribute [wasm_rule twp shlI64]       Wasm.SmallStep.twp_shlI64
attribute [wasm_rule twp shrUI64]      Wasm.SmallStep.twp_shrUI64
attribute [wasm_rule twp ctzI64]       Wasm.SmallStep.twp_ctzI64
attribute [wasm_rule twp wrapI64]      Wasm.SmallStep.twp_wrapI64
attribute [wasm_rule twp extendUI32]   Wasm.SmallStep.twp_extendUI32
attribute [wasm_rule twp block]        Wasm.SmallStep.twp_block
-- twp_brIfZero fires on .br_if when the condition is 0 (first tried).
-- twp_brIf fires when condition ≠ 0; decide closes `condition ≠ 0` and rfl closes
-- `branchTarget? = some (…)` for concrete operands (second tried, first success wins).
attribute [wasm_rule twp br_if]        Wasm.SmallStep.twp_brIfZero
attribute [wasm_rule twp br_if]        Wasm.SmallStep.twp_brIf

-- Rules whose arm is `iapply thm rfl` (rfl discharges the side condition):
attribute [wasm_rule twp localGet rfl]   Wasm.SmallStep.twp_localGet
attribute [wasm_rule twp localSet rfl]   Wasm.SmallStep.twp_localSet
attribute [wasm_rule twp localTee rfl]   Wasm.SmallStep.twp_localTee
attribute [wasm_rule twp br rfl]         Wasm.SmallStep.twp_br
attribute [wasm_rule twp eqz rfl]        Wasm.SmallStep.twp_eqz
attribute [wasm_rule twp eq rfl]         Wasm.SmallStep.twp_eq
attribute [wasm_rule twp ltU rfl]        Wasm.SmallStep.twp_ltU
attribute [wasm_rule twp gtU rfl]        Wasm.SmallStep.twp_gtU
attribute [wasm_rule twp ltUI64 rfl]     Wasm.SmallStep.twp_ltUI64
attribute [wasm_rule twp iff rfl]        Wasm.SmallStep.twp_iff

-- Additional TWP no-rfl rules (side condition closed by decide, or no side condition):
attribute [wasm_rule twp remU]         Wasm.SmallStep.twp_remU
attribute [wasm_rule twp drop]         Wasm.SmallStep.twp_drop

-- Additional TWP rfl rules (side condition of the form `result = if … then 1 else 0`):
attribute [wasm_rule twp ne rfl]       Wasm.SmallStep.twp_ne
attribute [wasm_rule twp ltS rfl]      Wasm.SmallStep.twp_ltS
attribute [wasm_rule twp geS rfl]      Wasm.SmallStep.twp_geS
attribute [wasm_rule twp leU rfl]      Wasm.SmallStep.twp_leU
attribute [wasm_rule twp geU rfl]      Wasm.SmallStep.twp_geU
attribute [wasm_rule twp select rfl]   Wasm.SmallStep.twp_select
attribute [wasm_rule twp eqI64 rfl]    Wasm.SmallStep.twp_eqI64
attribute [wasm_rule twp neI64 rfl]    Wasm.SmallStep.twp_neI64
attribute [wasm_rule twp gtUI64 rfl]   Wasm.SmallStep.twp_gtUI64

-- Sentinel for empty-code rule (fires when thread.code = []):
attribute [wasm_rule twp nil rfl]        Wasm.SmallStep.twp_exitControl

-- ─── TWP memory and global rules ─────────────────────────────────────────────
-- Registered with `wasm_mem_rule <modality> <head> <width> [<_addr-variant>?]`.
-- `wasm_mem` uses the _addr variant when the instruction offset is zero.
attribute [wasm_mem_rule twp load8U  byte Wasm.SmallStep.twp_load8U_addr]
    Wasm.SmallStep.twp_load8U
attribute [wasm_mem_rule twp store8  byte Wasm.SmallStep.twp_store8_addr]
    Wasm.SmallStep.twp_store8
attribute [wasm_mem_rule twp load32  u32  Wasm.SmallStep.twp_load32_addr]
    Wasm.SmallStep.twp_load32
attribute [wasm_mem_rule twp store32 u32  Wasm.SmallStep.twp_store32_addr]
    Wasm.SmallStep.twp_store32
-- No _addr variant for load64 in the codebase; the general rule handles offset 0 too.
attribute [wasm_mem_rule twp load64  u64]
    Wasm.SmallStep.twp_load64
attribute [wasm_mem_rule twp store64 u64  Wasm.SmallStep.twp_store64_addr]
    Wasm.SmallStep.twp_store64
attribute [wasm_mem_rule twp globalGet global]
    Wasm.SmallStep.twp_globalGet
attribute [wasm_mem_rule twp globalSet global]
    Wasm.SmallStep.twp_globalSet

-- Scalar-float fallback: registered under f32Const and f64Const (the actual instruction ctors):
attribute [wasm_rule twp f32Const rfl] Wasm.SmallStep.twp_scalarFloat0
attribute [wasm_rule twp f64Const rfl] Wasm.SmallStep.twp_scalarFloat0

-- Scalar-float unary rules (twp_scalarFloat1, rfl form):
attribute [wasm_rule twp f32Abs      rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f32Neg      rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f32Sqrt     rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f32Ceil     rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f32Floor    rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f32Trunc    rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f32Nearest  rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f64Abs      rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f64Neg      rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f64Sqrt     rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f64Ceil     rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f64Floor    rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f64Trunc    rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f64Nearest  rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f32ConvertI32S rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f32ConvertI32U rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f32ConvertI64S rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f32ConvertI64U rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f64ConvertI32S rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f64ConvertI32U rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f64ConvertI64S rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f64ConvertI64U rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp i32TruncSatF32S rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp i32TruncSatF32U rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp i32TruncSatF64S rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp i32TruncSatF64U rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp i64TruncSatF32S rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp i64TruncSatF32U rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp i64TruncSatF64S rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp i64TruncSatF64U rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f32DemoteF64    rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f64PromoteF32   rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp i32ReinterpretF32 rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp i64ReinterpretF64 rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f32ReinterpretI32 rfl] Wasm.SmallStep.twp_scalarFloat1
attribute [wasm_rule twp f64ReinterpretI64 rfl] Wasm.SmallStep.twp_scalarFloat1

-- Scalar-float binary rules (twp_scalarFloat2, rfl form):
attribute [wasm_rule twp f32Add      rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f32Sub      rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f32Mul      rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f32Div      rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f32Min      rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f32Max      rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f32Copysign rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f64Add      rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f64Sub      rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f64Mul      rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f64Div      rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f64Min      rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f64Max      rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f64Copysign rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f32Eq       rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f32Ne       rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f32Lt       rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f32Gt       rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f32Le       rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f32Ge       rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f64Eq       rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f64Ne       rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f64Lt       rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f64Gt       rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f64Le       rfl] Wasm.SmallStep.twp_scalarFloat2
attribute [wasm_rule twp f64Ge       rfl] Wasm.SmallStep.twp_scalarFloat2

-- ─── WP rules (modality `wp`, notation `{{ Φ }}`) ────────────────────────────
-- Mirrors the twp registry for the partial-WP (`Wp.wp`) rules from
-- SmallStepLifting.lean.  The `rfl` flag follows the `wasm_wp_pures` macro
-- arms in SmallStepLifting and the twp_ rfl pattern.

-- Rules whose arm is `iapply thm` (no rfl):
attribute [wasm_rule wp const]         Wasm.SmallStep.wp_const
attribute [wasm_rule wp add]           Wasm.SmallStep.wp_add
attribute [wasm_rule wp sub]           Wasm.SmallStep.wp_sub
attribute [wasm_rule wp mul]           Wasm.SmallStep.wp_mul
attribute [wasm_rule wp and]           Wasm.SmallStep.wp_and
attribute [wasm_rule wp or]            Wasm.SmallStep.wp_or
attribute [wasm_rule wp shl]           Wasm.SmallStep.wp_shl
attribute [wasm_rule wp constI64]      Wasm.SmallStep.wp_constI64
attribute [wasm_rule wp addI64]        Wasm.SmallStep.wp_addI64
attribute [wasm_rule wp subI64]        Wasm.SmallStep.wp_subI64
attribute [wasm_rule wp mulI64]        Wasm.SmallStep.wp_mulI64
attribute [wasm_rule wp andI64]        Wasm.SmallStep.wp_andI64
attribute [wasm_rule wp orI64]         Wasm.SmallStep.wp_orI64
attribute [wasm_rule wp shlI64]        Wasm.SmallStep.wp_shlI64
attribute [wasm_rule wp shrUI64]       Wasm.SmallStep.wp_shrUI64
attribute [wasm_rule wp ctzI64]        Wasm.SmallStep.wp_ctzI64
attribute [wasm_rule wp wrapI64]       Wasm.SmallStep.wp_wrapI64
attribute [wasm_rule wp extendUI32]    Wasm.SmallStep.wp_extendUI32
attribute [wasm_rule wp block]         Wasm.SmallStep.wp_block
-- wp_brIfZero fires on .br_if when the condition is 0 (first tried).
-- wp_brIf fires when condition ≠ 0 (second tried, first success wins).
attribute [wasm_rule wp br_if]         Wasm.SmallStep.wp_brIfZero
attribute [wasm_rule wp br_if]         Wasm.SmallStep.wp_brIf

-- Rules whose arm is `iapply thm rfl` (rfl discharges the side condition):
attribute [wasm_rule wp localGet rfl]  Wasm.SmallStep.wp_localGet
attribute [wasm_rule wp localSet rfl]  Wasm.SmallStep.wp_localSet
attribute [wasm_rule wp localTee rfl]  Wasm.SmallStep.wp_localTee
attribute [wasm_rule wp br rfl]        Wasm.SmallStep.wp_br
attribute [wasm_rule wp eqz rfl]       Wasm.SmallStep.wp_eqz
attribute [wasm_rule wp eq rfl]        Wasm.SmallStep.wp_eq
attribute [wasm_rule wp ltU rfl]       Wasm.SmallStep.wp_ltU
attribute [wasm_rule wp gtU rfl]       Wasm.SmallStep.wp_gtU
attribute [wasm_rule wp ltUI64 rfl]    Wasm.SmallStep.wp_ltUI64
attribute [wasm_rule wp iff rfl]       Wasm.SmallStep.wp_iff

-- Additional WP no-rfl rules:
attribute [wasm_rule wp drop]          Wasm.SmallStep.wp_drop
attribute [wasm_rule wp remU]          Wasm.SmallStep.wp_remU
attribute [wasm_rule wp xorI64]        Wasm.SmallStep.wp_xorI64
attribute [wasm_rule wp divUI64]       Wasm.SmallStep.wp_divUI64
attribute [wasm_rule wp remUI64]       Wasm.SmallStep.wp_remUI64

-- Additional WP rfl rules (i32 comparisons):
attribute [wasm_rule wp ne rfl]        Wasm.SmallStep.wp_ne
attribute [wasm_rule wp ltS rfl]       Wasm.SmallStep.wp_ltS
attribute [wasm_rule wp geS rfl]       Wasm.SmallStep.wp_geS
attribute [wasm_rule wp leU rfl]       Wasm.SmallStep.wp_leU
attribute [wasm_rule wp geU rfl]       Wasm.SmallStep.wp_geU
attribute [wasm_rule wp select rfl]    Wasm.SmallStep.wp_select

-- Additional WP rfl rules (i64 comparisons, all missing from the original registry):
attribute [wasm_rule wp eqI64 rfl]     Wasm.SmallStep.wp_eqI64
attribute [wasm_rule wp neI64 rfl]     Wasm.SmallStep.wp_neI64
attribute [wasm_rule wp gtUI64 rfl]    Wasm.SmallStep.wp_gtUI64
attribute [wasm_rule wp leUI64 rfl]    Wasm.SmallStep.wp_leUI64
attribute [wasm_rule wp gtSI64 rfl]    Wasm.SmallStep.wp_gtSI64
attribute [wasm_rule wp leSI64 rfl]    Wasm.SmallStep.wp_leSI64
attribute [wasm_rule wp geSI64 rfl]    Wasm.SmallStep.wp_geSI64
attribute [wasm_rule wp eqzI64 rfl]    Wasm.SmallStep.wp_eqzI64

-- Additional WP no-rfl rules (i32 bitwise / shift / div / misc):
attribute [wasm_rule wp xor]           Wasm.SmallStep.wp_xor
attribute [wasm_rule wp shrS]          Wasm.SmallStep.wp_shrS
attribute [wasm_rule wp rotl]          Wasm.SmallStep.wp_rotl
attribute [wasm_rule wp rotr]          Wasm.SmallStep.wp_rotr
attribute [wasm_rule wp divU]          Wasm.SmallStep.wp_divU
attribute [wasm_rule wp divS]          Wasm.SmallStep.wp_divS
attribute [wasm_rule wp remS]          Wasm.SmallStep.wp_remS
attribute [wasm_rule wp clz]           Wasm.SmallStep.wp_clz
attribute [wasm_rule wp nop]           Wasm.SmallStep.wp_nop

-- Additional WP rfl rules (remaining i32 signed comparisons):
attribute [wasm_rule wp leS rfl]       Wasm.SmallStep.wp_leS
attribute [wasm_rule wp gtS rfl]       Wasm.SmallStep.wp_gtS

-- Sentinel for empty-code rule (fires when thread.code = []):
attribute [wasm_rule wp nil rfl]       Wasm.SmallStep.wp_exitControl

-- Scalar-float fallback: registered under f32Const and f64Const (the actual instruction ctors):
attribute [wasm_rule wp f32Const rfl] Wasm.SmallStep.wp_scalarFloat0
attribute [wasm_rule wp f64Const rfl] Wasm.SmallStep.wp_scalarFloat0

-- Scalar-float unary rules (wp_scalarFloat1, rfl form):
attribute [wasm_rule wp f32Abs      rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f32Neg      rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f32Sqrt     rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f32Ceil     rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f32Floor    rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f32Trunc    rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f32Nearest  rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f64Abs      rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f64Neg      rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f64Sqrt     rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f64Ceil     rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f64Floor    rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f64Trunc    rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f64Nearest  rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f32ConvertI32S rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f32ConvertI32U rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f32ConvertI64S rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f32ConvertI64U rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f64ConvertI32S rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f64ConvertI32U rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f64ConvertI64S rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f64ConvertI64U rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp i32TruncSatF32S rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp i32TruncSatF32U rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp i32TruncSatF64S rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp i32TruncSatF64U rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp i64TruncSatF32S rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp i64TruncSatF32U rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp i64TruncSatF64S rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp i64TruncSatF64U rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f32DemoteF64    rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f64PromoteF32   rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp i32ReinterpretF32 rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp i64ReinterpretF64 rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f32ReinterpretI32 rfl] Wasm.SmallStep.wp_scalarFloat1
attribute [wasm_rule wp f64ReinterpretI64 rfl] Wasm.SmallStep.wp_scalarFloat1

-- Scalar-float binary rules (wp_scalarFloat2, rfl form):
attribute [wasm_rule wp f32Add      rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f32Sub      rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f32Mul      rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f32Div      rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f32Min      rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f32Max      rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f32Copysign rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f64Add      rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f64Sub      rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f64Mul      rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f64Div      rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f64Min      rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f64Max      rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f64Copysign rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f32Eq       rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f32Ne       rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f32Lt       rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f32Gt       rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f32Le       rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f32Ge       rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f64Eq       rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f64Ne       rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f64Lt       rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f64Gt       rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f64Le       rfl] Wasm.SmallStep.wp_scalarFloat2
attribute [wasm_rule wp f64Ge       rfl] Wasm.SmallStep.wp_scalarFloat2
