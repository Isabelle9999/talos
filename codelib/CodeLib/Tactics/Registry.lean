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

The rule-to-constructor correspondence and the `rfl` flag are copied verbatim
from the `macro_rules` arms at `SmallStepTotalLifting.lean:1664–1728` (twp)
and `SmallStepLifting.lean:780–833` (wp).
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
-- twp_brIfZero fires on .br_if when the top-of-stack value is 0.
attribute [wasm_rule twp br_if]        Wasm.SmallStep.twp_brIfZero

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

-- Sentinel for the scalar-float fallback (fires when evalScalarFloat0? succeeds):
attribute [wasm_rule twp scalarFloat0 rfl] Wasm.SmallStep.twp_scalarFloat0

-- ─── WP rules (modality `wp`, notation `{{ Φ }}`) ────────────────────────────
-- Mirrors the twp registry for the partial-WP (`Wp.wp`) rules from
-- SmallStepLifting.lean.  The `rfl` flag follows the `wasm_wp_pures` macro
-- arms (SmallStepLifting.lean:780-833) and the twp_ rfl pattern.

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
-- wp_brIfZero fires on .br_if when the top-of-stack value is 0.
attribute [wasm_rule wp br_if]         Wasm.SmallStep.wp_brIfZero

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

-- Sentinel for empty-code rule (fires when thread.code = []):
attribute [wasm_rule wp nil rfl]       Wasm.SmallStep.wp_exitControl

-- Sentinel for the scalar-float fallback (fires when evalScalarFloat0? succeeds):
attribute [wasm_rule wp scalarFloat0 rfl] Wasm.SmallStep.wp_scalarFloat0
