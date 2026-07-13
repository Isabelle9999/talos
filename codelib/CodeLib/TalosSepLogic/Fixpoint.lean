import CodeLib.TalosSepLogic.Core
import CodeLib.TalosSepLogic.BI

universe u

/-! # TalosSepLogic.Fixpoint — Knaster-Tarski least fixpoint over WasmProp

Built without iris-lean: `bi_least_fixpoint F x` is the (predicative, Prop-valued)
intersection of all post-fixpoints of F. -/

namespace TalosSepLogic

open WasmProp HeapFrag BI

-- ─── Monotone predicate class ─────────────────────────────────────────────────

/-- A functor `F` over `α → WasmProp` is monotone when entailment-wise monotone
    maps between predicates lift to entailment-wise monotone maps after applying F. -/
class BIMonoPred {α : Type u} (F : (α → WasmProp) → (α → WasmProp)) : Prop where
  mono_pred : ∀ {Φ Ψ : α → WasmProp},
    (∀ a, (Φ a).entails (Ψ a)) → ∀ a, (F Φ a).entails (F Ψ a)

-- ─── Least fixpoint ──────────────────────────────────────────────────────────

/-- The least fixpoint of `F`, defined as the intersection of all post-fixpoints.
    `bi_least_fixpoint F x h` holds iff `Φ x h` holds for every `Φ` that is a
    post-fixpoint of `F` (i.e., satisfies `F Φ a ⊢ Φ a` for all `a`). -/
def bi_least_fixpoint {α : Type u} (F : (α → WasmProp) → (α → WasmProp))
    (x : α) : WasmProp :=
  fun h => ∀ Φ : α → WasmProp, (∀ a, (F Φ a).entails (Φ a)) → Φ x h

-- ─── Core theorems ───────────────────────────────────────────────────────────

/-- lfp F is a post-fixpoint of F: `F (lfp F) x ⊢ lfp F x`

    Proof: given `h : F (lfp F) x h`, for any post-fixpoint Φ, use
    monotonicity (lfp F ⊢ Φ by definition of lfp) to get `F Φ x h`,
    then apply the post-fixpoint condition. -/
theorem least_fixpoint_unfold_mpr {α : Type u}
    {F : (α → WasmProp) → (α → WasmProp)} [inst : BIMonoPred F] (x : α) :
    (F (bi_least_fixpoint F) x).entails (bi_least_fixpoint F x) := by
  intro h hF Φ hΦ
  -- lfp F a ⊢ Φ a for each a (since lfp is the intersection of all post-fixpoints)
  have hlfp_le : ∀ a, (bi_least_fixpoint F a).entails (Φ a) :=
    fun a hfrag hlfp => hlfp Φ hΦ
  -- By monotonicity: F(lfp F) x h implies F Φ x h
  have hFΦ := inst.mono_pred hlfp_le x h hF
  -- Apply post-fixpoint condition for Φ
  exact hΦ x h hFΦ

/-- Iteration principle: any post-fixpoint is above lfp.
    `(∀ a, F Φ a ⊢ Φ a) → ∀ x, lfp F x ⊢ Φ x`

    Proof: direct from definition of lfp (instantiate Ψ with Φ). -/
theorem least_fixpoint_iter {α : Type u}
    {F : (α → WasmProp) → (α → WasmProp)} [BIMonoPred F]
    {Φ : α → WasmProp} (h : ∀ a, (F Φ a).entails (Φ a)) :
    ∀ x, (bi_least_fixpoint F x).entails (Φ x) :=
  fun _ _ hlfp => hlfp Φ h

/-- lfp F is also a pre-fixpoint: `lfp F x ⊢ F (lfp F) x`

    Combined with `least_fixpoint_unfold_mpr`, lfp F is a fixpoint of F.

    Proof: lfp is the least post-fixpoint. Show `F (lfp F)` is itself a
    post-fixpoint, then lfp ⊢ F(lfp) follows from the minimality of lfp.
    `F(lfp)` is a post-fixpoint because `F(F(lfp)) ⊢ F(lfp)` (monotonicity
    applied to `F(lfp) ⊢ lfp`, which is least_fixpoint_unfold_mpr). -/
theorem least_fixpoint_unfold_mp {α : Type u}
    {F : (α → WasmProp) → (α → WasmProp)} [inst : BIMonoPred F] (x : α) :
    (bi_least_fixpoint F x).entails (F (bi_least_fixpoint F) x) := by
  -- F(lfp F) is a post-fixpoint because F(F(lfp F)) ⊢ F(lfp F)
  have hFFlfp : ∀ a, (F (F (bi_least_fixpoint F)) a).entails (F (bi_least_fixpoint F) a) :=
    fun a => inst.mono_pred (fun b => least_fixpoint_unfold_mpr b) a
  -- By iteration, lfp F ⊢ F(lfp F)
  exact least_fixpoint_iter hFFlfp x

/-- Full fixpoint unfolding: `lfp F x = F (lfp F) x` as an entailment pair. -/
theorem least_fixpoint_unfold {α : Type u}
    {F : (α → WasmProp) → (α → WasmProp)} [BIMonoPred F] (x : α) :
    ∀ h, bi_least_fixpoint F x h ↔ F (bi_least_fixpoint F) x h :=
  fun h => ⟨least_fixpoint_unfold_mp x h, least_fixpoint_unfold_mpr x h⟩

end TalosSepLogic
