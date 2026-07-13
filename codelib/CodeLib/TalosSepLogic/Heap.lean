import CodeLib.TalosSepLogic.Core
import CodeLib.TalosSepLogic.BI
import Interpreter.Wasm

/-! # TalosSepLogic.Heap — byte/word ownership connecting HeapFrag to Wasm.Mem -/

namespace TalosSepLogic

open WasmProp HeapFrag BI

-- ─── Atomic ownership ────────────────────────────────────────────────────────

/-- Own exactly one byte at `addr` with value `v`. -/
def pointsTo_byte (addr : Nat) (v : UInt8) : WasmProp :=
  fun h => h addr = some v ∧ ∀ a, a ≠ addr → h a = none

-- ─── 4-byte word ownership ───────────────────────────────────────────────────

private def b0 (v : UInt32) : UInt8 := (v &&& 0xFF).toUInt8
private def b1 (v : UInt32) : UInt8 := ((v >>> 8) &&& 0xFF).toUInt8
private def b2 (v : UInt32) : UInt8 := ((v >>> 16) &&& 0xFF).toUInt8
private def b3 (v : UInt32) : UInt8 := ((v >>> 24) &&& 0xFF).toUInt8

/-- Own 4 consecutive bytes (little-endian u32) starting at `addr`. -/
def pointsTo_u32_bytes (addr : Nat) (v : UInt32) : WasmProp :=
  (pointsTo_byte addr (b0 v)).sep
    ((pointsTo_byte (addr + 1) (b1 v)).sep
      ((pointsTo_byte (addr + 2) (b2 v)).sep
        (pointsTo_byte (addr + 3) (b3 v))))

/-- Same as `pointsTo_u32_bytes` but with a `UInt32` address. -/
def pointsTo_u32 (addr : UInt32) (v : UInt32) : WasmProp :=
  pointsTo_u32_bytes addr.toNat v

/-- Own 8 consecutive bytes (little-endian u64) as two u32 words. -/
def pointsTo_u64 (addr : UInt32) (v : UInt64) : WasmProp :=
  (pointsTo_u32 addr v.toUInt32).sep
    (pointsTo_u32 (addr + 4) (v >>> 32).toUInt32)

-- ─── Heap interpretation ─────────────────────────────────────────────────────

/-- `heapInterp m h` holds when every byte owned by fragment `h` agrees with `m`. -/
def heapInterp (m : Wasm.Mem) : WasmProp :=
  fun h => ∀ i v, h i = some v → m.bytes i = v

-- ─── Key Lemmas ──────────────────────────────────────────────────────────────

/-- Disjointness: if two addresses differ, their singleton fragments are disjoint. -/
theorem pointsTo_byte_ne_disjoint {addr₁ addr₂ : Nat} (hne : addr₁ ≠ addr₂)
    {v₁ v₂ : UInt8} (h₁ : HeapFrag) (h₂ : HeapFrag)
    (hhf1 : pointsTo_byte addr₁ v₁ h₁) (hhf2 : pointsTo_byte addr₂ v₂ h₂) :
    h₁.disjoint h₂ := by
  intro i
  rcases hhf1 with ⟨_, hrest₁⟩
  rcases hhf2 with ⟨_, hrest₂⟩
  by_cases h1 : i = addr₁
  · right; rw [h1]; exact hrest₂ addr₁ hne
  · left; exact hrest₁ i h1

/-- Different addresses give satisfiable disjoint ownership.
    The witnesses are singleton HeapFrags. -/
theorem pointsTo_ne {addr₁ addr₂ : Nat} (hne : addr₁ ≠ addr₂) (v₁ v₂ : UInt8) :
    ∃ h, (pointsTo_byte addr₁ v₁).sep (pointsTo_byte addr₂ v₂) h := by
  refine ⟨(HeapFrag.singleton addr₁ v₁).union (HeapFrag.singleton addr₂ v₂),
    HeapFrag.singleton addr₁ v₁, HeapFrag.singleton addr₂ v₂, ?_, rfl, ?_, ?_⟩
  · -- disjointness of the two singletons
    intro i
    simp only [HeapFrag.singleton]
    by_cases h1 : i = addr₁
    · subst h1; right; simp [hne]
    · left; simp [h1]
  · -- pointsTo_byte addr₁ v₁ (singleton addr₁ v₁)
    constructor
    · simp [HeapFrag.singleton]
    · intro a ha; simp [HeapFrag.singleton, ha]
  · -- pointsTo_byte addr₂ v₂ (singleton addr₂ v₂)
    constructor
    · simp [HeapFrag.singleton]
    · intro a ha; simp [HeapFrag.singleton, ha]

-- ─── Agree lemmas ────────────────────────────────────────────────────────────

/-- If the combined fragment agrees with `m`, and we own `addr` with value `v`,
    then `m.bytes addr = v`.

    Note: In a concrete heap model without ghost state / fractional ownership,
    the standard separation `(heapInterp m) ∗ (pointsTo_byte addr v)` puts
    heapInterp on fragment h₁ and pointsTo on h₂, where h₁.disjoint h₂ implies
    h₁ does NOT own addr. Therefore heapInterp m h₁ says nothing about
    m.bytes addr (the "none ⇒ True" branch applies).

    The lemma as stated holds in the iris model because genHeapInterp uses an
    *authoritative* camera element that tracks ALL bytes even when individual
    pointsTo fragments have been handed out. Without that ghost state machinery,
    we must sorry this lemma.

    The closest provable statement is:
    ∀ i v, (h₁.union h₂) i = some v → m.bytes i = v (on the combined fragment),
    from which `m.bytes addr = v` follows directly. -/
theorem pointsTo_byte_agree {m : Wasm.Mem} {addr : Nat} {v : UInt8} :
    (heapInterp m).sep (pointsTo_byte addr v) ⊢ WasmProp.pure (m.bytes addr = v) := by
  sorry
  -- Cannot prove: heapInterp m h₁ (where h₁ is disjoint from h₂ owning addr)
  -- says nothing about m.bytes addr, since h₁ addr = none.
  -- Fix: use a camera-based authoritative/fragment model (as in iris genHeap).

/-- After writing `v_new` to `addr`, update the ownership accordingly.

    The forward direction (`heapInterp m ∗ pointsTo addr v_old →
    heapInterp (m.write8 addr v_new) ∗ pointsTo addr v_new`) requires
    "ghost state update" in iris (==∗ modality). In our concrete model,
    the same ghost-state issue as `pointsTo_byte_agree` applies.

    The proof sketch:
    - Let h₁ = heapInterp's fragment, h₂ = {addr ↦ v_old}
    - Define h₂' = {addr ↦ v_new}
    - h₁ still agrees with (m.write8 addr v_new) at all i ≠ addr (write8 only touches addr)
    - h₂' = pointsTo_byte addr v_new by definition
    - Combined fragment h₁.union h₂' still covers the right bytes -/
theorem pointsTo_byte_update {m : Wasm.Mem} {addr : UInt32} {v_old v_new : UInt8} :
    (heapInterp m).sep (pointsTo_byte addr.toNat v_old) ⊢
    (heapInterp (m.write8 addr v_new)).sep (pointsTo_byte addr.toNat v_new) := by
  sorry
  -- Same fundamental issue as pointsTo_byte_agree.
  -- In a model with ghost state, the ==∗ update would transfer ownership of
  -- addr from v_old to v_new while keeping heapInterp consistent.

/-- 4-byte read round-trip: if we own 4 bytes encoding `v` (little-endian),
    then `m.read32 addr = v`.

    This follows from 4 applications of `pointsTo_byte_agree`, plus the
    little-endian assembly identity. Also depends on sorry in pointsTo_byte_agree. -/
theorem pointsTo_u32_agree {m : Wasm.Mem} {addr : UInt32} {v : UInt32} :
    (heapInterp m).sep (pointsTo_u32 addr v) ⊢ WasmProp.pure (m.read32 addr = v) := by
  sorry
  -- Depends on pointsTo_byte_agree (×4) plus the arithmetic identity:
  --   b0 v ||| (b1 v <<< 8) ||| (b2 v <<< 16) ||| (b3 v <<< 24) = v
  -- The second part is a pure UInt32 identity (provable by omega/decide for any v).
  -- The first part is blocked by the ghost-state gap in pointsTo_byte_agree.

end TalosSepLogic
