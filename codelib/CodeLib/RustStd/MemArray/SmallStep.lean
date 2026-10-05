import CodeLib.RustStd.MemArray
import CodeLib.SepLogic.SmallStepAdequacy

/-! Small-step ownership facts for consecutive memory arrays. -/

namespace Wasm.SepLogic

open Iris Std
open Wasm.SmallStep

/-- Build a `WasmHeapMap` from a list of `u32` words starting at `base`. -/
def heap32Aux (σ : WasmHeapMap (Option UInt8)) (base : UInt32) :
    List UInt32 → WasmHeapMap (Option UInt8)
  | [] => σ
  | x :: xs => heap32Aux (store32Heap σ 0 base x) (base + 4) xs

theorem heap32Aux_agrees
    (σ : WasmHeapMap (Option UInt8)) (mem : Mem) (base : UInt32) (xs : List UInt32)
    (hagree : heapAgreesWithMem σ (fun id => if id = 0 then some mem else none))
    (hfit : base.toNat + 4 * xs.length ≤ UInt32.size) :
    heapAgreesWithMem (heap32Aux σ base xs)
      (fun id => if id = 0 then some (Mem.writeWords32 mem base xs) else none) := by
  induction xs generalizing σ mem base with
  | nil => simpa [heap32Aux, Mem.writeWords32]
  | cons x xs ih =>
    simp only [heap32Aux, Mem.writeWords32, List.length_cons] at *
    simp only [UInt32.size] at hfit
    have h4_le : (base + 4 : UInt32).toNat ≤ base.toNat + 4 := by
      have h := UInt32.toNat_add base 4
      simp only [show (4 : UInt32).toNat = 4 from by decide] at h
      rw [h]; exact Nat.mod_le _ _
    obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4 base (by omega)
    apply ih
    · exact store32_sound0 σ mem base x h1 h2 h3 hagree
    · simp only [UInt32.size]; omega

theorem heap32Aux_inBounds
    (σ : WasmHeapMap (Option UInt8)) (mem : Mem) (base : UInt32) (xs : List UInt32)
    (hinBounds : heapAddressesInBounds σ (fun id => if id = 0 then some mem else none))
    (hfit : base.toNat + 4 * xs.length ≤ UInt32.size)
    (hmem : base.toNat + 4 * xs.length ≤ mem.pages * 65536) :
    heapAddressesInBounds (heap32Aux σ base xs)
      (fun id => if id = 0 then some (Mem.writeWords32 mem base xs) else none) := by
  induction xs generalizing σ mem base with
  | nil => simpa [heap32Aux, Mem.writeWords32]
  | cons x xs ih =>
    simp only [heap32Aux, Mem.writeWords32, List.length_cons] at *
    simp only [UInt32.size] at hfit
    have h4_le : (base + 4 : UInt32).toNat ≤ base.toNat + 4 := by
      have h := UInt32.toNat_add base 4
      simp only [show (4 : UInt32).toNat = 4 from by decide] at h
      rw [h]; exact Nat.mod_le _ _
    have hpages : (mem.write32 base x).pages = mem.pages := by simp [Mem.write32]
    obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4 base (by omega)
    apply ih
    · exact store32_inBounds0 σ mem base x h1 h2 h3 (by omega) hinBounds
    · simp only [UInt32.size]; omega
    · rw [hpages]; omega

theorem heap32Aux_pointsTo [WasmHeapGS α]
    (σ : WasmHeapMap (Option UInt8)) (base : UInt32) (xs : List UInt32)
    (hdisjoint : ∀ a b, get? σ a = some b → a.addr.toNat < base.toNat)
    (hfit : base.toNat + 4 * xs.length < UInt32.size) :
    ([∗map] address ↦ value ∈ heap32Aux σ base xs,
        pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap) address (DFrac.own 1) value) ⊢
      arrayAt 0 base xs ∗
      ([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap) address (DFrac.own 1) value) := by
  induction xs generalizing σ base with
  | nil =>
    simp only [heap32Aux, arrayAt, BI.emp_sep.to_eq]
    iintro Hσ; iexact Hσ
  | cons x xs ih =>
    simp only [heap32Aux, List.length_cons] at *
    simp only [UInt32.size] at hfit
    have h4 : (base + 4 : UInt32).toNat = base.toNat + 4 :=
      UInt32.add_ofNat_toNat_noWrap base 4 (by decide) (by omega)
    have hfit' : (base + 4).toNat + 4 * xs.length < UInt32.size := by
      simp only [UInt32.size]; omega
    obtain ⟨hn1, hn2, hn3⟩ := UInt32.addSteps4 base (by omega)
    have hget0 : get? σ ⟨0, base⟩ = none := by
      by_contra h; obtain ⟨v, hget⟩ := Option.ne_none_iff_exists.mp h
      have hlt := hdisjoint (⟨0, base⟩ : MemoryKey) v hget.symm
      change base.toNat < base.toNat at hlt; exact absurd hlt (Nat.lt_irrefl _)
    have hget1 : get? σ ⟨0, base + 1⟩ = none := by
      by_contra h; obtain ⟨v, hget⟩ := Option.ne_none_iff_exists.mp h
      have hlt := hdisjoint (⟨0, base + 1⟩ : MemoryKey) v hget.symm
      change (base + 1).toNat < base.toNat at hlt; rw [hn1] at hlt; omega
    have hget2 : get? σ ⟨0, base + 2⟩ = none := by
      by_contra h; obtain ⟨v, hget⟩ := Option.ne_none_iff_exists.mp h
      have hlt := hdisjoint (⟨0, base + 2⟩ : MemoryKey) v hget.symm
      change (base + 2).toNat < base.toNat at hlt; rw [hn2] at hlt; omega
    have hget3 : get? σ ⟨0, base + 3⟩ = none := by
      by_contra h; obtain ⟨v, hget⟩ := Option.ne_none_iff_exists.mp h
      have hlt := hdisjoint (⟨0, base + 3⟩ : MemoryKey) v hget.symm
      change (base + 3).toNat < base.toNat at hlt; rw [hn3] at hlt; omega
    have hdisjoint' : ∀ a b, get? (store32Heap σ 0 base x) a = some b →
        a.addr.toNat < (base + 4).toNat := by
      rw [h4]
      intro a b hget
      by_cases h3 : a = ⟨0, base + 3⟩
      · subst h3; change (base + 3).toNat < base.toNat + 4; rw [hn3]; omega
      by_cases h2 : a = ⟨0, base + 2⟩
      · subst h2; change (base + 2).toNat < base.toNat + 4; rw [hn2]; omega
      by_cases h1 : a = ⟨0, base + 1⟩
      · subst h1; change (base + 1).toNat < base.toNat + 4; rw [hn1]; omega
      by_cases h0 : a = ⟨0, base⟩
      · subst h0; change base.toNat < base.toNat + 4; omega
      · simp only [store32Heap, get?_insert_ne (Ne.symm h3), get?_insert_ne (Ne.symm h2),
            get?_insert_ne (Ne.symm h1), get?_insert_ne (Ne.symm h0)] at hget
        have hlt := hdisjoint a b hget; omega
    iintro Hheap
    ihave ⟨Hxs, Hstore32⟩ := ih (store32Heap σ 0 base x) (base + 4) hdisjoint' hfit' $$ Hheap
    ihave ⟨Hword, Hσ⟩ :=
      store32Heap_pointsTo σ 0 base x hget0 hget1 hget2 hget3 hn1 hn2 hn3 $$ Hstore32
    simp only [arrayAt]
    isplitl [Hword Hxs]
    · isplitl_exact Hword; iexact Hxs
    · iexact Hσ

/-- Walking `arrayAt` ownership reads back exactly its sequence of `u32` words. -/
theorem arrayAt_readWords32 [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat) (obs : List StepKind) (threads : Nat)
    (base : UInt32) (output : List UInt32)
    (hfit : base.toNat + 4 * output.length ≤ UInt32.size) :
    stateInterp (GF := WasmHeapGF α) store steps obs threads ∗ arrayAt 0 base output ==∗
      stateInterp (GF := WasmHeapGF α) store steps obs threads ∗ arrayAt 0 base output ∗
      ⌜store.wasm.mem.readWords32 base output.length = output⌝ := by
  induction output generalizing base with
  | nil =>
    simp only [arrayAt, List.length_nil, Mem.readWords32]
    iintro ⟨Hstate, Hemp⟩
    imodintro
    isplitl_exacts [Hstate Hemp]
    ipureintro; trivial
  | cons x xs ih =>
    simp only [arrayAt, List.length_cons]
    simp only [List.length_cons, UInt32.size] at hfit
    have h4_le : (base + 4 : UInt32).toNat ≤ base.toNat + 4 := by
      have h := UInt32.toNat_add base 4
      simp only [show (4 : UInt32).toNat = 4 from by decide] at h
      rw [h]; exact Nat.mod_le _ _
    have hfit' : (base + 4).toNat + 4 * xs.length ≤ UInt32.size := by
      simp only [UInt32.size]; omega
    obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4 base (by omega)
    iintro ⟨Hstate, Hword, Hxs⟩
    imod stateInterp_pointsTo_u32_facts_frame store steps obs threads base x
      h1 h2 h3 $$ [$Hstate $Hword] with ⟨Hstate, Hword, %hfacts⟩
    imod ih (base + 4) hfit' $$ [$Hstate $Hxs] with ⟨Hstate, Hxs, %hread⟩
    imodintro
    isplitl_exact Hstate
    isplitl [Hword Hxs]
    · isplitl_exact Hword; iexact Hxs
    ipureintro
    simp only [Mem.readWords32, hfacts.1, hread]

end Wasm.SepLogic
