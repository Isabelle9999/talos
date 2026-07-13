import Interpreter.Wasm

/-! # HeapFrag — partial byte-addressed heap for Talos separation logic -/

def HeapFrag := Nat → Option UInt8

namespace HeapFrag

def empty : HeapFrag := fun _ => none

def singleton (addr : Nat) (v : UInt8) : HeapFrag :=
  fun i => if i = addr then some v else none

def disjoint (h₁ h₂ : HeapFrag) : Prop :=
  ∀ i, h₁ i = none ∨ h₂ i = none

def union (h₁ h₂ : HeapFrag) : HeapFrag :=
  fun i => match h₁ i with
    | some v => some v
    | none   => h₂ i

/-! ## Lemmas -/

theorem disjoint_comm {h₁ h₂ : HeapFrag} : h₁.disjoint h₂ ↔ h₂.disjoint h₁ := by
  constructor
  · intro hd i; rcases hd i with h | h <;> simp [h]
  · intro hd i; rcases hd i with h | h <;> simp [h]

theorem disjoint_empty_left (h : HeapFrag) : HeapFrag.empty.disjoint h := by
  intro i; left; rfl

theorem disjoint_empty_right (h : HeapFrag) : h.disjoint HeapFrag.empty := by
  intro i; right; rfl

theorem union_empty_left (h : HeapFrag) : HeapFrag.empty.union h = h := by
  funext i; simp [union, empty]

theorem union_empty_right (h : HeapFrag) : h.union HeapFrag.empty = h := by
  funext i; simp [union, empty]; cases h i <;> rfl

theorem union_comm {h₁ h₂ : HeapFrag} (hd : h₁.disjoint h₂) : h₁.union h₂ = h₂.union h₁ := by
  funext i
  simp only [union]
  rcases hd i with h | h
  · simp [h]; cases h₂ i <;> rfl
  · simp [h]; cases h₁ i <;> rfl

theorem union_assoc (h₁ h₂ h₃ : HeapFrag) :
    (h₁.union h₂).union h₃ = h₁.union (h₂.union h₃) := by
  funext i
  simp only [union]
  cases h₁ i <;> simp

theorem disjoint_union_left {h₁ h₂ h₃ : HeapFrag}
    (hd : (h₁.union h₂).disjoint h₃) : h₁.disjoint h₃ := by
  intro i
  rcases hd i with h | h
  · left
    match heq : h₁ i with
    | none   => rfl
    | some v => exact absurd h (by simp [union, heq])
  · right; exact h

theorem disjoint_union_right {h₁ h₂ h₃ : HeapFrag}
    (hd : h₁.disjoint (h₂.union h₃)) : h₁.disjoint h₂ := by
  intro i
  rcases hd i with h | h
  · left; exact h
  · right
    match heq : h₂ i with
    | none   => rfl
    | some v => exact absurd h (by simp [union, heq])

theorem union_none_iff {h₁ h₂ : HeapFrag} {i : Nat} :
    h₁.union h₂ i = none ↔ h₁ i = none ∧ h₂ i = none := by
  simp only [union]
  cases h₁ i with
  | some v => simp
  | none => simp

-- If h₁∪h₂ is disjoint from h₃, then h₂ is disjoint from h₃
theorem disjoint_of_union_disjoint_right {h₁ h₂ h₃ : HeapFrag}
    (_ : h₁.disjoint h₂) (hd : (h₁.union h₂).disjoint h₃) : h₂.disjoint h₃ := by
  intro i
  rcases hd i with h | h
  · left; exact (union_none_iff.mp h).2
  · right; exact h

-- From h₁⊥h₂ and (h₁∪h₂)⊥h₃, derive h₁⊥(h₂∪h₃)
theorem disjoint_of_left_disjoint_union {h₁ h₂ h₃ : HeapFrag}
    (hd₁₂ : h₁.disjoint h₂) (hd₁₂₃ : (h₁.union h₂).disjoint h₃) :
    h₁.disjoint (h₂.union h₃) := by
  intro i
  rcases hd₁₂ i with hl | hr
  · left; exact hl
  · rcases hd₁₂₃ i with h | h
    · left; exact (union_none_iff.mp h).1
    · right; exact union_none_iff.mpr ⟨hr, h⟩

-- From h₁⊥(h₂∪h₃) and h₂⊥h₃, derive (h₁∪h₂)⊥h₃
theorem disjoint_union_of_all {h₁ h₂ h₃ : HeapFrag}
    (hd₁₂₃ : h₁.disjoint (h₂.union h₃)) (hd₂₃ : h₂.disjoint h₃) :
    (h₁.union h₂).disjoint h₃ := by
  intro i
  rcases hd₁₂₃ i with hl | hr
  · rcases hd₂₃ i with hl2 | hr2
    · left; exact union_none_iff.mpr ⟨hl, hl2⟩
    · right; exact hr2
  · right; exact (union_none_iff.mp hr).2

end HeapFrag

/-! # WasmProp — separation logic propositions -/

def WasmProp := HeapFrag → Prop

/-! # Agreement between a heap fragment and a Wasm memory -/

def HeapFrag.agreesWith (h : HeapFrag) (m : Wasm.Mem) : Prop :=
  ∀ i, match h i with
    | some v => m.bytes i = v
    | none   => True
