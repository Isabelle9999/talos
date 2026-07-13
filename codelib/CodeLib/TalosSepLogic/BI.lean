import CodeLib.TalosSepLogic.Core

universe u

/-! # Talos BI — separation logic algebra on WasmProp (no iris-lean dependency) -/

namespace WasmProp

def entails (P Q : WasmProp) : Prop := ∀ h, P h → Q h

def emp : WasmProp := fun h => h = HeapFrag.empty

def pure (p : Prop) : WasmProp := fun _ => p

def sep (P Q : WasmProp) : WasmProp :=
  fun h => ∃ h₁ h₂, h₁.disjoint h₂ ∧ h = h₁.union h₂ ∧ P h₁ ∧ Q h₂

def wand (P Q : WasmProp) : WasmProp :=
  fun h => ∀ h', h.disjoint h' → P h' → Q (h.union h')

def forall_ {α : Type u} (Φ : α → WasmProp) : WasmProp := fun h => ∀ x, Φ x h

def exists_ {α : Type u} (Φ : α → WasmProp) : WasmProp := fun h => ∃ x, Φ x h

def and_ (P Q : WasmProp) : WasmProp := fun h => P h ∧ Q h

def or_ (P Q : WasmProp) : WasmProp := fun h => P h ∨ Q h

-- fupd as binary: P ==∗ Q means P entails the update of Q (trivial in this model)
def fupd (P Q : WasmProp) : WasmProp := P.wand Q

-- valid: P holds on all heaps (⊢ P in the BI sense)
def valid (P : WasmProp) : Prop := ∀ h, P h

end WasmProp

/-! ## Notation -/

namespace TalosSepLogic

scoped notation:25 P " ⊢ " Q => WasmProp.entails P Q
scoped infixr:35 " ∗ " => WasmProp.sep
scoped infixr:25 " -∗ " => WasmProp.wand
scoped notation "⌜" p "⌝" => WasmProp.pure p
scoped notation "emp" => WasmProp.emp
scoped notation:25 P " ==∗ " Q => WasmProp.fupd P Q
scoped macro "iprop% " t:term : term => `($t)

end TalosSepLogic

/-! ## BI laws (zero sorry) -/

namespace BI

open WasmProp HeapFrag

-- Reflexivity and transitivity of entailment
theorem entails_refl (P : WasmProp) : P.entails P := fun _ h => h

theorem entails_trans {P Q R : WasmProp} (hpq : P.entails Q) (hqr : Q.entails R) :
    P.entails R := fun h hp => hqr h (hpq h hp)

-- pure_intro: p → (P ⊢ ⌜p⌝)
theorem pure_intro {p : Prop} {P : WasmProp} (hp : p) : P.entails (WasmProp.pure p) :=
  fun _ _ => hp

-- pure_elim': (p → valid Q) → ⌜p⌝ ⊢ Q
theorem pure_elim' {p : Prop} {Q : WasmProp} (h : p → valid Q) :
    (WasmProp.pure p).entails Q :=
  fun hf hpf => h hpf hf

-- sep monotonicity
theorem sep_mono {P P' Q Q' : WasmProp} (hP : P.entails P') (hQ : Q.entails Q') :
    (P.sep Q).entails (P'.sep Q') := by
  rintro h ⟨h₁, h₂, hd, heq, hp, hq⟩
  exact ⟨h₁, h₂, hd, heq, hP h₁ hp, hQ h₂ hq⟩

theorem sep_mono_right {P Q Q' : WasmProp} (h : Q.entails Q') :
    (P.sep Q).entails (P.sep Q') :=
  sep_mono (entails_refl P) h

theorem sep_mono_left {P P' Q : WasmProp} (h : P.entails P') :
    (P.sep Q).entails (P'.sep Q) :=
  sep_mono h (entails_refl Q)

-- sep_congr_right
theorem sep_congr_right {P Q Q' : WasmProp} (h : Q.entails Q') :
    (P.sep Q).entails (P.sep Q') :=
  sep_mono_right h

-- sep_symm
theorem sep_symm {P Q : WasmProp} : (P.sep Q).entails (Q.sep P) := by
  rintro h ⟨h₁, h₂, hd, rfl, hp, hq⟩
  exact ⟨h₂, h₁, disjoint_comm.mp hd, union_comm hd, hq, hp⟩

-- sep_assoc: equality so .symm and direct rewriting both work
theorem sep_assoc {P Q R : WasmProp} :
    (P.sep Q).sep R = P.sep (Q.sep R) := by
  funext h; apply propext; constructor
  · rintro ⟨h₁₂, h₃, hd, rfl, ⟨h₁, h₂, hd₁₂, rfl, hp, hq⟩, hr⟩
    exact ⟨h₁, h₂.union h₃,
      disjoint_of_left_disjoint_union hd₁₂ hd,
      union_assoc h₁ h₂ h₃,
      hp,
      ⟨h₂, h₃, disjoint_of_union_disjoint_right hd₁₂ hd, rfl, hq, hr⟩⟩
  · rintro ⟨h₁, h₂₃, hd, rfl, hp, ⟨h₂, h₃, hd₂₃, rfl, hq, hr⟩⟩
    exact ⟨h₁.union h₂, h₃,
      disjoint_union_of_all hd hd₂₃,
      (union_assoc h₁ h₂ h₃).symm,
      ⟨h₁, h₂, disjoint_union_right hd, rfl, hp, hq⟩,
      hr⟩

-- sep_left_comm: P ∗ (Q ∗ R) ⊢ Q ∗ (P ∗ R)
theorem sep_left_comm {P Q R : WasmProp} :
    (P.sep (Q.sep R)).entails (Q.sep (P.sep R)) := by
  intro h hp
  rw [← sep_assoc] at hp
  have h2 := sep_mono_left sep_symm h hp
  rw [sep_assoc] at h2
  exact h2

-- emp is left unit of sep
theorem emp_sep {P : WasmProp} : WasmProp.emp.sep P = P := by
  funext h; apply propext; constructor
  · rintro ⟨h₁, h₂, _, rfl, rfl, hp⟩; rw [union_empty_left]; exact hp
  · intro hp
    exact ⟨HeapFrag.empty, h, disjoint_empty_left h, (union_empty_left h).symm, rfl, hp⟩

theorem emp_sep_symm {P : WasmProp} : P = WasmProp.emp.sep P := emp_sep.symm

-- emp is right unit of sep
theorem sep_emp {P : WasmProp} : P.sep WasmProp.emp = P := by
  funext h; apply propext; constructor
  · rintro ⟨h₁, h₂, _, rfl, hp, rfl⟩; rw [union_empty_right]; exact hp
  · intro hp
    exact ⟨h, HeapFrag.empty, disjoint_empty_right h, (union_empty_right h).symm, hp, rfl⟩

-- sep_elim_emp_valid_left: valid P → emp.sep P ⊢ P
theorem sep_elim_emp_valid_left {P : WasmProp} (_ : WasmProp.valid P) :
    (WasmProp.emp.sep P).entails P := emp_sep ▸ entails_refl P

-- wand_intro: (P ∗ Q ⊢ R) → Q ⊢ (P -∗ R)
theorem wand_intro {P Q R : WasmProp} (h : (P.sep Q).entails R) : Q.entails (P.wand R) := by
  intro hq hqv h' hd hp'
  apply h
  exact ⟨h', hq, disjoint_comm.mp hd, (union_comm (disjoint_comm.mp hd)).symm, hp', hqv⟩

-- wand_elim: (P -∗ Q) ∗ P ⊢ Q
theorem wand_elim {P Q : WasmProp} : ((P.wand Q).sep P).entails Q := by
  rintro _ ⟨h₁, h₂, hd, rfl, hw, hp⟩
  exact hw h₂ hd hp

theorem wand_elim_left {P Q : WasmProp} : ((P.wand Q).sep P).entails Q := wand_elim

-- wand_elim_right: P ∗ (P -∗ Q) ⊢ Q
theorem wand_elim_right {P Q : WasmProp} : (P.sep (P.wand Q)).entails Q := by
  rintro _ ⟨h₁, h₂, hd, rfl, hp, hw⟩
  rw [union_comm hd]
  exact hw h₁ (disjoint_comm.mp hd) hp

-- entails_wand: (P ⊢ Q) → emp ⊢ (P -∗ Q)
theorem entails_wand {P Q : WasmProp} (h : P.entails Q) :
    WasmProp.emp.entails (P.wand Q) := by
  intro hf hemp h' hd hph'
  have heq : hf.union h' = h' := by rw [hemp]; exact union_empty_left h'
  rw [heq]; exact h h' hph'

-- wand_entails: (emp ⊢ P -∗ Q) → P ⊢ Q
theorem wand_entails {P Q : WasmProp} (h : WasmProp.emp.entails (P.wand Q)) :
    P.entails Q := by
  intro hf hpf
  have hw := h HeapFrag.empty rfl hf (disjoint_empty_left hf) hpf
  rw [union_empty_left] at hw; exact hw

-- forall_intro: (∀ x, P ⊢ Φ x) → P ⊢ ∀ x, Φ x
theorem forall_intro {α : Type u} {P : WasmProp} {Φ : α → WasmProp}
    (h : ∀ x, P.entails (Φ x)) : P.entails (WasmProp.forall_ Φ) :=
  fun hf hp x => h x hf hp

-- forall_elim: (∀ x, Φ x) ⊢ Φ a
theorem forall_elim {α : Type u} {Φ : α → WasmProp} (a : α) :
    (WasmProp.forall_ Φ).entails (Φ a) :=
  fun _ h => h a

-- exists_intro: Φ a ⊢ ∃ x, Φ x
theorem exists_intro {α : Type u} {Φ : α → WasmProp} (a : α) :
    (Φ a).entails (WasmProp.exists_ Φ) :=
  fun _ h => ⟨a, h⟩

-- exists_elim: (∀ x, Φ x ⊢ Q) → (∃ x, Φ x) ⊢ Q
theorem exists_elim {α : Type u} {Φ : α → WasmProp} {Q : WasmProp}
    (h : ∀ x, (Φ x).entails Q) : (WasmProp.exists_ Φ).entails Q :=
  fun hf ⟨x, hx⟩ => h x hf hx

-- wand_frame_right: (P -∗ Q) ⊢ (P ∗ R) -∗ (Q ∗ R)
theorem wand_frame_right {P Q R : WasmProp} :
    (P.wand Q).entails ((P.sep R).wand (Q.sep R)) := by
  intro h hw h' hd hpr
  obtain ⟨hp, hr, hd', rfl, hhp, hhr⟩ := hpr
  -- hd : h.disjoint (hp.union hr)
  have hdhp : h.disjoint hp := disjoint_union_right hd
  have hq := hw hp hdhp hhp
  rw [← union_assoc]
  refine ⟨h.union hp, hr, ?_, rfl, hq, hhr⟩
  -- (h.union hp).disjoint hr
  intro i
  rcases hd i with hl | hr2
  · rcases hd' i with hl2 | hr3
    · left; exact union_none_iff.mpr ⟨hl, hl2⟩
    · right; exact hr3
  · right; exact (union_none_iff.mp hr2).2

-- wand_frame_left: (P -∗ Q) ⊢ (R ∗ P) -∗ (R ∗ Q)
-- derived from wand_frame_right via sep_symm
theorem wand_frame_left {P Q R : WasmProp} :
    (P.wand Q).entails ((R.sep P).wand (R.sep Q)) := by
  intro h hw h' hd hrp
  have hpr := sep_symm h' hrp
  have hqr := wand_frame_right h hw h' hd hpr
  exact sep_symm _ hqr

end BI
