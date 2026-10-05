import Project.FloatMinmax.Program
import CodeLib.IEEE32.Exec
import CodeLib.Attrs

/-!
# Specification for `float_minmax`

`check_min`/`check_max` each run two accumulation loops (naive via `f32.lt`/`f32.gt`,
optimised via `f32.min`/`f32.max`) and return 1 iff their results are `f32.eq`.
On NaN-free inputs the two loops agree up to ±0 equivalence, so the check returns 1.
-/

namespace Project.FloatMinmax.Spec

open Wasm

/-! ## Reference functions -/

def naiveMin : List UInt32 → UInt32
  | []     => 0
  | x :: t => t.foldl (fun m y => if f32Lt y m then y else m) x

def optMin : List UInt32 → UInt32
  | []     => 0
  | x :: t => t.foldl f32Min x

def naiveMax : List UInt32 → UInt32
  | []     => 0
  | x :: t => t.foldl (fun m y => if f32Gt y m then y else m) x

def optMax : List UInt32 → UInt32
  | []     => 0
  | x :: t => t.foldl f32Max x

/-! ## Proof helpers -/

private theorem f32Eq_refl {a : UInt32} (ha : f32IsNaN a = false) : f32Eq a a = true := by
  simp only [f32Eq, IEEE754.eq, f32IsNaN, IEEE754.isNaN] at *
  simp [ha]

private theorem f32Eq_both_zero {m m' : UInt32}
    (hm : f32IsNaN m = false) (hm' : f32IsNaN m' = false)
    (hzm : IEEE754.isZero IEEE754.binary32 m.toNat = true)
    (hzm' : IEEE754.isZero IEEE754.binary32 m'.toNat = true) :
    f32Eq m m' = true := by
  simp only [f32Eq, IEEE754.eq, f32IsNaN, IEEE754.isNaN, IEEE754.isZero,
    show IEEE754.binary32.signBit = 2147483648 from rfl] at *
  simp [hm, hm', hzm, hzm']

/-! ### Invariant -/

private def Inv (m m' : UInt32) : Prop :=
  m.toNat = m'.toNat ∨
  (IEEE754.isZero IEEE754.binary32 m.toNat = true ∧
   IEEE754.isZero IEEE754.binary32 m'.toNat = true)

private theorem inv_refl (m : UInt32) : Inv m m := Or.inl rfl

private theorem inv_isNaN_right {m m' : UInt32}
    (hinv : Inv m m') (hm : f32IsNaN m = false) : f32IsNaN m' = false := by
  rcases hinv with heq | ⟨_, hzm'⟩
  · simp only [f32IsNaN, IEEE754.isNaN] at *; rw [show m'.toNat = m.toNat from heq.symm]; exact hm
  · simp only [f32IsNaN, IEEE754.isNaN, IEEE754.isZero,
      show IEEE754.binary32.signBit = 2147483648 from rfl] at *
    have hlt := m'.toNat_lt
    have hval : m'.toNat = 0 ∨ m'.toNat = 2147483648 := by simp [beq_iff_eq] at hzm'; omega
    rcases hval with hv | hv <;> (rw [hv]; decide +kernel)

private theorem inv_to_f32Eq {m m' : UInt32}
    (hinv : Inv m m') (hm : f32IsNaN m = false) : f32Eq m m' = true := by
  rcases hinv with heq | ⟨hzm, hzm'⟩
  · rw [show m' = m from UInt32.toNat_inj.mp heq.symm]
    exact f32Eq_refl hm
  · exact f32Eq_both_zero hm (inv_isNaN_right (Or.inr ⟨hzm, hzm'⟩) hm) hzm hzm'

/-! ### Order lemmas for IEEE754.lt -/

-- Uses 4294967296 (not 2^32) so omega can reason about the modulus
private theorem uint32_toNat_ofNat (n : Nat) : n.toUInt32.toNat = n % 4294967296 := by
  have h := @UInt32.toNat_ofNat' n
  simp only [show (2 : Nat) ^ 32 = 4294967296 from by decide] at h; exact h

private theorem f32Lt_antisymm' {a b : UInt32}
    (ha : f32IsNaN a = false) (hb : f32IsNaN b = false)
    (h : f32Lt a b = true) : f32Lt b a = false := by
  have ha_lt : a.toNat < 4294967296 := by have := a.toNat_lt; simp [UInt32.size] at this; exact this
  have hb_lt : b.toNat < 4294967296 := by have := b.toNat_lt; simp [UInt32.size] at this; exact this
  simp only [f32Lt, IEEE754.lt, f32IsNaN, IEEE754.isNaN, IEEE754.isZero,
    show IEEE754.binary32.signBit = 2147483648 from rfl] at *
  simp only [ha, hb, Bool.false_or, Bool.or_false] at *
  split_ifs at h ⊢ <;> simp_all <;> omega

-- If neither lt holds for non-NaN inputs, values are equal or both zeros.
private theorem f32Lt_total_or_zero' {a b : UInt32}
    (ha : f32IsNaN a = false) (hb : f32IsNaN b = false)
    (hab : f32Lt a b = false) (hba : f32Lt b a = false) :
    a.toNat = b.toNat ∨
    (IEEE754.isZero IEEE754.binary32 a.toNat = true ∧
     IEEE754.isZero IEEE754.binary32 b.toNat = true) := by
  have ha_lt : a.toNat < 4294967296 := by have := a.toNat_lt; omega
  have hb_lt : b.toNat < 4294967296 := by have := b.toNat_lt; omega
  simp only [f32IsNaN] at ha hb
  simp only [f32Lt, IEEE754.lt, IEEE754.isZero,
    show IEEE754.binary32.signBit = 2147483648 from rfl, ha, hb,
    Bool.false_or, Bool.or_false] at hab hba
  -- split_ifs eliminates each Bool if-condition directly, avoiding if(false:Bool) issues.
  split_ifs at hab hba <;>
    simp_all [beq_iff_eq, decide_eq_true_eq, decide_eq_false_iff_not, not_le, not_lt] <;>
    first
      | exact Or.inl (by omega)
      | (right
         simp only [IEEE754.isZero, show IEEE754.binary32.signBit = 2147483648 from rfl, beq_iff_eq]
         constructor <;> omega)
      | omega

/-! ### Min/max step helpers -/

-- Helper for the both-zero OR case
private theorem bitor_mod_sb (m y : Nat)
    (hm : m % 2147483648 = 0) (hy : y % 2147483648 = 0)
    (hmlt : m < 4294967296) (hylt : y < 4294967296) :
    (m ||| y) % 2147483648 = 0 ∧ (m ||| y) < 4294967296 := by
  have hm_val : m = 0 ∨ m = 2147483648 := by omega
  have hy_val : y = 0 ∨ y = 2147483648 := by omega
  rcases hm_val with rfl | rfl <;> rcases hy_val with rfl | rfl <;> decide +kernel

-- Helper for the both-zero AND case
private theorem bitand_mod_sb (m y : Nat)
    (hm : m % 2147483648 = 0) (hy : y % 2147483648 = 0)
    (hmlt : m < 4294967296) (hylt : y < 4294967296) :
    (m &&& y) % 2147483648 = 0 ∧ (m &&& y) < 4294967296 := by
  have hm_val : m = 0 ∨ m = 2147483648 := by omega
  have hy_val : y = 0 ∨ y = 2147483648 := by omega
  rcases hm_val with rfl | rfl <;> rcases hy_val with rfl | rfl <;> decide +kernel

-- isZero of bitor of two zeros is a zero
private theorem isZero_bitor {m y : UInt32}
    (hzm : IEEE754.isZero IEEE754.binary32 m.toNat = true)
    (hzy : IEEE754.isZero IEEE754.binary32 y.toNat = true) :
    IEEE754.isZero IEEE754.binary32 (m.toNat ||| y.toNat).toUInt32.toNat = true := by
  simp only [IEEE754.isZero, show IEEE754.binary32.signBit = 2147483648 from rfl, beq_iff_eq] at *
  have hm_lt : m.toNat < 4294967296 := by have := m.toNat_lt; simp [UInt32.size] at this; exact this
  have hy_lt : y.toNat < 4294967296 := by have := y.toNat_lt; simp [UInt32.size] at this; exact this
  have ⟨hb, hbl⟩ := bitor_mod_sb m.toNat y.toNat hzm hzy hm_lt hy_lt
  rw [uint32_toNat_ofNat]; omega

-- isZero of bitand of two zeros is a zero
private theorem isZero_bitand {m y : UInt32}
    (hzm : IEEE754.isZero IEEE754.binary32 m.toNat = true)
    (hzy : IEEE754.isZero IEEE754.binary32 y.toNat = true) :
    IEEE754.isZero IEEE754.binary32 (m.toNat &&& y.toNat).toUInt32.toNat = true := by
  simp only [IEEE754.isZero, show IEEE754.binary32.signBit = 2147483648 from rfl, beq_iff_eq] at *
  have hm_lt : m.toNat < 4294967296 := by have := m.toNat_lt; simp [UInt32.size] at this; exact this
  have hy_lt : y.toNat < 4294967296 := by have := y.toNat_lt; simp [UInt32.size] at this; exact this
  have ⟨hb, hbl⟩ := bitand_mod_sb m.toNat y.toNat hzm hzy hm_lt hy_lt
  rw [uint32_toNat_ofNat]; omega

-- When not both zero and not NaN: f32Min m y = if f32Lt m y then m else y
private theorem f32Min_not_bz (m y : UInt32)
    (hm : f32IsNaN m = false) (hy : f32IsNaN y = false)
    (hnz : ¬(IEEE754.isZero IEEE754.binary32 m.toNat = true ∧
             IEEE754.isZero IEEE754.binary32 y.toNat = true)) :
    f32Min m y = if f32Lt m y then m else y := by
  have hbz : (IEEE754.isZero IEEE754.binary32 m.toNat &&
              IEEE754.isZero IEEE754.binary32 y.toNat) = false := by
    rcases Bool.eq_false_or_eq_true (IEEE754.isZero IEEE754.binary32 m.toNat) with hm2 | hm2 <;>
    rcases Bool.eq_false_or_eq_true (IEEE754.isZero IEEE754.binary32 y.toNat) with hy2 | hy2 <;>
    simp_all
  simp only [f32IsNaN] at hm hy
  simp only [f32Min, IEEE754.minimum, f32Lt, IEEE754.lt, hm, hy,
    Bool.false_or, Bool.or_false, hbz, Bool.false_eq_true, if_false]
  split_ifs <;> exact UInt32.ofNat_toNat

-- When not both zero and not NaN: f32Max m y = if f32Lt m y then y else m
-- (f32Gt y m = f32Lt m y, so naive max step equals f32Max directly)
private theorem f32Max_not_bz (m y : UInt32)
    (hm : f32IsNaN m = false) (hy : f32IsNaN y = false)
    (hnz : ¬(IEEE754.isZero IEEE754.binary32 m.toNat = true ∧
             IEEE754.isZero IEEE754.binary32 y.toNat = true)) :
    f32Max m y = if f32Lt m y then y else m := by
  have hbz : (IEEE754.isZero IEEE754.binary32 m.toNat &&
              IEEE754.isZero IEEE754.binary32 y.toNat) = false := by
    rcases Bool.eq_false_or_eq_true (IEEE754.isZero IEEE754.binary32 m.toNat) with hm2 | hm2 <;>
    rcases Bool.eq_false_or_eq_true (IEEE754.isZero IEEE754.binary32 y.toNat) with hy2 | hy2 <;>
    simp_all
  simp only [f32IsNaN] at hm hy
  simp only [f32Max, IEEE754.maximum, f32Lt, IEEE754.lt, hm, hy,
    Bool.false_or, Bool.or_false, hbz, Bool.false_eq_true, if_false]
  split_ifs <;> exact UInt32.ofNat_toNat

-- When both zero: f32Lt = false
private theorem f32Lt_bz_false (m y : UInt32)
    (hm : f32IsNaN m = false) (hy : f32IsNaN y = false)
    (hzm : IEEE754.isZero IEEE754.binary32 m.toNat = true)
    (hzy : IEEE754.isZero IEEE754.binary32 y.toNat = true) :
    f32Lt y m = false := by
  simp only [f32IsNaN] at hm hy
  simp only [f32Lt, IEEE754.lt, hm, hy, Bool.false_or, Bool.or_false]
  simp [hzm, hzy]

-- f32Lt m y = f32Lt m' y when m, m' are both zeros and y is not a zero
private theorem f32Lt_zeros_same_right (m m' y : UInt32)
    (hm : f32IsNaN m = false) (hm' : f32IsNaN m' = false) (hy : f32IsNaN y = false)
    (hzm : IEEE754.isZero IEEE754.binary32 m.toNat = true)
    (hzm' : IEEE754.isZero IEEE754.binary32 m'.toNat = true)
    (hzy : IEEE754.isZero IEEE754.binary32 y.toNat = false) :
    f32Lt m y = f32Lt m' y := by
  simp only [f32IsNaN] at hm hm' hy
  simp only [IEEE754.isZero, show IEEE754.binary32.signBit = 2147483648 from rfl,
    beq_iff_eq] at hzm hzm'
  have hzy_n : y.toNat % 2147483648 ≠ 0 := fun h => by
    simp [IEEE754.isZero, show IEEE754.binary32.signBit = 2147483648 from rfl, h] at hzy
  have hm_lt  : m.toNat  < 4294967296 := by have := m.toNat_lt; simp [UInt32.size] at this; exact this
  have hm'_lt : m'.toNat < 4294967296 := by have := m'.toNat_lt; simp [UInt32.size] at this; exact this
  have hm_val  : m.toNat  = 0 ∨ m.toNat  = 2147483648 := by omega
  have hm'_val : m'.toNat = 0 ∨ m'.toNat = 2147483648 := by omega
  simp only [f32Lt, IEEE754.lt, hm, hm', hy, Bool.false_or, Bool.or_false,
    IEEE754.isZero, show IEEE754.binary32.signBit = 2147483648 from rfl]
  rcases hm_val with hm_val | hm_val <;> rcases hm'_val with hm'_val | hm'_val <;>
    simp only [hm_val, hm'_val] <;>
    split_ifs <;> simp_all [beq_iff_eq, decide_eq_true_eq, not_le, not_lt] <;> omega

-- f32Lt m y = !f32Lt y m when m is a zero and y is not
private theorem f32Lt_zero_nonzero_bne (m y : UInt32)
    (hm : f32IsNaN m = false) (hy : f32IsNaN y = false)
    (hzm : IEEE754.isZero IEEE754.binary32 m.toNat = true)
    (hzy : IEEE754.isZero IEEE754.binary32 y.toNat = false) :
    f32Lt m y = !f32Lt y m := by
  simp only [f32IsNaN] at hm hy
  simp only [IEEE754.isZero, show IEEE754.binary32.signBit = 2147483648 from rfl,
    beq_iff_eq] at hzm
  have hzy_n : y.toNat % 2147483648 ≠ 0 := fun h => by
    simp [IEEE754.isZero, show IEEE754.binary32.signBit = 2147483648 from rfl, h] at hzy
  by_cases h : f32Lt m y = true
  · rw [h, show f32Lt y m = false from f32Lt_antisymm' hm hy h]; rfl
  · have hf : f32Lt m y = false := Bool.eq_false_of_not_eq_true h
    rw [hf]
    by_cases h' : f32Lt y m = true
    · rw [h']; rfl
    · exfalso
      have hf' : f32Lt y m = false := Bool.eq_false_of_not_eq_true h'
      rcases f32Lt_total_or_zero' hm hy hf hf' with heq | ⟨_, hzy_t⟩
      · rw [heq] at hzm; exact hzy_n hzm
      · exact absurd hzy_t (hzy.symm ▸ Bool.false_ne_true)

/-! ### Min step invariant -/

private theorem inv_step_min_same (m y : UInt32)
    (hm : f32IsNaN m = false) (hy : f32IsNaN y = false) :
    Inv (if f32Lt y m then y else m) (f32Min m y) := by
  by_cases h_bz : IEEE754.isZero IEEE754.binary32 m.toNat = true ∧
                  IEEE754.isZero IEEE754.binary32 y.toNat = true
  · -- Both zeros: f32Lt y m = false, f32Min = bitor
    obtain ⟨hzm, hzy⟩ := h_bz
    rw [if_neg ((f32Lt_bz_false m y hm hy hzm hzy).symm ▸ Bool.false_ne_true)]
    simp only [f32IsNaN] at hm hy
    simp only [f32Min, IEEE754.minimum, hm, hy,
      Bool.false_or, Bool.or_false, hzm, hzy, Bool.and_self, ↓reduceIte]
    exact Or.inr ⟨hzm, isZero_bitor hzm hzy⟩
  · -- Not both zeros: f32Min m y = if f32Lt m y then m else y
    rw [f32Min_not_bz m y hm hy h_bz]
    by_cases h_lt : f32Lt y m = true
    · -- y < m: LHS = y. f32Lt m y = false by antisymm. RHS = y.
      rw [if_pos h_lt, if_neg ((f32Lt_antisymm' hy hm h_lt).symm ▸ Bool.false_ne_true)]
      exact inv_refl y
    · -- ¬(y < m): LHS = m.
      rw [if_neg h_lt]
      by_cases h_lt2 : f32Lt m y = true
      · -- m < y: RHS = m. Done.
        rw [if_pos h_lt2]; exact inv_refl m
      · -- Neither: totality → equal or both-zero; both-zero excluded.
        rw [if_neg h_lt2]
        have hf1 : f32Lt m y = false := Bool.eq_false_of_not_eq_true h_lt2
        have hf2 : f32Lt y m = false := Bool.eq_false_of_not_eq_true h_lt
        rcases f32Lt_total_or_zero' hm hy hf1 hf2 with heq | hbz
        · exact Or.inl heq
        · exact absurd hbz h_bz

private theorem inv_step_min (m m' y : UInt32)
    (hinv : Inv m m') (hm : f32IsNaN m = false) (hy : f32IsNaN y = false) :
    Inv (if f32Lt y m then y else m) (f32Min m' y) := by
  have hm' : f32IsNaN m' = false := inv_isNaN_right hinv hm
  rcases hinv with heq | ⟨hzm, hzm'⟩
  · -- m.toNat = m'.toNat
    convert inv_step_min_same m y hm hy using 2
    congr 1; exact UInt32.toNat_inj.mp heq.symm
  · -- Both m and m' are zeros. Split on whether y is also a zero.
    by_cases hzy : IEEE754.isZero IEEE754.binary32 y.toNat = true
    · -- y is also a zero: f32Lt y m = false, f32Min m' y = (m' ||| y).toUInt32
      rw [if_neg ((f32Lt_bz_false m y hm hy hzm hzy).symm ▸ Bool.false_ne_true)]
      simp only [f32IsNaN] at hm' hy
      simp only [f32Min, IEEE754.minimum, hm', hy,
        Bool.false_or, Bool.or_false, hzm', hzy, Bool.and_self, ↓reduceIte]
      exact Or.inr ⟨hzm, isZero_bitor hzm' hzy⟩
    · -- y is not a zero: f32Min m' y = if f32Lt m' y then m' else y
      have hzy_f : IEEE754.isZero IEEE754.binary32 y.toNat = false :=
        Bool.eq_false_of_not_eq_true hzy
      rw [f32Min_not_bz m' y hm' hy (fun ⟨_, hzy_t⟩ => absurd hzy_t (hzy_f.symm ▸ Bool.false_ne_true))]
      have hlt_eq : f32Lt m y = f32Lt m' y :=
        f32Lt_zeros_same_right m m' y hm hm' hy hzm hzm' hzy_f
      have hlt_bne : f32Lt m y = !f32Lt y m :=
        f32Lt_zero_nonzero_bne m y hm hy hzm hzy_f
      by_cases h : f32Lt y m = true
      · rw [if_pos h]
        have hm'y : f32Lt m' y = false := by rw [← hlt_eq, hlt_bne, h]; rfl
        rw [if_neg (hm'y.symm ▸ Bool.false_ne_true)]
        exact inv_refl y
      · have hf : f32Lt y m = false := Bool.eq_false_of_not_eq_true h
        rw [if_neg (hf.symm ▸ Bool.false_ne_true)]
        have hm'y : f32Lt m' y = true := by rw [← hlt_eq, hlt_bne, hf]; rfl
        rw [if_pos hm'y]
        exact Or.inr ⟨hzm, hzm'⟩

/-! ### Max step invariant -/

-- f32Gt y m = f32Lt m y; IEEE754.maximum m y = if f32Lt m y then y else m (not both zero).
-- So naive and opt max steps are identical in the non-both-zero case.
private theorem inv_step_max_same (m y : UInt32)
    (hm : f32IsNaN m = false) (hy : f32IsNaN y = false) :
    Inv (if f32Gt y m then y else m) (f32Max m y) := by
  simp only [f32Gt]  -- f32Gt y m = f32Lt m y
  by_cases h_bz : IEEE754.isZero IEEE754.binary32 m.toNat = true ∧
                  IEEE754.isZero IEEE754.binary32 y.toNat = true
  · -- Both zeros: f32Lt m y = false, f32Max = bitand
    obtain ⟨hzm, hzy⟩ := h_bz
    have h_lt : f32Lt m y = false := f32Lt_bz_false y m hy hm hzy hzm
    simp only [f32Lt] at h_lt
    rw [if_neg (h_lt.symm ▸ Bool.false_ne_true)]
    simp only [f32IsNaN] at hm hy
    simp only [f32Max, IEEE754.maximum, hm, hy,
      Bool.false_or, Bool.or_false, hzm, hzy, Bool.and_self, ↓reduceIte]
    exact Or.inr ⟨hzm, isZero_bitand hzm hzy⟩
  · -- Not both zeros: f32Max m y = if f32Lt m y then y else m = LHS. Done.
    rw [f32Max_not_bz m y hm hy h_bz]
    exact inv_refl _

private theorem inv_step_max (m m' y : UInt32)
    (hinv : Inv m m') (hm : f32IsNaN m = false) (hy : f32IsNaN y = false) :
    Inv (if f32Gt y m then y else m) (f32Max m' y) := by
  have hm' : f32IsNaN m' = false := inv_isNaN_right hinv hm
  rw [show f32Gt y m = f32Lt m y from rfl]
  rcases hinv with heq | ⟨hzm, hzm'⟩
  · have hm'_eq : m = m' := UInt32.toNat_inj.mp heq
    rw [← hm'_eq]; exact inv_step_max_same m y hm hy
  · -- Both m and m' are zeros. Split on whether y is also a zero.
    by_cases hzy : IEEE754.isZero IEEE754.binary32 y.toNat = true
    · -- y is also a zero: f32Lt m y = false, f32Max m' y = (m' &&& y).toUInt32
      have h_lt : f32Lt m y = false := f32Lt_bz_false y m hy hm hzy hzm
      rw [if_neg (h_lt.symm ▸ Bool.false_ne_true)]
      simp only [f32IsNaN] at hm' hy
      simp only [f32Max, IEEE754.maximum, hm', hy,
        Bool.false_or, Bool.or_false, hzm', hzy, Bool.and_self, ↓reduceIte]
      exact Or.inr ⟨hzm, isZero_bitand hzm' hzy⟩
    · -- y is not a zero: f32Max m' y = if f32Lt m' y then y else m'
      have hzy_f : IEEE754.isZero IEEE754.binary32 y.toNat = false :=
        Bool.eq_false_of_not_eq_true hzy
      rw [f32Max_not_bz m' y hm' hy (fun ⟨_, hzy_t⟩ => absurd hzy_t (hzy_f.symm ▸ Bool.false_ne_true))]
      have hlt_eq : f32Lt m y = f32Lt m' y :=
        f32Lt_zeros_same_right m m' y hm hm' hy hzm hzm' hzy_f
      by_cases h : f32Lt m y = true
      · rw [if_pos h, if_pos (hlt_eq ▸ h)]
        exact inv_refl y
      · have hf : f32Lt m y = false := Bool.eq_false_of_not_eq_true h
        rw [if_neg (hf.symm ▸ Bool.false_ne_true),
            if_neg ((hlt_eq ▸ hf).symm ▸ Bool.false_ne_true)]
        exact Or.inr ⟨hzm, hzm'⟩

/-! ### NaN-free foldl -/

private theorem naiveMin_nan_free (m : UInt32) (xs : List UInt32)
    (hm : f32IsNaN m = false) (hxs : ∀ y ∈ xs, f32IsNaN y = false) :
    f32IsNaN (xs.foldl (fun m y => if f32Lt y m then y else m) m) = false := by
  induction xs generalizing m with
  | nil => exact hm
  | cons y ys ih =>
    simp only [List.foldl_cons]; apply ih
    · split_ifs with h
      · exact hxs y List.mem_cons_self
      · exact hm
    · intro z hz; exact hxs z (List.mem_cons_of_mem _ hz)

private theorem naiveMax_nan_free (m : UInt32) (xs : List UInt32)
    (hm : f32IsNaN m = false) (hxs : ∀ y ∈ xs, f32IsNaN y = false) :
    f32IsNaN (xs.foldl (fun m y => if f32Gt y m then y else m) m) = false := by
  induction xs generalizing m with
  | nil => exact hm
  | cons y ys ih =>
    simp only [List.foldl_cons]; apply ih
    · split_ifs with h
      · exact hxs y List.mem_cons_self
      · exact hm
    · intro z hz; exact hxs z (List.mem_cons_of_mem _ hz)

private theorem foldl_min_inv (xs : List UInt32) (m m' : UInt32)
    (hinv : Inv m m') (hm : f32IsNaN m = false) (hm' : f32IsNaN m' = false)
    (hxs : ∀ y ∈ xs, f32IsNaN y = false) :
    Inv (xs.foldl (fun m y => if f32Lt y m then y else m) m) (xs.foldl f32Min m') := by
  induction xs generalizing m m' with
  | nil => exact hinv
  | cons y ys ih =>
    simp only [List.foldl_cons]
    have hy := hxs y List.mem_cons_self
    have hstep := inv_step_min m m' y hinv hm hy
    apply ih _ _ hstep
    · split_ifs with h
      · exact hy
      · exact hm
    · exact inv_isNaN_right hstep (by split_ifs with h <;> [exact hy; exact hm])
    · intro z hz; exact hxs z (List.mem_cons_of_mem _ hz)

private theorem foldl_max_inv (xs : List UInt32) (m m' : UInt32)
    (hinv : Inv m m') (hm : f32IsNaN m = false) (hm' : f32IsNaN m' = false)
    (hxs : ∀ y ∈ xs, f32IsNaN y = false) :
    Inv (xs.foldl (fun m y => if f32Gt y m then y else m) m) (xs.foldl f32Max m') := by
  induction xs generalizing m m' with
  | nil => exact hinv
  | cons y ys ih =>
    simp only [List.foldl_cons]
    have hy := hxs y List.mem_cons_self
    have hstep := inv_step_max m m' y hinv hm hy
    apply ih _ _ hstep
    · split_ifs with h
      · exact hy
      · exact hm
    · exact inv_isNaN_right hstep (by split_ifs with h <;> [exact hy; exact hm])
    · intro z hz; exact hxs z (List.mem_cons_of_mem _ hz)

/-! ## Public equivalence theorems -/

theorem naiveMin_eq_optMin (xs : List UInt32)
    (hxs : ∀ x ∈ xs, f32IsNaN x = false) :
    f32Eq (naiveMin xs) (optMin xs) = true := by
  cases xs with
  | nil => decide +kernel
  | cons x rest =>
    simp only [naiveMin, optMin]
    have hx := hxs x List.mem_cons_self
    have hrest : ∀ y ∈ rest, f32IsNaN y = false :=
      fun y hy => hxs y (List.mem_cons_of_mem x hy)
    exact inv_to_f32Eq (foldl_min_inv rest x x (inv_refl x) hx hx hrest)
      (naiveMin_nan_free x rest hx hrest)

theorem naiveMax_eq_optMax (xs : List UInt32)
    (hxs : ∀ x ∈ xs, f32IsNaN x = false) :
    f32Eq (naiveMax xs) (optMax xs) = true := by
  cases xs with
  | nil => decide +kernel
  | cons x rest =>
    simp only [naiveMax, optMax]
    have hx := hxs x List.mem_cons_self
    have hrest : ∀ y ∈ rest, f32IsNaN y = false :=
      fun y hy => hxs y (List.mem_cons_of_mem x hy)
    exact inv_to_f32Eq (foldl_max_inv rest x x (inv_refl x) hx hx hrest)
      (naiveMax_nan_free x rest hx hrest)

end Project.FloatMinmax.Spec
