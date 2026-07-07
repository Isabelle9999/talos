import CodeLib.RustStd.Frame
import Interpreter.Wasm

/-! # Memory framing lemmas for Wasm separation logic

`a` = write address throughout; `b` = read address.
Disjointness hypothesis: `a.toNat + size_a ≤ b.toNat ∨ b.toNat + size_b ≤ a.toNat`. -/

namespace Wasm.SepLogic

open Wasm

-- re-exports from CodeLib.RustStd.Frame

alias read32_write32_same := Mem.read32_write32_same
alias read64_write64_same := Mem.read64_write64_same
alias write32_pages := Mem.write32_pages
alias write64_pages := Mem.write64_pages

-- helpers

private theorem write64_bytes_ne (m : Mem) (a : UInt32) (v : UInt64) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 8 ≤ i) : (m.write64 a v).bytes i = m.bytes i := by
  simp only [Mem.write64]
  have h0 : i ≠ a.toNat := by omega
  have h1 : i ≠ a.toNat + 1 := by omega
  have h2 : i ≠ a.toNat + 2 := by omega
  have h3 : i ≠ a.toNat + 3 := by omega
  have h4 : i ≠ a.toNat + 4 := by omega
  have h5 : i ≠ a.toNat + 5 := by omega
  have h6 : i ≠ a.toNat + 6 := by omega
  have h7 : i ≠ a.toNat + 7 := by omega
  simp [h0, h1, h2, h3, h4, h5, h6, h7]

private theorem write32_bytes_ne (m : Mem) (a v : UInt32) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 4 ≤ i) : (m.write32 a v).bytes i = m.bytes i := by
  simp only [Mem.write32]
  have h0 : i ≠ a.toNat := by omega
  have h1 : i ≠ a.toNat + 1 := by omega
  have h2 : i ≠ a.toNat + 2 := by omega
  have h3 : i ≠ a.toNat + 3 := by omega
  simp [h0, h1, h2, h3]

-- ne lemmas: read after disjoint write is unchanged

theorem read64_write64_ne (m : Mem) (a b : UInt32) (v : UInt64)
    (h : a.toNat + 8 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat) :
    (m.write64 a v).read64 b = m.read64 b := by
  simp only [Mem.read64]
  rw [write64_bytes_ne m a v b.toNat (by omega),
      write64_bytes_ne m a v (b.toNat + 1) (by omega),
      write64_bytes_ne m a v (b.toNat + 2) (by omega),
      write64_bytes_ne m a v (b.toNat + 3) (by omega),
      write64_bytes_ne m a v (b.toNat + 4) (by omega),
      write64_bytes_ne m a v (b.toNat + 5) (by omega),
      write64_bytes_ne m a v (b.toNat + 6) (by omega),
      write64_bytes_ne m a v (b.toNat + 7) (by omega)]

theorem read32_write32_ne (m : Mem) (a b : UInt32) (v : UInt32)
    (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [write32_bytes_ne m a v b.toNat (by omega),
      write32_bytes_ne m a v (b.toNat + 1) (by omega),
      write32_bytes_ne m a v (b.toNat + 2) (by omega),
      write32_bytes_ne m a v (b.toNat + 3) (by omega)]

-- 32-bit write, 64-bit read: write [a, a+4), read [b, b+8)
theorem read64_write32_ne (m : Mem) (a b : UInt32) (v : UInt32)
    (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat) :
    (m.write32 a v).read64 b = m.read64 b := by
  simp only [Mem.read64]
  rw [write32_bytes_ne m a v b.toNat (by omega),
      write32_bytes_ne m a v (b.toNat + 1) (by omega),
      write32_bytes_ne m a v (b.toNat + 2) (by omega),
      write32_bytes_ne m a v (b.toNat + 3) (by omega),
      write32_bytes_ne m a v (b.toNat + 4) (by omega),
      write32_bytes_ne m a v (b.toNat + 5) (by omega),
      write32_bytes_ne m a v (b.toNat + 6) (by omega),
      write32_bytes_ne m a v (b.toNat + 7) (by omega)]

-- 64-bit write, 32-bit read: write [a, a+8), read [b, b+4)
theorem read32_write64_ne (m : Mem) (a b : UInt32) (v : UInt64)
    (h : a.toNat + 8 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    (m.write64 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [write64_bytes_ne m a v b.toNat (by omega),
      write64_bytes_ne m a v (b.toNat + 1) (by omega),
      write64_bytes_ne m a v (b.toNat + 2) (by omega),
      write64_bytes_ne m a v (b.toNat + 3) (by omega)]

-- comm lemmas: disjoint writes commute

private theorem mem_ext : ∀ {m1 m2 : Mem},
    m1.pages = m2.pages → m1.bytes = m2.bytes → m1 = m2
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

-- proof helper: partition i into three regions, simp away the cross-conditions
private def ne8 (a b : Nat) (k l : Nat) (hk : k < 8) (hl : l < 8)
    (h : a + 8 ≤ b ∨ b + 8 ≤ a) : a + k ≠ b + l := by rcases h with h | h <;> omega

theorem write64_write64_comm (m : Mem) (a b : UInt32) (va vb : UInt64)
    (h : a.toNat + 8 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat) :
    (m.write64 a va).write64 b vb = (m.write64 b vb).write64 a va :=
  mem_ext (by simp) (funext fun i => by
    simp only [Mem.write64]
    by_cases ha : ∃ k : Nat, k < 8 ∧ i = a.toNat + k
    · obtain ⟨k, hk, rfl⟩ := ha
      simp only [show a.toNat + k ≠ b.toNat     from ne8 _ _ k 0 hk (by omega) h,
                 show a.toNat + k ≠ b.toNat + 1 from ne8 _ _ k 1 hk (by omega) h,
                 show a.toNat + k ≠ b.toNat + 2 from ne8 _ _ k 2 hk (by omega) h,
                 show a.toNat + k ≠ b.toNat + 3 from ne8 _ _ k 3 hk (by omega) h,
                 show a.toNat + k ≠ b.toNat + 4 from ne8 _ _ k 4 hk (by omega) h,
                 show a.toNat + k ≠ b.toNat + 5 from ne8 _ _ k 5 hk (by omega) h,
                 show a.toNat + k ≠ b.toNat + 6 from ne8 _ _ k 6 hk (by omega) h,
                 show a.toNat + k ≠ b.toNat + 7 from ne8 _ _ k 7 hk (by omega) h,
                 ↓reduceIte]
    · by_cases hb : ∃ l : Nat, l < 8 ∧ i = b.toNat + l
      · obtain ⟨l, hl, rfl⟩ := hb
        simp only [show b.toNat + l ≠ a.toNat     from (ne8 _ _ 0 l (by omega) hl h).symm,
                   show b.toNat + l ≠ a.toNat + 1 from (ne8 _ _ 1 l (by omega) hl h).symm,
                   show b.toNat + l ≠ a.toNat + 2 from (ne8 _ _ 2 l (by omega) hl h).symm,
                   show b.toNat + l ≠ a.toNat + 3 from (ne8 _ _ 3 l (by omega) hl h).symm,
                   show b.toNat + l ≠ a.toNat + 4 from (ne8 _ _ 4 l (by omega) hl h).symm,
                   show b.toNat + l ≠ a.toNat + 5 from (ne8 _ _ 5 l (by omega) hl h).symm,
                   show b.toNat + l ≠ a.toNat + 6 from (ne8 _ _ 6 l (by omega) hl h).symm,
                   show b.toNat + l ≠ a.toNat + 7 from (ne8 _ _ 7 l (by omega) hl h).symm,
                   ↓reduceIte]
      · push Not at ha hb
        have h_ia : i < a.toNat ∨ a.toNat + 8 ≤ i := by
          by_contra hc; push Not at hc; exact ha (i - a.toNat) (by omega) (by omega)
        have h_ib : i < b.toNat ∨ b.toNat + 8 ≤ i := by
          by_contra hc; push Not at hc; exact hb (i - b.toNat) (by omega) (by omega)
        simp only [show i ≠ a.toNat     from by omega,
                   show i ≠ a.toNat + 1 from by omega,
                   show i ≠ a.toNat + 2 from by omega,
                   show i ≠ a.toNat + 3 from by omega,
                   show i ≠ a.toNat + 4 from by omega,
                   show i ≠ a.toNat + 5 from by omega,
                   show i ≠ a.toNat + 6 from by omega,
                   show i ≠ a.toNat + 7 from by omega,
                   show i ≠ b.toNat     from by omega,
                   show i ≠ b.toNat + 1 from by omega,
                   show i ≠ b.toNat + 2 from by omega,
                   show i ≠ b.toNat + 3 from by omega,
                   show i ≠ b.toNat + 4 from by omega,
                   show i ≠ b.toNat + 5 from by omega,
                   show i ≠ b.toNat + 6 from by omega,
                   show i ≠ b.toNat + 7 from by omega,
                   ↓reduceIte])

private def ne4 (a b : Nat) (k l : Nat) (hk : k < 4) (hl : l < 4)
    (h : a + 4 ≤ b ∨ b + 4 ≤ a) : a + k ≠ b + l := by rcases h with h | h <;> omega

theorem write32_write32_comm (m : Mem) (a b : UInt32) (va vb : UInt32)
    (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    (m.write32 a va).write32 b vb = (m.write32 b vb).write32 a va :=
  mem_ext (by simp) (funext fun i => by
    simp only [Mem.write32]
    by_cases ha : ∃ k : Nat, k < 4 ∧ i = a.toNat + k
    · obtain ⟨k, hk, rfl⟩ := ha
      simp only [show a.toNat + k ≠ b.toNat from ne4 _ _ k 0 hk (by omega) h,
                 show a.toNat + k ≠ b.toNat + 1 from ne4 _ _ k 1 hk (by omega) h,
                 show a.toNat + k ≠ b.toNat + 2 from ne4 _ _ k 2 hk (by omega) h,
                 show a.toNat + k ≠ b.toNat + 3 from ne4 _ _ k 3 hk (by omega) h,
                 ↓reduceIte]
    · by_cases hb : ∃ l : Nat, l < 4 ∧ i = b.toNat + l
      · obtain ⟨l, hl, rfl⟩ := hb
        simp only [show b.toNat + l ≠ a.toNat from (ne4 _ _ 0 l (by omega) hl h).symm,
                   show b.toNat + l ≠ a.toNat + 1 from (ne4 _ _ 1 l (by omega) hl h).symm,
                   show b.toNat + l ≠ a.toNat + 2 from (ne4 _ _ 2 l (by omega) hl h).symm,
                   show b.toNat + l ≠ a.toNat + 3 from (ne4 _ _ 3 l (by omega) hl h).symm,
                   ↓reduceIte]
      · push Not at ha hb
        have h_ia : i < a.toNat ∨ a.toNat + 4 ≤ i := by
          by_contra hc; push Not at hc; exact ha (i - a.toNat) (by omega) (by omega)
        have h_ib : i < b.toNat ∨ b.toNat + 4 ≤ i := by
          by_contra hc; push Not at hc; exact hb (i - b.toNat) (by omega) (by omega)
        simp only [show i ≠ a.toNat from by omega,
                   show i ≠ a.toNat + 1 from by omega,
                   show i ≠ a.toNat + 2 from by omega,
                   show i ≠ a.toNat + 3 from by omega,
                   show i ≠ b.toNat from by omega,
                   show i ≠ b.toNat + 1 from by omega,
                   show i ≠ b.toNat + 2 from by omega,
                   show i ≠ b.toNat + 3 from by omega,
                   ↓reduceIte])

end Wasm.SepLogic
