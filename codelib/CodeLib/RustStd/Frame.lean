import Interpreter.Wasm

/-!
# `CodeLib.RustStd.Frame`

Foundational reasoning helpers for Rust functions compiled to wasm at
`opt-level = 0` (the corpus convention; see `programs/rust/Cargo.toml`).

At `-O0`, LLVM gives every function a stack frame and **spills results
through linear memory** before returning them. So *every* opt-0 spec proof
pushes a value through a `store`/`load` round-trip and has to show the
frame access stays in bounds. The lemmas here discharge that once, in a
form that does not care about the concrete spill address:

* `Mem.read{32,64}_write{32,64}_same` — read-after-write at the same
  address returns the value (no bound on the address needed).
* `Mem.write{32,64}_pages` — a store leaves the page count unchanged.

The in-bounds (no-trap) obligation also needs `sp - 16` not to underflow;
that is `UInt32.toNat_sub_of_le`, which Lean core already provides
(`Init.Data.UInt.Lemmas`), so it is used directly rather than re-proved here.

The four `Mem.*` lemmas are intentionally global `@[simp]` — confluent,
terminating rewrites used corpus-wide. Op-specific lemmas (e.g. `popcnt`
bounds) are added here only once a real proof first consumes them.
-/

namespace Wasm

/-! ## Store/load round-trips -/

/-- Reading a 32-bit word back from the address it was just written to
returns the stored value. -/
@[simp] theorem Mem.read32_write32_same (m : Mem) (a v : UInt32) :
    (m.write32 a v).read32 a = v := by
  simp only [Mem.read32, Mem.write32]
  have e1 : a.toNat + 1 ≠ a.toNat := by omega
  have e2 : a.toNat + 2 ≠ a.toNat := by omega
  have e3 : a.toNat + 3 ≠ a.toNat := by omega
  have e21 : a.toNat + 2 ≠ a.toNat + 1 := by omega
  have e31 : a.toNat + 3 ≠ a.toNat + 1 := by omega
  have e32 : a.toNat + 3 ≠ a.toNat + 2 := by omega
  simp only [e1, e2, e3, e21, e31, e32, ↓reduceIte]
  apply UInt32.ext
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toUInt32_toNat]
  have byte_of (x : UInt32) : x.toUInt8.toNat = x.toNat % 256 := by
    simp only [UInt32.toUInt8]
    simp [Nat.toUInt8, UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat,
          show (2:Nat)^8 = 256 from rfl]
  simp only [byte_of, UInt32.toNat_and, UInt32.toNat_shiftRight,
             show (255 : UInt32).toNat = 255 from rfl,
             show (8 : UInt32).toNat = 8 from rfl,
             show (16 : UInt32).toNat = 16 from rfl,
             show (24 : UInt32).toNat = 24 from rfl]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow,
             Nat.testBit_and, show (256 : Nat) = 2^8 from rfl,
             show (255 : Nat) = 2^8 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  have hv : v.toNat < 2^32 := v.toNat_lt
  have hfar : i ≥ 32 → v.toNat.testBit i = false :=
    fun hi => Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (@Nat.pow_le_pow_right 2 (by decide) 32 i hi))
  rcases Nat.lt_or_ge i 8 with h | h
  · simp [show i < 8 from h, show i < 32 from by omega,
           show ¬ i ≥ 8 from by omega, show ¬ i ≥ 16 from by omega, show ¬ i ≥ 24 from by omega]
  rcases Nat.lt_or_ge i 16 with h2 | h2
  · have heq : 8 + (i - 8) = i := Nat.add_sub_cancel' h
    simp [heq, show i < 32 from by omega, show i ≥ 8 from h,
          show i - 8 < 8 from by omega, show ¬ i ≥ 16 from by omega, show ¬ i ≥ 24 from by omega]
  rcases Nat.lt_or_ge i 24 with h3 | h3
  · have heq : 16 + (i - 16) = i := Nat.add_sub_cancel' h2
    simp [heq, show i < 32 from by omega, show i ≥ 8 from h, show i ≥ 16 from h2,
          show i - 16 < 8 from by omega, show ¬ i - 8 < 8 from by omega,
          show ¬ i ≥ 24 from by omega, show ¬ i < 8 from by omega]
  rcases Nat.lt_or_ge i 32 with h4 | h4
  · have heq : 24 + (i - 24) = i := Nat.add_sub_cancel' h3
    simp [heq, show i < 32 from by omega, show i ≥ 8 from h, show i ≥ 16 from h2,
          show i ≥ 24 from h3, show i - 24 < 8 from by omega,
          show ¬ i - 8 < 8 from by omega, show ¬ i - 16 < 8 from by omega,
          show ¬ i < 8 from by omega]
  · simp [hfar h4, show ¬ i < 32 from by omega]

/-- Reading a 64-bit word back from the address it was just written to
returns the stored value. -/
@[simp] theorem Mem.read64_write64_same (m : Mem) (a : UInt32) (v : UInt64) :
    (m.write64 a v).read64 a = v := by
  simp only [Mem.read64, Mem.write64]
  simp only [Nat.add_eq_left, OfNat.ofNat_ne_zero, Nat.succ_ne_self, ↓reduceIte,
             Nat.reduceEqDiff]
  apply UInt64.ext
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toUInt64_toNat]
  have byte_of (x : UInt64) : x.toUInt8.toNat = x.toNat % 256 := by
    simp only [UInt64.toUInt8]
    simp [Nat.toUInt8, UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat,
          show (2:Nat)^8 = 256 from rfl]
  simp only [byte_of, UInt64.toNat_and, UInt64.toNat_shiftRight,
             show (255 : UInt64).toNat = 255 from rfl,
             show (8 : UInt64).toNat = 8 from rfl,
             show (16 : UInt64).toNat = 16 from rfl,
             show (24 : UInt64).toNat = 24 from rfl,
             show (32 : UInt64).toNat = 32 from rfl,
             show (40 : UInt64).toNat = 40 from rfl,
             show (48 : UInt64).toNat = 48 from rfl,
             show (56 : UInt64).toNat = 56 from rfl]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow,
             Nat.testBit_and, show (256 : Nat) = 2^8 from rfl,
             show (255 : Nat) = 2^8 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  have hv : v.toNat < 2^64 := v.toNat_lt
  have hfar : i ≥ 64 → v.toNat.testBit i = false :=
    fun hi => Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (@Nat.pow_le_pow_right 2 (by decide) 64 i hi))
  rcases Nat.lt_or_ge i 8 with h | h
  · simp [show i < 8 from h, show i < 64 from by omega,
           show ¬ i ≥ 8 from by omega, show ¬ i ≥ 16 from by omega,
           show ¬ i ≥ 24 from by omega, show ¬ i ≥ 32 from by omega,
           show ¬ i ≥ 40 from by omega, show ¬ i ≥ 48 from by omega, show ¬ i ≥ 56 from by omega]
  rcases Nat.lt_or_ge i 16 with h2 | h2
  · have heq : 8 + (i - 8) = i := Nat.add_sub_cancel' h
    simp [heq, show i < 64 from by omega, show i ≥ 8 from h, show i - 8 < 8 from by omega,
          show ¬ i ≥ 16 from by omega, show ¬ i ≥ 24 from by omega,
          show ¬ i ≥ 32 from by omega, show ¬ i ≥ 40 from by omega,
          show ¬ i ≥ 48 from by omega, show ¬ i ≥ 56 from by omega]
  rcases Nat.lt_or_ge i 24 with h3 | h3
  · have heq : 16 + (i - 16) = i := Nat.add_sub_cancel' h2
    simp [heq, show i < 64 from by omega, show i ≥ 16 from h2, show i - 16 < 8 from by omega,
          show i ≥ 8 from h, show ¬ i - 8 < 8 from by omega,
          show ¬ i ≥ 24 from by omega, show ¬ i ≥ 32 from by omega,
          show ¬ i ≥ 40 from by omega, show ¬ i ≥ 48 from by omega, show ¬ i ≥ 56 from by omega]
  rcases Nat.lt_or_ge i 32 with h4 | h4
  · have heq : 24 + (i - 24) = i := Nat.add_sub_cancel' h3
    simp [heq, show i < 64 from by omega, show i ≥ 24 from h3, show i - 24 < 8 from by omega,
          show i ≥ 8 from h, show ¬ i - 8 < 8 from by omega,
          show i ≥ 16 from h2, show ¬ i - 16 < 8 from by omega,
          show ¬ i ≥ 32 from by omega, show ¬ i ≥ 40 from by omega,
          show ¬ i ≥ 48 from by omega, show ¬ i ≥ 56 from by omega]
  rcases Nat.lt_or_ge i 40 with h5 | h5
  · have heq : 32 + (i - 32) = i := Nat.add_sub_cancel' h4
    simp [heq, show i < 64 from by omega, show i ≥ 32 from h4, show i - 32 < 8 from by omega,
          show i ≥ 8 from h, show ¬ i - 8 < 8 from by omega,
          show i ≥ 16 from h2, show ¬ i - 16 < 8 from by omega,
          show i ≥ 24 from h3, show ¬ i - 24 < 8 from by omega,
          show ¬ i ≥ 40 from by omega, show ¬ i ≥ 48 from by omega, show ¬ i ≥ 56 from by omega]
  rcases Nat.lt_or_ge i 48 with h6 | h6
  · have heq : 40 + (i - 40) = i := Nat.add_sub_cancel' h5
    simp [heq, show i < 64 from by omega, show i ≥ 40 from h5, show i - 40 < 8 from by omega,
          show i ≥ 8 from h, show ¬ i - 8 < 8 from by omega,
          show i ≥ 16 from h2, show ¬ i - 16 < 8 from by omega,
          show i ≥ 24 from h3, show ¬ i - 24 < 8 from by omega,
          show i ≥ 32 from h4, show ¬ i - 32 < 8 from by omega,
          show ¬ i ≥ 48 from by omega, show ¬ i ≥ 56 from by omega]
  rcases Nat.lt_or_ge i 56 with h7 | h7
  · have heq : 48 + (i - 48) = i := Nat.add_sub_cancel' h6
    simp [heq, show i < 64 from by omega, show i ≥ 48 from h6, show i - 48 < 8 from by omega,
          show i ≥ 8 from h, show ¬ i - 8 < 8 from by omega,
          show i ≥ 16 from h2, show ¬ i - 16 < 8 from by omega,
          show i ≥ 24 from h3, show ¬ i - 24 < 8 from by omega,
          show i ≥ 32 from h4, show ¬ i - 32 < 8 from by omega,
          show i ≥ 40 from h5, show ¬ i - 40 < 8 from by omega,
          show ¬ i ≥ 56 from by omega]
  rcases Nat.lt_or_ge i 64 with h8 | h8
  · have heq : 56 + (i - 56) = i := Nat.add_sub_cancel' h7
    simp [heq, show i < 64 from by omega, show i ≥ 56 from h7, show i - 56 < 8 from by omega,
          show i ≥ 8 from h, show ¬ i - 8 < 8 from by omega,
          show i ≥ 16 from h2, show ¬ i - 16 < 8 from by omega,
          show i ≥ 24 from h3, show ¬ i - 24 < 8 from by omega,
          show i ≥ 32 from h4, show ¬ i - 32 < 8 from by omega,
          show i ≥ 40 from h5, show ¬ i - 40 < 8 from by omega,
          show i ≥ 48 from h6, show ¬ i - 48 < 8 from by omega]
  · simp [hfar h8, show ¬ i < 64 from by omega]

/-! ## Read from little-endian byte encoding -/

/-- If memory holds the 4-byte little-endian encoding of `v` at [a, a+4),
    then `read32 a = v`. The bytes are in the same form as `pointsTo_u32`. -/
theorem Mem.read32_of_le_bytes (m : Mem) (a v : UInt32)
    (h0 : m.bytes a.toNat = ⟨(v.toNat / 256 ^ 0) % 256, by omega⟩)
    (h1 : m.bytes (a.toNat + 1) = ⟨(v.toNat / 256 ^ 1) % 256, by omega⟩)
    (h2 : m.bytes (a.toNat + 2) = ⟨(v.toNat / 256 ^ 2) % 256, by omega⟩)
    (h3 : m.bytes (a.toNat + 3) = ⟨(v.toNat / 256 ^ 3) % 256, by omega⟩) :
    m.read32 a = v := by
  -- Bridge: pointsTo_u32 uses Nat division; write32 uses bitvector ops.
  -- Prove they encode the same bytes, then conclude via read32_write32_same.
  have land_mod : ∀ n : Nat, n &&& 255 = n % 256 := fun n => by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_mod_two_pow,
               show (256 : Nat) = 2^8 from by norm_num,
               show (255 : Nat) = 2^8 - 1 from by norm_num,
               Nat.testBit_two_pow_sub_one, Bool.and_comm]
  have e0 : m.bytes a.toNat = (v &&& 0xFF).toUInt8 := by
    rw [h0]; apply UInt8.ext
    simp only [UInt8.toNat, Nat.pow_zero, Nat.div_one]
    unfold UInt32.toUInt8 Nat.toUInt8
    simp only [UInt32.toNat_and, show (0xFF : UInt32).toNat = 255 from by rfl,
               UInt8.ofNat, BitVec.toNat, BitVec.ofNat, Fin.Internal.ofNat]
    have key := land_mod v.toNat; omega
  have e1 : m.bytes (a.toNat + 1) = ((v >>> 8) &&& 0xFF).toUInt8 := by
    rw [h1]; apply UInt8.ext
    simp only [UInt8.toNat, Nat.pow_succ, Nat.pow_zero]
    unfold UInt32.toUInt8 Nat.toUInt8
    simp only [UInt32.toNat_and, UInt32.toNat_shiftRight,
               show (0xFF : UInt32).toNat = 255 from by rfl,
               show (8 : UInt32).toNat = 8 from by rfl,
               show (8 : Nat) % 32 = 8 from by norm_num,
               UInt8.ofNat, BitVec.toNat, BitVec.ofNat, Fin.Internal.ofNat]
    have key := land_mod (v.toNat >>> 8); omega
  have e2 : m.bytes (a.toNat + 2) = ((v >>> 16) &&& 0xFF).toUInt8 := by
    rw [h2]; apply UInt8.ext
    simp only [UInt8.toNat, Nat.pow_succ, Nat.pow_zero]
    unfold UInt32.toUInt8 Nat.toUInt8
    simp only [UInt32.toNat_and, UInt32.toNat_shiftRight,
               show (0xFF : UInt32).toNat = 255 from by rfl,
               show (16 : UInt32).toNat = 16 from by rfl,
               show (16 : Nat) % 32 = 16 from by norm_num,
               UInt8.ofNat, BitVec.toNat, BitVec.ofNat, Fin.Internal.ofNat]
    have key := land_mod (v.toNat >>> 16); omega
  have e3 : m.bytes (a.toNat + 3) = ((v >>> 24) &&& 0xFF).toUInt8 := by
    rw [h3]; apply UInt8.ext
    simp only [UInt8.toNat, Nat.pow_succ, Nat.pow_zero]
    unfold UInt32.toUInt8 Nat.toUInt8
    simp only [UInt32.toNat_and, UInt32.toNat_shiftRight,
               show (0xFF : UInt32).toNat = 255 from by rfl,
               show (24 : UInt32).toNat = 24 from by rfl,
               show (24 : Nat) % 32 = 24 from by norm_num,
               UInt8.ofNat, BitVec.toNat, BitVec.ofNat, Fin.Internal.ofNat]
    have key := land_mod (v.toNat >>> 24); omega
  simp only [Mem.read32, e0, e1, e2, e3]
  apply UInt32.ext
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toUInt32_toNat]
  have byte_of (x : UInt32) : x.toUInt8.toNat = x.toNat % 256 := by
    simp only [UInt32.toUInt8]
    simp [Nat.toUInt8, UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat,
          show (2:Nat)^8 = 256 from rfl]
  simp only [byte_of, UInt32.toNat_and, UInt32.toNat_shiftRight,
             show (255 : UInt32).toNat = 255 from rfl,
             show (8 : UInt32).toNat = 8 from rfl,
             show (16 : UInt32).toNat = 16 from rfl,
             show (24 : UInt32).toNat = 24 from rfl]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow,
             Nat.testBit_and, show (256 : Nat) = 2^8 from rfl,
             show (255 : Nat) = 2^8 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  have hv : v.toNat < 2^32 := v.toNat_lt
  have hfar : i ≥ 32 → v.toNat.testBit i = false :=
    fun hi => Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (@Nat.pow_le_pow_right 2 (by decide) 32 i hi))
  rcases Nat.lt_or_ge i 8 with h | h
  · simp [show i < 8 from h, show i < 32 from by omega,
           show ¬ i ≥ 8 from by omega, show ¬ i ≥ 16 from by omega, show ¬ i ≥ 24 from by omega]
  rcases Nat.lt_or_ge i 16 with h2 | h2
  · have heq : 8 + (i - 8) = i := Nat.add_sub_cancel' h
    simp [heq, show i < 32 from by omega, show i ≥ 8 from h,
          show i - 8 < 8 from by omega, show ¬ i ≥ 16 from by omega, show ¬ i ≥ 24 from by omega]
  rcases Nat.lt_or_ge i 24 with h3 | h3
  · have heq : 16 + (i - 16) = i := Nat.add_sub_cancel' h2
    simp [heq, show i < 32 from by omega, show i ≥ 8 from h, show i ≥ 16 from h2,
          show i - 16 < 8 from by omega, show ¬ i - 8 < 8 from by omega,
          show ¬ i ≥ 24 from by omega, show ¬ i < 8 from by omega]
  rcases Nat.lt_or_ge i 32 with h4 | h4
  · have heq : 24 + (i - 24) = i := Nat.add_sub_cancel' h3
    simp [heq, show i < 32 from by omega, show i ≥ 8 from h, show i ≥ 16 from h2,
          show i ≥ 24 from h3, show i - 24 < 8 from by omega,
          show ¬ i - 8 < 8 from by omega, show ¬ i - 16 < 8 from by omega,
          show ¬ i < 8 from by omega]
  · simp [hfar h4, show ¬ i < 32 from by omega]

/-! ## Stores preserve the page count -/

@[simp] theorem Mem.write32_pages (m : Mem) (a v : UInt32) :
    (m.write32 a v).pages = m.pages := rfl

@[simp] theorem Mem.write64_pages (m : Mem) (a : UInt32) (v : UInt64) :
    (m.write64 a v).pages = m.pages := rfl

/-! ## Disjoint read/write -/

/-- A single byte survives a `write32` whose 4-byte footprint does not overlap it. -/
theorem Mem.read8_write32_of_ne (m : Mem) (a v : UInt32) (j : Nat)
    (h : j < a.toNat ∨ a.toNat + 3 < j) :
    (m.write32 a v).bytes j = m.bytes j := by
  simp only [Mem.write32]
  split_ifs <;> first | rfl | omega

/-- Reading a `u32` word from an address whose 4-byte footprint is disjoint from a `write32`
    returns the original value. -/
theorem Mem.read32_write32_of_disjoint (m : Mem) (a b v : UInt32)
    (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [Mem.read8_write32_of_ne m a v b.toNat (by omega),
      Mem.read8_write32_of_ne m a v (b.toNat + 1) (by omega),
      Mem.read8_write32_of_ne m a v (b.toNat + 2) (by omega),
      Mem.read8_write32_of_ne m a v (b.toNat + 3) (by omega)]

end Wasm
