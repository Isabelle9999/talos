import CodeLib.SepLogic.WasmHeap
import Interpreter.Wasm

/-! # Bridge: Talos Mem ↔ iris-lean GenHeap

The state interpretation maintains agreement between
the abstract GenHeap state σ and physical Mem.bytes.
We never build σ explicitly — GenHeap tracks it internally.
-/

namespace Wasm.SepLogic

open Iris Wasm Std

variable [inst : WasmHeapGS]

/-! Agreement: wherever GenHeap has an entry, Mem agrees. -/

def heapAgreesWithMem (σ : WasmHeapMap (Option UInt8)) (mem : Mem) : Prop :=
  ∀ (addr : UInt32) (v : UInt8),
    get? σ addr = some (some v) → mem.bytes addr.toNat = v

/-! Soundness of load:
If GenHeap says addr ↦ v and σ agrees with Mem,
then Mem.read8 addr = v. -/

theorem load_sound (σ : WasmHeapMap (Option UInt8)) (mem : Mem)
    (addr : UInt32) (v : UInt8)
    (h_agree : heapAgreesWithMem σ mem)
    (h_own : get? σ addr = some (some v)) :
    mem.bytes addr.toNat = v :=
  h_agree addr v h_own

/-! Soundness of store:
After Mem.write8, the updated σ still agrees with new Mem. -/

theorem store_sound (σ : WasmHeapMap (Option UInt8)) (mem : Mem)
    (addr : UInt32) (old_v new_v : UInt8)
    (h_agree : heapAgreesWithMem σ mem)
    (h_own : get? σ addr = some (some old_v)) :
    heapAgreesWithMem (insert σ addr (some new_v))
      ⟨mem.pages, fun n =>
        if n = addr.toNat then new_v else mem.bytes n⟩ := by
  intro addr' v' h_get
  by_cases h : addr' = addr
  · subst h
    simp [get?_insert_eq rfl] at h_get
    simp [h_get]
  · simp [get?_insert_ne (Ne.symm h)] at h_get
    have hne : addr'.toNat ≠ addr.toNat :=
      fun h' => h (UInt32.ext h')
    exact (if_neg hne).trans (h_agree addr' v' h_get)

-- GenHeap lemmas for our types:
#check @genHeap_valid (GF := WasmHeapGF) (L := UInt32)
    (V := Option UInt8) (H := WasmHeapMap)
#check @genHeap_update (GF := WasmHeapGF) (L := UInt32)
    (V := Option UInt8) (H := WasmHeapMap)

/-! After a 32-bit write, the 4-fold-inserted ghost state agrees with the new memory. -/

private lemma land_mod_256 (n : Nat) : n &&& 255 = n % 256 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow,
             show (256 : Nat) = 2^8 from by norm_num,
             show (255 : Nat) = 2^8 - 1 from by norm_num,
             Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem heapAgreesWithMem_write32_update
    {σ : WasmHeapMap (Option UInt8)} {mem : Mem} {addr v : UInt32}
    (hagree : heapAgreesWithMem σ mem)
    (hbounds : addr.toNat + 4 ≤ 4294967296) :
    heapAgreesWithMem
      (insert (insert (insert (insert σ
        addr       (some ⟨v.toNat / 256 ^ 0 % 256, by omega⟩))
        (addr + 1) (some ⟨v.toNat / 256 ^ 1 % 256, by omega⟩))
        (addr + 2) (some ⟨v.toNat / 256 ^ 2 % 256, by omega⟩))
        (addr + 3) (some ⟨v.toNat / 256 ^ 3 % 256, by omega⟩))
      (mem.write32 addr v) := by
  have ha1 : (addr + 1).toNat = addr.toNat + 1 := by
    rw [UInt32.toNat_add]; simp; omega
  have ha2 : (addr + 2).toNat = addr.toNat + 2 := by
    rw [UInt32.toNat_add]; simp; omega
  have ha3 : (addr + 3).toNat = addr.toNat + 3 := by
    rw [UInt32.toNat_add]; simp; omega
  -- Helper: byte equality via land_mod
  have land_mod : ∀ n : Nat, n &&& 255 = n % 256 := land_mod_256
  -- Helper to evaluate write32 at offset i
  have wb : ∀ i : Nat, (mem.write32 addr v).bytes i =
      if i = addr.toNat then (v &&& 0xFF).toUInt8
      else if i = addr.toNat + 1 then ((v >>> 8) &&& 0xFF).toUInt8
      else if i = addr.toNat + 2 then ((v >>> 16) &&& 0xFF).toUInt8
      else if i = addr.toNat + 3 then ((v >>> 24) &&& 0xFF).toUInt8
      else mem.bytes i := fun _ => rfl
  intro addr' byte' hget
  -- Case split on which of the 4 addresses addr' hits
  by_cases h3 : addr' = addr + 3
  · subst h3
    simp only [get?_insert_eq rfl] at hget
    have hbyte : ⟨v.toNat / 256 ^ 3 % 256, by omega⟩ = byte' :=
      Option.some.inj (Option.some.inj hget)
    subst hbyte
    rw [wb, ha3, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
    apply UInt8.ext
    simp only [UInt8.toNat]
    unfold UInt32.toUInt8 Nat.toUInt8
    simp only [UInt32.toNat_and, UInt32.toNat_shiftRight,
               show (0xFF : UInt32).toNat = 255 from rfl,
               show (24 : UInt32).toNat = 24 from rfl,
               show (24 : Nat) % 32 = 24 from by norm_num,
               UInt8.ofNat, BitVec.toNat, BitVec.ofNat, Fin.Internal.ofNat,
               Nat.pow_succ, Nat.pow_zero, Nat.mul_one]
    have := land_mod (v.toNat >>> 24); omega
  · by_cases h2 : addr' = addr + 2
    · subst h2
      simp only [get?_insert_ne (Ne.symm h3), get?_insert_eq rfl] at hget
      have hbyte : ⟨v.toNat / 256 ^ 2 % 256, by omega⟩ = byte' :=
        Option.some.inj (Option.some.inj hget)
      subst hbyte
      rw [wb, ha2, if_neg (by omega), if_neg (by omega), if_pos rfl]
      apply UInt8.ext
      simp only [UInt8.toNat]
      unfold UInt32.toUInt8 Nat.toUInt8
      simp only [UInt32.toNat_and, UInt32.toNat_shiftRight,
                 show (0xFF : UInt32).toNat = 255 from rfl,
                 show (16 : UInt32).toNat = 16 from rfl,
                 show (16 : Nat) % 32 = 16 from by norm_num,
                 UInt8.ofNat, BitVec.toNat, BitVec.ofNat, Fin.Internal.ofNat,
                 Nat.pow_succ, Nat.pow_zero, Nat.mul_one]
      have := land_mod (v.toNat >>> 16); omega
    · by_cases h1 : addr' = addr + 1
      · subst h1
        simp only [get?_insert_ne (Ne.symm h3), get?_insert_ne (Ne.symm h2),
                   get?_insert_eq rfl] at hget
        have hbyte : ⟨v.toNat / 256 ^ 1 % 256, by omega⟩ = byte' :=
          Option.some.inj (Option.some.inj hget)
        subst hbyte
        rw [wb, ha1, if_neg (by omega), if_pos rfl]
        apply UInt8.ext
        simp only [UInt8.toNat]
        unfold UInt32.toUInt8 Nat.toUInt8
        simp only [UInt32.toNat_and, UInt32.toNat_shiftRight,
                   show (0xFF : UInt32).toNat = 255 from rfl,
                   show (8 : UInt32).toNat = 8 from rfl,
                   show (8 : Nat) % 32 = 8 from by norm_num,
                   UInt8.ofNat, BitVec.toNat, BitVec.ofNat, Fin.Internal.ofNat,
                   Nat.pow_succ, Nat.pow_zero, Nat.mul_one]
        have := land_mod (v.toNat >>> 8); omega
      · by_cases h0 : addr' = addr
        · subst h0
          simp only [get?_insert_ne (Ne.symm h3), get?_insert_ne (Ne.symm h2),
                     get?_insert_ne (Ne.symm h1), get?_insert_eq rfl] at hget
          have hbyte : ⟨v.toNat / 256 ^ 0 % 256, by omega⟩ = byte' :=
            Option.some.inj (Option.some.inj hget)
          subst hbyte
          rw [wb, if_pos rfl]
          apply UInt8.ext
          simp only [UInt8.toNat]
          unfold UInt32.toUInt8 Nat.toUInt8
          simp only [UInt32.toNat_and,
                     show (0xFF : UInt32).toNat = 255 from rfl,
                     UInt8.ofNat, BitVec.toNat, BitVec.ofNat, Fin.Internal.ofNat,
                     Nat.pow_zero, Nat.div_one]
          have := land_mod v.toNat; omega
        · -- addr' is none of the 4 written addresses
          have hget_orig : get? σ addr' = some (some byte') := by
            simp only [get?_insert_ne (Ne.symm h3), get?_insert_ne (Ne.symm h2),
                       get?_insert_ne (Ne.symm h1), get?_insert_ne (Ne.symm h0)] at hget
            exact hget
          have h0n : addr'.toNat ≠ addr.toNat := fun h => h0 (UInt32.ext h)
          have h1n : addr'.toNat ≠ addr.toNat + 1 :=
            fun h => h1 (UInt32.ext (h.trans ha1.symm))
          have h2n : addr'.toNat ≠ addr.toNat + 2 :=
            fun h => h2 (UInt32.ext (h.trans ha2.symm))
          have h3n : addr'.toNat ≠ addr.toNat + 3 :=
            fun h => h3 (UInt32.ext (h.trans ha3.symm))
          rw [wb, if_neg h0n, if_neg h1n, if_neg h2n, if_neg h3n]
          exact hagree addr' byte' hget_orig

end Wasm.SepLogic
