import Iris.Std.HeapInstances

/-! # PosTrie: canonical positional binary trie for UInt32 keys

Key encoding: key 0 = root; even k ≠ 0 → left at k/2; odd k → right at k/2.
This is the ORIGINAL encoding from the old 3-constructor version.

Canonical form: a `Raw V` trie `.node v l r` satisfies
  • v ≠ none  ∨  l ≠ .empty  ∨  r ≠ .empty   (no spurious empty nodes)
  • l.nodeVal = none                              (position 0 of left subtrie is inaccessible
                                                   under even→left encoding; fixing it there
                                                   removes the one remaining non-uniqueness)
  • l.canonical  ∧  r.canonical                  (subtrees are canonical)

The public `PosTrie V` is the subtype `{t : Raw V // t.canonical}`.  Because every pair of
canonical tries with the same `get?` function must be structurally equal, we get
`equiv_iff_eq` for free by structural induction. -/

namespace Wasm.SepLogic

-- ─── Raw (unconstrained) trie ─────────────────────────────────────────────────

private inductive Raw (V : Type) where
  | empty : Raw V
  | node  : Option V → Raw V → Raw V → Raw V

namespace Raw

variable {V V' : Type}

-- ─── Accessors ────────────────────────────────────────────────────────────────

def nodeVal : Raw V → Option V
  | .node v _ _ => v | .empty => none

def lc : Raw V → Raw V
  | .node _ l _ => l | _ => .empty

def rc : Raw V → Raw V
  | .node _ _ r => r | _ => .empty

-- ─── UInt32 helpers ───────────────────────────────────────────────────────────

private theorem two_toNat : (2 : UInt32).toNat = 2 := by decide

private theorem toNat_div2 (k : UInt32) : (k / 2).toNat = k.toNat / 2 := by
  simp [UInt32.toNat_div, two_toNat]

private theorem toNat_mod2 (k : UInt32) : (k % 2).toNat = k.toNat % 2 := by
  simp [UInt32.toNat_mod, two_toNat]

private theorem toNat_ne_zero {k : UInt32} (h : k ≠ 0) : k.toNat ≠ 0 :=
  fun e => h (UInt32.toNat.inj (by simpa using e))

private theorem toNat_div_lt {k : UInt32} (h : k ≠ 0) : (k / 2).toNat < k.toNat := by
  rw [toNat_div2]; have := toNat_ne_zero h; omega

private theorem mod2_eq_one {k : UInt32} (h : k % 2 ≠ 0) : k % 2 = 1 := by
  apply UInt32.toNat.inj
  have hm := toNat_mod2 k
  have hn : (k % 2).toNat ≠ 0 := fun e => h (UInt32.toNat.inj (by simp [show (0:UInt32).toNat=0 from rfl, e]))
  have hl : k.toNat % 2 < 2 := Nat.mod_lt _ (by omega)
  simp [show (1:UInt32).toNat=1 from rfl]; omega

private theorem uint32_eq_of_div_mod {k k' : UInt32}
    (hdiv : k / 2 = k' / 2) (hmod : k % 2 = k' % 2) : k = k' := by
  apply UInt32.toNat.inj
  have hd : k.toNat / 2 = k'.toNat / 2 := by
    have := congrArg UInt32.toNat hdiv; rwa [toNat_div2, toNat_div2] at this
  have hm : k.toNat % 2 = k'.toNat % 2 := by
    have := congrArg UInt32.toNat hmod; rwa [toNat_mod2, toNat_mod2] at this
  omega

-- ─── get? ─────────────────────────────────────────────────────────────────────

def get? : Raw V → UInt32 → Option V
  | .empty,       _ => none
  | .node v l r,  k =>
    if k = 0 then v
    else if k % 2 = 0 then l.get? (k / 2)
    else r.get? (k / 2)

@[simp] theorem get?_empty (k : UInt32) : (Raw.empty : Raw V).get? k = none := rfl

@[simp] theorem get?_zero (t : Raw V) : t.get? 0 = t.nodeVal := by cases t <;> rfl

theorem get?_node_zero (v : Option V) (l r : Raw V) : (Raw.node v l r).get? 0 = v := rfl

theorem get?_node_nz (v : Option V) (l r : Raw V) (k : UInt32) (hk : k ≠ 0) :
    (Raw.node v l r).get? k = if k % 2 = 0 then l.get? (k / 2) else r.get? (k / 2) := by
  simp [get?, hk]

theorem get?_nz (t : Raw V) (k : UInt32) (hk : k ≠ 0) :
    t.get? k = if k % 2 = 0 then t.lc.get? (k / 2) else t.rc.get? (k / 2) := by
  cases t with
  | empty => simp [lc, rc]
  | node v l r => exact get?_node_nz v l r k hk

-- ─── Smart constructor ────────────────────────────────────────────────────────

def mkNode (v : Option V) (l r : Raw V) : Raw V :=
  match v, l, r with
  | none, .empty, .empty => .empty
  | _,    _,      _      => .node v l r

@[simp] theorem mkNode_nodeVal (v : Option V) (l r : Raw V) :
    (mkNode v l r).nodeVal = v := by
  unfold mkNode; split <;> simp [nodeVal]

theorem mkNode_get?_zero (v : Option V) (l r : Raw V) : (mkNode v l r).get? 0 = v := by
  unfold mkNode; split <;> simp [nodeVal]

theorem mkNode_get?_nz (v : Option V) (l r : Raw V) (k : UInt32) (hk : k ≠ 0) :
    (mkNode v l r).get? k = if k % 2 = 0 then l.get? (k / 2) else r.get? (k / 2) := by
  cases v with
  | none =>
    cases l with
    | empty =>
      cases r with
      | empty => simp [mkNode, get?_empty]
      | node u rl rr => simp only [mkNode]; exact get?_node_nz _ _ _ _ hk
    | node w ll lr => simp only [mkNode]; exact get?_node_nz _ _ _ _ hk
  | some a => simp only [mkNode]; exact get?_node_nz _ _ _ _ hk

-- ─── insert / delete ──────────────────────────────────────────────────────────

def insert (t : Raw V) (k : UInt32) (v : V) : Raw V :=
  if k = 0 then mkNode (some v) t.lc t.rc
  else if k % 2 = 0 then mkNode t.nodeVal (t.lc.insert (k / 2) v) t.rc
  else mkNode t.nodeVal t.lc (t.rc.insert (k / 2) v)
termination_by k.toNat
decreasing_by all_goals exact toNat_div_lt (by simp_all)

def delete (t : Raw V) (k : UInt32) : Raw V :=
  if k = 0 then mkNode none t.lc t.rc
  else if k % 2 = 0 then mkNode t.nodeVal (t.lc.delete (k / 2)) t.rc
  else mkNode t.nodeVal t.lc (t.rc.delete (k / 2))
termination_by k.toNat
decreasing_by all_goals exact toNat_div_lt (by simp_all)

-- ─── get?_insert ──────────────────────────────────────────────────────────────

theorem get?_insert (t : Raw V) (k k' : UInt32) (v : V) :
    (t.insert k v).get? k' = if k = k' then some v else t.get? k' := by
  suffices h : ∀ n, ∀ k : UInt32, k.toNat ≤ n → ∀ k' (t : Raw V),
      (t.insert k v).get? k' = if k = k' then some v else t.get? k' from
    h k.toNat k (Nat.le_refl _) k' t
  intro n; induction n with
  | zero =>
    intro k hle k' t
    have hk0 : k = 0 := UInt32.toNat.inj (Nat.le_zero.mp hle ▸ rfl)
    subst hk0; simp only [insert, ↓reduceIte]
    by_cases hk' : k' = 0
    · subst hk'; simp
    · simp [mkNode_get?_nz _ _ _ _ hk', get?_nz t k' hk', Ne.symm hk']
  | succ n ih =>
    intro k hle k' t
    by_cases hk0 : k = 0
    · subst hk0; simp only [insert, ↓reduceIte]
      by_cases hk' : k' = 0
      · subst hk'; simp
      · simp [mkNode_get?_nz _ _ _ _ hk', get?_nz t k' hk', Ne.symm hk']
    · have hdivle : (k / 2).toNat ≤ n := by
        rw [toNat_div2]; have := toNat_ne_zero hk0; omega
      unfold insert; rw [if_neg hk0]
      by_cases hmod : k % 2 = 0
      · simp only [hmod, ↓reduceIte]
        by_cases hk'0 : k' = 0
        · subst hk'0; simp [if_neg hk0, get?_zero]
        · rw [mkNode_get?_nz _ _ _ _ hk'0, get?_nz t k' hk'0]
          by_cases hmod' : k' % 2 = 0
          · simp only [hmod', ↓reduceIte]
            rw [ih (k / 2) hdivle (k' / 2) t.lc]
            by_cases heq : k / 2 = k' / 2
            · simp [uint32_eq_of_div_mod heq (by rw [hmod, hmod'])]
            · simp [if_neg heq, if_neg (fun e : k = k' => heq (congrArg (· / 2) e))]
          · exact if_neg (fun e : k = k' => hmod' (e ▸ hmod)) ▸ by simp [hmod']
      · simp only [show k % 2 ≠ 0 from hmod, ↓reduceIte]
        by_cases hk'0 : k' = 0
        · subst hk'0; simp [if_neg hk0, get?_zero]
        · rw [mkNode_get?_nz _ _ _ _ hk'0, get?_nz t k' hk'0]
          by_cases hmod' : k' % 2 = 0
          · exact if_neg (fun e : k = k' => hmod (e ▸ hmod')) ▸ by simp [hmod']
          · simp only [show k' % 2 ≠ 0 from hmod', ↓reduceIte]
            rw [ih (k / 2) hdivle (k' / 2) t.rc]
            by_cases heq : k / 2 = k' / 2
            · simp [uint32_eq_of_div_mod heq (by rw [mod2_eq_one hmod, mod2_eq_one hmod'])]
            · simp [if_neg heq, if_neg (fun e : k = k' => heq (congrArg (· / 2) e))]

-- ─── get?_delete ──────────────────────────────────────────────────────────────

theorem get?_delete (t : Raw V) (k k' : UInt32) :
    (t.delete k).get? k' = if k = k' then none else t.get? k' := by
  suffices h : ∀ n, ∀ k : UInt32, k.toNat ≤ n → ∀ k' (t : Raw V),
      (t.delete k).get? k' = if k = k' then none else t.get? k' from
    h k.toNat k (Nat.le_refl _) k' t
  intro n; induction n with
  | zero =>
    intro k hle k' t
    have hk0 : k = 0 := UInt32.toNat.inj (Nat.le_zero.mp hle ▸ rfl)
    subst hk0; simp only [delete, ↓reduceIte]
    by_cases hk' : k' = 0
    · subst hk'; simp
    · simp [mkNode_get?_nz _ _ _ _ hk', get?_nz t k' hk', Ne.symm hk']
  | succ n ih =>
    intro k hle k' t
    by_cases hk0 : k = 0
    · subst hk0; simp only [delete, ↓reduceIte]
      by_cases hk' : k' = 0
      · subst hk'; simp
      · simp [mkNode_get?_nz _ _ _ _ hk', get?_nz t k' hk', Ne.symm hk']
    · have hdivle : (k / 2).toNat ≤ n := by
        rw [toNat_div2]; have := toNat_ne_zero hk0; omega
      unfold delete; rw [if_neg hk0]
      by_cases hmod : k % 2 = 0
      · simp only [hmod, ↓reduceIte]
        by_cases hk'0 : k' = 0
        · subst hk'0; simp [if_neg hk0, get?_zero]
        · rw [mkNode_get?_nz _ _ _ _ hk'0, get?_nz t k' hk'0]
          by_cases hmod' : k' % 2 = 0
          · simp only [hmod', ↓reduceIte]
            rw [ih (k / 2) hdivle (k' / 2) t.lc]
            by_cases heq : k / 2 = k' / 2
            · simp [uint32_eq_of_div_mod heq (by rw [hmod, hmod'])]
            · simp [if_neg heq, if_neg (fun e : k = k' => heq (congrArg (· / 2) e))]
          · exact if_neg (fun e : k = k' => hmod' (e ▸ hmod)) ▸ by simp [hmod']
      · simp only [show k % 2 ≠ 0 from hmod, ↓reduceIte]
        by_cases hk'0 : k' = 0
        · subst hk'0; simp [if_neg hk0, get?_zero]
        · rw [mkNode_get?_nz _ _ _ _ hk'0, get?_nz t k' hk'0]
          by_cases hmod' : k' % 2 = 0
          · exact if_neg (fun e : k = k' => hmod (e ▸ hmod')) ▸ by simp [hmod']
          · simp only [show k' % 2 ≠ 0 from hmod', ↓reduceIte]
            rw [ih (k / 2) hdivle (k' / 2) t.rc]
            by_cases heq : k / 2 = k' / 2
            · simp [uint32_eq_of_div_mod heq (by rw [mod2_eq_one hmod, mod2_eq_one hmod'])]
            · simp [if_neg heq, if_neg (fun e : k = k' => heq (congrArg (· / 2) e))]

-- ─── bindAlterAux / mergeAux ──────────────────────────────────────────────────

def bindAlterAux (f : UInt32 → V → Option V')
    (t : Raw V) (step pfx : UInt32) : Raw V' :=
  match t with
  | .empty      => .empty
  | .node v l r =>
    mkNode (v.bind (f pfx))
           (bindAlterAux f l (step * 2) pfx)
           (bindAlterAux f r (step * 2) (pfx + step))

def bindAlter (f : UInt32 → V → Option V') (t : Raw V) : Raw V' :=
  t.bindAlterAux f 1 0

private theorem mul1_add0 (k : UInt32) : k * 1 + 0 = k := by
  apply UInt32.toNat.inj
  simp

theorem get?_bindAlterAux (f : UInt32 → V → Option V')
    (t : Raw V) (step pfx j : UInt32) :
    (t.bindAlterAux f step pfx).get? j = (t.get? j).bind (f (j * step + pfx)) := by
  induction t generalizing step pfx j with
  | empty => simp [bindAlterAux]
  | node v l r ihl ihr =>
    simp only [bindAlterAux]
    by_cases hj : j = 0
    · subst hj; rw [mkNode_get?_zero, get?_node_zero]; simp
    · rw [mkNode_get?_nz _ _ _ _ hj, get?_node_nz v l r j hj]
      by_cases hmod : j % 2 = 0
      · simp only [hmod, ↓reduceIte]
        have hkey : j / 2 * (step * 2) + pfx = j * step + pfx := by
          apply UInt32.toNat.inj
          simp [UInt32.toNat_add, UInt32.toNat_mul, two_toNat]
          have hm : j.toNat % 2 = 0 := by
            have := toNat_mod2 j; have h3 : (j % 2).toNat = 0 := by rw [hmod]; rfl
            omega
          have hd : j.toNat / 2 * 2 = j.toNat := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hm)
          have h1 : j.toNat / 2 * (step.toNat * 2) = j.toNat * step.toNat := by
            rw [Nat.mul_comm step.toNat 2, ← Nat.mul_assoc, hd]
          congr 1; omega
        rw [ihl (step * 2) pfx (j / 2), hkey]
      · simp only [show j % 2 ≠ 0 from hmod, ↓reduceIte]
        have hkey : j / 2 * (step * 2) + (pfx + step) = j * step + pfx := by
          apply UInt32.toNat.inj
          simp [UInt32.toNat_add, UInt32.toNat_mul, two_toNat]
          have hm : j.toNat % 2 = 1 := by
            have := toNat_mod2 j
            have hne : j.toNat % 2 ≠ 0 := by
              intro e; exact hmod (UInt32.toNat.inj (by simp [show (0:UInt32).toNat=0 from rfl, e]))
            have hl : j.toNat % 2 < 2 := Nat.mod_lt _ (by omega)
            omega
          have hd2 : j.toNat / 2 * 2 + 1 = j.toNat := by
            have := Nat.div_add_mod j.toNat 2; omega
          have h1 : j.toNat / 2 * (step.toNat * 2) = j.toNat / 2 * 2 * step.toNat := by
            rw [Nat.mul_comm step.toNat 2, ← Nat.mul_assoc]
          have h2 : j.toNat / 2 * 2 * step.toNat + step.toNat = j.toNat * step.toNat := by
            rw [← hd2, Nat.add_mul, Nat.one_mul]
          congr 1; omega
        rw [ihr (step * 2) (pfx + step) (j / 2), hkey]

theorem get?_bindAlter (f : UInt32 → V → Option V') (t : Raw V) (k : UInt32) :
    (t.bindAlter f).get? k = (t.get? k).bind (f k) := by
  simp [bindAlter, get?_bindAlterAux]

def mergeAux (op : UInt32 → V → V → V)
    (t1 t2 : Raw V) (step pfx : UInt32) : Raw V :=
  match t1, t2 with
  | .empty, t  => t
  | t, .empty  => t
  | .node v l1 r1, .node w l2 r2 =>
    mkNode (Option.merge (op pfx) v w)
           (mergeAux op l1 l2 (step * 2) pfx)
           (mergeAux op r1 r2 (step * 2) (pfx + step))

def merge (op : UInt32 → V → V → V) (t1 t2 : Raw V) : Raw V :=
  t1.mergeAux op t2 1 0

theorem get?_mergeAux (op : UInt32 → V → V → V)
    (t1 t2 : Raw V) (step pfx j : UInt32) :
    (t1.mergeAux op t2 step pfx).get? j =
      Option.merge (op (j * step + pfx)) (t1.get? j) (t2.get? j) := by
  induction t1 generalizing t2 step pfx j with
  | empty => simp [mergeAux]
  | node v l1 r1 ihl ihr =>
    cases t2 with
    | empty => simp [mergeAux]
    | node w l2 r2 =>
      simp only [mergeAux]
      by_cases hj : j = 0
      · subst hj; rw [mkNode_get?_zero, get?_node_zero, get?_node_zero]; simp
      · rw [mkNode_get?_nz _ _ _ _ hj, get?_node_nz v l1 r1 j hj, get?_node_nz w l2 r2 j hj]
        by_cases hmod : j % 2 = 0
        · simp only [hmod, ↓reduceIte]
          have hkey : j / 2 * (step * 2) + pfx = j * step + pfx := by
            apply UInt32.toNat.inj
            simp [UInt32.toNat_add, UInt32.toNat_mul, two_toNat]
            have hm : j.toNat % 2 = 0 := by
              have := toNat_mod2 j; have h3 : (j % 2).toNat = 0 := by rw [hmod]; rfl
              omega
            have hd : j.toNat / 2 * 2 = j.toNat := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hm)
            have h1 : j.toNat / 2 * (step.toNat * 2) = j.toNat * step.toNat := by
              rw [Nat.mul_comm step.toNat 2, ← Nat.mul_assoc, hd]
            congr 1; omega
          rw [ihl l2 (step * 2) pfx (j / 2), hkey]
        · simp only [show j % 2 ≠ 0 from hmod, ↓reduceIte]
          have hkey : j / 2 * (step * 2) + (pfx + step) = j * step + pfx := by
            apply UInt32.toNat.inj
            simp [UInt32.toNat_add, UInt32.toNat_mul, two_toNat]
            have hm : j.toNat % 2 = 1 := by
              have := toNat_mod2 j
              have hne : j.toNat % 2 ≠ 0 := by
                intro e; exact hmod (UInt32.toNat.inj (by simp [show (0:UInt32).toNat=0 from rfl, e]))
              have hl : j.toNat % 2 < 2 := Nat.mod_lt _ (by omega)
              omega
            have hd2 : j.toNat / 2 * 2 + 1 = j.toNat := by
              have := Nat.div_add_mod j.toNat 2; omega
            have h1 : j.toNat / 2 * (step.toNat * 2) = j.toNat / 2 * 2 * step.toNat := by
              rw [Nat.mul_comm step.toNat 2, ← Nat.mul_assoc]
            have h2 : j.toNat / 2 * 2 * step.toNat + step.toNat = j.toNat * step.toNat := by
              rw [← hd2, Nat.add_mul, Nat.one_mul]
            congr 1; omega
          rw [ihr r2 (step * 2) (pfx + step) (j / 2), hkey]

theorem get?_merge (op : UInt32 → V → V → V) (t1 t2 : Raw V) (k : UInt32) :
    (t1.merge op t2).get? k = Option.merge (op k) (t1.get? k) (t2.get? k) := by
  simp [merge, get?_mergeAux]

-- ─── toListAux ────────────────────────────────────────────────────────────────

-- skipRoot: when true, skip position 0 in this trie (position 0 of the left subtrie
-- is inaccessible under the even→left encoding; we skip it to avoid phantom elements).
def toListAux (t : Raw V) (d : Nat) (pfx : UInt32) (skipRoot : Bool) :
    List (UInt32 × V) :=
  match t with
  | .empty  => []
  | .node v l r =>
    (if skipRoot then [] else match v with | none => [] | some u => [(pfx, u)]) ++
    if d ≥ 32 then [] else
      toListAux l (d + 1) pfx true ++
      toListAux r (d + 1) (pfx + UInt32.ofNat (2 ^ d)) false

def toList (t : Raw V) : List (UInt32 × V) := t.toListAux 0 0 false

-- ─── Depth-bounded canonical predicate ───────────────────────────────────────

private def canonicalAux : Raw V → Nat → Prop
  | .empty, _          => True
  | .node v l r, 0     => v ≠ none ∧ l = .empty ∧ r = .empty
  | .node v l r, d + 1 => (v ≠ none ∨ l ≠ .empty ∨ r ≠ .empty) ∧
                           l.nodeVal = none ∧
                           l.canonicalAux d ∧ r.canonicalAux d

def canonical (t : Raw V) : Prop := t.canonicalAux 32

@[simp] theorem canonical_empty : (Raw.empty : Raw V).canonical := trivial

theorem canonical_node {v : Option V} {l r : Raw V} :
    (Raw.node v l r).canonical ↔
    (v ≠ none ∨ l ≠ .empty ∨ r ≠ .empty) ∧ l.nodeVal = none ∧
    l.canonicalAux 31 ∧ r.canonicalAux 31 :=
  Iff.rfl

-- ─── mkNode preserves canonicity (depth-bounded) ─────────────────────────────

private theorem canonicalAux_mono : ∀ (t : Raw V) (d : Nat), t.canonicalAux d → t.canonicalAux (d + 1) := by
  intro t; induction t with
  | empty => intros; trivial
  | node v l r ihl ihr =>
    intro d h
    cases d with
    | zero =>
      obtain ⟨hv, hl, hr⟩ := h
      subst hl; subst hr
      exact ⟨Or.inl hv, rfl, trivial, trivial⟩
    | succ d' =>
      obtain ⟨hnonempty, hlv, hld, hrd⟩ := h
      exact ⟨hnonempty, hlv, ihl d' hld, ihr d' hrd⟩

private theorem mkNode_canonicalAux (d : Nat) (v : Option V) (l r : Raw V)
    (hl : l.canonicalAux d) (hlv : l.nodeVal = none) (hr : r.canonicalAux d) :
    (mkNode v l r).canonicalAux (d + 1) := by
  unfold mkNode
  rcases v with _ | a
  · rcases l with _ | ⟨w, ll, lr⟩
    · rcases r with _ | ⟨u, rl, rr⟩
      · trivial
      · show (Raw.node none .empty (Raw.node u rl rr)).canonicalAux (d + 1)
        exact ⟨Or.inr (Or.inr (by simp)), rfl, trivial, hr⟩
    · show (Raw.node none (Raw.node w ll lr) r).canonicalAux (d + 1)
      exact ⟨Or.inr (Or.inl (by simp)), hlv, hl, hr⟩
  · show (Raw.node (some a) l r).canonicalAux (d + 1)
    exact ⟨Or.inl (by simp), hlv, hl, hr⟩

-- ─── nodeVal preservation under insert/delete ────────────────────────────────

theorem insert_nodeVal_of_ne (t : Raw V) (k : UInt32) (v : V) (hk : k ≠ 0) :
    (t.insert k v).nodeVal = t.nodeVal := by
  unfold insert; rw [if_neg hk]
  by_cases hmod : k % 2 = 0 <;> simp only [hmod, ↓reduceIte, mkNode_nodeVal]

theorem delete_nodeVal_of_ne (t : Raw V) (k : UInt32) (hk : k ≠ 0) :
    (t.delete k).nodeVal = t.nodeVal := by
  unfold delete; rw [if_neg hk]
  by_cases hmod : k % 2 = 0 <;> simp only [hmod, ↓reduceIte, mkNode_nodeVal]

private theorem div2_ne_zero_of_even_ne {k : UInt32} (hk : k ≠ 0) (hmod : k % 2 = 0) :
    k / 2 ≠ 0 := by
  intro h
  have h' := congrArg UInt32.toNat h
  rw [toNat_div2, show (0:UInt32).toNat = 0 from rfl] at h'
  have hm0 : k.toNat % 2 = 0 := by
    have hm := toNat_mod2 k; have h3 : (k % 2).toNat = 0 := by rw [hmod]; rfl
    omega
  have hkn := toNat_ne_zero hk
  omega

-- ─── insert preserves canonicity ─────────────────────────────────────────────

private theorem insert_canonicalAux (v : V) :
    ∀ (d : Nat) (k : UInt32), k.toNat < 2^d →
    ∀ (t : Raw V), t.canonicalAux d → (t.insert k v).canonicalAux d := by
  intro d; induction d with
  | zero =>
    intro k hk t ht
    have hk0 : k = 0 := UInt32.toNat.inj (by
      simp only [show (0:UInt32).toNat = 0 from rfl]
      simp only [Nat.pow_zero] at hk; omega)
    subst hk0; simp only [insert, ↓reduceIte]
    cases t with
    | empty => exact ⟨by simp, rfl, rfl⟩
    | node v' l r =>
      obtain ⟨_, hl, hr⟩ := ht; subst hl; subst hr
      simp only [lc, rc]; exact ⟨by simp, rfl, rfl⟩
  | succ d' ih =>
    intro k hk t ht
    by_cases hk0 : k = 0
    · subst hk0; simp only [insert, ↓reduceIte]
      apply mkNode_canonicalAux d'
      · cases t with | empty => trivial | node v l r => exact ht.2.2.1
      · cases t with | empty => rfl | node v l r => exact ht.2.1
      · cases t with | empty => trivial | node v l r => exact ht.2.2.2
    · have hdiv_lt : (k / 2).toNat < 2^d' := by
        rw [toNat_div2]; have := toNat_ne_zero hk0; omega
      unfold insert; rw [if_neg hk0]
      by_cases hmod : k % 2 = 0
      · simp only [hmod, ↓reduceIte]
        apply mkNode_canonicalAux d'
        · exact ih (k/2) hdiv_lt t.lc
            (by cases t with | empty => trivial | node v l r => exact ht.2.2.1)
        · rw [insert_nodeVal_of_ne _ _ _ (div2_ne_zero_of_even_ne hk0 hmod)]
          cases t with | empty => rfl | node v l r => exact ht.2.1
        · cases t with | empty => trivial | node v l r => exact ht.2.2.2
      · simp only [show k % 2 ≠ 0 from hmod, ↓reduceIte]
        apply mkNode_canonicalAux d'
        · cases t with | empty => trivial | node v l r => exact ht.2.2.1
        · cases t with | empty => rfl | node v l r => exact ht.2.1
        · exact ih (k/2) hdiv_lt t.rc
            (by cases t with | empty => trivial | node v l r => exact ht.2.2.2)

theorem insert_canonical (t : Raw V) (ht : t.canonical) (k : UInt32) (v : V) :
    (t.insert k v).canonical := by
  apply insert_canonicalAux v 32 k _ t ht
  have h := k.toNat_lt; simp only [UInt32.size] at h
  have h32 : (2:Nat)^32 = 4294967296 := by native_decide
  omega

-- ─── delete preserves canonicity ─────────────────────────────────────────────

private theorem delete_canonicalAux :
    ∀ (d : Nat) (k : UInt32), k.toNat < 2^d →
    ∀ (t : Raw V), t.canonicalAux d → (t.delete k).canonicalAux d := by
  intro d; induction d with
  | zero =>
    intro k hk t ht
    have hk0 : k = 0 := UInt32.toNat.inj (by
      simp only [show (0:UInt32).toNat = 0 from rfl]
      simp only [Nat.pow_zero] at hk; omega)
    subst hk0; simp only [delete, ↓reduceIte]
    cases t with
    | empty => trivial
    | node v' l r =>
      obtain ⟨_, hl, hr⟩ := ht; subst hl; subst hr
      simp [canonicalAux]
  | succ d' ih =>
    intro k hk t ht
    by_cases hk0 : k = 0
    · subst hk0; simp only [delete, ↓reduceIte]
      apply mkNode_canonicalAux d'
      · cases t with | empty => trivial | node v l r => exact ht.2.2.1
      · cases t with | empty => rfl | node v l r => exact ht.2.1
      · cases t with | empty => trivial | node v l r => exact ht.2.2.2
    · have hdiv_lt : (k / 2).toNat < 2^d' := by
        rw [toNat_div2]; have := toNat_ne_zero hk0; omega
      unfold delete; rw [if_neg hk0]
      by_cases hmod : k % 2 = 0
      · simp only [hmod, ↓reduceIte]
        apply mkNode_canonicalAux d'
        · exact ih (k/2) hdiv_lt t.lc
            (by cases t with | empty => trivial | node v l r => exact ht.2.2.1)
        · rw [delete_nodeVal_of_ne _ _ (div2_ne_zero_of_even_ne hk0 hmod)]
          cases t with | empty => rfl | node v l r => exact ht.2.1
        · cases t with | empty => trivial | node v l r => exact ht.2.2.2
      · simp only [show k % 2 ≠ 0 from hmod, ↓reduceIte]
        apply mkNode_canonicalAux d'
        · cases t with | empty => trivial | node v l r => exact ht.2.2.1
        · cases t with | empty => rfl | node v l r => exact ht.2.1
        · exact ih (k/2) hdiv_lt t.rc
            (by cases t with | empty => trivial | node v l r => exact ht.2.2.2)

theorem delete_canonical (t : Raw V) (ht : t.canonical) (k : UInt32) :
    (t.delete k).canonical := by
  apply delete_canonicalAux 32 k _ t ht
  have h := k.toNat_lt; simp only [UInt32.size] at h
  have h32 : (2:Nat)^32 = 4294967296 := by native_decide
  omega

-- ─── bindAlterAux / mergeAux preserve canonicity ─────────────────────────────

theorem bindAlterAux_nodeVal (f : UInt32 → V → Option V')
    (t : Raw V) (step pfx : UInt32) :
    (t.bindAlterAux f step pfx).nodeVal = (t.nodeVal).bind (f pfx) := by
  cases t with
  | empty => rfl
  | node v l r =>
    simp only [bindAlterAux]
    rw [mkNode_nodeVal]
    simp only [nodeVal]

private theorem bindAlterAux_canonicalAux (f : UInt32 → V → Option V') :
    ∀ (d : Nat) (t : Raw V), t.canonicalAux d → ∀ (step pfx : UInt32),
    (t.bindAlterAux f step pfx).canonicalAux d := by
  intro d; induction d with
  | zero =>
    intro t ht step pfx
    cases t with
    | empty => simp [bindAlterAux, canonicalAux]
    | node v l r =>
      obtain ⟨hv, hl, hr⟩ := ht; subst hl; subst hr
      have step1 : bindAlterAux f (.node v .empty .empty) step pfx =
          mkNode (v.bind (f pfx)) .empty .empty := by unfold bindAlterAux; rfl
      rw [step1]
      rcases v.bind (f pfx) with _ | w
      · simp [mkNode, canonicalAux]
      · exact ⟨by simp, rfl, rfl⟩
  | succ d' ih =>
    intro t ht step pfx
    cases t with
    | empty => simp [bindAlterAux, canonicalAux]
    | node v l r =>
      obtain ⟨_, hlv, hcanl, hcanr⟩ := ht
      simp only [bindAlterAux]
      apply mkNode_canonicalAux d'
      · exact ih l hcanl (step * 2) pfx
      · rw [bindAlterAux_nodeVal, hlv]; rfl
      · exact ih r hcanr (step * 2) (pfx + step)

theorem bindAlterAux_canonical (f : UInt32 → V → Option V')
    (t : Raw V) (ht : t.canonical) (step pfx : UInt32) :
    (t.bindAlterAux f step pfx).canonical :=
  bindAlterAux_canonicalAux f 32 t ht step pfx

theorem mergeAux_nodeVal (op : UInt32 → V → V → V)
    (t1 t2 : Raw V) (step pfx : UInt32) :
    (t1.mergeAux op t2 step pfx).nodeVal =
      Option.merge (op pfx) t1.nodeVal t2.nodeVal := by
  cases t1 with
  | empty => simp [mergeAux, nodeVal]
  | node v l1 r1 =>
    cases t2 with
    | empty => simp [mergeAux, nodeVal]
    | node w l2 r2 => simp only [mergeAux, nodeVal]

private theorem mergeAux_canonicalAux (op : UInt32 → V → V → V) :
    ∀ (d : Nat) (t1 t2 : Raw V),
    t1.canonicalAux d → t2.canonicalAux d → ∀ (step pfx : UInt32),
    (t1.mergeAux op t2 step pfx).canonicalAux d := by
  intro d; induction d with
  | zero =>
    intro t1 t2 ht1 ht2 step pfx
    cases t1 with
    | empty => simp [mergeAux]; exact ht2
    | node v l1 r1 =>
      obtain ⟨hv1, hl1, hr1⟩ := ht1; subst hl1; subst hr1
      cases t2 with
      | empty => simp [mergeAux]; exact ⟨hv1, rfl, rfl⟩
      | node w l2 r2 =>
        obtain ⟨_, hl2, hr2⟩ := ht2; subst hl2; subst hr2
        have step1 : mergeAux op (.node v .empty .empty) (.node w .empty .empty) step pfx =
            mkNode (Option.merge (op pfx) v w) .empty .empty := by rfl
        rw [step1]
        rcases Option.merge (op pfx) v w with _ | u
        · simp [mkNode, canonicalAux]
        · exact ⟨by simp, rfl, rfl⟩
  | succ d' ih =>
    intro t1 t2 ht1 ht2 step pfx
    cases t1 with
    | empty => simp [mergeAux]; exact ht2
    | node v l1 r1 =>
      cases t2 with
      | empty => simp [mergeAux]; exact ht1
      | node w l2 r2 =>
        obtain ⟨_, hlv₁, hcanl₁, hcanr₁⟩ := ht1
        obtain ⟨_, hlv₂, hcanl₂, hcanr₂⟩ := ht2
        simp only [mergeAux]
        apply mkNode_canonicalAux d'
        · exact ih l1 l2 hcanl₁ hcanl₂ (step * 2) pfx
        · rw [mergeAux_nodeVal, hlv₁, hlv₂]; rfl
        · exact ih r1 r2 hcanr₁ hcanr₂ (step * 2) (pfx + step)

theorem mergeAux_canonical (op : UInt32 → V → V → V)
    (t1 t2 : Raw V) (ht1 : t1.canonical) (ht2 : t2.canonical) (step pfx : UInt32) :
    (t1.mergeAux op t2 step pfx).canonical :=
  mergeAux_canonicalAux op 32 t1 t2 ht1 ht2 step pfx

-- ─── canonical_nonempty: every non-empty canonical trie has a populated key ──

private theorem canonical_nonempty_aux :
    ∀ (d : Nat), d ≤ 32 → ∀ (t : Raw V), t.canonicalAux d → t ≠ .empty →
    ∃ j : Nat, j < 2^d ∧ t.get? (UInt32.ofNat j) ≠ none := by
  intro d
  induction d with
  | zero =>
    intro _ t ht hne
    cases t with
    | empty => exact absurd rfl hne
    | node v l r =>
      obtain ⟨hv, hl, hr⟩ := ht; subst hl; subst hr
      exact ⟨0, by omega, by
        have : (UInt32.ofNat 0 : UInt32) = 0 := rfl
        rw [this, get?_node_zero]; exact hv⟩
  | succ d' ih =>
    intro hd t ht hne
    cases t with
    | empty => exact absurd rfl hne
    | node v l r =>
      obtain ⟨hcond, hlv, hcanl, hcanr⟩ := ht
      rcases hcond with hv | hl_ne | hr_ne
      · exact ⟨0, by omega, by
          have : (UInt32.ofNat 0 : UInt32) = 0 := rfl
          rw [this, get?_node_zero]; exact hv⟩
      · obtain ⟨jl, hjl_lt, hjl_ne⟩ := ih (by omega) l hcanl hl_ne
        have h2pow : (2:Nat)^(d'+1) = 2 * 2^d' := by rw [Nat.pow_succ]; exact Nat.mul_comm _ _
        have hjl_sz : jl < UInt32.size := by
          simp only [UInt32.size]
          have hle : 2^d' ≤ 2^32 := Nat.pow_le_pow_right (by omega) (by omega : d' ≤ 32)
          have h32 : (2:Nat)^32 = 4294967296 := by native_decide
          linarith
        have h2jl_lt : 2 * jl < 2^(d'+1) := by omega
        have h2jl_sz : 2 * jl < UInt32.size := by
          simp only [UInt32.size]
          have hle : 2^(d'+1) ≤ 2^32 := Nat.pow_le_pow_right (by omega) hd
          have h32 : (2:Nat)^32 = 4294967296 := by native_decide
          linarith
        refine ⟨2 * jl, h2jl_lt, ?_⟩
        have hk0 : UInt32.ofNat (2 * jl) ≠ 0 := by
          intro h; have h' := congrArg UInt32.toNat h
          rw [ofNat_toNat' h2jl_sz, show (0:UInt32).toNat=0 from rfl] at h'; omega
        rw [get?_node_nz _ _ _ _ hk0]
        have hkmod : UInt32.ofNat (2 * jl) % 2 = 0 := by
          apply UInt32.toNat.inj; rw [toNat_mod2, show (0:UInt32).toNat=0 from rfl,
            ofNat_toNat' h2jl_sz]; omega
        rw [if_pos hkmod]
        have hkdiv : UInt32.ofNat (2 * jl) / 2 = UInt32.ofNat jl := by
          apply UInt32.toNat.inj; rw [toNat_div2, ofNat_toNat' h2jl_sz,
            ofNat_toNat' hjl_sz]; omega
        rw [hkdiv]; exact hjl_ne
      · obtain ⟨jr, hjr_lt, hjr_ne⟩ := ih (by omega) r hcanr hr_ne
        have h2pow : (2:Nat)^(d'+1) = 2 * 2^d' := by rw [Nat.pow_succ]; exact Nat.mul_comm _ _
        have hjr_sz : jr < UInt32.size := by
          simp only [UInt32.size]
          have hle : 2^d' ≤ 2^32 := Nat.pow_le_pow_right (by omega) (by omega : d' ≤ 32)
          have h32 : (2:Nat)^32 = 4294967296 := by native_decide
          linarith
        have h2jr1_lt : 2 * jr + 1 < 2^(d'+1) := by omega
        have h2jr1_sz : 2 * jr + 1 < UInt32.size := by
          simp only [UInt32.size]
          have hle : 2^(d'+1) ≤ 2^32 := Nat.pow_le_pow_right (by omega) hd
          have h32 : (2:Nat)^32 = 4294967296 := by native_decide
          linarith
        refine ⟨2 * jr + 1, h2jr1_lt, ?_⟩
        have hk0 : UInt32.ofNat (2 * jr + 1) ≠ 0 := by
          intro h; have h' := congrArg UInt32.toNat h
          rw [ofNat_toNat' h2jr1_sz, show (0:UInt32).toNat=0 from rfl] at h'; omega
        rw [get?_node_nz _ _ _ _ hk0]
        have hkmod : UInt32.ofNat (2 * jr + 1) % 2 ≠ 0 := by
          intro h; have h' := congrArg UInt32.toNat h
          rw [toNat_mod2, show (0:UInt32).toNat=0 from rfl, ofNat_toNat' h2jr1_sz] at h'; omega
        rw [if_neg hkmod]
        have hkdiv : UInt32.ofNat (2 * jr + 1) / 2 = UInt32.ofNat jr := by
          apply UInt32.toNat.inj; rw [toNat_div2, ofNat_toNat' h2jr1_sz,
            ofNat_toNat' hjr_sz]; omega
        rw [hkdiv]; exact hjr_ne

theorem canonical_nonempty (t : Raw V) (ht : t.canonical) (hne : t ≠ .empty) :
    ∃ k, t.get? k ≠ none :=
  let ⟨j, _, hjne⟩ := canonical_nonempty_aux 32 (by omega) t ht hne
  ⟨UInt32.ofNat j, hjne⟩

-- ─── Extensionality for canonical tries ───────────────────────────────────────

private theorem canonical_equiv_implies_eq_aux :
    ∀ (d : Nat), d ≤ 32 → ∀ (t₁ t₂ : Raw V),
    t₁.canonicalAux d → t₂.canonicalAux d →
    (∀ j : Nat, j < 2^d → t₁.get? (UInt32.ofNat j) = t₂.get? (UInt32.ofNat j)) →
    t₁ = t₂ := by
  intro d
  induction d with
  | zero =>
    intro _ t₁ t₂ ht₁ ht₂ heq
    cases t₁ with
    | empty =>
      cases t₂ with
      | empty => rfl
      | node v₂ l₂ r₂ =>
        obtain ⟨hv₂, _, _⟩ := ht₂
        have h := heq 0 (by omega)
        have hzero : (UInt32.ofNat 0 : UInt32) = 0 := rfl
        rw [hzero, get?_empty, get?_node_zero] at h
        exact absurd h.symm hv₂
    | node v₁ l₁ r₁ =>
      obtain ⟨hv₁, hl₁, hr₁⟩ := ht₁; subst hl₁; subst hr₁
      cases t₂ with
      | empty =>
        have h := heq 0 (by omega)
        have hzero : (UInt32.ofNat 0 : UInt32) = 0 := rfl
        rw [hzero, get?_empty, get?_node_zero] at h
        exact absurd h hv₁
      | node v₂ l₂ r₂ =>
        obtain ⟨_, hl₂, hr₂⟩ := ht₂; subst hl₂; subst hr₂
        have hv : v₁ = v₂ := by
          have h := heq 0 (by omega)
          have hzero : (UInt32.ofNat 0 : UInt32) = 0 := rfl
          rw [hzero, get?_node_zero, get?_node_zero] at h; exact h
        subst hv; rfl
  | succ d' ih =>
    intro hd t₁ t₂ ht₁ ht₂ heq
    cases t₁ with
    | empty =>
      cases t₂ with
      | empty => rfl
      | node v₂ l₂ r₂ =>
        exfalso
        obtain ⟨j, hj_lt, hj_ne⟩ := canonical_nonempty_aux (d'+1) hd (.node v₂ l₂ r₂) ht₂ (by simp)
        have h := heq j hj_lt
        simp only [get?_empty] at h
        exact hj_ne h.symm
    | node v₁ l₁ r₁ =>
      obtain ⟨hcond₁, hlv₁, hcanl₁, hcanr₁⟩ := ht₁
      cases t₂ with
      | empty =>
        exfalso
        obtain ⟨j, hj_lt, hj_ne⟩ := canonical_nonempty_aux (d'+1) hd (.node v₁ l₁ r₁) ⟨hcond₁, hlv₁, hcanl₁, hcanr₁⟩ (by simp)
        have h := heq j hj_lt
        simp only [get?_empty] at h
        exact hj_ne h
      | node v₂ l₂ r₂ =>
        obtain ⟨_, hlv₂, hcanl₂, hcanr₂⟩ := ht₂
        have hd' : d' ≤ 32 := by omega
        have hv : v₁ = v₂ := by
          have h := heq 0 (by omega)
          have hzero : (UInt32.ofNat 0 : UInt32) = 0 := rfl
          rw [hzero, get?_node_zero, get?_node_zero] at h; exact h
        have hl : l₁ = l₂ := ih hd' l₁ l₂ hcanl₁ hcanl₂ (fun j hj => by
          by_cases hj0 : j = 0
          · subst hj0
            have hzero : (UInt32.ofNat 0 : UInt32) = 0 := rfl
            simp only [hzero, get?_zero, hlv₁, hlv₂]
          · have h2pow : (2:Nat)^(d'+1) = 2 * 2^d' := by rw [Nat.pow_succ]; exact Nat.mul_comm _ _
            have h2j_lt : 2 * j < 2^(d'+1) := by omega
            have hj_sz : j < UInt32.size := by
              simp only [UInt32.size]
              have hle : 2^d' ≤ 2^32 := Nat.pow_le_pow_right (by omega) hd'
              have h32 : (2:Nat)^32 = 4294967296 := by native_decide
              linarith
            have h2j_sz : 2 * j < UInt32.size := by
              simp only [UInt32.size]
              have hle : 2^(d'+1) ≤ 2^32 := Nat.pow_le_pow_right (by omega) hd
              have h32 : (2:Nat)^32 = 4294967296 := by native_decide
              linarith
            have hne0 : UInt32.ofNat (2 * j) ≠ 0 := by
              intro h; have h' := congrArg UInt32.toNat h
              rw [ofNat_toNat' h2j_sz, show (0:UInt32).toNat=0 from rfl] at h'; omega
            have hmod : UInt32.ofNat (2 * j) % 2 = 0 := by
              apply UInt32.toNat.inj; rw [toNat_mod2, show (0:UInt32).toNat=0 from rfl,
                ofNat_toNat' h2j_sz]; omega
            have hdiv : UInt32.ofNat (2 * j) / 2 = UInt32.ofNat j := by
              apply UInt32.toNat.inj; rw [toNat_div2, ofNat_toNat' h2j_sz, ofNat_toNat' hj_sz]
              omega
            have h2j := heq (2 * j) h2j_lt
            rw [get?_node_nz v₁ l₁ r₁ _ hne0, get?_node_nz v₂ l₂ r₂ _ hne0,
                if_pos hmod, if_pos hmod, hdiv, hdiv] at h2j
            exact h2j)
        have hr : r₁ = r₂ := ih hd' r₁ r₂ hcanr₁ hcanr₂ (fun j hj => by
          have h2pow : (2:Nat)^(d'+1) = 2 * 2^d' := by rw [Nat.pow_succ]; exact Nat.mul_comm _ _
          have h2j1_lt : 2 * j + 1 < 2^(d'+1) := by omega
          have hj_sz : j < UInt32.size := by
            simp only [UInt32.size]
            have hle : 2^d' ≤ 2^32 := Nat.pow_le_pow_right (by omega) hd'
            have h32 : (2:Nat)^32 = 4294967296 := by native_decide
            linarith
          have h2j1_sz : 2 * j + 1 < UInt32.size := by
            simp only [UInt32.size]
            have hle : 2^(d'+1) ≤ 2^32 := Nat.pow_le_pow_right (by omega) hd
            have h32 : (2:Nat)^32 = 4294967296 := by native_decide
            linarith
          have hne0 : UInt32.ofNat (2 * j + 1) ≠ 0 := by
            intro h; have h' := congrArg UInt32.toNat h
            rw [ofNat_toNat' h2j1_sz, show (0:UInt32).toNat=0 from rfl] at h'; omega
          have hmod : UInt32.ofNat (2 * j + 1) % 2 ≠ 0 := by
            intro h; have h' := congrArg UInt32.toNat h
            rw [toNat_mod2, show (0:UInt32).toNat=0 from rfl, ofNat_toNat' h2j1_sz] at h'; omega
          have hdiv : UInt32.ofNat (2 * j + 1) / 2 = UInt32.ofNat j := by
            apply UInt32.toNat.inj; rw [toNat_div2, ofNat_toNat' h2j1_sz, ofNat_toNat' hj_sz]
            omega
          have h2j1 := heq (2 * j + 1) h2j1_lt
          rw [get?_node_nz v₁ l₁ r₁ _ hne0, get?_node_nz v₂ l₂ r₂ _ hne0,
              if_neg hmod, if_neg hmod, hdiv, hdiv] at h2j1
          exact h2j1)
        subst hv; subst hl; subst hr; rfl

theorem canonical_equiv_implies_eq (t₁ : Raw V) :
    ∀ t₂ : Raw V, t₁.canonical → t₂.canonical →
      (∀ k, t₁.get? k = t₂.get? k) → t₁ = t₂ :=
  fun t₂ h₁ h₂ heq =>
    canonical_equiv_implies_eq_aux 32 (by omega) t₁ t₂ h₁ h₂ (fun j _ => heq (UInt32.ofNat j))

-- ─── toListAux correctness ────────────────────────────────────────────────────

-- Key bounds lemmas
private theorem ofNat_lt_size {d j : Nat} (_ : d ≤ 32) (hj : j < 2^(32-d)) :
    j < UInt32.size := by
  simp only [UInt32.size]
  calc j < 2^(32-d) := hj
    _ ≤ 2^32 := Nat.pow_le_pow_right (by omega) (Nat.sub_le 32 d)

private theorem j_pow_lt_size {d j : Nat} (hd : d ≤ 32) (hj : j < 2^(32-d)) :
    j * 2^d < UInt32.size := by
  simp only [UInt32.size]
  have := @Nat.pow_le_pow_right 2 (by omega) (32-d) d (Nat.le_refl _)
  have h : 2^(32-d) * 2^d = 2^32 := by
    rw [← Nat.pow_add]; congr 1; omega
  linarith [Nat.mul_lt_mul_right (Nat.two_pow_pos d) hj, show (2:Nat)^32 = 4294967296 from by native_decide]

private theorem pfx_j_pow_lt_size {d j : Nat} (hd : d ≤ 32) (hj : j < 2^(32-d))
    (pfx : UInt32) (hpfx : pfx.toNat < 2^d) :
    pfx.toNat + j * 2^d < UInt32.size := by
  simp only [UInt32.size]
  have hj2 : j * 2^d ≤ 2^32 - 2^d := by
    have h2eq : 2^(32-d) * 2^d = 2^32 := by rw [← Nat.pow_add]; congr 1; omega
    have := Nat.mul_le_mul_right (2^d) (Nat.lt_iff_add_one_le.mp hj)
    simp only [Nat.pow_add] at *; omega
  have := Nat.two_pow_pos d
  omega

private theorem ofNat_toNat' {n : Nat} (h : n < UInt32.size) :
    (UInt32.ofNat n).toNat = n := by
  simp [Nat.mod_eq_of_lt h]

private theorem ofNat_add_no_overflow {a b : Nat} (h : a + b < UInt32.size) :
    (UInt32.ofNat a + UInt32.ofNat b).toNat = a + b := by
  rw [UInt32.toNat_add, ofNat_toNat' (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h),
      ofNat_toNat' (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h), Nat.mod_eq_of_lt h]

private theorem ofNat_pow_d_lt_size {d : Nat} (hd : d < 32) : 2^d < UInt32.size := by
  simp only [UInt32.size]; exact Nat.pow_lt_pow_right (by omega) (by omega)

-- Key: (k, v) ∈ toListAux t d pfx skip ↔ ∃ j < 2^(32-d), (skip → j≠0)
--      ∧ k.toNat = pfx.toNat + j * 2^d ∧ t.get? (UInt32.ofNat j) = some v
-- (Under conditions: d ≤ 32, pfx.toNat < 2^d)
private theorem mem_toListAux_iff (t : Raw V) :
    ∀ d, d ≤ 32 → ∀ (pfx : UInt32), pfx.toNat < 2^d → ∀ (skip : Bool) (k : UInt32) (v : V),
    (k, v) ∈ t.toListAux d pfx skip ↔
    ∃ j : Nat, j < 2^(32-d) ∧ (skip → j ≠ 0) ∧
      k.toNat = pfx.toNat + j * 2^d ∧ t.get? (UInt32.ofNat j) = some v := by
  induction t with
  | empty =>
    intro d _ pfx _ skip k v
    simp [toListAux, get?_empty]
  | node o l r ih_l ih_r =>
    intro d hd pfx hpfx skip k v
    simp only [toListAux, List.mem_append]
    -- Root part: (k,v) in root ↔ ¬skip ∧ o = some v ∧ k = pfx (j=0 case)
    -- Child parts (when d < 32): left at d+1 pfx true, right at d+1 (pfx+2^d) false
    constructor
    · rintro (hroot | hchild)
      · -- Root
        cases hskip : skip with
        | true => simp [hskip] at hroot
        | false =>
          simp only [hskip] at hroot
          cases ho : o with
          | none => simp [ho] at hroot
          | some u =>
            simp only [ho] at hroot
            obtain ⟨rfl, rfl⟩ := hroot
            refine ⟨0, Nat.two_pow_pos _, by simp, by simp, ?_⟩
            simp [get?_node_zero, ho]
      · -- Children
        by_cases hge : d ≥ 32
        · simp [if_pos hge] at hchild
        · simp only [if_neg hge] at hchild
          simp only [List.mem_append] at hchild
          have hd32 : d < 32 := by omega
          rcases hchild with hmem | hmem
          · -- Left subtrie: d+1, pfx, skip=true
            rw [ih_l (d+1) (by omega) pfx (by omega) true k v] at hmem
            obtain ⟨jl, hjl, hskipl, hkl, hgetl⟩ := hmem
            have hjl_ne0 : jl ≠ 0 := hskipl (by rfl)
            -- parent j = 2*jl (even nonzero)
            have h2jl_lt : 2 * jl < 2^(32-d) := by
              have h2pow : 2^(32-d) = 2 * 2^(32-d-1) := by
                rw [show 32-d = 32-d-1+1 from by omega, Nat.pow_add, Nat.pow_one]
              omega
            refine ⟨2 * jl, h2jl_lt, by simp, ?_, ?_⟩
            · -- k.toNat = pfx.toNat + (2*jl) * 2^d
              have h2jl_pow : 2 * jl * 2^d = jl * 2^(d+1) := by
                rw [Nat.pow_succ, Nat.mul_comm (2^d) 2, ← Nat.mul_assoc jl 2 (2^d), Nat.mul_comm jl 2]
              have hno_ov : pfx.toNat + jl * 2^(d+1) < UInt32.size := by
                apply pfx_j_pow_lt_size (by omega) hjl pfx (by omega)
              rw [h2jl_pow]
              have hkl_eq : k.toNat = pfx.toNat + jl * 2^(d+1) := hkl
              exact hkl_eq
            · -- get?
              rw [get?_node_nz]
              · have hmod : UInt32.ofNat (2 * jl) % 2 = 0 := by
                  apply UInt32.toNat.inj; rw [toNat_mod2, show (0:UInt32).toNat=0 from rfl]
                  have h2jl_sz : 2 * jl < UInt32.size := ofNat_lt_size hd h2jl_lt
                  rw [ofNat_toNat' h2jl_sz]; omega
                have hdiv : UInt32.ofNat (2 * jl) / 2 = UInt32.ofNat jl := by
                  apply UInt32.toNat.inj; rw [toNat_div2]
                  have h2jl_sz : 2 * jl < UInt32.size := ofNat_lt_size hd h2jl_lt
                  have hjl_sz : jl < UInt32.size := ofNat_lt_size (by omega) hjl
                  rw [ofNat_toNat' h2jl_sz, ofNat_toNat' hjl_sz]; omega
                rw [if_pos hmod, hdiv]; exact hgetl
              · intro h; apply UInt32.toNat.inj at h
                have h2jl_sz : 2 * jl < UInt32.size := ofNat_lt_size hd h2jl_lt
                rw [ofNat_toNat' h2jl_sz, show (0:UInt32).toNat=0 from rfl] at h
                omega
          · -- Right subtrie: d+1, pfx+2^d, skip=false
            have h2d_sz : 2^d < UInt32.size := ofNat_pow_d_lt_size hd32
            have hpfx_new : (pfx + UInt32.ofNat (2^d)).toNat = pfx.toNat + 2^d := by
              rw [UInt32.toNat_add, ofNat_toNat' h2d_sz]
              have := pfx.toNat_lt; simp only [UInt32.size] at *; omega
            rw [ih_r (d+1) (by omega) (pfx + UInt32.ofNat (2^d)) (by rw [hpfx_new]; omega)
                false k v] at hmem
            obtain ⟨jr, hjr, _, hkr, hgetr⟩ := hmem
            -- parent j = 2*jr+1 (odd)
            have h2jr1_lt : 2 * jr + 1 < 2^(32-d) := by
              have h2pow : 2^(32-d) = 2 * 2^(32-d-1) := by
                rw [show 32-d = 32-d-1+1 from by omega, Nat.pow_add, Nat.pow_one]
              omega
            refine ⟨2 * jr + 1, h2jr1_lt, by simp, ?_, ?_⟩
            · -- k.toNat = pfx.toNat + (2*jr+1) * 2^d
              rw [hpfx_new] at hkr
              rw [hkr]
              have h2pow : (2:Nat)^(d+1) = 2 * 2^d := by rw [Nat.pow_succ]; exact Nat.mul_comm _ _
              have h_jr : jr * 2^(d+1) = 2 * jr * 2^d := by
                rw [h2pow, ← Nat.mul_assoc jr 2 (2^d), Nat.mul_comm jr 2]
              have h_factor : (2 * jr + 1) * 2^d = 2 * jr * 2^d + 2^d := by
                rw [Nat.add_mul, Nat.one_mul]
              linarith
            · -- get?
              rw [get?_node_nz]
              · have hmod : UInt32.ofNat (2 * jr + 1) % 2 ≠ 0 := by
                  intro h; apply UInt32.toNat.inj at h
                  have h_sz : 2 * jr + 1 < UInt32.size := ofNat_lt_size hd h2jr1_lt
                  rw [toNat_mod2, ofNat_toNat' h_sz, show (0:UInt32).toNat=0 from rfl] at h
                  omega
                have hdiv : UInt32.ofNat (2 * jr + 1) / 2 = UInt32.ofNat jr := by
                  apply UInt32.toNat.inj; rw [toNat_div2]
                  have h_sz : 2 * jr + 1 < UInt32.size := ofNat_lt_size hd h2jr1_lt
                  have hjr_sz : jr < UInt32.size := ofNat_lt_size (by omega) hjr
                  rw [ofNat_toNat' h_sz, ofNat_toNat' hjr_sz]; omega
                rw [if_neg hmod, hdiv]; exact hgetr
              · intro h; apply UInt32.toNat.inj at h
                have h_sz : 2 * jr + 1 < UInt32.size := ofNat_lt_size hd h2jr1_lt
                rw [ofNat_toNat' h_sz, show (0:UInt32).toNat=0 from rfl] at h; omega
    · intro ⟨j, hjlt, hskip_j, hknat, hget⟩
      -- Which part does j belong to?
      by_cases hj0 : j = 0
      · subst hj0
        simp only [Nat.zero_mul, Nat.add_zero, Nat.mul_zero] at hknat
        -- k = pfx (from k.toNat = pfx.toNat + 0)
        have hkpfx : k = pfx := UInt32.toNat.inj (by simp [hknat])
        -- get? (ofNat 0) = o = some v
        have hojv : o = some v := by
          simp [get?_node_zero] at hget; exact hget
        left  -- go to root part
        cases hskp : skip with
        | true => exact absurd hj0 (hskip_j rfl)
        | false =>
          simp only [hskp, ↓reduceIte, hojv, List.mem_singleton, Prod.mk.injEq]
          exact ⟨hkpfx, rfl⟩
      · -- j > 0: go to children
        right
        have hd32 : d < 32 := by
          by_contra hge
          simp only [not_lt] at hge
          -- j < 2^(32-d) with d ≥ 32 means j < 1, i.e., j = 0, contradiction
          have : 2^(32-d) ≤ 1 := by
            cases Nat.eq_or_gt_of_le (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hjlt (by omega))) with
            | inl h => exact h ▸ le_refl _
            | inr h => exact absurd h (Nat.not_lt.mpr (Nat.one_le_iff_ne_zero.mpr (fun e => by simp [e] at hjlt; omega)))
          omega
        simp only [if_neg (show ¬ d ≥ 32 from by omega), List.mem_append]
        have h2d_sz : 2^d < UInt32.size := ofNat_pow_d_lt_size hd32
        have hj_sz : j < UInt32.size := ofNat_lt_size hd hjlt
        -- get? (ofNat j) with j ≠ 0: depends on parity
        rw [get?_node_nz] at hget
        · by_cases hmod : j % 2 = 0
          · -- j even, j ≥ 2: left subtrie with jl = j/2
            simp only [if_pos (show UInt32.ofNat j % 2 = 0 from by
              apply UInt32.toNat.inj; rw [toNat_mod2, show (0:UInt32).toNat=0 from rfl]
              rw [ofNat_toNat' hj_sz]; exact hmod)] at hget
            have hkdiv : UInt32.ofNat j / 2 = UInt32.ofNat (j / 2) := by
              apply UInt32.toNat.inj; rw [toNat_div2, ofNat_toNat' hj_sz, ofNat_toNat']
              exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hj_sz
            rw [hkdiv] at hget
            set jl := j / 2
            have hjl_ne0 : jl ≠ 0 := by
              intro h; rw [h, Nat.zero_div] at *; omega
            have hjl_lt : jl < 2^(32-(d+1)) := by
              have h2pow : 2^(32-d) = 2 * 2^(32-d-1) := by
                rw [show 32-d = 32-d-1+1 from by omega, Nat.pow_add, Nat.pow_one]
              rw [show 32-(d+1) = 32-d-1 from by omega]
              have hj2 := Nat.div_lt_iff_lt_mul (Nat.two_pos) |>.mpr (by rw [← h2pow]; exact hjlt)
              exact hj2
            have hknat_l : k.toNat = pfx.toNat + jl * 2^(d+1) := by
              rw [hknat, show 32-d = 32-d-1+1 from by omega] at *
              simp only [Nat.pow_add, Nat.pow_one] at hknat
              have : j * 2^d = jl * (2^d * 2) := by
                simp [jl]; rw [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)]
                ring
              linarith [this.symm]
            left
            rw [ih_l (d+1) (by omega) pfx (by omega) true k v]
            exact ⟨jl, hjl_lt, fun _ => hjl_ne0, hknat_l, hget⟩
          · -- j odd: right subtrie with jr = j/2
            simp only [if_neg (show UInt32.ofNat j % 2 ≠ 0 from by
              intro h; apply UInt32.toNat.inj at h
              rw [toNat_mod2, ofNat_toNat' hj_sz, show (0:UInt32).toNat=0 from rfl] at h
              exact hmod h)] at hget
            have hkdiv : UInt32.ofNat j / 2 = UInt32.ofNat (j / 2) := by
              apply UInt32.toNat.inj; rw [toNat_div2, ofNat_toNat' hj_sz, ofNat_toNat']
              exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hj_sz
            rw [hkdiv] at hget
            set jr := j / 2
            have hjr_lt : jr < 2^(32-(d+1)) := by
              rw [show 32-(d+1) = 32-d-1 from by omega]
              have h2pow : 2^(32-d) = 2 * 2^(32-d-1) := by
                rw [show 32-d = 32-d-1+1 from by omega, Nat.pow_add, Nat.pow_one]
              have : j = 2 * jr + 1 := by
                simp [jr]; omega
              omega
            have hpfx_new : (pfx + UInt32.ofNat (2^d)).toNat = pfx.toNat + 2^d := by
              rw [UInt32.toNat_add, ofNat_toNat' h2d_sz]
              have := pfx.toNat_lt; simp only [UInt32.size] at *; omega
            have hknat_r : k.toNat = (pfx + UInt32.ofNat (2^d)).toNat + jr * 2^(d+1) := by
              rw [hpfx_new, hknat]
              have hjodd : j = 2 * jr + 1 := by simp [jr]; omega
              rw [hjodd]; ring
            right
            rw [ih_r (d+1) (by omega) (pfx + UInt32.ofNat (2^d)) (by rw [hpfx_new]; omega)
                false k v]
            exact ⟨jr, hjr_lt, by simp, hknat_r, hget⟩
        · -- j ≠ 0 as UInt32
          intro h; apply UInt32.toNat.inj at h
          rw [ofNat_toNat' hj_sz, show (0:UInt32).toNat=0 from rfl] at h
          exact hj0 h

-- toListAux has no duplicate pairs
private theorem toListAux_nodup (t : Raw V) :
    ∀ d, d ≤ 32 → ∀ (pfx : UInt32), pfx.toNat < 2^d → ∀ (skip : Bool),
    (t.toListAux d pfx skip).Nodup := by
  induction t with
  | empty => intro d _ pfx _ skip; simp [toListAux]
  | node o l r ih_l ih_r =>
    intro d hd pfx hpfx skip
    simp only [toListAux]
    by_cases hge : d ≥ 32
    · simp only [if_pos hge, List.append_nil]
      cases skip with
      | true => exact List.nodup_nil
      | false => cases o <;> simp
    · simp only [if_neg hge]
      have hd32 : d < 32 := by omega
      have h2d_sz : 2^d < UInt32.size := ofNat_pow_d_lt_size hd32
      have hpfx_new : (pfx + UInt32.ofNat (2^d)).toNat = pfx.toNat + 2^d := by
        rw [UInt32.toNat_add, ofNat_toNat' h2d_sz]
        have := pfx.toNat_lt; simp only [UInt32.size] at *; omega
      rw [show (if skip then [] else match o with | none => [] | some u => [(pfx, u)]) ++
           (l.toListAux (d+1) pfx true ++ r.toListAux (d+1) (pfx + UInt32.ofNat (2^d)) false) =
           (if skip then [] else match o with | none => [] | some u => [(pfx, u)]) ++
           l.toListAux (d+1) pfx true ++
           r.toListAux (d+1) (pfx + UInt32.ofNat (2^d)) false from by rw [List.append_assoc]]
      rw [List.nodup_append, List.nodup_append]
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · -- root part nodup
        cases skip with
        | true => exact List.nodup_nil
        | false => cases o <;> simp
      · -- left nodup
        exact ih_l (d+1) (by omega) pfx (by omega) true
      · -- root and left are disjoint
        intro ⟨k₁, v₁⟩ hkv₁ ⟨k₂, v₂⟩ hkv₂ heq
        simp only at heq; subst heq
        cases hskp : skip with
        | true => simp [hskp] at hkv₁
        | false =>
          simp only [hskp, ↓reduceIte] at hkv₁
          cases ho : o with
          | none => simp [ho] at hkv₁
          | some u =>
            simp only [ho, List.mem_singleton, Prod.mk.injEq] at hkv₁
            obtain ⟨rfl, rfl⟩ := hkv₁
            rw [ih_l (d+1) (by omega) pfx (by omega) true k₂ v₂] at hkv₂
            obtain ⟨jl, hjl, hskipl, hknat, _⟩ := hkv₂
            have hjl_ne0 := hskipl (by rfl)
            -- k₁ = pfx: k₂.toNat = pfx.toNat + jl * 2^(d+1) with jl ≥ 1
            have : k₂.toNat > pfx.toNat := by
              rw [hknat]; have := Nat.two_pow_pos (d+1); omega
            -- But k₁ = pfx = k₂ from heq... but k₁.toNat = pfx.toNat and k₂.toNat > pfx.toNat
            have hk12 : k₁.toNat = k₂.toNat := by rfl  -- k₁ = k₂ from heq
            linarith [show k₁.toNat = pfx.toNat from by simp]
      · -- right nodup
        exact ih_r (d+1) (by omega) (pfx + UInt32.ofNat (2^d)) (by rw [hpfx_new]; omega) false
      · -- (root ++ left) and right are disjoint
        intro ⟨k₁, v₁⟩ hkv₁ ⟨k₂, v₂⟩ hkv₂ heq
        simp only at heq; subst heq
        simp only [List.mem_append] at hkv₁
        rw [ih_r (d+1) (by omega) (pfx + UInt32.ofNat (2^d)) (by rw [hpfx_new]; omega)
            false k₂ v₂] at hkv₂
        obtain ⟨jr, hjr, _, hknat_r, _⟩ := hkv₂
        -- k₂.toNat = pfx.toNat + 2^d + jr * 2^(d+1)
        rw [hpfx_new] at hknat_r
        -- k₂.toNat ≡ pfx.toNat + 2^d (mod 2^(d+1)), i.e., odd multiple of 2^d after pfx
        -- But elements from root have k.toNat = pfx.toNat (j=0)
        -- Elements from left have k.toNat = pfx.toNat + jl * 2^(d+1) (even multiple after pfx)
        -- These differ from right (odd multiple + 2^d after pfx) by parity mod 2^(d+1)
        -- Key parity: (k₂.toNat - pfx.toNat) mod 2^(d+1) = 2^d ≠ 0
        -- For root: (k₁.toNat - pfx.toNat) mod 2^(d+1) = 0 mod 2^(d+1)
        -- For left: (k₁.toNat - pfx.toNat) mod 2^(d+1) = (jl * 2^(d+1)) mod 2^(d+1) = 0
        -- Contradiction since 2^d ≠ 0 and 0 ≠ 2^d mod 2^(d+1) = 2^d
        rcases hkv₁ with hkv₁_root | hkv₁_left
        · -- root: k₁ = pfx
          cases hskp : skip with
          | true => simp [hskp] at hkv₁_root
          | false =>
            simp only [hskp, ↓reduceIte] at hkv₁_root
            cases ho : o with
            | none => simp [ho] at hkv₁_root
            | some u =>
              simp only [ho, List.mem_singleton, Prod.mk.injEq] at hkv₁_root
              obtain ⟨rfl, _⟩ := hkv₁_root
              -- k₁ = pfx, k₂ = k₁ means pfx.toNat = pfx.toNat + 2^d + jr * 2^(d+1)
              have := Nat.two_pow_pos d; omega
        · -- left: k₁.toNat = pfx.toNat + jl * 2^(d+1)
          rw [ih_l (d+1) (by omega) pfx (by omega) true k₂ v₁] at hkv₁_left
          obtain ⟨jl, hjl, _, hknat_l, _⟩ := hkv₁_left
          -- k₁.toNat = k₂.toNat (since k₁ = k₂)
          -- pfx.toNat + jl * 2^(d+1) = pfx.toNat + 2^d + jr * 2^(d+1)
          -- jl * 2^(d+1) = 2^d + jr * 2^(d+1)
          -- (jl - jr) * 2^(d+1) = 2^d  (or the signed version)
          -- 2^d divides both sides, so 2 * (jl - jr) = 1 → impossible (parity)
          have heqnat : jl * 2^(d+1) = 2^d + jr * 2^(d+1) := by omega
          have := Nat.two_pow_pos d
          have := Nat.two_pow_pos (d+1)
          -- 2^(d+1) = 2 * 2^d, so jl * 2 * 2^d = 2^d + jr * 2 * 2^d
          -- 2^d * (2*jl) = 2^d * (1 + 2*jr) → 2*jl = 1 + 2*jr (impossible)
          have h2d : 2^(d+1) = 2 * 2^d := by rw [Nat.pow_add, Nat.pow_one]
          rw [h2d] at heqnat
          have hmod2 : (2 * jl) * 2^d = (1 + 2 * jr) * 2^d := by linarith
          have hfact := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos d) hmod2
          omega  -- 2*jl = 1 + 2*jr has no nat solution

end Raw

-- ─── Public PosTrie type ─────────────────────────────────────────────────────

def PosTrie (V : Type) := {t : Raw V // t.canonical}

namespace PosTrie

variable {V V' : Type}

def empty : PosTrie V := ⟨.empty, Raw.canonical_empty⟩

def get? (t : PosTrie V) (k : UInt32) : Option V := t.val.get? k

def insert (t : PosTrie V) (k : UInt32) (v : V) : PosTrie V :=
  ⟨t.val.insert k v, Raw.insert_canonical t.val t.property k v⟩

def delete (t : PosTrie V) (k : UInt32) : PosTrie V :=
  ⟨t.val.delete k, Raw.delete_canonical t.val t.property k⟩

def bindAlter (f : UInt32 → V → Option V') (t : PosTrie V) : PosTrie V' :=
  ⟨t.val.bindAlter f, Raw.bindAlterAux_canonical f t.val t.property 1 0⟩

def merge (op : UInt32 → V → V → V) (t1 t2 : PosTrie V) : PosTrie V :=
  ⟨t1.val.mergeAux op t2.val 1 0,
   Raw.mergeAux_canonical op t1.val t2.val t1.property t2.property 1 0⟩

def toList (t : PosTrie V) : List (UInt32 × V) := t.val.toList

-- ─── API theorems ─────────────────────────────────────────────────────────────

@[simp] theorem get?_empty (k : UInt32) : (PosTrie.empty : PosTrie V).get? k = none := rfl

theorem get?_insert (t : PosTrie V) (k k' : UInt32) (v : V) :
    (t.insert k v).get? k' = if k = k' then some v else t.get? k' :=
  Raw.get?_insert t.val k k' v

theorem get?_insert_eq (t : PosTrie V) (k : UInt32) (v : V) :
    (t.insert k v).get? k = some v := by simp [get?_insert]

theorem get?_insert_ne (t : PosTrie V) (k k' : UInt32) (v : V) (h : k ≠ k') :
    (t.insert k v).get? k' = t.get? k' := by simp [get?_insert, h]

theorem get?_delete (t : PosTrie V) (k k' : UInt32) :
    (t.delete k).get? k' = if k = k' then none else t.get? k' :=
  Raw.get?_delete t.val k k'

theorem get?_delete_eq (t : PosTrie V) (k : UInt32) : (t.delete k).get? k = none := by
  simp [get?_delete]

theorem get?_delete_ne (t : PosTrie V) (k k' : UInt32) (h : k ≠ k') :
    (t.delete k).get? k' = t.get? k' := by simp [get?_delete, h]

theorem get?_bindAlter (f : UInt32 → V → Option V') (t : PosTrie V) (k : UInt32) :
    (t.bindAlter f).get? k = (t.get? k).bind (f k) :=
  Raw.get?_bindAlter f t.val k

theorem get?_merge (op : UInt32 → V → V → V) (t1 t2 : PosTrie V) (k : UInt32) :
    (t1.merge op t2).get? k = Option.merge (op k) (t1.get? k) (t2.get? k) :=
  Raw.get?_merge op t1.val t2.val k

-- ─── Extensionality ──────────────────────────────────────────────────────────

theorem equiv_iff_eq {m₁ m₂ : PosTrie V} :
    (∀ k, m₁.get? k = m₂.get? k) ↔ m₁ = m₂ := by
  constructor
  · intro heq
    exact Subtype.ext (Raw.canonical_equiv_implies_eq m₁.val m₂.val m₁.property m₂.property heq)
  · intro h; subst h; intro _; rfl

-- ─── toList ───────────────────────────────────────────────────────────────────

private theorem mem_toListAux_iff (t : PosTrie V) (d : Nat) (hd : d ≤ 32)
    (pfx : UInt32) (hpfx : pfx.toNat < 2^d) (skip : Bool) (k : UInt32) (v : V) :
    (k, v) ∈ t.val.toListAux d pfx skip ↔
    ∃ j : Nat, j < 2^(32-d) ∧ (skip → j ≠ 0) ∧
      k.toNat = pfx.toNat + j * 2^d ∧ t.val.get? (UInt32.ofNat j) = some v :=
  Raw.mem_toListAux_iff t.val d hd pfx hpfx skip k v

private theorem toListAux_nodup (t : PosTrie V) (d : Nat) (hd : d ≤ 32)
    (pfx : UInt32) (hpfx : pfx.toNat < 2^d) (skip : Bool) :
    (t.val.toListAux d pfx skip).Nodup :=
  Raw.toListAux_nodup t.val d hd pfx hpfx skip

end PosTrie

-- ─── PartialMap and LawfulPartialMap instances ────────────────────────────────

open Iris.Std in
instance : Iris.Std.PartialMap PosTrie UInt32 where
  get?      t k   := t.get? k
  insert    t k v := t.insert k v
  delete    t k   := t.delete k
  empty           := PosTrie.empty
  bindAlter f t   := t.bindAlter f
  merge op  t1 t2 := t1.merge op t2

open Iris.Std in
instance : Iris.Std.LawfulPartialMap PosTrie UInt32 where
  get?_empty k := rfl
  get?_insert_eq {V m k k' v} h := by
    simp only [Iris.Std.get?, Iris.Std.insert, PosTrie.get?_insert]
  get?_insert_ne {V m k k' v} h := by
    simp [Iris.Std.get?, Iris.Std.insert, PosTrie.get?_insert, h]
  get?_delete_eq {V m k k'} h := by
    simp [Iris.Std.get?, Iris.Std.delete, PosTrie.get?_delete, h]
  get?_delete_ne {V m k k'} h := by
    simp [Iris.Std.get?, Iris.Std.delete, PosTrie.get?_delete, h]
  get?_bindAlter {V V' f m k} := PosTrie.get?_bindAlter f m k
  get?_merge {V op m₁ m₂ k} := PosTrie.get?_merge op m₁ m₂ k
  equiv_iff_eq {V m₁ m₂} := by
    simp only [Iris.Std.get?]; exact PosTrie.equiv_iff_eq

-- ─── FiniteMap and LawfulFiniteMap instances ──────────────────────────────────

open Iris.Std in
instance : Iris.Std.FiniteMap PosTrie UInt32 where
  toList t := t.toList

open Iris.Std in
instance : Iris.Std.LawfulFiniteMap PosTrie UInt32 where
  toList_empty := rfl
  toList_noDupKeys {V m} := by
    show ((m.val.toListAux 0 0 false).map Prod.fst).Nodup
    have hnodup := Raw.toListAux_nodup m.val 0 (by omega) 0 (by simp) false
    have hinj : ∀ p₁ ∈ m.val.toListAux 0 0 false, ∀ p₂ ∈ m.val.toListAux 0 0 false,
        p₁.1 = p₂.1 → p₁ = p₂ := by
      intro ⟨k₁, v₁⟩ hm₁ ⟨k₂, v₂⟩ hm₂ hkeq
      simp only at hkeq; subst hkeq
      rw [Raw.mem_toListAux_iff m.val 0 (by omega) 0 (by simp) false k₁ v₁] at hm₁
      rw [Raw.mem_toListAux_iff m.val 0 (by omega) 0 (by simp) false k₁ v₂] at hm₂
      obtain ⟨j₁, hb₁, _, hk₁, hg₁⟩ := hm₁
      obtain ⟨j₂, hb₂, _, hk₂, hg₂⟩ := hm₂
      simp only [Nat.mul_one, Nat.zero_add, show (2:Nat)^0 = 1 from rfl] at hk₁ hk₂
      have hj : j₁ = j₂ := by
        have h1 : (UInt32.ofNat j₁).toNat = j₁ :=
          Raw.ofNat_toNat' (Raw.ofNat_lt_size (by omega) hb₁)
        have h2 : (UInt32.ofNat j₂).toNat = j₂ :=
          Raw.ofNat_toNat' (Raw.ofNat_lt_size (by omega) hb₂)
        omega
      rw [← hj] at hg₂
      exact congrArg (Prod.mk k₁) (Option.some.inj (hg₁.symm.trans hg₂))
    exact List.pairwise_map.mpr
      (hnodup.imp_of_mem (fun ha hb hne hfst => hne (hinj _ ha _ hb hfst)))
  toList_get {V m k v} := by
    show (k, v) ∈ m.val.toListAux 0 0 false ↔ m.val.get? k = some v
    rw [Raw.mem_toListAux_iff m.val 0 (by omega) 0 (by simp) false k v]
    constructor
    · rintro ⟨j, _, _, hkj, hget⟩
      simp only [Nat.pow_zero, Nat.mul_one, Nat.zero_add] at hkj
      have hjsz : j < UInt32.size := by
        have := k.toNat_lt; simp only [UInt32.size] at *; omega
      have hkj' : UInt32.ofNat j = k := by rw [← hkj]; exact UInt32.ofNat_toNat k
      rw [hkj'] at hget; exact hget
    · intro hget
      refine ⟨k.toNat, ?_, fun h => absurd h (by decide), by simp [Nat.pow_zero], ?_⟩
      · simp only [Nat.sub_zero]
        linarith [k.toNat_lt, show (2:Nat)^32 = UInt32.size from by native_decide]
      · rwa [UInt32.ofNat_toNat]

end Wasm.SepLogic
