import Papers.PODC2016.CollaborativeListSpec.Spec
import Papers.PODC2016.CollaborativeListSpec.ListFacts

/-!
# The executions of the lower-bound proof (Theorem 9, Figure 4)

For a bit string `w` (bits `w 1, …, w d`) the encoding execution `α_w` (Figure 4(a)) runs at
replica `R₁` only:

```
ins [₀ ; ins ]₀ ; for i = 1..d: send mᵢ ; ins [ᵢ ]ᵢ just after ]ᵢ₋₁ (wᵢ = 1) / just before [ᵢ₋₁ (wᵢ = 0)
send m_{d+1} ; ins ∗ between [_d and ]_d ; send m_{d+2} ;
del [₀ ; del ]₀ ; … ; del [_d ; del ]_d ; (D odd: ins b ; del b) ; send m_{d+3}
```

Positions: `ins [ⱼ` at `3j`, `ins ]ⱼ` at `3j+1`, `send m_{j+1}` at `3j+2` (`j ≤ d`); `ins ∗` at
`3d+3`, `send m_{d+2}` at `3d+4`, the deletions from `3d+5` on, the last send at `Lα - 1`. The
paper describes positions relative to earlier insertions ("just after ]ᵢ₋₁"); we compute the
integer positions from the intended list `A_j ++ [[ⱼ, ]ⱼ] ++ B_j` (`AB`), and prove that the
responses are these lists.

The execution `γ_w^i` (the paper's `β_w^i` followed by `R₃`'s part) extends `α_w`:

```
recv₂ m₁ ; recv₁ m₁ ; … ; recv₂ mᵢ ; recv₁ mᵢ ; read₂ ; ins₂ x (between [ᵢ₋₁ and ]ᵢ₋₁) ; send₂ mₓ ;
recv₂ mₓ ; recv₁ mₓ ; read₁ (= y) ;                                         -- end of β_w^i
recv₃ m₁ ; … ; recv₃ mᵢ ; recv₃ mₓ ; recv₃ m_{i+1} ; … ; recv₃ m_{d+2} ; read₃ (= z)
```

All executions are prefixes `pre g n` of one infinite sequence `g : ℕ → Act`.
-/

namespace Podc.CollaborativeListSpec

/-- The prefix of length `n` of an infinite sequence of actions. -/
def pre {Rep Op : Type} (g : ℕ → Act Rep Op) (n : ℕ) : List (Act Rep Op) :=
  (List.range n).map g

section Pre

variable {Rep Op : Type} (g : ℕ → Act Rep Op)

@[simp] theorem length_pre (n : ℕ) : (pre g n).length = n := by simp [pre]

theorem pre_getElem? (n p : ℕ) : (pre g n)[p]? = if p < n then some (g p) else none := by
  by_cases h : p < n
  · simp [pre, h]
  · simp [pre, h]

theorem pre_getElem?_of_lt {n p : ℕ} (h : p < n) : (pre g n)[p]? = some (g p) := by
  rw [pre_getElem?, if_pos h]

theorem pre_take (n m : ℕ) : (pre g n).take m = pre g (min m n) := by
  simp [pre, ← List.map_take, List.take_range]

theorem pre_prefix {m n : ℕ} (h : m ≤ n) : pre g m <+: pre g n := by
  rw [List.prefix_iff_eq_take, length_pre, pre_take, min_eq_left h]

theorem pre_succ (n : ℕ) : pre g (n + 1) = pre g n ++ [g n] := by
  simp [pre, List.range_succ]

theorem pre_congr {g' : ℕ → Act Rep Op} {n : ℕ} (h : ∀ p < n, g p = g' p) : pre g n = pre g' n := by
  simp only [pre]; apply List.map_congr_left; intro p hp; simp at hp; exact h p hp

end Pre

/-- The parameters of the construction: `d`, the parity of `D`, three distinct replicas and an
injective supply of list elements. -/
structure Params (Rep U : Type) where
  d : ℕ
  odd : Bool
  r1 : Rep
  r2 : Rep
  r3 : Rep
  sym : ℕ → U
  sym_inj : Function.Injective sym
  h12 : r1 ≠ r2
  h13 : r1 ≠ r3
  h23 : r2 ≠ r3

namespace Params

variable {Rep U : Type} (E : Params Rep U)

/-- The element `x` inserted by `R₂` in `Recover`. -/
def X : U := E.sym 0
/-- The element `∗`. -/
def Star : U := E.sym 1
/-- The extra element `b` for odd `D`. -/
def Bee : U := E.sym 2
/-- The element `[ⱼ`. -/
def Op (j : ℕ) : U := E.sym (2 * j + 3)
/-- The element `]ⱼ`. -/
def Cl (j : ℕ) : U := E.sym (2 * j + 4)

/-- The intended list after step `j` is `A_j ++ [[ⱼ, ]ⱼ] ++ B_j`. -/
def AB (w : ℕ → Bool) : ℕ → List U × List U
  | 0 => ([], [])
  | j + 1 =>
    if w (j + 1) then ((AB w j).1 ++ [E.Op j, E.Cl j], (AB w j).2)
    else ((AB w j).1, [E.Op j, E.Cl j] ++ (AB w j).2)

/-- The intended list after step `j`. -/
def L (w : ℕ → Bool) (j : ℕ) : List U := (E.AB w j).1 ++ [E.Op j, E.Cl j] ++ (E.AB w j).2

/-- The intended list after the insertion of `∗`. -/
def Lstar (w : ℕ → Bool) : List U := (E.AB w E.d).1 ++ [E.Op E.d, E.Star, E.Cl E.d] ++ (E.AB w E.d).2

/-- `|A_j|`. -/
def lenA (w : ℕ → Bool) (j : ℕ) : ℕ := (E.AB w j).1.length

/-- The length of `α_w`. -/
def Lα : ℕ := 5 * E.d + 8 + (if E.odd then 2 else 0)

/-- The actions of `α_w` (Figure 4(a)). -/
def act (w : ℕ → Bool) (p : ℕ) : Act Rep (LOp U) :=
  if p < 3 * (E.d + 1) then
    if p % 3 = 0 then .doOp E.r1 (.ins (E.Op (p / 3)) (E.lenA w (p / 3)))
    else if p % 3 = 1 then .doOp E.r1 (.ins (E.Cl (p / 3)) (E.lenA w (p / 3) + 1))
    else .send E.r1
  else if p = 3 * E.d + 3 then .doOp E.r1 (.ins E.Star (E.lenA w E.d + 1))
  else if p = 3 * E.d + 4 then .send E.r1
  else if p < 5 * E.d + 7 then
    if (p - (3 * E.d + 5)) % 2 = 0 then .doOp E.r1 (.del (E.Op ((p - (3 * E.d + 5)) / 2)))
    else .doOp E.r1 (.del (E.Cl ((p - (3 * E.d + 5)) / 2)))
  else if E.odd ∧ p = 5 * E.d + 7 then .doOp E.r1 (.ins E.Bee 0)
  else if E.odd ∧ p = 5 * E.d + 8 then .doOp E.r1 (.del E.Bee)
  else .send E.r1

/-- The position of the send of `m_j` (`1 ≤ j ≤ d + 2`). -/
def mpos (j : ℕ) : ℕ := if j ≤ E.d + 1 then 3 * j - 1 else 3 * E.d + 4

/-- The position of the send of `mₓ` in `γ_w^i`. -/
def pmx (i : ℕ) : ℕ := E.Lα + 2 * i + 2

/-- The suffix of `γ_w^i` after `α_w`, indexed from `0`. -/
def suf (w : ℕ → Bool) (i q : ℕ) : Act Rep (LOp U) :=
  if q < 2 * i then
    if q % 2 = 0 then .recv E.r2 (E.mpos (q / 2 + 1)) else .recv E.r1 (E.mpos (q / 2 + 1))
  else if q = 2 * i then .doOp E.r2 .read
  else if q = 2 * i + 1 then .doOp E.r2 (.ins E.X (E.lenA w (i - 1) + 1))
  else if q = 2 * i + 2 then .send E.r2
  else if q = 2 * i + 3 then .recv E.r2 (E.pmx i)
  else if q = 2 * i + 4 then .recv E.r1 (E.pmx i)
  else if q = 2 * i + 5 then .doOp E.r1 .read
  else if q < 3 * i + 6 then .recv E.r3 (E.mpos (q - (2 * i + 6) + 1))
  else if q = 3 * i + 6 then .recv E.r3 (E.pmx i)
  else if q < 2 * i + E.d + 9 then .recv E.r3 (E.mpos (i + 1 + (q - (3 * i + 7))))
  else .doOp E.r3 .read

/-- The infinite action sequence whose prefixes are `α_w`, `β_w^i` and `γ_w^i`. -/
def g (w : ℕ → Bool) (i p : ℕ) : Act Rep (LOp U) :=
  if p < E.Lα then E.act w p else E.suf w i (p - E.Lα)

/-- The length of `γ_w^i`. -/
def Lγ (i : ℕ) : ℕ := E.Lα + 2 * i + E.d + 10

/-- `γ_w^i`. -/
def γ (w : ℕ → Bool) (i : ℕ) : List (Act Rep (LOp U)) := pre (E.g w i) (E.Lγ i)

/-- `α_w` followed by a read at `R₁`. -/
def gr (w : ℕ → Bool) (p : ℕ) : Act Rep (LOp U) :=
  if p < E.Lα then E.act w p else .doOp E.r1 .read

/-! ### The intended lists -/

section Lists

variable {E} {w : ℕ → Bool}

theorem sym_eq_iff {a b : ℕ} : E.sym a = E.sym b ↔ a = b := E.sym_inj.eq_iff

@[simp] theorem Op_inj {j t : ℕ} : E.Op j = E.Op t ↔ j = t := by
  simp only [Op, sym_eq_iff]; omega
@[simp] theorem Cl_inj {j t : ℕ} : E.Cl j = E.Cl t ↔ j = t := by
  simp only [Cl, sym_eq_iff]; omega
@[simp] theorem Op_ne_Cl {j t : ℕ} : E.Op j ≠ E.Cl t := by
  simp only [Op, Cl, ne_eq, sym_eq_iff]; omega
@[simp] theorem Cl_ne_Op {j t : ℕ} : E.Cl j ≠ E.Op t := fun h => Op_ne_Cl h.symm
@[simp] theorem Star_ne_Op {j : ℕ} : E.Star ≠ E.Op j := by
  simp only [Star, Op, ne_eq, sym_eq_iff]; omega
@[simp] theorem Star_ne_Cl {j : ℕ} : E.Star ≠ E.Cl j := by
  simp only [Star, Cl, ne_eq, sym_eq_iff]; omega
@[simp] theorem X_ne_Op {j : ℕ} : E.X ≠ E.Op j := by
  simp only [X, Op, ne_eq, sym_eq_iff]; omega
@[simp] theorem X_ne_Cl {j : ℕ} : E.X ≠ E.Cl j := by
  simp only [X, Cl, ne_eq, sym_eq_iff]; omega
@[simp] theorem Bee_ne_Op {j : ℕ} : E.Bee ≠ E.Op j := by
  simp only [Bee, Op, ne_eq, sym_eq_iff]; omega
@[simp] theorem Bee_ne_Cl {j : ℕ} : E.Bee ≠ E.Cl j := by
  simp only [Bee, Cl, ne_eq, sym_eq_iff]; omega
@[simp] theorem Op_ne_Star {j : ℕ} : E.Op j ≠ E.Star := fun h => Star_ne_Op h.symm
@[simp] theorem Cl_ne_Star {j : ℕ} : E.Cl j ≠ E.Star := fun h => Star_ne_Cl h.symm
@[simp] theorem Op_ne_X {j : ℕ} : E.Op j ≠ E.X := fun h => X_ne_Op h.symm
@[simp] theorem Cl_ne_X {j : ℕ} : E.Cl j ≠ E.X := fun h => X_ne_Cl h.symm
@[simp] theorem Op_ne_Bee {j : ℕ} : E.Op j ≠ E.Bee := fun h => Bee_ne_Op h.symm
@[simp] theorem Cl_ne_Bee {j : ℕ} : E.Cl j ≠ E.Bee := fun h => Bee_ne_Cl h.symm
@[simp] theorem X_ne_Star : E.X ≠ E.Star := by simp [X, Star, sym_eq_iff]
@[simp] theorem Star_ne_X : E.Star ≠ E.X := fun h => X_ne_Star h.symm
@[simp] theorem X_ne_Bee : E.X ≠ E.Bee := by simp [X, Bee, sym_eq_iff]
@[simp] theorem Bee_ne_X : E.Bee ≠ E.X := fun h => X_ne_Bee h.symm
@[simp] theorem Star_ne_Bee : E.Star ≠ E.Bee := by simp [Star, Bee, sym_eq_iff]
@[simp] theorem Bee_ne_Star : E.Bee ≠ E.Star := fun h => Star_ne_Bee h.symm

theorem AB_succ_append (j : ℕ) : (E.AB w (j + 1)).1 ++ (E.AB w (j + 1)).2 = E.L w j := by
  simp only [AB, L]; split_ifs <;> simp

theorem mem_AB {j : ℕ} {x : U} :
    x ∈ (E.AB w j).1 ++ (E.AB w j).2 ↔ ∃ t < j, x = E.Op t ∨ x = E.Cl t := by
  induction j with
  | zero => simp [AB]
  | succ j ih =>
    rw [AB_succ_append]
    simp only [L, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    have := ih; simp only [List.mem_append] at this
    constructor
    · rintro ((h | h | h) | h)
      · obtain ⟨t, ht, h⟩ := this.1 (Or.inl h); exact ⟨t, by omega, h⟩
      · exact ⟨j, by omega, Or.inl h⟩
      · exact ⟨j, by omega, Or.inr h⟩
      · obtain ⟨t, ht, h⟩ := this.1 (Or.inr h); exact ⟨t, by omega, h⟩
    · rintro ⟨t, ht, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · rcases this.2 ⟨t, ht, h⟩ with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases h with h | h
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr h))

theorem mem_L {j : ℕ} {x : U} : x ∈ E.L w j ↔ ∃ t ≤ j, x = E.Op t ∨ x = E.Cl t := by
  rw [← AB_succ_append, mem_AB]; simp [Nat.lt_succ_iff]

theorem nodup_AB (j : ℕ) : ((E.AB w j).1 ++ (E.AB w j).2).Nodup := by
  induction j with
  | zero => simp [AB]
  | succ j ih =>
    rw [AB_succ_append, L]
    have hp : ((E.AB w j).1 ++ [E.Op j, E.Cl j] ++ (E.AB w j).2).Perm
        (E.Op j :: E.Cl j :: ((E.AB w j).1 ++ (E.AB w j).2)) := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact List.perm_middle.trans (List.Perm.cons _ List.perm_middle)
    rw [hp.nodup_iff]
    refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, ih⟩⟩
    · simp only [List.mem_cons, Op_ne_Cl, false_or]
      rw [mem_AB]; rintro ⟨t, ht, h | h⟩
      · rw [Op_inj] at h; omega
      · exact Op_ne_Cl h
    · rw [mem_AB]; rintro ⟨t, ht, h | h⟩
      · exact Cl_ne_Op h
      · rw [Cl_inj] at h; omega

theorem nodup_L (j : ℕ) : (E.L w j).Nodup := by
  rw [← AB_succ_append]; exact nodup_AB _

theorem lenA_le (j : ℕ) : E.lenA w j ≤ (E.L w (j - 1)).length ∨ j = 0 := by
  rcases j with _ | j
  · right; rfl
  · left; rw [lenA, show j + 1 - 1 = j by omega, ← AB_succ_append]; simp

theorem insertIdx_append_length_add {α : Type} (l₁ l₂ : List α) (n : ℕ) (x : α) :
    (l₁ ++ l₂).insertIdx (l₁.length + n) x = l₁ ++ l₂.insertIdx n x := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    rw [List.cons_append, List.length_cons, show l.length + 1 + n = (l.length + n) + 1 by omega,
      List.insertIdx_succ_cons, ih]; rfl

/-- After `ins [ⱼ` (for `j ≥ 1`). -/
theorem insertIdx_Op (j : ℕ) :
    (E.L w j).insertIdx (E.lenA w (j + 1)) (E.Op (j + 1)) =
      (E.AB w (j + 1)).1 ++ [E.Op (j + 1)] ++ (E.AB w (j + 1)).2 := by
  rw [← AB_succ_append, lenA, ← Nat.add_zero (List.length _), insertIdx_append_length_add]
  simp

/-- After `ins ]ⱼ`. -/
theorem insertIdx_Cl (j : ℕ) :
    ((E.AB w j).1 ++ [E.Op j] ++ (E.AB w j).2).insertIdx (E.lenA w j + 1) (E.Cl j) = E.L w j := by
  rw [lenA, L, List.append_assoc, List.append_assoc, insertIdx_append_length_add]
  simp

/-- After `ins ∗`. -/
theorem insertIdx_Star : (E.L w E.d).insertIdx (E.lenA w E.d + 1) E.Star = E.Lstar w := by
  rw [lenA, L, Lstar, List.append_assoc, List.append_assoc, insertIdx_append_length_add]
  simp

/-- After `R₂`'s `ins x`. -/
theorem insertIdx_X (j : ℕ) : (E.L w j).insertIdx (E.lenA w j + 1) E.X =
    (E.AB w j).1 ++ [E.Op j, E.X, E.Cl j] ++ (E.AB w j).2 := by
  rw [lenA, L, List.append_assoc, List.append_assoc, insertIdx_append_length_add]
  simp

theorem AB_fst_prefix {j k : ℕ} (h : j ≤ k) : (E.AB w j).1 <+: (E.AB w k).1 := by
  induction k with
  | zero => obtain rfl : j = 0 := by omega
            exact List.prefix_refl _
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with h' | rfl
    · refine (ih (by omega)).trans ?_
      simp only [AB]; split_ifs
      · exact List.prefix_append _ _
      · exact List.prefix_refl _
    · exact List.prefix_refl _

theorem AB_snd_suffix {j k : ℕ} (h : j ≤ k) : (E.AB w j).2 <:+ (E.AB w k).2 := by
  induction k with
  | zero => obtain rfl : j = 0 := by omega
            exact List.suffix_refl _
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with h' | rfl
    · refine (ih (by omega)).trans ?_
      simp only [AB]; split_ifs
      · exact List.suffix_refl _
      · exact List.suffix_append _ _
    · exact List.suffix_refl _

/-- If `wᵢ = 1`, `]ᵢ₋₁` precedes `∗` in the final list. -/
theorem Cl_before_Star {i : ℕ} (hi : 1 ≤ i) (hid : i ≤ E.d) (hw : w i = true) :
    [E.Cl (i - 1), E.Star].Sublist (E.Lstar w) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hmem : E.Cl j ∈ (E.AB w E.d).1 := by
    have := (AB_fst_prefix (w := w) (E := E) hid).subset
    apply this; simp [AB, hw]
  simp only [Nat.add_sub_cancel, Lstar]
  obtain ⟨l₁, l₂, h⟩ := List.append_of_mem hmem
  rw [h]
  simp

/-- If `wᵢ = 0`, `∗` precedes `[ᵢ₋₁` in the final list. -/
theorem Star_before_Op {i : ℕ} (hi : 1 ≤ i) (hid : i ≤ E.d) (hw : w i = false) :
    [E.Star, E.Op (i - 1)].Sublist (E.Lstar w) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hmem : E.Op j ∈ (E.AB w E.d).2 := by
    have := (AB_snd_suffix (w := w) (E := E) hid).subset
    apply this; simp [AB, hw]
  simp only [Nat.add_sub_cancel, Lstar]
  obtain ⟨l₁, l₂, h⟩ := List.append_of_mem hmem
  rw [h]
  simp

end Lists

end Params

end Podc.CollaborativeListSpec
