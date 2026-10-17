import Mathlib.Data.ZMod.Basic

/-!
# `mex` (minimum excludant) of a list of naturals

`mex l = min (ℕ ∖ l)`, written with structural recursion so that the kernel can evaluate it
(`decide` on concrete executions).
-/

namespace AsyncCycle

/-- Search for the least `k ≥ i` not in `l`, with fuel. -/
def mexFrom (l : List ℕ) : ℕ → ℕ → ℕ
  | i, 0 => i
  | i, fuel + 1 => if i ∈ l then mexFrom l (i + 1) fuel else i

/-- The minimum excludant `min (ℕ ∖ l)`. -/
def mex (l : List ℕ) : ℕ := mexFrom l 0 (l.length + 1)

/-- Every `k < mexFrom l i fuel` with `k ≥ i` belongs to `l`. -/
lemma lt_mexFrom_mem (l : List ℕ) :
    ∀ fuel i k, i ≤ k → k < mexFrom l i fuel → k ∈ l := by
  intro fuel
  induction fuel with
  | zero => intro i k hik hk; simp [mexFrom] at hk; omega
  | succ fuel ih =>
    intro i k hik hk
    simp only [mexFrom] at hk
    split_ifs at hk with hi
    · rcases Nat.eq_or_lt_of_le hik with rfl | hlt
      · exact hi
      · exact ih (i + 1) k hlt hk
    · omega

lemma le_mexFrom (l : List ℕ) : ∀ fuel i, i ≤ mexFrom l i fuel := by
  intro fuel
  induction fuel with
  | zero => intro i; simp [mexFrom]
  | succ fuel ih =>
    intro i; simp only [mexFrom]; split_ifs
    · exact (Nat.le_succ i).trans (ih (i + 1))
    · exact le_rfl

lemma mexFrom_le (l : List ℕ) : ∀ fuel i, mexFrom l i fuel ≤ i + fuel := by
  intro fuel
  induction fuel with
  | zero => intro i; simp [mexFrom]
  | succ fuel ih =>
    intro i; simp only [mexFrom]; split_ifs
    · have := ih (i + 1); omega
    · omega

lemma mexFrom_not_mem_or (l : List ℕ) :
    ∀ fuel i, mexFrom l i fuel ∉ l ∨ mexFrom l i fuel = i + fuel := by
  intro fuel
  induction fuel with
  | zero => intro i; right; simp [mexFrom]
  | succ fuel ih =>
    intro i; simp only [mexFrom]; split_ifs with h
    · rcases ih (i + 1) with h' | h'
      · exact Or.inl h'
      · right; omega
    · exact Or.inl h

lemma lt_mex_mem {l : List ℕ} {k : ℕ} (hk : k < mex l) : k ∈ l :=
  lt_mexFrom_mem l _ 0 k (Nat.zero_le _) hk

lemma mex_le_length (l : List ℕ) : mex l ≤ l.length := by
  by_contra h
  replace h := not_le.mp h
  -- then `0, …, l.length` all belong to `l`, which has only `l.length` elements
  have hsub : ∀ k ∈ List.range (l.length + 1), k ∈ l := fun k hk =>
    lt_mex_mem (lt_of_lt_of_le (List.mem_range.1 hk) (Nat.succ_le_of_lt h))
  have := List.Subperm.length_le
    ((List.nodup_range).subperm (fun k hk => hsub k hk))
  simp at this

lemma mex_not_mem (l : List ℕ) : mex l ∉ l := by
  rcases mexFrom_not_mem_or l (l.length + 1) 0 with h | h
  · exact h
  · have := mex_le_length l
    unfold mex at this; omega

lemma mex_eq_zero_of_not_mem {l : List ℕ} (h : 0 ∉ l) : mex l = 0 := by
  by_contra h'
  exact h (lt_mex_mem (Nat.pos_of_ne_zero h'))

lemma mex_ne_of_mem {l : List ℕ} {k : ℕ} (h : k ∈ l) : mex l ≠ k := by
  rintro rfl; exact mex_not_mem l h

@[simp] lemma mex_nil : mex [] = 0 := rfl

/-- `mex` only depends on the membership predicate. -/
lemma mex_congr {l l' : List ℕ} (h : ∀ k, k ∈ l ↔ k ∈ l') : mex l = mex l' := by
  apply le_antisymm
  · by_contra hlt; replace hlt := not_le.mp hlt
    exact mex_not_mem l' ((h _).1 (lt_mex_mem hlt))
  · by_contra hlt; replace hlt := not_le.mp hlt
    exact mex_not_mem l ((h _).2 (lt_mex_mem hlt))

end AsyncCycle
