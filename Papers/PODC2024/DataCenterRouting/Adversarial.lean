import Papers.PODC2024.DataCenterRouting.Model

/-!
# The adversarial collections of flows of Section 4

`C_n` with `n = k + 1`. Indices are 0-based: the paper's `I_i`, `i ∈ [n]`, is `tor (i-1)`, and
`I_{n+1}` is `torN k`; the paper's server `s_i^j` is `(tor (i-1), j-1)`.

* type 1: `p` copies of `(s_i^j, t_i^j)`, `i ∈ [n]`, `j ∈ [2, n]` (`t1 i j c`, server `j.succ`);
* type 2.a: `(s_i^1, t_i^1)`, `i ∈ [n]` (`t2 i none`);
* type 2.b: `(s_i^1, t_{n+1}^j)`, `i ∈ [n]`, `j ∈ [n-1]` (`t2 i (some j)`, server `j.castSucc`);
* type 3: `(s_{n+1}^n, t_{n+1}^n)` (`t3`, server `Fin.last k`).

Example 4.1 / Theorem 4.2 use `p = 1`, Theorem 4.3 uses `p = n + 1`. This file computes the link
loads of an arbitrary allocation for these flows.
-/

namespace Podc.DataCenterRouting

open Cslib.RateAllocation Finset

/-- The input/output switch `I_{i+1}` / `O_{i+1}` for `i < n = k + 1`. -/
def tor {k : ℕ} (i : Fin (k + 1)) : Fin (2 * (k + 1)) := ⟨i, by omega⟩

/-- The input/output switch `I_{n+1}` / `O_{n+1}` (`n = k + 1`). -/
def torN (k : ℕ) : Fin (2 * (k + 1)) := ⟨k + 1, by omega⟩

@[simp] theorem tor_inj {k : ℕ} {i i' : Fin (k + 1)} : tor i = tor i' ↔ i = i' := by
  simp [tor, Fin.ext_iff]

@[simp] theorem tor_ne_torN {k : ℕ} (i : Fin (k + 1)) : tor i ≠ torN k := by
  simp only [tor, torN, ne_eq, Fin.ext_iff]; omega

@[simp] theorem torN_ne_tor {k : ℕ} (i : Fin (k + 1)) : torN k ≠ tor i := (tor_ne_torN i).symm

/-- Every switch index is some `tor i`, or `torN k`, or neither. -/
theorem switch_cases {k : ℕ} (x : Fin (2 * (k + 1))) :
    (∃ i, x = tor i) ∨ x = torN k ∨ ((∀ i, x ≠ tor i) ∧ x ≠ torN k) := by
  by_cases h1 : x.val < k + 1
  · exact Or.inl ⟨⟨x, h1⟩, Fin.ext rfl⟩
  · by_cases h2 : x.val = k + 1
    · exact Or.inr (Or.inl (Fin.ext h2))
    · refine Or.inr (Or.inr ⟨fun i h => ?_, fun h => h2 (by rw [h]; rfl)⟩)
      rw [h] at h1; exact h1 i.isLt

/-- Flow index type of the adversarial collections of Section 4 (see the module docstring). -/
abbrev AdvFlow (k p : ℕ) := (Fin (k + 1) × Fin k × Fin p) ⊕ (Fin (k + 1) × Option (Fin k)) ⊕ Unit

variable {k p : ℕ}

/-- Copy `c` of the type-1 flow `(s_{i+1}^{j+2}, t_{i+1}^{j+2})`. -/
abbrev t1 (i : Fin (k + 1)) (j : Fin k) (c : Fin p) : AdvFlow k p := .inl (i, j, c)
/-- The type-2 flows leaving `s_{i+1}^1`: 2.a for `y = none`, 2.b towards `t_{n+1}^{j+1}` for
`y = some j`. -/
abbrev t2 (i : Fin (k + 1)) (y : Option (Fin k)) : AdvFlow k p := .inr (.inl (i, y))
/-- The type-3 flow `(s_{n+1}^n, t_{n+1}^n)`. -/
abbrev t3 : AdvFlow k p := .inr (.inr ())

variable (k p) in
/-- The adversarial collection of flows of Example 4.1 (`p = 1`) and Theorem 4.3 (`p = n + 1`). -/
def adv : Flows (k + 1) (AdvFlow k p) where
  src
    | .inl (i, j, _) => (tor i, j.succ)
    | .inr (.inl (i, _)) => (tor i, 0)
    | .inr (.inr _) => (torN k, Fin.last k)
  dst
    | .inl (i, j, _) => (tor i, j.succ)
    | .inr (.inl (i, none)) => (tor i, 0)
    | .inr (.inl (_, some j)) => (torN k, j.castSucc)
    | .inr (.inr _) => (torN k, Fin.last k)

@[simp] theorem adv_src_t1 (i : Fin (k + 1)) (j : Fin k) (c : Fin p) :
    (adv k p).src (t1 i j c) = (tor i, j.succ) := rfl
@[simp] theorem adv_src_t2 (i : Fin (k + 1)) (y : Option (Fin k)) :
    (adv k p).src (t2 i y) = (tor i, 0) := rfl
@[simp] theorem adv_src_t3 : (adv k p).src t3 = (torN k, Fin.last k) := rfl
@[simp] theorem adv_dst_t1 (i : Fin (k + 1)) (j : Fin k) (c : Fin p) :
    (adv k p).dst (t1 i j c) = (tor i, j.succ) := rfl
@[simp] theorem adv_dst_t2a (i : Fin (k + 1)) :
    (adv k p).dst (t2 i none) = (tor i, 0) := rfl
@[simp] theorem adv_dst_t2b (i : Fin (k + 1)) (j : Fin k) :
    (adv k p).dst (t2 i (some j)) = (torN k, j.castSucc) := rfl
@[simp] theorem adv_dst_t3 : (adv k p).dst t3 = (torN k, Fin.last k) := rfl

variable (k p) in
/-- The allocation giving `1/p` to type-1 flows, `1/n` to type-2 flows and `θ` to the type-3
flow. -/
noncomputable def advRate (θ : ℝ) : AdvFlow k p → ℝ
  | .inl _ => 1 / p
  | .inr (.inl _) => 1 / (k + 1)
  | .inr (.inr _) => θ

@[simp] theorem advRate_t1 (θ : ℝ) (i : Fin (k + 1)) (j : Fin k) (c : Fin p) :
    advRate k p θ (t1 i j c) = 1 / p := rfl
@[simp] theorem advRate_t2 (θ : ℝ) (i : Fin (k + 1)) (y : Option (Fin k)) :
    advRate k p θ (t2 i y) = 1 / (k + 1) := rfl
@[simp] theorem advRate_t3 (θ : ℝ) : advRate k p θ t3 = θ := rfl

/-- Case analysis on adversarial flows. -/
theorem AdvFlow.cases (f : AdvFlow k p) :
    (∃ i j c, f = t1 i j c) ∨ (∃ i y, f = t2 i y) ∨ f = t3 := by
  rcases f with ⟨i, j, c⟩ | ⟨i, y⟩ | ⟨⟩
  · exact Or.inl ⟨i, j, c, rfl⟩
  · exact Or.inr (Or.inl ⟨i, y, rfl⟩)
  · exact Or.inr (Or.inr rfl)

/-! ### Loads of server links (same in the macro-switch and in the Clos network) -/

section ServerLoads

variable (b : AdvFlow k p → ℝ)

theorem srcSum_t1 (i : Fin (k + 1)) (j : Fin k) :
    (∑ f, if (adv k p).src f = (tor i, j.succ) then b f else 0) = ∑ c, b (t1 i j c) := by
  rw [sum_ite_eq_of_injective _ b (fun c : Fin p => t1 i j c) (by intro c c' h; simpa using h)]
  · simp
  · intro f hf
    rcases f.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl
    · simp only [adv_src_t1, Prod.mk.injEq, tor_inj, Fin.succ_inj] at hf
      obtain ⟨rfl, rfl⟩ := hf; exact ⟨c', rfl⟩
    · simp [(Fin.succ_ne_zero j).symm] at hf
    · simp at hf

theorem srcSum_t2 (i : Fin (k + 1)) :
    (∑ f, if (adv k p).src f = (tor i, 0) then b f else 0) = ∑ y, b (t2 i y) := by
  rw [sum_ite_eq_of_injective _ b (fun y => t2 i y) (by intro c c' h; simpa using h)]
  · simp
  · intro f hf
    rcases f.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl
    · simp [Fin.succ_ne_zero] at hf
    · simp only [adv_src_t2, Prod.mk.injEq, tor_inj, and_true] at hf
      subst hf; exact ⟨y, rfl⟩
    · simp at hf

theorem srcSum_t3 :
    (∑ f, if (adv k p).src f = (torN k, Fin.last k) then b f else 0) = b t3 := by
  rw [Finset.sum_eq_single t3]
  · simp
  · intro f _ hf
    rcases f.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl
    · simp
    · simp
    · exact absurd rfl hf
  · simp

theorem srcSum_zero (s : Server (k + 1)) (hs : ∀ f, (adv k p).src f ≠ s) :
    (∑ f, if (adv k p).src f = s then b f else 0) = 0 :=
  Finset.sum_eq_zero fun f _ => ite_eq_right (hs f)

theorem dstSum_t1 (i : Fin (k + 1)) (j : Fin k) :
    (∑ f, if (adv k p).dst f = (tor i, j.succ) then b f else 0) = ∑ c, b (t1 i j c) := by
  rw [sum_ite_eq_of_injective _ b (fun c : Fin p => t1 i j c) (by intro c c' h; simpa using h)]
  · simp
  · intro f hf
    rcases f.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl
    · simp only [adv_dst_t1, Prod.mk.injEq, tor_inj, Fin.succ_inj] at hf
      obtain ⟨rfl, rfl⟩ := hf; exact ⟨c', rfl⟩
    · cases y <;> simp [(Fin.succ_ne_zero j).symm] at hf
    · simp at hf

theorem dstSum_t2a (i : Fin (k + 1)) :
    (∑ f, if (adv k p).dst f = (tor i, 0) then b f else 0) = b (t2 i none) := by
  rw [Finset.sum_eq_single (t2 i none)]
  · simp
  · intro f _ hf
    rcases f.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl
    · simp [Fin.succ_ne_zero]
    · cases y with
      | none =>
        simp only [adv_dst_t2a, Prod.mk.injEq, tor_inj, and_true]
        rw [ite_eq_right]; rintro rfl; exact hf rfl
      | some j => simp
    · simp
  · simp

theorem dstSum_t2b (j : Fin k) :
    (∑ f, if (adv k p).dst f = (torN k, j.castSucc) then b f else 0) =
      ∑ i, b (t2 i (some j)) := by
  rw [sum_ite_eq_of_injective _ b (fun i => t2 i (some j)) (by intro c c' h; simpa using h)]
  · simp
  · intro f hf
    rcases f.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl
    · simp at hf
    · cases y with
      | none => simp at hf
      | some j' =>
        simp only [adv_dst_t2b, Prod.mk.injEq, true_and, Fin.castSucc_inj] at hf
        subst hf; exact ⟨i', rfl⟩
    · simp [Fin.ext_iff] at hf; omega

theorem dstSum_t3 :
    (∑ f, if (adv k p).dst f = (torN k, Fin.last k) then b f else 0) = b t3 := by
  rw [Finset.sum_eq_single t3]
  · simp
  · intro f _ hf
    rcases f.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl
    · simp
    · cases y with
      | none => simp
      | some j => simp [Fin.ext_iff]; omega
    · exact absurd rfl hf
  · simp

theorem dstSum_zero (s : Server (k + 1)) (hs : ∀ f, (adv k p).dst f ≠ s) :
    (∑ f, if (adv k p).dst f = s then b f else 0) = 0 :=
  Finset.sum_eq_zero fun f _ => ite_eq_right (hs f)

end ServerLoads

/-! ### Loads of the links inside the Clos network -/

section InnerLoads

variable (b : AdvFlow k p → ℝ) (r : AdvFlow k p → Fin (k + 1))

theorem upSum_tor (i : Fin (k + 1)) (m : Fin (k + 1)) :
    (∑ f, if ((adv k p).src f).1 = tor i ∧ r f = m then b f else 0) =
      (∑ x : Fin k × Fin p, if r (t1 i x.1 x.2) = m then b (t1 i x.1 x.2) else 0) +
      ∑ y, if r (t2 i y) = m then b (t2 i y) else 0 := by
  let e : (Fin k × Fin p) ⊕ Option (Fin k) → AdvFlow k p
    | .inl x => t1 i x.1 x.2
    | .inr y => t2 i y
  have he : Function.Injective e := by
    rintro (⟨j, c⟩ | y) (⟨j', c'⟩ | y') h <;> simp_all [e]
  rw [sum_ite_eq_of_injective _ b e he, Fintype.sum_sum_type]
  · simp [e]
  · intro f hf
    rcases f.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl
    · simp only [adv_src_t1, tor_inj] at hf
      obtain ⟨rfl, -⟩ := hf; exact ⟨.inl (j', c'), rfl⟩
    · simp only [adv_src_t2, tor_inj] at hf
      obtain ⟨rfl, -⟩ := hf; exact ⟨.inr y, rfl⟩
    · simp at hf

theorem upSum_torN (m : Fin (k + 1)) :
    (∑ f, if ((adv k p).src f).1 = torN k ∧ r f = m then b f else 0) =
      if r t3 = m then b t3 else 0 := by
  rw [Finset.sum_eq_single t3]
  · simp
  · intro f _ hf
    rcases f.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl
    · simp
    · simp
    · exact absurd rfl hf
  · simp

theorem upSum_zero (x : Fin (2 * (k + 1))) (m : Fin (k + 1)) (h1 : ∀ i, x ≠ tor i)
    (h2 : x ≠ torN k) :
    (∑ f, if ((adv k p).src f).1 = x ∧ r f = m then b f else 0) = 0 := by
  refine Finset.sum_eq_zero fun f _ => ite_eq_right ?_
  rcases f.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl
  · rintro ⟨h, -⟩; exact h1 i' h.symm
  · rintro ⟨h, -⟩; exact h1 i' h.symm
  · rintro ⟨h, -⟩; exact h2 h.symm

theorem downSum_tor (m : Fin (k + 1)) (i : Fin (k + 1)) :
    (∑ f, if r f = m ∧ ((adv k p).dst f).1 = tor i then b f else 0) =
      (∑ x : Fin k × Fin p, if r (t1 i x.1 x.2) = m then b (t1 i x.1 x.2) else 0) +
      if r (t2 i none) = m then b (t2 i none) else 0 := by
  let e : (Fin k × Fin p) ⊕ Unit → AdvFlow k p
    | .inl x => t1 i x.1 x.2
    | .inr _ => t2 i none
  have he : Function.Injective e := by
    rintro (⟨j, c⟩ | y) (⟨j', c'⟩ | y') h <;> simp_all [e]
  rw [sum_ite_eq_of_injective _ b e he, Fintype.sum_sum_type]
  · simp [e]
  · intro f hf
    rcases f.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl
    · simp only [adv_dst_t1, tor_inj] at hf
      obtain ⟨-, rfl⟩ := hf; exact ⟨.inl (j', c'), rfl⟩
    · cases y with
      | none =>
        simp only [adv_dst_t2a, tor_inj] at hf
        obtain ⟨-, rfl⟩ := hf; exact ⟨.inr (), rfl⟩
      | some j => simp at hf
    · simp at hf

theorem downSum_torN (m : Fin (k + 1)) :
    (∑ f, if r f = m ∧ ((adv k p).dst f).1 = torN k then b f else 0) =
      (∑ x : Fin (k + 1) × Fin k, if r (t2 x.1 (some x.2)) = m then b (t2 x.1 (some x.2))
        else 0) + if r t3 = m then b t3 else 0 := by
  let e : (Fin (k + 1) × Fin k) ⊕ Unit → AdvFlow k p
    | .inl x => t2 x.1 (some x.2)
    | .inr _ => t3
  have he : Function.Injective e := by
    rintro (⟨j, c⟩ | y) (⟨j', c'⟩ | y') h <;> simp_all [e]
  rw [sum_ite_eq_of_injective _ b e he, Fintype.sum_sum_type]
  · simp [e]
  · intro f hf
    rcases f.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl
    · simp at hf
    · cases y with
      | none => simp at hf
      | some j => exact ⟨.inl (i', j), rfl⟩
    · exact ⟨.inr (), rfl⟩

theorem downSum_zero (m : Fin (k + 1)) (x : Fin (2 * (k + 1))) (h1 : ∀ i, x ≠ tor i)
    (h2 : x ≠ torN k) :
    (∑ f, if r f = m ∧ ((adv k p).dst f).1 = x then b f else 0) = 0 := by
  refine Finset.sum_eq_zero fun f _ => ite_eq_right ?_
  rcases f.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl
  · simpa using fun _ h => h1 i' h.symm
  · cases y with
    | none => simpa using fun _ h => h1 i' h.symm
    | some j => simpa using fun _ h => h2 h.symm
  · simpa using fun _ h => h2 h.symm

end InnerLoads

end Podc.DataCenterRouting
