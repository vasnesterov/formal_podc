import Mathlib

/-!
# Summing hash values "up the tree"

In Protocols 1 and 2 every node `v` checks `a_v = c_v + ∑_{u ∈ C(v)} a_u`, where
`C(v) = {u ∈ N(v) | t_u = v}` and `t_u` is the parent pointer the prover gave to `u`.

* `treeSum_root`: a **global summation argument** (no tree structure needed). If every non-root node's
  pointer lies in its neighbourhood, summing all the checks gives
  `a_r = ∑_v c_v + [r is counted as somebody's child] · a_r`. So either the root is never counted
  as a child, and then `a_r = ∑_v c_v` (Lemma 3.3), or it is, and then `∑_v c_v = 0`.
  With the paper's literal `C(v)`, the root *is* counted as a child of `t_r` whenever `t_r ∈ N(r)`
  (e.g. `t_r = r`); excluding the root from `C(v)` (flag `excl`) restores Lemma 3.3.
* `exists_treeSol`: if the "child" relation increases a bounded depth label by one, the checks have
  a solution (used for completeness: the honest prover's hash values).
-/

open Finset

namespace Podc.InteractiveDistributedProofs

variable {V : Type*} [Fintype V] [DecidableEq V] {K : Type*} [AddCommGroup K]

/-- The children of `v` as computed by the nodes: `{u ∈ nb v | t u = v}`, without the root `r` if
`excl` holds. -/
def children (nb : V → Finset V) (t : V → V) (r : V) (excl : Bool) (v : V) : Finset V :=
  (nb v).filter fun u => t u = v ∧ (excl = true → u ≠ r)

-- CSLib candidate
/-- **Global summation argument.** If all nodes pass the tree-sum check, then
`a r = ∑ c + (if the root is counted as a child then a r else 0)`. -/
theorem treeSum_root (nb : V → Finset V) (hnb : ∀ u v, u ∈ nb v ↔ v ∈ nb u) (r : V)
    (t : V → V) (ht : ∀ v, v ≠ r → t v ∈ nb v) (excl : Bool) (a c : V → K)
    (h : ∀ v, a v = c v + ∑ u ∈ children nb t r excl v, a u) :
    a r = (∑ v, c v) + (if excl = false ∧ t r ∈ nb r then a r else 0) := by
  -- the double sum `∑_v ∑_{u ∈ C(v)} a u` counts each `u` once if `u` is somebody's child
  have hdouble : ∑ v, ∑ u ∈ children nb t r excl v, a u =
      ∑ u, if t u ∈ nb u ∧ (excl = true → u ≠ r) then a u else 0 := by
    have hin : ∀ v, ∑ u ∈ children nb t r excl v, a u =
        ∑ u, if u ∈ children nb t r excl v then a u else 0 := by
      intro v
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp only [hin]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_eq_single (t u)]
    · by_cases h1 : t u ∈ nb u
      · have h1' : u ∈ nb (t u) := (hnb _ _).2 h1
        simp [children, h1, h1']
      · have h1' : u ∉ nb (t u) := fun h' => h1 ((hnb _ _).1 h')
        simp [children, h1, h1']
    · intro v _ hv
      simp [children, Ne.symm hv]
    · simp
  have hsum : ∑ v, a v = ∑ v, c v + ∑ v, ∑ u ∈ children nb t r excl v, a u := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => h v
  rw [hdouble] at hsum
  -- split off the root
  have hrest : ∑ u ∈ univ.erase r, (if t u ∈ nb u ∧ (excl = true → u ≠ r) then a u else 0) =
      ∑ u ∈ univ.erase r, a u := by
    refine Finset.sum_congr rfl fun u hu => ?_
    have hur : u ≠ r := Finset.ne_of_mem_erase hu
    simp [ht u hur, hur]
  have hroot : (if t r ∈ nb r ∧ (excl = true → r ≠ r) then a r else 0) =
      (if excl = false ∧ t r ∈ nb r then a r else 0) := by
    cases excl <;> simp [and_comm]
  have e1 := (Finset.add_sum_erase univ a (Finset.mem_univ r)).symm
  have e2 := (Finset.add_sum_erase univ
    (fun u => if t u ∈ nb u ∧ (excl = true → u ≠ r) then a u else 0) (Finset.mem_univ r)).symm
  rw [e1, e2, hrest, hroot] at hsum
  have h3 : a r + ∑ u ∈ univ.erase r, a u =
      ((∑ v, c v) + (if excl = false ∧ t r ∈ nb r then a r else 0)) + ∑ u ∈ univ.erase r, a u := by
    rw [hsum]; abel
  exact add_right_cancel h3

/-- If the root is not counted as a child, the root value is the total sum (Lemma 3.3). -/
theorem treeSum_root_eq (nb : V → Finset V) (hnb : ∀ u v, u ∈ nb v ↔ v ∈ nb u) (r : V)
    (t : V → V) (ht : ∀ v, v ≠ r → t v ∈ nb v) (excl : Bool) (a c : V → K)
    (h : ∀ v, a v = c v + ∑ u ∈ children nb t r excl v, a u)
    (hr : excl = true ∨ t r ∉ nb r) : a r = ∑ v, c v := by
  have := treeSum_root nb hnb r t ht excl a c h
  have hn : ¬ (excl = false ∧ t r ∈ nb r) := by
    rintro ⟨h1, h2⟩
    rcases hr with hr | hr
    · rw [hr] at h1; exact Bool.noConfusion h1
    · exact hr h2
  simpa [hn] using this

/-- If the root is counted as a child, the total sum vanishes. -/
theorem treeSum_eq_zero (nb : V → Finset V) (hnb : ∀ u v, u ∈ nb v ↔ v ∈ nb u) (r : V)
    (t : V → V) (ht : ∀ v, v ≠ r → t v ∈ nb v) (a c : V → K)
    (h : ∀ v, a v = c v + ∑ u ∈ children nb t r false v, a u) (hr : t r ∈ nb r) :
    ∑ v, c v = 0 := by
  have := treeSum_root nb hnb r t ht false a c h
  simp only [hr, and_self, ite_true] at this
  have h2 := congrArg (fun z => z - a r) this
  simp only [sub_self, add_sub_cancel_right] at h2
  exact h2.symm

omit [Fintype V] [DecidableEq V] in
/-- **Solvability of the tree-sum checks.** If every child has depth one more than its parent and
depths are bounded, the checks `a v = c v + ∑_{u ∈ C v} a u` have a solution. -/
theorem exists_treeSol (C : V → Finset V) (d : V → ℕ) (N : ℕ) (hd : ∀ v, d v < N)
    (hC : ∀ v, ∀ u ∈ C v, d u = d v + 1) (c : V → K) :
    ∃ a : V → K, ∀ v, a v = c v + ∑ u ∈ C v, a u := by
  let aux : ℕ → V → K := fun k => Nat.rec c (fun _ prev v => c v + ∑ u ∈ C v, prev u) k
  have hsucc : ∀ k v, aux (k + 1) v = c v + ∑ u ∈ C v, aux k u := fun _ _ => rfl
  have stab : ∀ k v, N ≤ k + d v → aux k v = aux (k + 1) v := by
    intro k
    induction k with
    | zero => intro v hv; have := hd v; omega
    | succ k ih =>
      intro v hv
      rw [hsucc k v, hsucc (k + 1) v]
      congr 1
      refine Finset.sum_congr rfl fun u hu => ?_
      exact ih u (by rw [hC v u hu]; omega)
  refine ⟨aux N, fun v => ?_⟩
  rw [stab N v (by omega), hsucc]

end Podc.InteractiveDistributedProofs
