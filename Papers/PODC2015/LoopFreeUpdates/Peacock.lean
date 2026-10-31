import Papers.PODC2015.LoopFreeUpdates.PeacockCount

/-!
# Peacock (Algorithm 1) and Theorem 3 of Ludwig–Marcinkowski–Schmid (PODC 2015)

`peacock I` is Algorithm 1, written recursively over the merged line:
while the current line has at least two nodes, Peacock
* (odd round, *shortcut*) updates the greedy selection `C = I.greedy` of far-reaching forward
  dashed edges (Algorithm 1, lines 6–9);
* (even round, *prune*) updates all nodes not on the `s`–`d` path, `prune C` (line 11);
* merges every updated node into the target of its new rule; the result is again a line
  (`reduce`, Lemma 3), on which Peacock continues.

Theorem 3: the resulting schedule is relaxed loop-free (`peacock_isRLF`) and has at most
`2 log_{3/2} n` rounds, `n` being the number of nodes (`peacock_length_le`).
-/

set_option linter.unusedSectionVars false

namespace Podc.LoopFreeUpdates

open Relation

variable {V : Type*} [DecidableEq V]

namespace Instance

/-- **Algorithm 1 (Peacock)**: the list of rounds `U₁, U₂, …`. -/
def peacock (I : Instance V) : List (Finset V) :=
  if _h : I.old.length ≤ 1 then [] else
    I.greedy :: I.prune I.greedy :: peacock (I.reduce I.greedy_good)
termination_by I.old.length
decreasing_by exact I.greedy_good.reduce_length_lt (by omega)

variable (I : Instance V)

theorem peacock_of_le_one (h : I.old.length ≤ 1) : I.peacock = [] := by
  rw [peacock]; simp [h]

theorem peacock_of_two_le (h : 2 ≤ I.old.length) :
    I.peacock = I.greedy :: I.prune I.greedy :: (I.reduce I.greedy_good).peacock := by
  rw [peacock]; simp [show ¬ I.old.length ≤ 1 by omega]

theorem eq_d_of_length_le_one (h : I.old.length ≤ 1) {v : V} (hv : v ∈ I.old) : v = I.d := by
  have h1 := I.pos₁_lt hv
  have h2 := I.pos₁_d
  exact I.pos₁_inj hv I.d_mem (by omega)

/-- The invariants of Peacock: rounds are disjoint sets of nodes, every node except the destination
is updated, and every round is relaxed loop-free. -/
theorem peacock_spec : ∀ (n : ℕ) (I : Instance V), I.old.length = n →
    (∀ r ∈ I.peacock, r ⊆ I.nodes) ∧ I.peacock.Pairwise Disjoint ∧
    (∀ v ∈ I.nodes, v ≠ I.d → ∃ r ∈ I.peacock, v ∈ r) ∧
    (∀ (t : ℕ) (ht : t < I.peacock.length), ∀ X ⊆ I.peacock[t],
      I.RelaxedLoopFree (done I.peacock t ∪ X)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro I hn
    by_cases h1 : I.old.length ≤ 1
    · rw [I.peacock_of_le_one h1]
      refine ⟨by simp, by simp, fun v hv hvd => ?_, by simp⟩
      exact absurd (I.eq_d_of_length_le_one h1 ((I.mem_nodes).1 hv)) hvd
    have h2 : 2 ≤ I.old.length := by omega
    set C := I.greedy
    have hC : I.GoodSelection C := I.greedy_good
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih _ (hn ▸ hC.reduce_length_lt h2) (I.reduce hC) rfl
    have hsub' : ∀ r ∈ (I.reduce hC).peacock, ∀ v ∈ r, v ∈ I.old ∧ I.Keep C v := by
      intro r hr v hv
      exact (hC.mem_reduce_old).1 (((I.reduce hC).mem_nodes).1 (ih1 r hr hv))
    rw [I.peacock_of_two_le h2]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr v hv
      rw [I.mem_nodes]
      simp only [List.mem_cons] at hr
      rcases hr with rfl | rfl | hr
      · exact I.mem_old_of_fwd (hC.fwd v hv)
      · exact ((mem_prune).1 hv).1
      · exact (hsub' r hr v hv).1
    · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ ih2)
      · intro r hr
        simp only [List.mem_cons] at hr
        rw [Finset.disjoint_left]
        rcases hr with rfl | hr
        · intro v hv hv'; exact ((mem_prune).1 hv').2.1 hv
        · intro v hv hv'; exact (hsub' r hr v hv').2.1 hv
      · intro r hr
        rw [Finset.disjoint_left]
        intro v hv hv'; exact (hsub' r hr v hv').2.2 ((mem_prune).1 hv).2.2
    · intro v hv hvd
      by_cases hvC : v ∈ C
      · exact ⟨C, List.mem_cons_self .., hvC⟩
      by_cases hin : I.Inside C v
      · exact ⟨I.prune C, List.mem_cons_of_mem _ (List.mem_cons_self ..), (mem_prune).2 ⟨(I.mem_nodes).1 hv, hvC, hin⟩⟩
      · obtain ⟨r, hr, hvr⟩ := ih3 v (((I.reduce hC).mem_nodes).2
          ((hC.mem_reduce_old).2 ⟨(I.mem_nodes).1 hv, hvC, hin⟩)) (by rwa [hC.reduce_d])
        exact ⟨r, by simp [hr], hvr⟩
    · intro t ht X hX
      match t, ht, hX with
      | 0, _, hX =>
        rw [done_zero, Finset.empty_union]
        exact (hC.odd_round hX).relaxed
      | 1, _, hX =>
        rw [done_cons_succ, done_zero, Finset.union_empty]
        exact hC.even_round hX
      | t + 2, ht, hX =>
        rw [done_cons_succ, done_cons_succ, ← Finset.union_assoc, Finset.union_assoc]
        exact hC.rlf_of_reduce (ih4 t (by simpa using ht) X (by simpa using hX))

/-- **Theorem 3** (correctness part): Peacock computes a relaxed loop-free schedule. -/
theorem peacock_isRLF : I.IsRLF I.peacock := by
  obtain ⟨-, h2, h3, h4⟩ := peacock_spec _ I rfl
  exact ⟨⟨h2, fun v hv => h3 v ((I.mem_nodes).2 (I.mem_old_of_mem_toUpdate hv))
    (I.ne_d_of_mem_toUpdate hv)⟩, h4⟩

/-- **Theorem 3** (round bound): Peacock uses at most `2 log_{3/2} n` rounds, where `n` is the number
of nodes. -/
theorem peacock_length_le :
    (I.peacock.length : ℝ) ≤ 2 * Real.logb (3 / 2) I.old.length := by
  suffices ∀ (n : ℕ) (I : Instance V), I.old.length = n →
      (I.peacock.length : ℝ) ≤ 2 * Real.logb (3 / 2) I.old.length from this _ I rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro I hn
    have hpos := I.length_pos
    by_cases h1 : I.old.length ≤ 1
    · rw [I.peacock_of_le_one h1]
      have : (1 : ℝ) ≤ I.old.length := by exact_mod_cast hpos
      have := Real.logb_nonneg (b := 3 / 2) (by norm_num) this
      simp; linarith
    have h2 : 2 ≤ I.old.length := by omega
    have hC := I.greedy_good
    have hred := hC.reduce_length h2
    have hih := ih _ (hn ▸ hC.reduce_length_lt h2) (I.reduce hC) rfl
    rw [I.peacock_of_two_le h2]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    have hN' : (1 : ℝ) ≤ (I.reduce hC).old.length := by exact_mod_cast (I.reduce hC).length_pos
    have hle : ((I.reduce hC).old.length : ℝ) ≤ I.old.length * (3 / 2)⁻¹ := by
      have : (3 * (I.reduce hC).old.length + 1 : ℝ) ≤ 2 * I.old.length := by exact_mod_cast hred
      norm_num; linarith
    have hlog := Real.logb_le_logb_of_le (b := 3 / 2) (by norm_num) (by linarith) hle
    have hNpos : (0 : ℝ) < I.old.length := by exact_mod_cast hpos
    rw [Real.logb_mul hNpos.ne' (by norm_num), Real.logb_inv,
      Real.logb_self_eq_one (by norm_num)] at hlog
    linarith

/-- **Theorem 3** (Ludwig–Marcinkowski–Schmid, PODC 2015): Peacock solves every instance with a
relaxed loop-free schedule of `O(log n)` rounds; precisely, at most `2 log_{3/2} n` rounds, where `n`
is the number of nodes. -/
theorem theorem3 :
    I.IsRLF I.peacock ∧ (I.peacock.length : ℝ) ≤ 2 * Real.logb (3 / 2) I.old.length :=
  ⟨I.peacock_isRLF, I.peacock_length_le⟩

/-- Every instance has a relaxed loop-free schedule with at most `2 log_{3/2} n` rounds. -/
theorem exists_rlf_log :
    ∃ k : ℕ, (k : ℝ) ≤ 2 * Real.logb (3 / 2) I.old.length ∧ I.HasRLF k :=
  ⟨I.peacock.length, I.peacock_length_le, I.peacock, rfl, I.peacock_isRLF⟩

end Instance

end Podc.LoopFreeUpdates
